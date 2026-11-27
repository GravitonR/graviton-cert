#!/usr/bin/env python3
"""
rtbt-propofol-benchmark.py — Graviton Research Foundation (graviton-cert)
Real Human Controlled Propofol Sedation EEG Validation (OpenNeuro ds005620)
for Relational Temporal Binding Theory (RTBT, Working Paper 06).

Dataset: Bajwa, Nilsen, Skukies, Aamodt, Ernst, Storm & Juel (2024),
  "A Repeated Awakening Study Exploring the Capacity of Complexity Measures to
  Capture Dreaming During Propofol Sedation" (OpenNeuro ds005620, CC-BY-4.0).

Streams 64-channel BrainVision EEG directly from public OpenNeuro S3 across
10 consecutive non-excluded healthy volunteers (sub-1010..sub-1054), comparing
paired within-subject:
  1. Awake Eyes-Closed Rest       (task-awake_acq-EC)
  2. Propofol Sedation Rest       (task-sed_acq-rest_run-1)
  3. Deep Propofol Sedation Rest  (task-sed2_acq-rest_run-1)
"""

from __future__ import annotations

import argparse
import concurrent.futures
import importlib.util
import json
import os
import sys
from typing import Dict, List

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))

def _load_mod(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, os.path.join(SCRIPT_DIR, filename))
    assert spec and spec.loader
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

eeg = _load_mod("rtbt_eeg_analyzer", "rtbt-eeg-analyzer.py")
cohort = _load_mod("rtbt_cohort_benchmark", "rtbt-cohort-benchmark.py")

# 10 consecutive non-excluded volunteers from ds005620 (sub-1037 excluded in participants.tsv)
SUBJECTS = [
    "sub-1010", "sub-1016", "sub-1017", "sub-1022", "sub-1024",
    "sub-1033", "sub-1036", "sub-1045", "sub-1046", "sub-1054",
]

TEN_TWENTY_19 = [
    "Fp1", "Fp2", "F7", "F3", "Fz", "F4", "F8",
    "T7", "C3", "Cz", "C4", "T8",
    "P7", "P3", "Pz", "P4", "P8", "O1", "O2",
]


def run_subject(sub_id: str) -> Dict:
    base = f"https://s3.amazonaws.com/openneuro.org/ds005620/{sub_id}/eeg"
    runs = {
        "awake_ec": f"{base}/{sub_id}_task-awake_acq-EC_eeg.vhdr",
        "propofol_sed1": f"{base}/{sub_id}_task-sed_acq-rest_run-1_eeg.vhdr",
        "propofol_sed2": f"{base}/{sub_id}_task-sed2_acq-rest_run-1_eeg.vhdr",
    }
    try:
        out = {"subject": sub_id, "skipped": False, "states": {}}
        for state, url in runs.items():
            # Deterministic 10 s clean mid-recording window (t = 15..25 s)
            labels, sigs, sf = eeg.read_brainvision_window(
                url, start_s=15.0, duration_s=10.0, selected_channels=TEN_TWENTY_19
            )
            out["states"][state] = eeg.analyze_eeg_epoch(
                labels, sigs, sf, label_name=f"{sub_id} {state} [15-25s]"
            )
        return out
    except Exception as exc:
        return {"subject": sub_id, "skipped": True, "reason": str(exc)}


def main() -> int:
    parser = argparse.ArgumentParser(description="Run OpenNeuro ds005620 human propofol sedation RTBT validation.")
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--out-json", default=os.path.join(SCRIPT_DIR, "..", "AUDITS", "rtbt-propofol-validation.json"))
    parser.add_argument("--out-md", default=os.path.join(SCRIPT_DIR, "..", "AUDITS", "rtbt-propofol-validation.md"))
    args = parser.parse_args()

    print(f"Running Cohort E: OpenNeuro ds005620 Controlled Human Propofol Sedation ({len(SUBJECTS)} subjects)...", flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as ex:
        raw = list(ex.map(run_subject, SUBJECTS))

    ok = [r for r in raw if not r.get("skipped")]
    skip = [r for r in raw if r.get("skipped")]
    print(f"Completed: {len(ok)} paired propofol volunteers ({len(skip)} skipped)", flush=True)

    def _vec(state: str, key: str) -> List[float]:
        if key == "delta":
            return [r["states"][state]["biomarkers"]["bands"]["delta"] for r in ok]
        return [r["states"][state]["biomarkers"][key] for r in ok]

    metrics = ["lz76_single_mean", "spectral_entropy", "tau_1e_ms", "D_eff", "rho_abs_mean", "delta", "rtbt_binding_index"]

    stats = {
        "awake_vs_sed1": {m: cohort.paired_wilcoxon_signed_rank(_vec("awake_ec", m), _vec("propofol_sed1", m)) for m in metrics},
        "awake_vs_sed2": {m: cohort.paired_wilcoxon_signed_rank(_vec("awake_ec", m), _vec("propofol_sed2", m)) for m in metrics},
        "auroc_awake_vs_sed2": {
            "lz76_single_mean": cohort.compute_auroc(_vec("awake_ec", "lz76_single_mean"), _vec("propofol_sed2", "lz76_single_mean")),
            "spectral_entropy": cohort.compute_auroc(_vec("awake_ec", "spectral_entropy"), _vec("propofol_sed2", "spectral_entropy")),
            "inv_tau_1e_ms": cohort.compute_auroc([-v for v in _vec("awake_ec", "tau_1e_ms")], [-v for v in _vec("propofol_sed2", "tau_1e_ms")]),
            "D_eff": cohort.compute_auroc(_vec("awake_ec", "D_eff"), _vec("propofol_sed2", "D_eff")),
            "rtbt_binding_index": cohort.compute_auroc(_vec("awake_ec", "rtbt_binding_index"), _vec("propofol_sed2", "rtbt_binding_index")),
        },
        "auroc_awake_vs_sed1": {
            "lz76_single_mean": cohort.compute_auroc(_vec("awake_ec", "lz76_single_mean"), _vec("propofol_sed1", "lz76_single_mean")),
            "spectral_entropy": cohort.compute_auroc(_vec("awake_ec", "spectral_entropy"), _vec("propofol_sed1", "spectral_entropy")),
            "inv_tau_1e_ms": cohort.compute_auroc([-v for v in _vec("awake_ec", "tau_1e_ms")], [-v for v in _vec("propofol_sed1", "tau_1e_ms")]),
            "D_eff": cohort.compute_auroc(_vec("awake_ec", "D_eff"), _vec("propofol_sed1", "D_eff")),
            "rtbt_binding_index": cohort.compute_auroc(_vec("awake_ec", "rtbt_binding_index"), _vec("propofol_sed1", "rtbt_binding_index")),
        },
    }

    report = {
        "title": "RTBT Controlled Human Propofol Sedation Validation (OpenNeuro ds005620, Bajwa et al. 2024)",
        "epistemic_quarantine": "RTBT-GATE-01: Research biomarker validation only; not a medical device.",
        "included_subjects": len(ok),
        "skipped": skip,
        "stats": stats,
        "subjects": ok,
    }

    os.makedirs(os.path.dirname(os.path.abspath(args.out_json)), exist_ok=True)
    with open(args.out_json, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)

    md = [
        "# RTBT Controlled Human Propofol Sedation Validation (OpenNeuro `ds005620`)",
        "",
        f"> **Dataset:** Bajwa, Nilsen, Skukies, Aamodt, Ernst, Storm & Juel (2024), OpenNeuro `ds005620` (CC-BY-4.0). `N = {len(ok)}` consecutive non-excluded healthy volunteers (`sub-1010`–`sub-1054`), 19-ch International 10–20 scalp EEG, CAR, `1–45 Hz`, deterministic `15–25 s` window.",
        "",
        "## 1. Awake Eyes-Closed vs. Propofol Sedation Level 1 (`task-sed`)",
        "| Biomarker (RTBT Theorem) | Mean Awake | Mean Propofol 1 | Paired Concordance | Cohen's $d_z$ | Exact Wilcoxon $p$ | AUROC (95% CI) |",
        "| :--- | :---: | :---: | :---: | :---: | :---: | :---: |",
    ]
    for m, label, expect_pos, auc_key in [
        ("lz76_single_mean", "`LZ76` Complexity (`RTBT-22`)", True, "lz76_single_mean"),
        ("spectral_entropy", "Spectral Entropy $H_{\\mathrm{spec}}$", True, "spectral_entropy"),
        ("tau_1e_ms", "Memory Timescale $\\tau_{1/e}$ ms (`RTBT-28`)", False, "inv_tau_1e_ms"),
        ("D_eff", "Dimensionality $D_{\\mathrm{eff}}$ (`RTBT-19`)", True, "D_eff"),
        ("rtbt_binding_index", "RTBT Binding Index $\\widehat{\\mathcal{B}}$", True, "rtbt_binding_index"),
    ]:
        s = stats["awake_vs_sed1"][m]
        a = stats["auroc_awake_vs_sed1"][auc_key]
        conc = f"{s['pos']}/{s['n']} (Awake>Prop)" if expect_pos else f"{s['neg']}/{s['n']} (Prop>Awake)"
        md.append(f"| {label} | {s['mean_x']:.3f} | {s['mean_y']:.3f} | {conc} | {s['cohens_dz']:+.2f} | `{s['p_value']:.2e}` | **{a['auroc']:.3f}** ({a['ci95'][0]:.3f}–{a['ci95'][1]:.3f}) |")

    md += [
        "",
        "## 2. Awake Eyes-Closed vs. Propofol Sedation Level 2 (`task-sed2`)",
        "| Biomarker (RTBT Theorem) | Mean Awake | Mean Propofol 2 | Paired Concordance | Cohen's $d_z$ | Exact Wilcoxon $p$ | AUROC (95% CI) |",
        "| :--- | :---: | :---: | :---: | :---: | :---: | :---: |",
    ]
    for m, label, expect_pos, auc_key in [
        ("lz76_single_mean", "`LZ76` Complexity (`RTBT-22`)", True, "lz76_single_mean"),
        ("spectral_entropy", "Spectral Entropy $H_{\\mathrm{spec}}$", True, "spectral_entropy"),
        ("tau_1e_ms", "Memory Timescale $\\tau_{1/e}$ ms (`RTBT-28`)", False, "inv_tau_1e_ms"),
        ("D_eff", "Dimensionality $D_{\\mathrm{eff}}$ (`RTBT-19`)", True, "D_eff"),
        ("rtbt_binding_index", "RTBT Binding Index $\\widehat{\\mathcal{B}}$", True, "rtbt_binding_index"),
    ]:
        s = stats["awake_vs_sed2"][m]
        a = stats["auroc_awake_vs_sed2"][auc_key]
        conc = f"{s['pos']}/{s['n']} (Awake>Prop)" if expect_pos else f"{s['neg']}/{s['n']} (Prop>Awake)"
        md.append(f"| {label} | {s['mean_x']:.3f} | {s['mean_y']:.3f} | {conc} | {s['cohens_dz']:+.2f} | `{s['p_value']:.2e}` | **{a['auroc']:.3f}** ({a['ci95'][0]:.3f}–{a['ci95'][1]:.3f}) |")

    md += [
        "",
        "## 3. Per-Subject Propofol Trajectories (`Awake EC -> Propofol 1 -> Propofol 2`)",
        "| Subject | `LZ76` | $H_{\\mathrm{spec}}$ | $\\tau_{1/e}$ (ms) | $D_{\\mathrm{eff}}$ | Delta |",
        "| :--- | :--- | :--- | :--- | :--- | :--- |",
    ]
    for r in ok:
        eps = [r["states"][k]["biomarkers"] for k in ("awake_ec", "propofol_sed1", "propofol_sed2")]
        md.append(
            f"| `{r['subject']}` | "
            f"`{eps[0]['lz76_single_mean']:.3f} -> {eps[1]['lz76_single_mean']:.3f} -> {eps[2]['lz76_single_mean']:.3f}` | "
            f"`{eps[0]['spectral_entropy']:.3f} -> {eps[1]['spectral_entropy']:.3f} -> {eps[2]['spectral_entropy']:.3f}` | "
            f"`{eps[0]['tau_1e_ms']:.1f} -> {eps[1]['tau_1e_ms']:.1f} -> {eps[2]['tau_1e_ms']:.1f}` | "
            f"`{eps[0]['D_eff']:.2f} -> {eps[1]['D_eff']:.2f} -> {eps[2]['D_eff']:.2f}` | "
            f"`{eps[0]['bands']['delta']:.0%} -> {eps[1]['bands']['delta']:.0%} -> {eps[2]['bands']['delta']:.0%}` |"
        )

    with open(args.out_md, "w", encoding="utf-8") as f:
        f.write("\n".join(md) + "\n")

    print("\n" + "\n".join(md))
    print(f"\nSaved -> {args.out_json} and {args.out_md}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
