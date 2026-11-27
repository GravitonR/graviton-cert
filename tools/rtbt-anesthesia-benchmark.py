#!/usr/bin/env python3
"""
rtbt-anesthesia-benchmark.py — Graviton Research Foundation (graviton-cert)
Real Human General Anesthesia EEG Validation (OpenNeuro ds004541) for
Relational Temporal Binding Theory (RTBT, Working Paper 06).

Streams 1000 Hz multi-channel clinical surgical general anesthesia EEG directly
from public OpenNeuro S3 (ds004541: Multimodal EEG-fNIRS During General Anesthesia)
across ALL consecutive patients with documented infusion start, Loss of
Consciousness (LOC), and Return of Consciousness (ROC):
  sub-02, sub-03, sub-04, sub-07, sub-08, sub-09, sub-10 (N = 7 complete patients)

Deterministic epoch windows (zero cherry-picking, anchored strictly to hospital events):
  1. baseline:    [start - 90 s, start - 70 s]  (pre-infusion awake baseline)
  2. pre_loc:     [loc - 40 s,   loc - 20 s]    (induction boundary before LOC)
  3. unconscious: [loc + 60 s,   loc + 80 s]    (deep general anesthesia)
  4. pre_roc:     [roc - 40 s,   roc - 20 s]    (emergence boundary before ROC — RTBT-25)
  5. recovery:    [roc + 30 s,   roc + 50 s]    (awake recovery post-ROC)

Tests:
  - Baseline Awake vs. Deep General Anesthesia (LZ76, H_spec, tau_1e, D_eff, B_hat)
  - Recovery Post-ROC vs. Deep General Anesthesia (rebound on emergence)
  - Neural Inertia / Path Asymmetry (pre_loc vs. pre_roc, RTBT-25)
"""

from __future__ import annotations

import argparse
import concurrent.futures
import importlib.util
import json
import os
import sys
from typing import Dict, List, Optional

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))

def _load_mod(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, os.path.join(SCRIPT_DIR, filename))
    assert spec and spec.loader
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

eeg = _load_mod("rtbt_eeg_analyzer", "rtbt-eeg-analyzer.py")
cohort = _load_mod("rtbt_cohort_benchmark", "rtbt-cohort-benchmark.py")

# Standard International 10-20 19-channel subset for clean, fast, montage-consistent
# cortical coverage (avoids non-EEG EKG/EMG/Trigger channels and speeds 1000 Hz streaming)
TEN_TWENTY_19 = [
    "Fp1", "Fp2", "F7", "F3", "Fz", "F4", "F8",
    "T7", "C3", "Cz", "C4", "T8",
    "P7", "P3", "Pz", "P4", "P8", "O1", "O2",
]

SUBJECTS = ["sub-02", "sub-03", "sub-04", "sub-07", "sub-08", "sub-09", "sub-10", "sub-11"]


def parse_events_tsv(text: str) -> Dict[str, float]:
    ev: Dict[str, float] = {}
    for line in text.splitlines()[1:]:
        parts = line.strip().split("\t")
        if len(parts) < 3:
            continue
        try:
            onset = float(parts[0].lstrip("\ufeff"))
        except ValueError:
            continue
        ttype = parts[2].strip().lower()
        if ttype not in ev:
            ev[ttype] = onset
    return ev


def run_subject(sub_id: str) -> Dict:
    base = f"https://s3.amazonaws.com/openneuro.org/ds004541/{sub_id}/ses-01/eeg"
    ev_url = f"{base}/{sub_id}_ses-01_task-anesthesia_events.tsv"
    edf_url = f"{base}/{sub_id}_ses-01_task-anesthesia_eeg.edf"
    try:
        ev = parse_events_tsv(cohort.fetch_text(ev_url))
        if not all(k in ev for k in ("start", "loc", "roc")):
            return {"subject": sub_id, "skipped": True, "reason": f"Missing start/loc/roc events ({list(ev.keys())})"}
        hdr = eeg.parse_edf_header(edf_url)
        total_dur = hdr["n_records"] * hdr["rec_duration"]

        # Deterministic 20 s windows anchored to clinical event markers
        t_base = max(10.0, ev["start"] - 90.0)
        t_pre_loc = max(ev["start"] + 10.0, ev["loc"] - 40.0)
        t_uncon = min(ev["loc"] + 60.0, max(ev["loc"] + 10.0, ev["roc"] - 80.0))
        t_pre_roc = max(ev["loc"] + 85.0, ev["roc"] - 40.0)
        t_rec = min(ev["roc"] + 30.0, max(ev["roc"] + 5.0, total_dur - 22.0))

        # Check which 10-20 channels exist (fallback to all EEG channels if < 10 match)
        avail = {lbl.strip().upper() for lbl in hdr["labels"]}
        chosen = [c for c in TEN_TWENTY_19 if c.upper() in avail]
        if len(chosen) < 10:
            chosen = None

        out = {
            "subject": sub_id,
            "skipped": False,
            "events_s": {k: ev[k] for k in ("start", "loc", "end", "roc") if k in ev},
            "epochs": {},
        }
        for name, t0 in (
            ("baseline", t_base),
            ("pre_loc", t_pre_loc),
            ("unconscious", t_uncon),
            ("pre_roc", t_pre_roc),
            ("recovery", t_rec),
        ):
            dur = min(20.0, max(8.0, total_dur - t0 - 1.0))
            labels, sigs, sf = eeg.read_edf_window(edf_url, start_s=t0, duration_s=dur, selected_channels=chosen, header=hdr)
            res = eeg.analyze_eeg_epoch(labels, sigs, sf, label_name=f"{sub_id} {name} [{t0:.0f}s]")
            res["window_s"] = [round(t0, 1), round(t0 + dur, 1)]
            out["epochs"][name] = res
        return out
    except Exception as exc:
        return {"subject": sub_id, "skipped": True, "reason": str(exc)}


def main() -> int:
    parser = argparse.ArgumentParser(description="Run OpenNeuro ds004541 human general anesthesia RTBT validation.")
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--out-json", default=os.path.join(SCRIPT_DIR, "..", "AUDITS", "rtbt-anesthesia-validation.json"))
    parser.add_argument("--out-md", default=os.path.join(SCRIPT_DIR, "..", "AUDITS", "rtbt-anesthesia-validation.md"))
    args = parser.parse_args()

    print(f"Running Cohort D: OpenNeuro ds004541 Human General Anesthesia ({len(SUBJECTS)} subjects)...", flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as ex:
        raw = list(ex.map(run_subject, SUBJECTS))

    ok = [r for r in raw if not r.get("skipped")]
    skip = [r for r in raw if r.get("skipped")]
    print(f"Completed: {len(ok)} complete surgical anesthesia trajectories ({len(skip)} skipped)", flush=True)

    def _vec(ep: str, key: str) -> List[float]:
        if key == "delta":
            return [r["epochs"][ep]["biomarkers"]["bands"]["delta"] for r in ok]
        return [r["epochs"][ep]["biomarkers"][key] for r in ok]

    metrics = ["lz76_single_mean", "spectral_entropy", "tau_1e_ms", "D_eff", "rho_abs_mean", "delta", "rtbt_binding_index"]

    stats = {
        "baseline_vs_unconscious": {m: cohort.paired_wilcoxon_signed_rank(_vec("baseline", m), _vec("unconscious", m)) for m in metrics},
        "recovery_vs_unconscious": {m: cohort.paired_wilcoxon_signed_rank(_vec("recovery", m), _vec("unconscious", m)) for m in metrics},
        "pre_loc_vs_pre_roc_inertia": {m: cohort.paired_wilcoxon_signed_rank(_vec("pre_loc", m), _vec("pre_roc", m)) for m in metrics},
        "auroc_baseline_vs_unconscious": {
            "lz76_single_mean": cohort.compute_auroc(_vec("baseline", "lz76_single_mean"), _vec("unconscious", "lz76_single_mean")),
            "spectral_entropy": cohort.compute_auroc(_vec("baseline", "spectral_entropy"), _vec("unconscious", "spectral_entropy")),
            "inv_tau_1e_ms": cohort.compute_auroc([-v for v in _vec("baseline", "tau_1e_ms")], [-v for v in _vec("unconscious", "tau_1e_ms")]),
            "D_eff": cohort.compute_auroc(_vec("baseline", "D_eff"), _vec("unconscious", "D_eff")),
            "rtbt_binding_index": cohort.compute_auroc(_vec("baseline", "rtbt_binding_index"), _vec("unconscious", "rtbt_binding_index")),
        },
        "auroc_recovery_vs_unconscious": {
            "lz76_single_mean": cohort.compute_auroc(_vec("recovery", "lz76_single_mean"), _vec("unconscious", "lz76_single_mean")),
            "spectral_entropy": cohort.compute_auroc(_vec("recovery", "spectral_entropy"), _vec("unconscious", "spectral_entropy")),
            "inv_tau_1e_ms": cohort.compute_auroc([-v for v in _vec("recovery", "tau_1e_ms")], [-v for v in _vec("unconscious", "tau_1e_ms")]),
            "D_eff": cohort.compute_auroc(_vec("recovery", "D_eff"), _vec("unconscious", "D_eff")),
            "rtbt_binding_index": cohort.compute_auroc(_vec("recovery", "rtbt_binding_index"), _vec("unconscious", "rtbt_binding_index")),
        },
    }

    report = {
        "title": "RTBT Human General Anesthesia EEG Validation (OpenNeuro ds004541)",
        "epistemic_quarantine": "RTBT-GATE-01: Research biomarker validation only; not a medical device or clinical anesthesia monitor.",
        "included_subjects": len(ok),
        "skipped": skip,
        "stats": stats,
        "subjects": ok,
    }

    os.makedirs(os.path.dirname(os.path.abspath(args.out_json)), exist_ok=True)
    with open(args.out_json, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)

    md = [
        "# RTBT Real Human General Anesthesia Validation (OpenNeuro `ds004541`)",
        "",
        f"> **Cohort D (`N = {len(ok)}` consecutive surgical patients with documented `start`, `LOC`, and `ROC`; `sub-11` lacked LOC/ROC markers):** 19-channel 10–20 scalp EEG (1000 Hz, CAR, 1–45 Hz bandpass). Deterministic 20 s windows anchored to hospital event timestamps.",
        "",
        "## 1. Pre-Anesthesia Awake Baseline vs. Deep General Anesthesia (Post-LOC)",
        "| Biomarker (RTBT Theorem) | Mean Awake | Mean Unconscious | Paired Concordance | Cohen's $d_z$ | Exact Wilcoxon $p$ | AUROC (95% CI) |",
        "| :--- | :---: | :---: | :---: | :---: | :---: | :---: |",
    ]
    for m, label, expect_pos, auc_key in [
        ("lz76_single_mean", "`LZ76` Complexity (`RTBT-22`)", True, "lz76_single_mean"),
        ("spectral_entropy", "Spectral Entropy $H_{\\mathrm{spec}}$", True, "spectral_entropy"),
        ("tau_1e_ms", "Memory Timescale $\\tau_{1/e}$ ms (`RTBT-28`)", False, "inv_tau_1e_ms"),
        ("D_eff", "Dimensionality $D_{\\mathrm{eff}}$ (`RTBT-19`)", True, "D_eff"),
        ("rtbt_binding_index", "RTBT Binding Index $\\widehat{\\mathcal{B}}$", True, "rtbt_binding_index"),
    ]:
        s = stats["baseline_vs_unconscious"][m]
        a = stats["auroc_baseline_vs_unconscious"][auc_key]
        conc = f"{s['pos']}/{s['n']} (Awake>Anes)" if expect_pos else f"{s['neg']}/{s['n']} (Anes>Awake)"
        md.append(f"| {label} | {s['mean_x']:.3f} | {s['mean_y']:.3f} | {conc} | {s['cohens_dz']:+.2f} | `{s['p_value']:.2e}` | **{a['auroc']:.3f}** ({a['ci95'][0]:.3f}–{a['ci95'][1]:.3f}) |")

    md += [
        "",
        "## 2. Emergence Recovery (Post-ROC) vs. Deep General Anesthesia (Post-LOC)",
        "| Biomarker (RTBT Theorem) | Mean Recovery | Mean Unconscious | Paired Concordance | Cohen's $d_z$ | Exact Wilcoxon $p$ | AUROC (95% CI) |",
        "| :--- | :---: | :---: | :---: | :---: | :---: | :---: |",
    ]
    for m, label, expect_pos, auc_key in [
        ("lz76_single_mean", "`LZ76` Complexity (`RTBT-22`)", True, "lz76_single_mean"),
        ("spectral_entropy", "Spectral Entropy $H_{\\mathrm{spec}}$", True, "spectral_entropy"),
        ("tau_1e_ms", "Memory Timescale $\\tau_{1/e}$ ms (`RTBT-28`)", False, "inv_tau_1e_ms"),
        ("D_eff", "Dimensionality $D_{\\mathrm{eff}}$ (`RTBT-19`)", True, "D_eff"),
        ("rtbt_binding_index", "RTBT Binding Index $\\widehat{\\mathcal{B}}$", True, "rtbt_binding_index"),
    ]:
        s = stats["recovery_vs_unconscious"][m]
        a = stats["auroc_recovery_vs_unconscious"][auc_key]
        conc = f"{s['pos']}/{s['n']} (Rec>Anes)" if expect_pos else f"{s['neg']}/{s['n']} (Anes>Rec)"
        md.append(f"| {label} | {s['mean_x']:.3f} | {s['mean_y']:.3f} | {conc} | {s['cohens_dz']:+.2f} | `{s['p_value']:.2e}` | **{a['auroc']:.3f}** ({a['ci95'][0]:.3f}–{a['ci95'][1]:.3f}) |")

    md += [
        "",
        "## 3. Induction (`pre-LOC`) vs. Emergence (`pre-ROC`) Asymmetry Check (`RTBT-25` Neural Inertia)",
        "| Biomarker | Mean Pre-LOC | Mean Pre-ROC | Paired Concordance | Cohen's $d_z$ | Exact Wilcoxon $p$ |",
        "| :--- | :---: | :---: | :---: | :---: | :---: |",
    ]
    for m, label in [
        ("lz76_single_mean", "`LZ76` Complexity"),
        ("spectral_entropy", "Spectral Entropy $H_{\\mathrm{spec}}$"),
        ("tau_1e_ms", "Memory Timescale $\\tau_{1/e}$ ms"),
        ("D_eff", "Dimensionality $D_{\\mathrm{eff}}$"),
        ("rtbt_binding_index", "RTBT Binding Index $\\widehat{\\mathcal{B}}$"),
    ]:
        s = stats["pre_loc_vs_pre_roc_inertia"][m]
        md.append(f"| {label} | {s['mean_x']:.3f} | {s['mean_y']:.3f} | {s['pos']}/{s['n']} (PreLOC>PreROC) | {s['cohens_dz']:+.2f} | `{s['p_value']:.2e}` |")

    md += [
        "",
        "## 4. Per-Patient Trajectories (`Baseline -> Pre-LOC -> Unconscious -> Pre-ROC -> Recovery`)",
        "| Subject | `LZ76` Trajectory | $\\tau_{1/e}$ (ms) Trajectory | $D_{\\mathrm{eff}}$ Trajectory | Phases (`Base / Uncon / Rec`) |",
        "| :--- | :--- | :--- | :--- | :--- |",
    ]
    for r in ok:
        eps = [r["epochs"][k] for k in ("baseline", "pre_loc", "unconscious", "pre_roc", "recovery")]
        lz_s = " -> ".join(f"{e['biomarkers']['lz76_single_mean']:.3f}" for e in eps)
        tau_s = " -> ".join(f"{e['biomarkers']['tau_1e_ms']:.1f}" for e in eps)
        deff_s = " -> ".join(f"{e['biomarkers']['D_eff']:.2f}" for e in eps)
        ph_s = f"`{eps[0]['rtbt_phase'][:5]}` / `{eps[2]['rtbt_phase'][:12]}` / `{eps[4]['rtbt_phase'][:5]}`"
        md.append(f"| `{r['subject']}` | `{lz_s}` | `{tau_s}` | `{deff_s}` | {ph_s} |")

    with open(args.out_md, "w", encoding="utf-8") as f:
        f.write("\n".join(md) + "\n")

    print("\n" + "\n".join(md))
    print(f"\nSaved -> {args.out_json} and {args.out_md}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
