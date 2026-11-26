#!/usr/bin/env python3
"""
pqc-audit.py — Graviton Post-Quantum Cryptography Security & Anti-CVE Auditor
=============================================================================
Practical companion CLI to GravitonCert.Studies.PostQuantumHQC (HQC-01..HQC-10).

Directly audits C, C++, Rust, Go, Python, and JS/TS codebases for the four real-world
PQC implementation failures missed by static CBOM scanners and abstract proofs:

  1. KyberSlash-class secret-dependent division/modulo (`/` or `%`, CVE-2024-36405)
  2. CVE-2025-48946 implicit-rejection missing full ciphertext/public-key binding
  3. Broken naive XOR hybrid KEM combiners (`k_cl ^ k_pq` violating MAL-BIND)
  4. Classical fallback / downgrade flags (`allow_classical_fallback`, etc.)

Also includes `--self-test` verifying official NIST HQC-128/192/256 padding-slack geometry,
𝔽₂[X]/⟨Xⁿ-1⟩ HQC decryption cancellation, and division-free ML-KEM Barrett reduction (q=3329).

License: MIT — Graviton Research Foundation (https://gravitonresearch.org)
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import List


SCAN_EXTS = {".c", ".h", ".cc", ".cpp", ".hpp", ".rs", ".go", ".py", ".js", ".ts"}

SECRET_IDENT = (
    r"(?:sk|secret|seed|msg|message|coeff|poly|syndrome|err|error|noise|"
    r"shared|ss|k_pq|k_cl|decap|key|nonce|z_rej|u_vec|v_vec)"
)

RULES = [
    {
        "id": "PQC-DIV-KYBERSLASH",
        "theorem_ref": "HQC-09",
        "severity": "HIGH",
        "pattern": re.compile(
            rf"\b{SECRET_IDENT}[a-zA-Z0-9_\[\]]*\s*(?:/|%)\s*(?:3329|q\b|Q\b|modulus|8380417|[a-zA-Z0-9_]+)",
            re.IGNORECASE,
        ),
        "message": "Potential secret-dependent division/modulo (KyberSlash / CVE-2024-36405 class). Replace `/` or `%` with division-free Barrett/Montgomery reduction (see HQC-09).",
    },
    {
        "id": "PQC-XOR-COMBINER",
        "theorem_ref": "HQC-07",
        "severity": "HIGH",
        "pattern": re.compile(
            r"(?:k_cl|ss_cl|shared_cl|classic_key|x25519_ss)\s*\^\s*(?:k_pq|ss_pq|shared_pq|pq_key|mlkem_ss|hqc_ss)"
            r"|(?:k_pq|ss_pq|shared_pq|pq_key|mlkem_ss|hqc_ss)\s*\^\s*(?:k_cl|ss_cl|shared_cl|classic_key|x25519_ss)",
            re.IGNORECASE,
        ),
        "message": "Broken naive XOR hybrid KEM combiner violates MAL-BIND ciphertext/key binding (HQC-07). Use an X-Wing/CFRG domain-separated KDF binding both keys, both ciphertexts, and both public keys.",
    },
    {
        "id": "PQC-IMPLICIT-REJ-CVE-2025-48946",
        "theorem_ref": "HQC-06",
        "severity": "HIGH",
        "pattern": re.compile(
            r"(?:implicit_reject|rej_key|reject_key|k_rej)\s*=\s*(?:prf|hash|shake[0-9]*|sha3[0-9_]*|kdf)\s*\(\s*[a-zA-Z0-9_]+\s*(?:,\s*(?:pk|pub|public_key))?\s*\)",
            re.IGNORECASE,
        ),
        "message": "Implicit-rejection derivation appears to omit full ciphertext `ct` (CVE-2025-48946 collision class, HQC-06). Bind domain tag, secret `z`, `pk`, and complete canonical `ct`.",
    },
    {
        "id": "PQC-DOWNGRADE-FALLBACK",
        "theorem_ref": "HQC-08",
        "severity": "MEDIUM",
        "pattern": re.compile(
            r"(?:allow_classical_fallback|fallback_to_classical|pqc_optional|downgrade_allowed)\s*(?:=|:)\s*(?:true|True|1)",
        ),
        "message": "Classical fallback enabled: an active middlebox downgrade collapses hybrid security to classical-only even when PQC is unbroken (HQC-08).",
    },
]


@dataclass
class Finding:
    rule_id: str
    theorem_ref: str
    severity: str
    file: str
    line: int
    snippet: str
    message: str


def scan_file(path: Path) -> List[Finding]:
    findings: List[Finding] = []
    try:
        text = path.read_text(encoding="utf-8", errors="ignore")
    except OSError:
        return findings

    for idx, raw_line in enumerate(text.splitlines(), start=1):
        stripped = raw_line.strip()
        if not stripped or stripped.startswith(("//", "#", "/*", "*")):
            continue
        for rule in RULES:
            if rule["pattern"].search(raw_line):
                findings.append(
                    Finding(
                        rule_id=rule["id"],
                        theorem_ref=rule["theorem_ref"],
                        severity=rule["severity"],
                        file=str(path),
                        line=idx,
                        snippet=stripped[:140],
                        message=rule["message"],
                    )
                )
    return findings


def scan_target(target: Path) -> List[Finding]:
    if target.is_file():
        return scan_file(target)
    findings: List[Finding] = []
    for root, dirs, files in os.walk(target):
        dirs[:] = [d for d in dirs if d not in {".git", ".lake", "node_modules", "target", "build", "dist", "__pycache__"}]
        for name in sorted(files):
            p = Path(root) / name
            if p.suffix.lower() in SCAN_EXTS:
                findings.extend(scan_file(p))
    return findings


def run_self_test() -> int:
    print("Graviton PQC-Audit Self-Test (HQC-01..HQC-10 Differential Oracle)")
    print("================================================================")

    # 1. Exhaustive Barrett reduction check across key boundaries (exact floor 20158 = floor(2^26 / 3329))
    q = 3329
    m = 20158
    for x in list(range(0, 50000)) + list(range(q * q - 50000, q * q)):
        t = (x * m) >> 26
        r = x - t * q
        assert 0 <= r < 2 * q, f"Range violation at x={x}: r={r}"
        assert r % q == x % q, f"Modulus violation at x={x}: r={r}"
    # Confirm rounded 20159 DOES underflow unsigned x < q^2 (demonstrating why Lean 4 verification matters!)
    assert 11032241 - ((11032241 * 20159) >> 26) * q < 0
    print("[OK] HQC-09: Division-free Barrett reduction (q=3329, m=20158, >>26) exact across 100,000 boundary values (and confirmed rounded 20159 underflows at x=11032241).")

    # 2. Exact NIST HQC-128 / 192 / 256 padding-slack verification
    hqc_sets = [
        ("HQC-128", 17669, 46, 16, 31, 384, 5),
        ("HQC-192", 35851, 56, 24, 33, 640, 11),
        ("HQC-256", 57637, 90, 32, 59, 640, 37),
    ]
    for name, n, n_rs, k_rs, d_rs, n_rm, expected_slack in hqc_sets:
        assert d_rs == n_rs - k_rs + 1
        slack = n - n_rs * n_rm
        assert slack == expected_slack, f"{name} slack mismatch: {slack} != {expected_slack}"
    print("[OK] HQC-05: NIST HQC-128 / 192 / 256 MDS geometry & padding slack (5, 11, 37 bits) verified.")

    # 3. Toy F2[X]/(X^n - 1) HQC exact decryption noise cancellation (HQC-02 & HQC-03)
    n = 31
    def poly_add(a, b): return [x ^ y for x, y in zip(a, b)]
    def poly_mul(a, b):
        out = [0] * n
        for i in range(n):
            acc = 0
            for j in range(n):
                acc ^= (a[j] & b[(i - j) % n])
            out[i] = acc
        return out
    def wt(a): return sum(a)

    x = [1 if i in (1, 7, 19) else 0 for i in range(n)]
    y = [1 if i in (2, 11, 23) else 0 for i in range(n)]
    h = [1 if i % 3 == 0 else 0 for i in range(n)]
    r1 = [1 if i in (0, 5) else 0 for i in range(n)]
    r2 = [1 if i in (3, 13) else 0 for i in range(n)]
    e = [1 if i in (8,) else 0 for i in range(n)]
    mG = [1 if i % 2 == 0 else 0 for i in range(n)]

    s = poly_add(x, poly_mul(h, y))
    u = poly_add(r1, poly_mul(h, r2))
    v = poly_add(poly_add(mG, poly_mul(s, r2)), e)
    dec_in = poly_add(v, poly_mul(u, y))
    eff_noise = poly_add(poly_add(poly_mul(x, r2), poly_mul(r1, y)), e)
    assert dec_in == poly_add(mG, eff_noise)
    assert wt(eff_noise) <= wt(x) * wt(r2) + wt(r1) * wt(y) + wt(e)
    print(f"[OK] HQC-02 & HQC-03: Exact F2[X]/(X^{n}-1) noise cancellation & weight bound ({wt(eff_noise)} <= {wt(x)*wt(r2)+wt(r1)*wt(y)+wt(e)}) verified.")

    # 4. Verify scanner detects all 4 Anti-CVE patterns on synthetic vulnerable sample
    vuln_sample = "\n".join([
        "uint16_t coeff_mod = secret_coeff % 3329;",
        "shared = k_cl ^ k_pq;",
        "k_rej = shake256(z_secret, pk);",
        "allow_classical_fallback = true;",
    ])
    tmp_findings = []
    for idx, line in enumerate(vuln_sample.splitlines(), 1):
        for rule in RULES:
            if rule["pattern"].search(line):
                tmp_findings.append(rule["id"])
    expected_rules = {r["id"] for r in RULES}
    assert set(tmp_findings) == expected_rules, f"Missing detections: {expected_rules - set(tmp_findings)}"
    print("[OK] HQC-06..HQC-10: Static Anti-CVE scanner caught all 4 vulnerable patterns (KyberSlash, XOR combiner, CVE-2025-48946, classical downgrade).")
    print("ALL SELF-TESTS PASSED.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Graviton PQC-Audit: Detect KyberSlash, CVE-2025-48946, broken XOR hybrid combiners, and downgrade flags."
    )
    parser.add_argument("target", nargs="?", help="File or directory to scan")
    parser.add_argument("--json", action="store_true", help="Emit JSON report")
    parser.add_argument("--self-test", action="store_true", help="Run differential oracle & scanner self-tests")
    args = parser.parse_args()

    if args.self_test:
        return run_self_test()

    if not args.target:
        parser.print_help()
        return 2

    target_path = Path(args.target)
    if not target_path.exists():
        print(f"Error: target not found: {target_path}", file=sys.stderr)
        return 2

    findings = scan_target(target_path)
    if args.json:
        print(json.dumps({"target": str(target_path), "findings": [asdict(f) for f in findings]}, indent=2))
    else:
        print(f"Graviton PQC-Audit Report — {target_path}")
        print("=" * 60)
        if not findings:
            print("PASS: 0 high/medium PQC anti-patterns detected.")
        else:
            for f in findings:
                print(f"[{f.severity}] {f.rule_id} ({f.theorem_ref}) — {f.file}:{f.line}")
                print(f"  Code: {f.snippet}")
                print(f"  Fix : {f.message}\n")
    return 1 if findings else 0


if __name__ == "__main__":
    raise SystemExit(main())
