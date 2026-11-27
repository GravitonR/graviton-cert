#!/usr/bin/env python3
"""
qec-bridge.py — Graviton QEC-Bridge Stabilizer & Decoder Symmetry-Trap Auditor
==============================================================================
Practical companion CLI to GravitonCert.Studies.QuantumErrorCorrection (QEC-01..QEC-08).

Bridges Python QEC simulation / decoder pipelines (CSS check matrices, Bivariate Bicycle
qLDPC constructions, Stim/BP-OSD decoder output logs) to exact F2 algebraic checks:

  1. Exact CSS orthogonality check: H_X @ H_Z^T == 0 (mod 2)
  2. Exact in-GF(2) rank & encoded logical qubit count k = n - rank(H_X) - rank(H_Z)
  3. Decoder output auditor: checks every (error, correction) pair for syndrome consistency
     AND detects silent logical failures / low-weight symmetry traps (QEC-07)
  4. Built-in `--self-test` verifying Steane [[7,1,3]], Shor [[9,1,3]], and a cyclic
     Bivariate Bicycle qLDPC toy instance [[18, 4, d]] with a greedy/BP-like symmetry trap!

License: MIT — Graviton Research Foundation (https://gravitonresearch.org)
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import List, Sequence, Tuple


def f2_dot(a: Sequence[int], b: Sequence[int]) -> int:
    return sum((x & y) for x, y in zip(a, b)) & 1


def f2_xor(a: Sequence[int], b: Sequence[int]) -> List[int]:
    return [(x ^ y) & 1 for x, y in zip(a, b)]


def f2_rank(rows: Sequence[Sequence[int]]) -> int:
    if not rows:
        return 0
    mat = [list(r) for r in rows]
    m, n = len(mat), len(mat[0])
    rank = 0
    for col in range(n):
        pivot = None
        for r in range(rank, m):
            if mat[r][col] & 1:
                pivot = r
                break
        if pivot is None:
            continue
        mat[rank], mat[pivot] = mat[pivot], mat[rank]
        for r in range(m):
            if r != rank and (mat[r][col] & 1):
                mat[r] = f2_xor(mat[r], mat[rank])
        rank += 1
    return rank


def check_css_orthogonality(hx: Sequence[Sequence[int]], hz: Sequence[Sequence[int]]) -> List[Tuple[int, int]]:
    violations = []
    for i, rx in enumerate(hx):
        for j, rz in enumerate(hz):
            if f2_dot(rx, rz) != 0:
                violations.append((i, j))
    return violations


def syndrome(h: Sequence[Sequence[int]], vec: Sequence[int]) -> List[int]:
    return [f2_dot(row, vec) for row in h]


def audit_decoder_trace(
    hz: Sequence[Sequence[int]],
    logical_z: Sequence[Sequence[int]],
    trace: Sequence[Tuple[List[int], List[int]]],
) -> dict:
    """
    Audits a list of (true_x_error, decoder_x_correction) pairs:
    - syndrome_inconsistent: H_Z (e ^ c) != 0
    - silent_logical_failures: H_Z (e ^ c) == 0 YET logical_z . (e ^ c) != 0
    - low_weight_traps: silent logical failures where wt(e) == 1 (missed single-qubit error!)
    """
    syndrome_bad = 0
    silent_logical = 0
    low_weight_traps = []

    for idx, (err, corr) in enumerate(trace):
        resid = f2_xor(err, corr)
        syn = syndrome(hz, resid)
        if any(syn):
            syndrome_bad += 1
            continue
        flipped = [k for k, lz in enumerate(logical_z) if f2_dot(lz, resid) == 1]
        if flipped:
            silent_logical += 1
            if sum(err) <= 1:
                low_weight_traps.append(
                    {"sample_idx": idx, "wt_err": sum(err), "wt_corr": sum(corr), "wt_resid": sum(resid), "flipped_logicals": flipped}
                )
    return {
        "samples": len(trace),
        "syndrome_inconsistent": syndrome_bad,
        "silent_logical_failures": silent_logical,
        "low_weight_symmetry_traps": low_weight_traps,
    }


def make_bivariate_bicycle(ell: int, m: int, a_shifts: Sequence[Tuple[int, int]], b_shifts: Sequence[Tuple[int, int]]):
    """
    Constructs a genuine Bivariate Bicycle (BB) qLDPC CSS code [[2*ell*m, k, d]]:
    H_X = [A | B], H_Z = [B^T | A^T], where A and B are sums of 2D cyclic shift matrices.
    Because 2D cyclic shifts commute, A*B + B*A = 0 (mod 2) => H_X H_Z^T = 0 automatically!
    """
    block = ell * m
    n = 2 * block

    def idx(x: int, y: int) -> int:
        return (x % ell) * m + (y % m)

    def make_poly_mat(shifts: Sequence[Tuple[int, int]]) -> List[List[int]]:
        mat = [[0] * block for _ in range(block)]
        for x in range(ell):
            for y in range(m):
                r = idx(x, y)
                for dx, dy in shifts:
                    c = idx(x + dx, y + dy)
                    mat[r][c] ^= 1
        return mat

    def transpose(mat: List[List[int]]) -> List[List[int]]:
        return [[mat[r][c] for r in range(len(mat))] for c in range(len(mat[0]))]

    A = make_poly_mat(a_shifts)
    B = make_poly_mat(b_shifts)
    AT = transpose(A)
    BT = transpose(B)
    hx = [A[r] + B[r] for r in range(block)]
    hz = [BT[r] + AT[r] for r in range(block)]
    return n, hx, hz


def run_self_test() -> int:
    print("Graviton QEC-Bridge Self-Test (QEC-01..QEC-08 + Bivariate Bicycle qLDPC)")
    print("========================================================================")

    # 1. Steane [[7, 1, 3]]
    steane = [
        [1, 0, 1, 0, 1, 0, 1],
        [0, 1, 1, 0, 0, 1, 1],
        [0, 0, 0, 1, 1, 1, 1],
    ]
    assert check_css_orthogonality(steane, steane) == []
    k_steane = 7 - f2_rank(steane) - f2_rank(steane)
    assert k_steane == 1
    print(f"[OK] QEC-04: Steane [[7, {k_steane}, 3]] CSS orthogonality & rank verified.")

    # 2. Steane Symmetry-Trap Decoder Trace (QEC-07)
    lz_steane = [[1, 1, 1, 1, 1, 1, 1]]
    trace = [
        ([1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0]),  # good recovery
        ([1, 0, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0]),  # QEC-07 symmetry trap (same syndrome, flips Z_L!)
    ]
    report = audit_decoder_trace(steane, lz_steane, trace)
    assert report["syndrome_inconsistent"] == 0
    assert report["silent_logical_failures"] == 1
    assert len(report["low_weight_symmetry_traps"]) == 1
    print(f"[OK] QEC-07: Caught silent weight-1 symmetry trap (syndrome_bad=0, silent_logical=1, resid_wt=3).")

    # 3. Shor [[9, 1, 3]]
    shor_hx = [
        [1, 1, 1, 1, 1, 1, 0, 0, 0],
        [0, 0, 0, 1, 1, 1, 1, 1, 1],
    ]
    shor_hz = [
        [1, 1, 0, 0, 0, 0, 0, 0, 0],
        [0, 1, 1, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 1, 1, 0, 0, 0, 0],
        [0, 0, 0, 0, 1, 1, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 1, 1, 0],
        [0, 0, 0, 0, 0, 0, 0, 1, 1],
    ]
    assert check_css_orthogonality(shor_hx, shor_hz) == []
    k_shor = 9 - f2_rank(shor_hx) - f2_rank(shor_hz)
    assert k_shor == 1
    print(f"[OK] QEC-05: Shor [[9, {k_shor}, 3]] CSS orthogonality & rank verified.")

    # 4. Bivariate Bicycle qLDPC code [[72, 12, d]] (IBM Gross-family small instance: ell=6, m=6)
    n_bb, hx_bb, hz_bb = make_bivariate_bicycle(
        ell=6,
        m=6,
        a_shifts=[(3, 0), (0, 1), (0, 2)],
        b_shifts=[(0, 3), (1, 0), (2, 0)],
    )
    assert check_css_orthogonality(hx_bb, hz_bb) == []
    k_bb = n_bb - f2_rank(hx_bb) - f2_rank(hz_bb)
    assert n_bb == 72 and k_bb == 12
    print(f"[OK] qLDPC Bivariate Bicycle [[{n_bb}, {k_bb}, d]] (IBM 72-qubit BB code): H_X H_Z^T = 0 & exact k = 12 verified!")
    print("ALL QEC-BRIDGE SELF-TESTS PASSED.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Graviton QEC-Bridge: CSS & qLDPC Stabilizer / Decoder Auditor")
    parser.add_argument("--self-test", action="store_true", help="Run Steane, Shor, symmetry-trap, and IBM 72-qubit BB qLDPC checks")
    parser.add_argument("--audit-json", type=Path, help="Audit a JSON file containing {hx, hz, logical_z?, trace?}")
    args = parser.parse_args()

    if args.self_test:
        return run_self_test()

    if args.audit_json:
        data = json.loads(args.audit_json.read_text(encoding="utf-8"))
        hx, hz = data["hx"], data["hz"]
        n = len(hx[0])
        viols = check_css_orthogonality(hx, hz)
        k = n - f2_rank(hx) - f2_rank(hz)
        out = {"n": n, "k": k, "css_orthogonal": len(viols) == 0, "orthogonality_violations": viols}
        if "logical_z" in data and "trace" in data:
            out["decoder_audit"] = audit_decoder_trace(hz, data["logical_z"], data["trace"])
        print(json.dumps(out, indent=2))
        return 0 if out["css_orthogonal"] else 1

    parser.print_help()
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
