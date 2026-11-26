# `graviton-cert`

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24570906.svg)](https://doi.org/10.5281/zenodo.24570906)

**Boundary-Explicit Science in Lean 4** — an open-source framework and kernel-verified research ledger from the [Graviton Research Foundation](https://gravitonresearch.org).

- **Preprint PDF DOI (Zenodo):** https://doi.org/10.5281/zenodo.24571255 (all versions: https://doi.org/10.5281/zenodo.24571254)
- **Software Archive DOI (`v0.4.1`):** https://doi.org/10.5281/zenodo.24570906 (all versions: https://doi.org/10.5281/zenodo.24570905)
- **Live Kernel Audit Ledger:** https://gravitonresearch.org/#kernel-audit
- **Repository:** https://github.com/GravitonR/graviton-cert
- **License:** MIT

> *"We want researchers to be able to explain both what their methods reveal and where those methods stop."*

## What Makes This Different

Most formalization efforts either build general textbook libraries (like `Mathlib` or `Physlib`) or ship untrusted floating-point Python scripts beside research prose.

`graviton-cert` sits at the **research-note layer**: every study compiles into a **machine-checked Epistemic Manifest** directly from Lean 4's kernel (`Lean.collectAxioms`), explicitly separating:

1. **Kernel-Verified Claims** — theorems, null benchmarks, algebraic repairs, and exclusion bounds verified with **zero `sorryAx`** and **zero custom axioms**.
2. **Explicit Assumptions** — the exact physical regime, idealizations, or numerical scope required.
3. **Explicit Non-Claims (`does_not_establish`)** — what the proof formally does *not* prove.
4. **Open Empirical Gates** — unmeasured biological, physical, or theoretical obligations that mathematics alone cannot close.

## Included Certified Studies (v0.5.0 — 60/60 Kernel-Verified Claims across 8 Studies)

All active research lines on `gravitonresearch.org` are formally verified with zero external dependencies beyond Lean 4's core kernel (`0 sorryAx`, `0 custom axioms`, zero floating-point proofs):

| Study | Domain | Key Machine-Checked Results |
| :--- | :--- | :--- |
| **`PostQuantumHQC`** (10 claims) | Post-Quantum Crypto (NIST HQC 2025) | Exact `𝔽₂[X]/⟨Xⁿ-1⟩` quasi-cyclic ring laws (`HQC-01`); exact HQC decryption noise cancellation & Hamming-weight ceiling (`HQC-02`–`04`); official NIST HQC-128/192/256 MDS geometry & padding slack (`5, 11, 37` bits, `HQC-05`); formal `CVE-2025-48946` implicit-rejection collision & full-ciphertext binding fix (`HQC-06`); broken XOR combiner vs. X-Wing `MAL-BIND` & anti-downgrade (`HQC-07`–`08`); Anti-KyberSlash branchless `cmov` & division-free ML-KEM Barrett reduction (`q=3329, m=20158`, catching unsigned `20159` underflow, `HQC-09`); executable `PQCImplementationAcceptanceGate` (`HQC-10`). Paired with CLI auditor [`tools/pqc-audit.py`](tools/pqc-audit.py). |
| **`TimelessGravity`** (12 claims) | Quantum Gravity / Linearized GR | Pure-gauge Riemann vanishing (`R^(1)_{abcd} = 0`, all 256 components); contracted 4D Bianchi identity (`∂^μ G^(1)_{μν} = 0`); ADM Fierz–Pauli uniqueness (`c₂ = 1`); de Sitter Higuchi ghost bound (`μ² ≥ 2Λ/3`); unified quadratic ghost filter; exact partially massless scalar gauge invariance iff `μ² = 2Λ/3`. |
| **`GeometricMatter`** (11 claims) | Warped 5D Gravity & Gauge Emergence | Constructive emergence of `U(1)` Maxwell curvature & field equations (`2 R̂^(1)_{5ν} = -∂^μ F_{μν} = 0`); `5 = 2+2+1` ghost-free split; relativistic rest mass & auto Fierz–Pauli; warped exponential hierarchy (`GM-07`); Goldberger–Wise stabilization & Yukawa fifth-force screening (`GM-08`); full KK-tower Higuchi survival (`GM-09`); non-Abelian `SU(2)` Yang–Mills algebra (`GM-10`); relational clock–mass duality (`GM-11`). Paired with arXiv LaTeX preprint [`paper/main.tex`](paper/main.tex). |
| **`PageWootters`** (6 claims) | Quantum Foundations / Relational Time | Universal constraint annihilation `𝒞|Ψ_n⟩ = 0` (`n ≥ 1`); exact conditional phase-state recovery; qutrit noise discrimination `(2/9)(V²-1)² cos 2θ`; universal clock-bandwidth backreaction law `‖𝒞_λ|Ψ_{m+1}⟩‖² = λ² m(m-1)(m²+1)/30` (`PW-06`). |
| **`NullConeGravity`** (5 claims) | Independent External Paper Audit | Independent Lean 4 & epistemic audit of `arXiv:2611.34924` (Raychaudhuri area ceiling, boost correlator attenuation, cycle-grouping variance & sign gap, unconditional trace finiteness, 4D harmonic/radial degeneracy) + 4 explicit open gates ([`AUDITS/arXiv-2611.34924.md`](AUDITS/arXiv-2611.34924.md)). |
| **`SpinChemistry`** (5 claims) | Quantum Biology / Kinetics | Exact steady-state & SI-unit accounting; opposite-shift antisymmetry; **Universal Pathway Exclusion Theorem** (`|Δŷ| ≤ G_max F_max B_Φ / k_min < δ_y`); 4 typed open wet-lab `EmpiricalGate`s. |
| **`CircadianTiming`** (4 claims) | Circadian Psychophysics / Timing Reliability | Scale-invariance of `CV²`; universal Kuramoto bounds `0 ≤ R_φ² ≤ 1`; statistical identifiability of `κ > 0`; tier classifier soundness (`CT-04`); paired with **ChronoScope** (`/lab/chronoscope/`). |
| **`ObservationWindow`** (7 claims, 0 open gates) | Quantum Many-Body Dynamics | Exact 4-qubit Majorana Clifford algebra (64 pairs); spectator conservation across all 35 quartic terms; exact 4-block 2×2 Clifford reduction; **zero-floating-point rational-interval proof** of the window sign reversal between `[12,24]` and `[36,48]` (`propext` only). |

## Preprint, PDF & JOSS Peer-Review Package

- **Compiled Preprint PDF:** [`paper/graviton-working-paper-03.pdf`](paper/graviton-working-paper-03.pdf) (also hosted live at https://gravitonresearch.org/writing/geometric-origin-of-matter/graviton-working-paper-03.pdf)
- **arXiv LaTeX Source:** [`paper/main.tex`](paper/main.tex) (*Machine-Checked Obstructions and Constructive Geometric Matter Emergence in Warped 5D Relational Gravity*)
- **JOSS Submission Package:** [`paper/joss/paper.md`](paper/joss/paper.md) + [`paper/joss/paper.bib`](paper/joss/paper.bib)
- **Submission & Distribution Guide:** [`paper/ARXIV-SUBMISSION-GUIDE.md`](paper/ARXIV-SUBMISSION-GUIDE.md)
- **Live Interactive Paper:** https://gravitonresearch.org/writing/geometric-origin-of-matter/

## Quickstart

Requires [Lean 4](https://lean-lang.org) (`v4.36.0`, managed via `elan`).

```bash
# 1. Build and kernel-verify every theorem
lake build

# 2. Run the kernel axiom auditor & generate epistemic-manifest.json + VERIFICATION.md
lake exe graviton-cert
```

If any registered claim introduces `sorry`, a missing declaration, or an unapproved custom axiom, `lake exe graviton-cert` exits with a non-zero status code—making it directly usable as **CI/CD for scientific truth**.

## License

MIT License — Graviton Research Foundation.
