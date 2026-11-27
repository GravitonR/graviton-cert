# `graviton-cert`

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24570906.svg)](https://doi.org/10.5281/zenodo.24570906)

**Boundary-Explicit Science in Lean 4** — an open-source framework and kernel-verified research ledger from the [Graviton Research Foundation](https://gravitonresearch.org).

- **Working Paper 03 Preprint DOI (Warped 5D Gravity):** https://doi.org/10.5281/zenodo.24571255 (all versions: https://doi.org/10.5281/zenodo.24571254)
- **Working Paper 04 Preprint DOI (Post-Quantum HQC & Hybrid KEM):** https://doi.org/10.5281/zenodo.24576927 (all versions: https://doi.org/10.5281/zenodo.24576926)
- **Working Paper 05 Preprint DOI (Biophysical Quantum-to-Neuron Gates):** https://doi.org/10.5281/zenodo.24577879 (all versions: https://doi.org/10.5281/zenodo.24577878)
- **Software Archive DOI (`graviton-cert`):** https://doi.org/10.5281/zenodo.24570906 (all versions: https://doi.org/10.5281/zenodo.24570905)
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

## Included Certified Studies (v1.0.0 — 100/100 Kernel-Verified Claims across 13 Studies)

All active research lines on `gravitonresearch.org` are formally verified with zero external dependencies beyond Lean 4's core kernel (`0 sorryAx`, `0 custom axioms`, zero floating-point proofs):

| Study | Domain | Key Machine-Checked Results |
| :--- | :--- | :--- |
| **`RelationalTemporalBinding`** (12 claims) | Consciousness Theory / Relational Clocks (Working Paper 06 v2.0) | Graviton's hardened **Relational Temporal Binding Theory (RTBT v2.0)**: differentiated binding & anesthesia collapse (`RTBT-01`); AM–GM specious-present optimality (`τ* = √(A/B)`, `RTBT-02`); awake MRI immunity vs. critical-strip tipping (`RTBT-03`); microscopic TUR floor (`RTBT-04`); clean Classical-vs-Quantum branch decoupling (`RTBT-05`); **Seizure / Hypersynchrony Unconsciousness** (`ℬ_diff → 0` for `ρ > ρ_seiz` even at `R_φ² = 1`, `RTBT-07`); **Wilson–Cowan E/I Derivation** of recurrent gain, GABA suppression & epileptic blow-up (`RTBT-08`); **Nested Multi-Timescale Clocks & Cubic Colored-Noise Optimality** (`4E_{2,1}³ ≥ 27AB²`, `RTBT-09`); **Macroscopic Synaptic ATP Power Floor** closing the 16-order TUR gap (`RTBT-10`); quantitative empirical falsification criteria (`RTBT-11`); unified 4-regime clinical classifier (`RTBT-12`, quarantining Hard Problem `RTBT-GATE-01`). Paired with [`paper/graviton-working-paper-06.pdf`](paper/graviton-working-paper-06.pdf) and live lab at `/writing/relational-temporal-binding/`. |
| **`NeuralQuantumAssembly`** (7 claims) | Quantum Neurobiology / Cortical Assemblies (Working Paper 06) | Micro-to-macro obstructions & COGITATE-style protocols: No-Free-Coupling partial-trace invariance (`NQA-01`); Correlated-Noise Cortical Assembly Ceiling (`SNR_pop² < SNR₁²/ρ` for all `N ≥ 1`, `NQA-02`); recurrent loop shared-noise SNR invariance & readout-floor boost (`NQA-03`); bracketed 3-isotope (`¹²⁸Xe/¹²⁹Xe/¹³⁰Xe`) linear-mass confound cancellation (`NQA-04`); non-Markovian spin-yield memory bound (`NQA-05`); exact two-arm pre-registration sample-size equivalence (`NQA-06`); 4-way `AdversarialProtocolClassifier` (`NQA-07`). Paired with executable simulator [`tools/bioquantum-sim.py`](tools/bioquantum-sim.py). |
| **`BioQuantumGates`** (6 claims) | Quantum Biology / Computational Neuroscience (Working Paper 05) | Machine-checked Three-Gate standard for quantum-brain claims: 310 K decoherence separation (`≥ 10¹¹×` charge gap vs. radical-pair & `³¹P` spin windows, `BQ-01`); Johnson–Nyquist thermal noise variance `σ_I² = 4k_B T Δf / R_m` & SNR exclusion (`BQ-02`); nanoscale microdomain inverse-volume amplification & exact exclusion ceiling `V_max = |g'|ΔN / δ_y` closing `SC-04`'s caveat (`BQ-03`); matched-SAR Larmor RF confound cancellation (`BQ-04`); nonlinear LIF firing-threshold margin (`BQ-05`); executable `QuantumNeuralAcceptanceGate` quarantining the Hard Problem (`BQ-06`, `BQ-GATE-01`). Paired with Working Paper 05 PDF [`paper/graviton-working-paper-05.pdf`](paper/graviton-working-paper-05.pdf). |
| **`PostQuantumAgentAuth`** (7 claims) | Post-Quantum Protocol & AI Agent Security (`PQ-Guard`) | Merkle-batched PQ capability delegation strictly beating per-call `ML-DSA-65` signing (`>13×` wire savings at 64 calls, `PQA-01`); transitive monotone spend/expiry/bitmask attenuation (`PQA-02`); pre-execution authority firewall & replay-nonce double-spend blocking (`PQA-03`–`04`); hybrid `Ed25519 + ML-DSA` anti-downgrade (`PQA-05`); TLS 1.3 `ML-DSA-65`/`ML-KEM-768` MTU fragmentation bounds (`PQA-06`); executable `PQGuardAcceptanceGate` (`PQA-07`). Paired with [`tools/pq-probe.py`](tools/pq-probe.py) and [`tools/pq-auth.py`](tools/pq-auth.py). |
| **`PostQuantumHQC`** (10 claims) | Post-Quantum Crypto (NIST HQC 2025) | Exact `𝔽₂[X]/⟨Xⁿ-1⟩` quasi-cyclic ring laws (`HQC-01`); exact HQC decryption noise cancellation & Hamming-weight ceiling (`HQC-02`–`04`); official NIST HQC-128/192/256 MDS geometry & padding slack (`5, 11, 37` bits, `HQC-05`); formal `CVE-2025-48946` implicit-rejection collision & full-ciphertext binding fix (`HQC-06`); broken XOR combiner vs. X-Wing `MAL-BIND` & anti-downgrade (`HQC-07`–`08`); Anti-KyberSlash branchless `cmov` & division-free ML-KEM Barrett reduction (`q=3329, m=20158`, catching unsigned `20159` underflow, `HQC-09`); executable `PQCImplementationAcceptanceGate` (`HQC-10`). Paired with CLI auditor [`tools/pqc-audit.py`](tools/pqc-audit.py), live `liboqs` audit [`AUDITS/liboqs-hqc-audit.md`](AUDITS/liboqs-hqc-audit.md), and Working Paper 04 PDF [`paper/graviton-working-paper-04.pdf`](paper/graviton-working-paper-04.pdf). |
| **`QuantumErrorCorrection`** (8 claims) | Quantum Error Correction (`QEC-Bridge`) | Universal binary symplectic Pauli laws (`QEC-01`); CSS orthogonality `H_X H_Z^T = 0` & stabilizer invisibility (`QEC-02`–`03`); complete in-kernel Steane `[[7,1,3]]` (exhaustive distance-3 proof over all 128 errors, `QEC-04`) & Shor `[[9,1,3]]` (`QEC-05`); verified in-kernel `𝔽₂` Gaussian elimination kernel preservation (`QEC-06`); decoder syndrome consistency vs. silent logical symmetry-trap witness (`QEC-07`); executable `QECBridgeAcceptanceGate` (`QEC-08`). Paired with [`tools/qec-bridge.py`](tools/qec-bridge.py) (including IBM 72-qubit Bivariate Bicycle qLDPC verification). |
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
