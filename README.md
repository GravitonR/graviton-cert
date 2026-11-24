# `graviton-cert`

**Boundary-Explicit Science in Lean 4** — an open-source framework and kernel-verified research ledger from the [Graviton Research Foundation](https://gravitonresearch.org).

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

## Included Certified Studies (v0.2 — 24/24 Kernel-Verified Claims)

All active research lines on `gravitonresearch.org` are formally verified with zero external dependencies beyond Lean 4's core kernel (`0 sorryAx`, `0 custom axioms`, zero floating-point proofs):

| Study | Domain | Key Machine-Checked Results |
| :--- | :--- | :--- |
| **`TimelessGravity`** (7 claims) | Quantum Gravity / Linearized GR | Universal pure-gauge Riemann vanishing (`R^(1)_{abcd} = 0`, all 256 components); formal tensor-divergence exclusion; Eq. 9 & Eq. 22 repairs; exact radial Laplacian `∇²(e^{sr}/r) = s² e^{sr}/r`; executable `GeometricMatterAcceptanceGate`. |
| **`PageWootters`** (5 claims) | Quantum Foundations / Relational Time | Universal constraint annihilation `𝒞|Ψ_n⟩ = 0` for all `n ≥ 1`; exact conditional phase-state recovery; universal qutrit noise-model discrimination `(2/9)(V²-1)² cos 2θ` (`18/625 = 0.0288` at `V = 0.8`); exact interaction residual `‖𝒞_λ|Ψ_3⟩‖² = λ²/3`. |
| **`SpinChemistry`** (5 claims) | Quantum Biology / Kinetics | Exact steady-state & SI-unit accounting; opposite-shift antisymmetry; **Universal Pathway Exclusion Theorem** (`|Δŷ| ≤ G_max F_max B_Φ / k_min < δ_y`); 4 typed open wet-lab `EmpiricalGate`s. |
| **`ObservationWindow`** (7 claims, 0 open gates) | Quantum Many-Body Dynamics | Exact 4-qubit Majorana Clifford algebra (64 pairs); spectator conservation across all 35 quartic terms; exact 4-block 2×2 Clifford reduction of `H₀ + λP₁₂₃₅`; exact RMS ratio `α² = 9583/9983`; **zero-floating-point rational-interval proof** of the window sign reversal between `[12,24]` and `[36,48]` (`propext` only). |

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
