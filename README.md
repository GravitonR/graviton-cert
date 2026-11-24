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

## Included Certified Studies (v0.1)

All three active research lines on `gravitonresearch.org` are formally verified with zero external dependencies beyond Lean 4's core kernel:

| Study | Domain | Key Machine-Checked Results |
| :--- | :--- | :--- |
| **`TimelessGravity`** | Quantum Gravity / Linearized GR | Universal pure-gauge Riemann vanishing (`R^(1)_{abcd} = 0` for *all* smooth covectors & all 256 components); formal tensor-divergence exclusion (`∂^μ ℰ_{μν} = 0 ∧ ∂^μ h_{μν} = 0 ∧ μ² ≠ 0 → ∂_ν h = 0`); Eq. 9 & Eq. 22 algebraic repairs; executable `GeometricMatterAcceptanceGate`. |
| **`SpinChemistry`** | Quantum Biology / Kinetics | Exact steady-state & SI-unit accounting; opposite-shift antisymmetry; **Universal Pathway Exclusion Theorem** (`|Δŷ| ≤ G_max F_max B_Φ / k_min < δ_y`); 4 typed open wet-lab `EmpiricalGate`s. |
| **`ObservationWindow`** | Quantum Many-Body Dynamics | Exact 4-qubit Jordan–Wigner Majorana Clifford algebra (all 64 pairs); **Exact Spectator Conservation** (`[P_{abcd}, ψ₈] = 0` across all 35 quartic terms / 180 Hamiltonians); commuting controls `P_{1267}, P_{4567}`; non-commutativity of `P_{1235}`; formal window-reversal refutation theorem. |

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
