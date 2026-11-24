# Introducing `graviton-cert`: A Lean 4 Open Standard for Boundary-Explicit Research Notes

*By Graviton Research Foundation · gravitonresearch.org*

> “We want researchers to be able to explain both what their methods reveal and where those methods stop.”

---

### The Problem With How Scientific Claims Are Published

Open almost any theoretical physics, quantum biology, or computational science paper today and you will find three very different kinds of statements woven seamlessly into the same prose:

1. **Exact mathematical deductions** (algebraic identities, conservation laws, exclusion inequalities).
2. **Scoped numerical checks** (finite-grid sweeps, parameter scans, toy models).
3. **Unmeasured empirical or theoretical assumptions** (biological plausibility, UV completion, unmodeled confounders).

When a paper ships with a Python script, a reader still has to trust floating-point tolerances, silent scope jumps, and prose disclaimers about what a calculation actually proved. And when a foundational lemma breaks—or a key parameter turns out to be unmeasured—there is no compiler to tell you *which* downstream claims still hold and *which* ones collapse.

Formalization libraries like **Mathlib** and **Physlib** are doing extraordinary work formalizing textbook mathematics and physics from the bottom up. What has been missing is a lightweight, open-source standard at the **research-note layer**: a way for working scientists and independent labs to publish **proof-carrying research notes** whose logical boundaries are audited mechanically.

Today we are open-sourcing **`graviton-cert` v0.1** (MIT License) — a zero-dependency Lean 4 framework and kernel axiom auditor for **Boundary-Explicit Science**.

---

### How `graviton-cert` Works

Instead of trying to formalize all of nature from first principles, `graviton-cert` enforces a strict contract on every published research note. Each study compiles in Lean 4 into an **`epistemic-manifest.json`** and **`VERIFICATION.md`** generated directly from Lean's kernel via `Lean.collectAxioms`, separating every claim into four explicit buckets:

1. **Kernel-Verified Claims** — Theorems, algebraic repairs, null benchmarks, and exclusion bounds verified with **zero `sorryAx`** and **zero custom axioms**. If a single claim introduces `sorry` or an unapproved axiom, `lake exe graviton-cert` exits non-zero in CI.
2. **Explicit Assumptions** — The exact mathematical, physical, or discretization regime required.
3. **Explicit Non-Claims (`does_not_establish`)** — What the proof formally does *not* prove, attached directly to the machine-checked record so it travels with the result.
4. **Open Empirical Gates** — Unmeasured wet-lab, observational, or theoretical obligations that mathematics alone cannot close. In pure math, a `sorry` means *"prove this lemma."* In `graviton-cert`, an `EmpiricalGate` means **"measure this exact quantity with this control before advancing the hypothesis."**

---

### Eating Our Own Cooking: Three Live Studies Verified Today

To make the standard concrete from day one, we upgraded all three active research lines on [gravitonresearch.org](https://gravitonresearch.org) into `graviton-cert` v0.1 (**16/16 kernel-checked claims, 0 `sorryAx`, 0 custom axioms, 6 quarantined open gates**):

- **Quantum Gravity (`TimelessGravity`):**
  - Proves universally that any smooth pure-gauge perturbation $h_{\mu\nu} = \partial_\mu A_\nu + \partial_\nu A_\mu$ has identically vanishing linearized Riemann curvature $R^{(1)}_{abcd} = 0$ across all 256 index combinations.
  - Upgrades our earlier prose analytical deduction into a kernel proof: source conservation ($\partial^\mu \mathcal{E}_{\mu\nu} = 0$, $\mu^2 \ne 0$) combined with $\partial^\mu h_{\mu\nu} = 0$ forces $\partial_\nu h = 0$, ruling out nonconstant radial trace profiles.
  - Encodes an executable `GeometricMatterAcceptanceGate` that formally rejects pure-gauge coordinate artifacts.
- **Quantum Biology (`SpinChemistry` — Research Note 01):**
  - Proves the **Universal Pathway Exclusion Theorem**: for *any* bounded biological parameters satisfying $G_{\max} F_{\max} B_\Phi / k_{\min} < \delta_y$, the predicted neuronal current change strictly satisfies $|\Delta\hat{y}| < \delta_y$—while quarantining all 4 unmeasured biophysical quantities ($F_{\text{RP}}, \Delta\Phi_S, k_{\text{clear}}, g'(x_0)$) as typed `EmpiricalGate`s.
- **Quantum Many-Body Dynamics (`ObservationWindow` — Research Note 02):**
  - Formally verifies the exact 4-qubit Jordan–Wigner Majorana Clifford algebra ($\{\psi_i, \psi_j\} = \delta_{ij} I$ for all 64 pairs) using only `propext`.
  - Proves **exact spectator conservation** ($[P_{abcd}, \psi_8] = 0$) across all 35 quartic operators (all 180 Hamiltonians and all continuous times).
  - Proves that the two control perturbations $P_{1267}$ and $P_{4567}$ commute term-by-term with $H_0$, while the reference perturbation $P_{1235}$ anticommutes with $P_{1245} \in H_0$ *(Lean actually caught a manual index guess during compilation—exactly what a proof kernel is for)*.
  - Formalizes how a single verified window reversal (`[12, 24]` vs. `[36, 48]`) refutes global sign invariance without invalidating the bounded-window result.

---

### How Any Researcher or Lab Can Adopt `graviton-cert`

You do not need a 2 GB dependency tree or a full formalization of QFT to use `graviton-cert`. It compiles in seconds on standard Lean 4 (`v4.36.0`) with zero external dependencies:

1. **Define your study's algebraic/exclusion core** in a Lean 4 module under `Studies/`.
2. **Attach a `StudyCertificate`** listing your exact `assumptions`, `claims`, `doesNotEstablish` boundaries, and unmeasured `openGates`.
3. **Run the kernel auditor in CI:**
   ```bash
   lake build
   lake exe graviton-cert
   ```
4. **Embed `epistemic-manifest.json`** straight into your research website, preprint repository, or supplementary materials so readers—and AI agents—can inspect what was proved, what was assumed, and what still needs an experiment.

---

### What Comes Next (v0.2 Roadmap)

- **Rigorous continuous-time numerics (`OW-GATE-01`):** Replacing floating-point witnesses with rational Taylor-remainder / interval-arithmetic certificates inside Lean 4.
- **Hamiltonian ghost-freedom checks (`GeometricMatterAcceptanceGate`):** Integrating Sum-of-Squares positivity certificates to check quadratic stability for modified-gravity models.
- **`Physlib` interoperability:** Optional adapters so studies can import `Physlib`'s Lorentz tensors and quantum-information primitives directly.

Science moves faster when our claims carry their own receipts—and their own stop signs.

Explore the live Kernel Audit Ledger on **[gravitonresearch.org](https://gravitonresearch.org)**, open a PR with your own study at **[github.com/GravitonR/graviton-cert](https://github.com/GravitonR/graviton-cert)**, or fork the standard for your lab.
