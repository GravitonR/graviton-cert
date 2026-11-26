---
title: 'graviton-cert: Zero-Dependency Lean 4 Epistemic Verification for Physics and Quantitative Research'
tags:
  - Lean 4
  - formal verification
  - theoretical physics
  - general relativity
  - quantum mechanics
  - reproducibility
authors:
  - name: Inam Haq
    orcid: 0009-0005-4331-0409
    affiliation: 1
affiliations:
  - name: Graviton Research Foundation
    index: 1
date: 26 November 2026
bibliography: paper.bib
---

# Summary

`graviton-cert` is an open-source, zero-dependency Lean 4 framework and verification harness that compiles machine-checked mathematical claims directly into structured **Epistemic Manifests** (`epistemic-manifest.json` and `VERIFICATION.md`). Rather than building an all-purpose textbook mathematics library, `graviton-cert` operates at the *research-note layer*: every certified study pairs kernel-verified Lean 4 theorems with explicit physical assumptions, explicit non-claims (`does_not_establish`), and typed open empirical or theoretical gates (`open_gates`). Running `lake exe graviton-cert` inspects every registered theorem declaration via `Lean.collectAxioms`, enforces zero `sorryAx` and zero custom axioms, and exits with a non-zero status code if any proof regresses—enabling continuous integration for scientific rigor.

Version `v0.4.1` [@haq2026gravitoncert] ships **50 kernel-checked theorems across 7 research studies** with zero external dependencies beyond Lean 4's core library (`v4.36.0`) and zero floating-point proof steps.

# Statement of Need

Computational and theoretical research notes frequently suffer from two structural gaps:

1. **Unverified algebraic steps and floating-point drift:** Key derivations, conservation laws, exclusion bounds, and parameter-regime boundaries are commonly published only in prose or unchecked numerical scripts, making sign errors, omitted factors, or hidden assumptions easy to miss.
2. **Epistemic overclaiming:** Even when a mathematical identity is formally proved, prose summaries often blur the boundary between what a linearized or finite-dimensional model actually proves and what requires nonlinear theory or laboratory measurement.

Existing formalization ecosystems such as Mathlib [@mathlib2020] and Physlib provide broad mathematical infrastructure, but can carry heavy build footprints and do not natively bind each proved theorem to machine-readable scientific scope boundaries (`does_not_establish`) and experimental falsification gates (`open_gates`). `graviton-cert` addresses this need by providing a lightweight, self-contained Lean 4 kernel auditor (`< 30 s` clean build on commodity hardware) that emits machine-readable certificates directly consumable by static web dashboards, continuous-integration pipelines, and archival preprints.

# Architecture and Verification Standard

`graviton-cert` is organized into a compact core (`GravitonCert/Core/`) and modular study packages (`GravitonCert/Studies/`):

- **`GravitonCert/Core/Boundary.lean`**: Defines typed `StudyCertificate`, `Assumption`, `CertifiedClaim`, and `OpenGate` records, requiring every claim to declare its exact `assumptionIds` and `doesNotEstablish` boundaries.
- **`GravitonCert/Core/Inspect.lean`**: Invokes Lean 4's metaprogramming API (`Lean.collectAxioms`) on each claim's `leanDecl` name at runtime, rejecting any declaration that uses `sorryAx`, custom axioms, or unapproved extensions outside Lean's standard logical foundations (`propext`, `Classical.choice`, `Quot.sound`).
- **`GravitonCert/Core/Interval.lean`**: Provides exact rational interval arithmetic for proving numerical sign reversals and spectral bounds without IEEE-754 floating-point approximations.

# Certified Studies and Research Applications

Release `v0.4.1` certifies 50 theorems across 7 active studies from the Graviton Research Foundation (`https://gravitonresearch.org`):

1. **`TimelessGravity` (`TG-01`–`TG-12`, 12 theorems):** Proves universal vanishing of all 256 linearized 4D Riemann components for pure-gauge perturbations, the contracted 4D linearized Bianchi identity ($\partial^\mu G^{(1)}_{\mu\nu} = 0$), ADM uniqueness of Fierz–Pauli mass tuning ($c_2 = 1$) [@FierzPauli1939], the de Sitter Higuchi ghost bound ($\mu^2 \ge \frac{2}{3}\Lambda$) [@Higuchi1987], and exact partially massless scalar gauge invariance iff $\mu^2 = \frac{2}{3}\Lambda$.
2. **`GeometricMatter` (`GM-01`–`GM-11`, 11 theorems):** Constructively passes Graviton's `GeometricMatterAcceptanceGate` via warped 5D vacuum Einstein–Hilbert gravity, deriving $U(1)$ Maxwell curvature and vacuum equations ($2\widehat{R}^{(1)}_{5\nu} = -\partial^\mu F_{\mu\nu} = 0$), ghost-free $5 = 2+2+1$ mode splitting, automatic Fierz–Pauli massive spin-2 towers, exponential warped hierarchies [@RandallSundrum1999], Goldberger–Wise radion stabilization and Yukawa fifth-force screening [@GoldbergerWise1999], full KK-tower de Sitter Higuchi survival, non-Abelian $SU(2)$ Yang–Mills curvature invariance from $S^3$ fiber isometries, and relational clock–mass duality.
3. **`PageWootters` (`PW-01`–`PW-06`, 6 theorems):** Universal $n$-level constraint annihilation, conditional phase recovery, qutrit noise-model discrimination, and the exact clock-bandwidth backreaction law $\|\widehat{\mathcal{C}}_\lambda|\Psi_{m+1}\rangle\|^2 = \lambda^2 m(m-1)(m^2+1)/30$ [@PageWootters1983].
4. **`NullConeGravity` (`NC-01`–`NC-05`, 5 theorems):** Independent formal and epistemic audit of an external quantum-gravity preprint, paired with 4 explicit open gates.
5. **`SpinChemistry` (`SC-01`–`SC-05`, 5 theorems):** Exact steady-state compartment kinetics and a Universal Pathway Exclusion Theorem bounding radical-pair neural signals below threshold before claiming biological effects.
6. **`CircadianTiming` (`CT-01`–`CT-04`, 4 theorems):** Scale invariance of timing reliability ($\mathrm{CV}^2$), Kuramoto order-parameter bounds, statistical identifiability, and tier-classifier soundness backing the ChronoScope psychophysics instrument.
7. **`ObservationWindow` (`OW-01`–`OW-07`, 7 theorems):** Exact 4-qubit Majorana Clifford algebra, spectator conservation, block-diagonal reduction, and a zero-floating-point rational-interval proof of finite-window autocorrelation sign reversal.

# Reproducibility and Usage

`graviton-cert` requires only Lean 4 (`v4.36.0` via `elan`):

```bash
git clone https://github.com/GravitonR/graviton-cert.git
cd graviton-cert
lake build && lake exe graviton-cert
```

A passing run prints the axiom audit for all 50 theorems, regenerates `epistemic-manifest.json` and `VERIFICATION.md`, and exits with code `0`.

# References
