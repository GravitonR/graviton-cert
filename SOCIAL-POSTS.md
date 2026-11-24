# Launch Posts for `graviton-cert`

Full long-form blog/Substack post: [`ANNOUNCEMENT.md`](./ANNOUNCEMENT.md)  
Live Kernel Audit Ledger: https://gravitonresearch.org/#kernel-audit  
Public MIT Repository: https://github.com/GravitonR/graviton-cert

---

## 1. Show HN

**Title:**
`Show HN: Graviton-Cert – Open-source Lean 4 standard for proof-carrying research notes`

**Body:**
Hi HN — we built and open-sourced `graviton-cert` (MIT, zero-dependency Lean 4) at Graviton Research Foundation (https://gravitonresearch.org).

Libraries like Mathlib and Physlib formalize textbook math and physics from the bottom up. We wanted something complementary at the *research-note layer*: a tiny kernel auditor so any paper or research note can ship with a machine-checked `epistemic-manifest.json` separating:

1. **Kernel-verified claims** (audited via `Lean.collectAxioms`; CI fails if any claim touches `sorryAx` or an unapproved custom axiom)
2. **Explicit assumptions** (physical regime, idealizations, discretization)
3. **Explicit non-claims (`does_not_establish`)** traveling with every theorem
4. **Open empirical gates** — unmeasured wet-lab/observational obligations that math alone cannot close

All three active research lines on `gravitonresearch.org` are formally verified in Lean 4 (`0 sorryAx`, `0 custom axioms`), including linearized pure-gauge & tensor-divergence constraints, Page–Wootters relational clocks, radical-pair kinetic exclusion bounds, and exact 4-qubit Majorana Clifford algebra & observation-window reversals.

Repo: https://github.com/GravitonR/graviton-cert
Live ledger: https://gravitonresearch.org/#kernel-audit

It builds in seconds with `lake build && lake exe graviton-cert`. Would love feedback from Lean users, physicists, and open-science researchers on the manifest schema and roadmap.

---

## 2. X / Twitter Thread

**1/4**
Most science papers mix exact math, finite numerical checks, and unmeasured assumptions into the same prose.

Today we're open-sourcing **`graviton-cert`** (MIT) — a zero-dependency Lean 4 standard for **proof-carrying, boundary-explicit research notes**.

Not just what a calculation proves, but *exactly where it stops*.
https://github.com/GravitonR/graviton-cert

**2/4**
Every study compiles in Lean 4 and runs `Lean.collectAxioms` in CI to emit an `epistemic-manifest.json`:
- Kernel-verified theorems (0 `sorryAx`, 0 custom axioms)
- Explicit assumptions
- `does_not_establish` boundaries attached to every theorem
- Open empirical gates (the wet-lab / observational `sorry`s math can't close)

**3/4**
We launched by formally verifying all active studies on gravitonresearch.org:
- Linearized gravity: universal pure-gauge $R^{(1)}_{abcd} = 0$, tensor-divergence exclusion, radial Laplacian & Page–Wootters clocks
- Quantum biology: universal neural-pathway exclusion bound + 4 open lab gates
- Quantum dynamics: exact 4-qubit Majorana Clifford algebra, spectator conservation & window-reversal refutation

**4/4**
No 2 GB dependency tree required — builds in seconds on standard Lean 4 and drops a live kernel audit ledger onto any research site or preprint repo.

Live audit & interactive models: https://gravitonresearch.org
MIT repo: https://github.com/GravitonR/graviton-cert

---

## 3. LinkedIn / Research Communities (Lean Zulip, Physics & Bio Slacks)

**Open-sourcing `graviton-cert`: Boundary-Explicit Science in Lean 4**

At Graviton Research Foundation (https://gravitonresearch.org), our core principle is that researchers should be able to explain both what their methods reveal and where those methods stop.

Today we are releasing **`graviton-cert`** (MIT License), a lightweight, zero-dependency Lean 4 framework that compiles individual research notes into machine-checked `epistemic-manifest.json` ledgers audited directly from Lean's kernel (`Lean.collectAxioms`).

Rather than duplicating textbook formalization libraries like Mathlib or Physlib, `graviton-cert` sits at the publishing layer—forcing every study to separate kernel-verified theorems (0 `sorryAx`, 0 custom axioms) from explicit non-claims (`does_not_establish`) and unmeasured `EmpiricalGate`s.

Our initial release formally verifies Graviton's active research lines across linearized gravity & relational clocks, radical-pair biophysical kinetics, and finite-size four-qubit Majorana dynamics.

Any lab, independent researcher, or AI-for-science team can drop a study module into `Studies/`, run `lake build && lake exe graviton-cert` in CI, and publish verifiable receipts alongside their preprints.

GitHub (MIT): https://github.com/GravitonR/graviton-cert
Live Kernel Audit Ledger: https://gravitonresearch.org/#kernel-audit
