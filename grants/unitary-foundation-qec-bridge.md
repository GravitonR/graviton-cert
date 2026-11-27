# Unitary Foundation Microgrant Application Draft ($4,000)

**Project Title:** `QEC-Bridge`: Zero-Dependency In-Kernel Lean 4 Verification of qLDPC Stabilizer Codes & Decoder Symmetry-Trap Auditing  
**Applicant:** Inam Haq (ORCID: `0009-0005-4331-0409`) · Graviton Research Foundation  
**Repository:** https://github.com/GravitonR/graviton-cert (MIT License, active v0.6.0–v0.7.0)  
**Live Verification Ledger:** https://gravitonresearch.org/#kernel-audit  
**Requested Funding:** $4,000 (Unitary Foundation Rolling Microgrant)  
**Timeline:** 12 Weeks (3 Milestones)

---

## 1. Problem Statement (The Verification–Simulation Chasm in QEC)

As quantum hardware transitions from 2D surface codes to high-rate **quantum Low-Density Parity-Check (qLDPC)** codes (such as IBM's Bivariate Bicycle family), a sharp tooling gap has emerged between formal verification and high-throughput decoding:

1. **External-basis trust gap in static Lean 4 QEC tools:** Existing Lean 4 QEC frameworks focus on static code-distance certification (`[[n, k, d]]`) and often rely on external, unverified matrix/kernel basis generators.
2. **Decoder symmetry traps missed by syndrome checks:** Recent 2025–2026 qLDPC results show that graph symmetries cause heuristic decoders (`BP-OSD`, greedy/MWPM) to miss low-weight error patterns *below* $\lfloor(d-1)/2\rfloor$, producing silent logical failures even when the residual satisfies $H(e \oplus c) = 0$.
3. **Heavy dependency barriers:** Most formal QEC libraries depend on large Mathlib builds, slowing adoption by experimental QEC engineers working primarily in Python (`Stim`, `PyMatching`, `ldpc`).

---

## 2. What Is Already Built & Working (Zero Hype, Live Today)

`graviton-cert` already ships a working, MIT-licensed, **zero-dependency core Lean 4** foundation (`< 30 s` clean build, zero `sorryAx`, zero custom axioms) with **Study 9 (`QuantumErrorCorrection.lean`, `QEC-01`–`QEC-08`)** and **`tools/qec-bridge.py`**:

- **Kernel-verified foundations (`QEC-01`–`QEC-06`):** Universal binary symplectic Pauli commutation laws over $\mathbb{F}_2^{2n}$, CSS orthogonality $H_X H_Z^T = 0 \Rightarrow$ full stabilizer commutation, syndrome linearity & stabilizer invisibility, complete in-kernel distance-$3$ certification of Steane `[[7, 1, 3]]` (exhaustive across all 128 error patterns) and Shor `[[9, 1, 3]]`, plus **in-kernel $\mathbb{F}_2$ Gaussian elimination row-operation soundness** (`QEC-06`).
- **Decoder failure formalization (`QEC-07`–`QEC-08`):** Formal proof of syndrome consistency ($s(e \oplus c) = 0 \iff s(c) = s(e)$), explicit low-weight symmetry-trap witness, and executable `QECBridgeAcceptanceGate`.
- **Working Python CLI (`tools/qec-bridge.py`):** Already verifies CSS orthogonality, exact $\mathbb{F}_2$ rank / logical qubit count $k$, silent logical failure traces, and **IBM's 72-qubit Bivariate Bicycle qLDPC code `[[72, 12, d]]`**.

---

## 3. 12-Week Microgrant Deliverables & Milestones

- **Milestone 1 (Weeks 1–4): Full Pivoted In-Kernel $\mathbb{F}_2$ Gaussian Elimination & Bivariate Bicycle Family Certification in Lean 4**
  - Extend `QEC-06` to a complete, executable in-kernel pivoted $\mathbb{F}_2$ rank & nullspace certifier with zero external matrix oracles.
  - Formally certify the general **2D cyclic Bivariate Bicycle commutativity theorem** ($AB + BA = 0 \implies H_X H_Z^T = 0$ for arbitrary $(\ell, m)$ and shift polynomials $A, B$).
- **Milestone 2 (Weeks 5–8): Direct `Stim` Detector Error Model (DEM) & `BP-OSD` Trace Bridge**
  - Add native `.dem` and `Stim` shot-log ingestion to `tools/qec-bridge.py`, automatically exporting minimal Lean 4 counterexample witnesses whenever `BP-OSD` / `PyMatching` suffers a low-weight logical failure below $\lfloor(d-1)/2\rfloor$.
  - Publish an open benchmark dataset of certified symmetry-trap failure patterns on `[[72, 12, 6]]` and `[[144, 12, 12]]` Bivariate Bicycle codes.
- **Milestone 3 (Weeks 9–12): Public Release, Documentation & JOSS / Unitary Community Demo**
  - Publish `v1.0` MIT release + permanent Zenodo DOI + interactive browser visualizer on `gravitonresearch.org` + Unitary Foundation community talk / blog post.

---

## 4. Budget ($4,000)

- **$2,400:** Engineering & formal-verification compute/dev time (in-kernel $\mathbb{F}_2$ solver + `Stim`/`BP-OSD` benchmark harness on `[[72,12,6]]` and `[[144,12,12]]` BB codes).
- **$1,000:** Cloud CPU compute for large-shot `Stim` + `BP-OSD` rare-event symmetry-trap sweeps.
- **$600:** Open-access documentation, interactive web explorer hosting, and reproducible benchmark packaging.

---

## 5. How to Submit (2 Minutes)
Submit directly at **https://unitary.foundation/grants/** using the text above and linking `https://github.com/GravitonR/graviton-cert` and `https://doi.org/10.5281/zenodo.24570906`.
