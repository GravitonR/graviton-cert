# arXiv Submission & Visibility Guide (`v0.4.0`)

This folder contains the camera-ready LaTeX preprint for **Graviton Working Paper 03**:

- **Manuscript:** `paper/main.tex`
- **Title:** *Machine-Checked Obstructions and Constructive Geometric Matter Emergence in Warped 5D Relational Gravity*
- **Author & ORCID:** Inam Haq (`https://orcid.org/0009-0005-4331-0409`)
- **Permanent Zenodo DOI (`v0.4.1`):** `https://doi.org/10.5281/zenodo.24570906` (Concept DOI: `https://doi.org/10.5281/zenodo.24570905`)
- **Verified Codebase Tag:** `https://github.com/GravitonR/graviton-cert/releases/tag/v0.4.1`
- **Live Interactive Paper:** `https://gravitonresearch.org/writing/geometric-origin-of-matter/`
- **Live Stability Explorer:** `https://gravitonresearch.org/inquiry/timeless-gravity/`

---

## 1. Quick Compile Check (Overleaf or Local TeX)

`paper/main.tex` uses only standard TeXLive packages (`amsmath`, `amssymb`, `amsthm`, `booktabs`, `array`, `geometry`, `xcolor`, `hyperref`) so it compiles cleanly on both **arXiv's AutoTeX** and **Overleaf** with zero extra `.sty` files.

- **Overleaf (fastest preview):** Upload `paper/main.tex` to a blank Overleaf project → compile with `pdfLaTeX` → inspect Table 1 and equations → download PDF if desired.
- **Optional Co-Authors:** If **Ahmad Farag Ali** or **Hasan Alshal** review and join as co-authors, add their `\and` entries inside `\author{...}` before uploading to arXiv.

---

## 2. arXiv Upload Checklist

1. **Primary Category:** `gr-qc` (*General Relativity and Quantum Cosmology*)
2. **Cross-List Category:** `hep-th` (*High Energy Physics - Theory*)
3. **Files to Upload:** Upload `paper/main.tex` directly (self-contained single file; bibliography is embedded cleanly via `\begin{thebibliography}`).
4. **Comments Field (recommended):**
   > `9 pages, 1 table. All 29 theorems (TG-01..12, PW-01..06, GM-01..11) are machine-checked in Lean 4 (v4.36.0, zero sorryAx, zero custom axioms) in graviton-cert v0.4.1 (DOI: 10.5281/zenodo.24570906, https://github.com/GravitonR/graviton-cert)`
5. **Endorsement Note (if first `gr-qc` upload):** Either Ahmad Farag Ali or Hasan Alshal (both published arXiv authors in `gr-qc`/`hep-th`) can endorse the `gr-qc` submission in one click via the arXiv endorsement link.

---

## 3. Mint a Permanent Zenodo DOI (5 Minutes)

1. Go to [zenodo.org](https://zenodo.org) → sign in with GitHub (`haqinam`).
2. Enable **GitHub → Zenodo** for `GravitonR/graviton-cert`.
3. Because `v0.4.0` is already tagged and released, Zenodo will mint a citable DOI for the exact Lean 4 proof bundle (and you can paste that DOI into the footnote of `paper/main.tex` before submitting to arXiv!).

---

## 4. High-Signal Places to Share Once Live

- **Lean Zulip** (`#new members` or `#physics` / `#mathematics`): Share the `v0.4.0` release — 50 zero-dependency core Lean 4 physics theorems including contracted 4D Bianchi (`TG-08`), ADM Fierz–Pauli (`TG-09`), de Sitter Higuchi (`TG-10`, `GM-09`), 5D Maxwell emergence (`GM-01..06`), and `SU(2)` Yang–Mills (`GM-10`).
- **X & LinkedIn:** Lead with the concrete result (*"50/50 Lean 4 kernel-verified physics theorems — zero sorryAx — taking geometric matter emergence from 4D no-go obstructions to warped, radion-stabilized, Higuchi-safe 5D relational gravity, with explicit open gates"*), linking directly to the interactive page and `v0.4.0` GitHub release.
- **Hacker News (`Show HN`):** *"Show HN: Graviton-Cert v0.4 – 50 Lean 4 proofs auditing 4D/5D gravity and emergent Maxwell/SU(2) fields"*.
