# Experimental Pre-Registration Brief — Relational Temporal Binding Theory (RTBT)

**Author:** Inam Haq, Graviton Research Foundation (`https://gravitonresearch.org`, ORCID `0009-0005-4331-0409`)  
**Formal Proof Suite:** `https://github.com/GravitonR/graviton-cert` (`v1.5.0`, 117/117 Lean 4 theorems, 0 `sorryAx`)  
**Preprint:** Working Paper 06 (Zenodo Concept DOI: `10.5281/zenodo.24598696`)  
**Epistemic Quarantine (`RTBT-GATE-01`):** All three protocols below test third-person dynamical, psychophysical, and biophysical predictions of RTBT. None claims to measure subjective qualia or bridge the metaphysical Hard Problem.

---

## Protocol A — Human Circadian & Sedation Temporal-Precision Test (`P1`, `P2`, `RTBT-02`, `RTBT-04`)
- **Target Labs:** Human psychophysics, sleep/circadian neuroscience, and anesthesia-sedation groups.
- **Open Instrument:** `https://gravitonresearch.org/lab/chronoscope/` (local-only browser auditory/visual temporal resolution & interval-reproduction precision instrument).
- **Primary Hypotheses:**
  1. **Circadian Phase Tracking (`P1`):** Within-subject timing precision $\Pi_{\mathrm{time}} = 1/\mathrm{CV}^2$ co-varies systematically with circadian alignment ($R_\phi^2$) across morning, midday, evening, and biological-night sessions, independent of mean simple reaction time.
  2. **Specious-Present Widening (`P2`):** Sleep deprivation (24 h) or sub-anesthetic sedation (e.g., low-dose propofol/dexmedetomidine) increases internal neural noise $A$, monotonically widening the optimal temporal integration/fusion window $\tau^* = \sqrt{A/B}$ prior to behavioral unresponsiveness.
- **Falsification Criterion:** Absence of within-subject $\Pi_{\mathrm{time}}$ circadian modulation ($p > 0.05$ across $N \ge 40$ repeated-measures participants) or narrowing of temporal-fusion windows under verified sleep deprivation / sub-anesthetic sedation.

---

## Protocol B — Prospective Clinical EEG Phase-Boundary & Neural-Inertia Test (`RTBT-14`, `RTBT-19`, `RTBT-25`, `RTBT-28`)
- **Target Labs:** Anesthesiology EEG monitoring groups, sleep medicine centers, and epilepsy monitoring units (EMU).
- **Open Analysis Code:** `tools/rtbt-eeg-analyzer.py` (zero-dependency Python 3, supports `.edf`, BrainVision `.vhdr`/`.eeg`, `.csv`) and local browser port (`https://gravitonresearch.org/writing/relational-temporal-binding/#eeg-lab`).
- **Retrospective Baseline Already Established (`N = 72` real human subjects, `210` epochs):**
  - HMC Sleep PSG (`N=20`): Wake vs. N3 $\tau_{1/e}$ AUROC `0.914` ($p = 3.81 \times 10^{-6}$); Covert REM vs. N3 $\widehat{\mathcal{B}}$ AUROC `0.946` ($19/20$, $p = 3.81 \times 10^{-6}$).
  - OpenNeuro `ds004541` (`N=7`): `pre-LOC` vs. `pre-ROC` $H_{\mathrm{spec}}$ neural inertia asymmetry `6/7` ($d_z = +1.04$, $p = 0.0469$).
- **Mandatory Prospective Preprocessing Controls (Derived from Honest Failure-Mode Audits):**
  1. Automated bad-electrode rejection (`> 6×` median channel SD) before CAR on monopolar caps.
  2. EOG ocular-blink regression/ICA for Eyes-Open frontal recordings (`1–4 Hz` blink control).
  3. Stratification of epilepsy seizures into **awake-onset generalized** vs. **sleep-onset / focal-aware** seizures with `1–20 Hz` EMG-suppressed sensitivity checks.
- **Primary Prospective Endpoint:** Within-subject paired difference in $\tau_{1/e}$, $H_{\mathrm{spec}}$, `LZ76`, and $D_{\mathrm{eff}}$ across **Awake Baseline → Pre-LOC → Deep Anesthesia (Target Effect-Site Concentration) → Pre-ROC → Recovery**, testing whether `pre-ROC` remains significantly lower in $H_{\mathrm{spec}}$ and slower in $\tau_{1/e}$ than `pre-LOC` at matched estimated effect-site concentration (`RTBT-25`).

---

## Protocol C — Zero-Confound Quantum Boundary Falsification (`P3`, `NQA-04`, `NQA-06`, `RTBT-03`, `RTBT-17`)
- **Target Labs:** Anesthesiology pharmacology labs (xenon anesthesia) and biological spin-chemistry / magnetoreception groups.
- **Design:** Blinded, pre-registered two-arm or three-arm titration **strictly near the anesthesia critical boundary** (wide-awake extinction is forbidden by `RTBT-03`):
  - **Arm 1 (Bracketed 3-Isotope Xenon Cancellation, `NQA-04`):** Compare nuclear spin-½ `${}^{129}\mathrm{Xe}` against the exact arithmetic midpoint of spin-0 `${}^{128}\mathrm{Xe}` and `${}^{130}\mathrm{Xe}`:
    $$\Delta_{\mathrm{spin}} = P(129) - \tfrac{1}{2}\big(P(128) + P(130)\big)$$
    which cancels 100% of linear atomic-mass and pharmacokinetic bias identically (proved in `NeuralQuantumAssembly.lean`).
  - **Arm 2 (Matched-SAR Larmor RF Control, `BQ-04`):** On-resonance Zeeman/Larmor RF vs. matched-SAR off-resonance RF at identical tissue heating during critical-strip sedation.
- **Exact Sample Size (`NQA-06`):** $n \ge 2(z_\alpha + z_\beta)^2 \sigma^2 / \Delta_{\min}^2$ per arm for 90% power at two-sided $\alpha = 0.05$ (e.g., $n = 54$/arm for $\Delta_{\min}/\sigma = 0.62$).
- **Asymmetric Falsification Rule:** A well-powered null result ($\Delta_{\mathrm{spin}} = 0$ within pre-registered equivalence bounds) **cleanly falsifies the quantum-modulation branch** of RTBT while leaving Classical RTBT (`RTBT-01`–`29` macroscopic binding, sleep, anesthesia, and seizure laws) intact.
