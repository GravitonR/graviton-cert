# RTBT Real Human General Anesthesia Validation (OpenNeuro `ds004541`)

> **Cohort D (`N = 7` consecutive surgical patients with documented `start`, `LOC`, and `ROC`; `sub-11` lacked LOC/ROC markers):** 19-channel 10–20 scalp EEG (1000 Hz, CAR, 1–45 Hz bandpass). Deterministic 20 s windows anchored to hospital event timestamps.

## 1. Pre-Anesthesia Awake Baseline vs. Deep General Anesthesia (Post-LOC)
| Biomarker (RTBT Theorem) | Mean Awake | Mean Unconscious | Paired Concordance | Cohen's $d_z$ | Exact Wilcoxon $p$ | AUROC (95% CI) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `LZ76` Complexity (`RTBT-22`) | 0.825 | 0.874 | 2/7 (Awake>Anes) | -0.60 | `1.56e-01` | **0.306** (0.041–0.612) |
| Spectral Entropy $H_{\mathrm{spec}}$ | 0.726 | 0.760 | 3/7 (Awake>Anes) | -0.48 | `4.69e-01` | **0.347** (0.061–0.653) |
| Memory Timescale $\tau_{1/e}$ ms (`RTBT-28`) | 46.840 | 32.256 | 2/7 (Anes>Awake) | +0.75 | `1.56e-01` | **0.306** (0.020–0.612) |
| Dimensionality $D_{\mathrm{eff}}$ (`RTBT-19`) | 3.695 | 3.700 | 4/7 (Awake>Anes) | -0.01 | `1.00e+00` | **0.500** (0.184–0.816) |
| RTBT Binding Index $\widehat{\mathcal{B}}$ | 0.080 | 0.086 | 3/7 (Awake>Anes) | -0.17 | `8.12e-01` | **0.429** (0.102–0.775) |

## 2. Emergence Recovery (Post-ROC) vs. Deep General Anesthesia (Post-LOC)
| Biomarker (RTBT Theorem) | Mean Recovery | Mean Unconscious | Paired Concordance | Cohen's $d_z$ | Exact Wilcoxon $p$ | AUROC (95% CI) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `LZ76` Complexity (`RTBT-22`) | 0.791 | 0.874 | 1/7 (Rec>Anes) | -0.61 | `4.69e-02` | **0.204** (0.000–0.490) |
| Spectral Entropy $H_{\mathrm{spec}}$ | 0.715 | 0.760 | 2/7 (Rec>Anes) | -0.37 | `2.97e-01` | **0.408** (0.122–0.735) |
| Memory Timescale $\tau_{1/e}$ ms (`RTBT-28`) | 37.481 | 32.256 | 4/7 (Anes>Rec) | +0.15 | `1.00e+00` | **0.429** (0.122–0.755) |
| Dimensionality $D_{\mathrm{eff}}$ (`RTBT-19`) | 3.324 | 3.700 | 2/7 (Rec>Anes) | -0.39 | `3.75e-01` | **0.429** (0.122–0.796) |
| RTBT Binding Index $\widehat{\mathcal{B}}$ | 0.069 | 0.086 | 2/7 (Rec>Anes) | -0.45 | `3.75e-01` | **0.388** (0.102–0.735) |

## 3. Induction (`pre-LOC`) vs. Emergence (`pre-ROC`) Asymmetry Check (`RTBT-25` Neural Inertia)
| Biomarker | Mean Pre-LOC | Mean Pre-ROC | Paired Concordance | Cohen's $d_z$ | Exact Wilcoxon $p$ |
| :--- | :---: | :---: | :---: | :---: | :---: |
| `LZ76` Complexity | 0.854 | 0.820 | 5/7 (PreLOC>PreROC) | +0.33 | `4.69e-01` |
| Spectral Entropy $H_{\mathrm{spec}}$ | 0.775 | 0.713 | 6/7 (PreLOC>PreROC) | +1.04 | `4.69e-02` |
| Memory Timescale $\tau_{1/e}$ ms | 31.161 | 38.937 | 1/7 (PreLOC>PreROC) | -0.50 | `2.19e-01` |
| Dimensionality $D_{\mathrm{eff}}$ | 3.396 | 3.547 | 3/7 (PreLOC>PreROC) | -0.22 | `8.12e-01` |
| RTBT Binding Index $\widehat{\mathcal{B}}$ | 0.082 | 0.074 | 4/7 (PreLOC>PreROC) | +0.22 | `4.69e-01` |

## 4. Per-Patient Trajectories (`Baseline -> Pre-LOC -> Unconscious -> Pre-ROC -> Recovery`)
| Subject | `LZ76` Trajectory | $\tau_{1/e}$ (ms) Trajectory | $D_{\mathrm{eff}}$ Trajectory | Phases (`Base / Uncon / Rec`) |
| :--- | :--- | :--- | :--- | :--- |
| `sub-02` | `0.967 -> 0.490 -> 0.925 -> 0.645 -> 0.557` | `15.6 -> 62.0 -> 18.4 -> 91.2 -> 91.8` | `3.48 -> 1.24 -> 3.06 -> 1.54 -> 1.30` | `AWAKE` / `AWAKE_OR_REM` / `UNCON` |
| `sub-03` | `0.906 -> 0.927 -> 0.908 -> 0.886 -> 0.867` | `20.3 -> 16.1 -> 18.9 -> 17.2 -> 14.7` | `4.65 -> 4.76 -> 4.24 -> 4.17 -> 3.65` | `AWAKE` / `AWAKE_OR_REM` / `AWAKE` |
| `sub-04` | `0.838 -> 0.944 -> 0.916 -> 0.932 -> 0.888` | `53.0 -> 18.2 -> 20.2 -> 30.9 -> 31.2` | `3.18 -> 3.82 -> 3.48 -> 4.05 -> 3.83` | `UNCON` / `AWAKE_OR_REM` / `AWAKE` |
| `sub-07` | `0.810 -> 0.925 -> 0.869 -> 0.772 -> 0.728` | `57.8 -> 27.5 -> 24.7 -> 41.2 -> 37.3` | `2.45 -> 3.44 -> 3.58 -> 4.53 -> 4.68` | `UNCON` / `AWAKE_OR_REM` / `AWAKE` |
| `sub-08` | `0.709 -> 0.956 -> 0.854 -> 0.812 -> 0.828` | `74.0 -> 21.5 -> 64.5 -> 36.4 -> 39.1` | `3.78 -> 3.45 -> 2.83 -> 3.02 -> 2.54` | `UNCON` / `AWAKE_OR_REM` / `AWAKE` |
| `sub-09` | `0.700 -> 0.810 -> 0.846 -> 0.832 -> 0.844` | `42.7 -> 54.4 -> 52.0 -> 34.1 -> 23.9` | `3.55 -> 3.85 -> 4.93 -> 4.80 -> 4.76` | `CRITI` / `CRITICAL_BOU` / `AWAKE` |
| `sub-10` | `0.847 -> 0.928 -> 0.798 -> 0.861 -> 0.824` | `64.5 -> 18.5 -> 27.1 -> 21.5 -> 24.4` | `4.77 -> 3.20 -> 3.77 -> 2.72 -> 2.52` | `CRITI` / `AWAKE_OR_REM` / `AWAKE` |
