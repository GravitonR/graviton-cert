# RTBT Controlled Human Propofol Sedation Validation (OpenNeuro `ds005620`)

> **Dataset:** Bajwa, Nilsen, Skukies, Aamodt, Ernst, Storm & Juel (2024), OpenNeuro `ds005620` (CC-BY-4.0). `N = 10` consecutive non-excluded healthy volunteers (`sub-1010`–`sub-1054`), 19-ch International 10–20 scalp EEG, CAR, `1–45 Hz`, deterministic `15–25 s` window.

## 1. Awake Eyes-Closed vs. Propofol Sedation Level 1 (`task-sed`)
| Biomarker (RTBT Theorem) | Mean Awake | Mean Propofol 1 | Paired Concordance | Cohen's $d_z$ | Exact Wilcoxon $p$ | AUROC (95% CI) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `LZ76` Complexity (`RTBT-22`) | 0.851 | 0.833 | 6/10 (Awake>Prop) | +0.35 | `3.75e-01` | **0.610** (0.330–0.880) |
| Spectral Entropy $H_{\mathrm{spec}}$ | 0.768 | 0.772 | 6/10 (Awake>Prop) | -0.05 | `1.00e+00` | **0.560** (0.280–0.820) |
| Memory Timescale $\tau_{1/e}$ ms (`RTBT-28`) | 20.679 | 19.539 | 1/10 (Prop>Awake) | +0.91 | `2.15e-02` | **0.410** (0.170–0.690) |
| Dimensionality $D_{\mathrm{eff}}$ (`RTBT-19`) | 3.914 | 3.975 | 4/10 (Awake>Prop) | -0.12 | `7.69e-01` | **0.515** (0.240–0.790) |
| RTBT Binding Index $\widehat{\mathcal{B}}$ | 0.071 | 0.069 | 5/10 (Awake>Prop) | +0.07 | `8.46e-01` | **0.540** (0.270–0.820) |

## 2. Awake Eyes-Closed vs. Propofol Sedation Level 2 (`task-sed2`)
| Biomarker (RTBT Theorem) | Mean Awake | Mean Propofol 2 | Paired Concordance | Cohen's $d_z$ | Exact Wilcoxon $p$ | AUROC (95% CI) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `LZ76` Complexity (`RTBT-22`) | 0.851 | 0.815 | 6/10 (Awake>Prop) | +0.42 | `3.22e-01` | **0.680** (0.410–0.910) |
| Spectral Entropy $H_{\mathrm{spec}}$ | 0.768 | 0.743 | 6/10 (Awake>Prop) | +0.18 | `6.95e-01` | **0.600** (0.330–0.850) |
| Memory Timescale $\tau_{1/e}$ ms (`RTBT-28`) | 20.679 | 31.815 | 6/10 (Prop>Awake) | -0.43 | `3.75e-01` | **0.550** (0.280–0.820) |
| Dimensionality $D_{\mathrm{eff}}$ (`RTBT-19`) | 3.914 | 3.974 | 6/10 (Awake>Prop) | -0.06 | `1.00e+00` | **0.560** (0.290–0.830) |
| RTBT Binding Index $\widehat{\mathcal{B}}$ | 0.071 | 0.061 | 7/10 (Awake>Prop) | +0.27 | `3.75e-01` | **0.640** (0.370–0.900) |

## 3. Per-Subject Propofol Trajectories (`Awake EC -> Propofol 1 -> Propofol 2`)
| Subject | `LZ76` | $H_{\mathrm{spec}}$ | $\tau_{1/e}$ (ms) | $D_{\mathrm{eff}}$ | Delta |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `sub-1010` | `0.903 -> 0.835 -> 0.828` | `0.797 -> 0.684 -> 0.675` | `30.1 -> 28.8 -> 33.3` | `4.66 -> 4.21 -> 3.93` | `35% -> 52% -> 56%` |
| `sub-1016` | `0.850 -> 0.903 -> 0.697` | `0.827 -> 0.799 -> 0.529` | `19.1 -> 16.7 -> 92.5` | `3.90 -> 4.46 -> 3.60` | `25% -> 26% -> 76%` |
| `sub-1017` | `0.874 -> 0.813 -> 0.848` | `0.796 -> 0.762 -> 0.786` | `18.6 -> 19.8 -> 16.6` | `4.07 -> 3.40 -> 3.75` | `19% -> 22% -> 15%` |
| `sub-1022` | `0.905 -> 0.885 -> 0.810` | `0.834 -> 0.816 -> 0.776` | `17.0 -> 15.2 -> 19.1` | `4.30 -> 4.42 -> 3.17` | `22% -> 13% -> 25%` |
| `sub-1024` | `0.953 -> 0.847 -> 0.849` | `0.864 -> 0.819 -> 0.831` | `16.9 -> 13.5 -> 13.7` | `4.35 -> 4.03 -> 4.05` | `15% -> 10% -> 12%` |
| `sub-1033` | `0.774 -> 0.796 -> 0.817` | `0.627 -> 0.768 -> 0.775` | `22.9 -> 22.3 -> 22.2` | `2.84 -> 3.65 -> 3.67` | `15% -> 25% -> 27%` |
| `sub-1036` | `0.877 -> 0.834 -> 0.766` | `0.805 -> 0.774 -> 0.656` | `21.8 -> 20.2 -> 62.7` | `4.30 -> 4.33 -> 5.77` | `30% -> 33% -> 65%` |
| `sub-1045` | `0.781 -> 0.792 -> 0.899` | `0.685 -> 0.719 -> 0.869` | `21.9 -> 21.2 -> 15.8` | `2.95 -> 3.24 -> 4.50` | `15% -> 33% -> 28%` |
| `sub-1046` | `0.752 -> 0.791 -> 0.786` | `0.704 -> 0.792 -> 0.766` | `18.4 -> 17.9 -> 19.4` | `3.30 -> 3.90 -> 3.55` | `11% -> 14% -> 19%` |
| `sub-1054` | `0.840 -> 0.834 -> 0.849` | `0.746 -> 0.789 -> 0.767` | `20.2 -> 19.8 -> 22.7` | `4.47 -> 4.11 -> 3.75` | `8% -> 27% -> 36%` |
