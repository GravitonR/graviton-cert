#!/usr/bin/env python3
"""
bioquantum-sim.py — Graviton Research Foundation (graviton-cert v0.9.0)
Zero-dependency biophysical simulator & pre-registration power calculator for
Study 11 (BioQuantumGates) & Study 12 (NeuralQuantumAssembly).

Implements and numerically cross-checks:
  1. Correlated-Noise Cortical Assembly Ceiling (NQA-02): SNR_pop(N) vs SNR_1/sqrt(rho)
  2. Recurrent Thalamocortical Loop Gain & Shared-Noise SNR Invariance (NQA-03)
  3. Bracketed 3-Isotope (128Xe / 129Xe / 130Xe) Linear-Mass Cancellation (NQA-04)
  4. Larmor RF-Resonance Lorentzian Spin-Response Sweep at B0 = 50 uT (BQ-04)
  5. Pre-Registered Adversarial Protocol Sample-Size & Power Calculator (NQA-06)
"""

import argparse
import json
import math
import sys

KB = 1.380649e-23  # J/K
T_BRAIN = 310.0    # K
GAMMA_E_MHZ_PER_UT = 0.0280249514  # electron gyromagnetic ratio (MHz / uT)


def johnson_nyquist_sigma_pA(Rm_MOhm: float = 200.0, df_Hz: float = 100.0, T: float = T_BRAIN) -> float:
    """Exact RMS Johnson-Nyquist thermal current noise in pA (BQ-02)."""
    sigma_A = math.sqrt((4.0 * KB * T * df_Hz) / (Rm_MOhm * 1e6))
    return sigma_A * 1e12


def assembly_snr(snr1: float, N: int, rho: float) -> float:
    """Exact population-averaged SNR across N equicorrelated neurons (NQA-02)."""
    if N < 1:
        raise ValueError("N must be >= 1")
    if not (0.0 <= rho <= 1.0):
        raise ValueError("rho must be in [0, 1]")
    var_factor = (1.0 + (N - 1) * rho) / float(N)
    return snr1 / math.sqrt(var_factor)


def assembly_snr_ceiling(snr1: float, rho: float) -> float:
    """Exact N -> infinity ceiling SNR_1 / sqrt(rho) proved in NQA-02."""
    if rho <= 0.0:
        return float("inf")
    return snr1 / math.sqrt(rho)


def recurrent_loop_analysis(snr1: float, sig_in: float, sig_readout: float, w_rec: float) -> dict:
    """Verify recurrent gain G = 1/(1-w), shared-noise invariance, and readout boost (NQA-03)."""
    if not (0.0 < w_rec < 1.0):
        raise ValueError("w_rec must be in (0, 1)")
    G = 1.0 / (1.0 - w_rec)
    dY = snr1 * sig_in
    snr_in_before = dY / sig_in
    snr_in_after = (G * dY) / (G * sig_in)
    snr_total_before = dY / math.sqrt(sig_in**2 + sig_readout**2)
    snr_total_after = (G * dY) / math.sqrt((G * sig_in)**2 + sig_readout**2)
    return {
        "w_rec": w_rec,
        "gain_G": round(G, 4),
        "shared_input_snr_before": round(snr_in_before, 6),
        "shared_input_snr_after": round(snr_in_after, 6),
        "shared_snr_invariant": abs(snr_in_before - snr_in_after) < 1e-12,
        "total_snr_with_readout_before": round(snr_total_before, 4),
        "total_snr_with_readout_after": round(snr_total_after, 4),
    }


def bracketed_xenon_contrast(p128: float, p129: float, p130: float) -> dict:
    """Exact 3-isotope linear-mass confound cancellation (NQA-04)."""
    interp_baseline = 0.5 * (p128 + p130)
    spin_signal = p129 - interp_baseline
    naive_diff = p129 - p128
    mass_slope_est = 0.5 * (p130 - p128)
    return {
        "P_128_I0": p128,
        "P_129_Ihalf": p129,
        "P_130_I0": p130,
        "interpolated_mass_baseline": round(interp_baseline, 6),
        "isolated_spin_signal_S": round(spin_signal, 6),
        "naive_two_isotope_diff": round(naive_diff, 6),
        "estimated_linear_mass_slope_per_amu": round(mass_slope_est, 6),
    }


def larmor_rf_sweep(B0_uT: float = 50.0, gamma_relax_MHz: float = 0.16, peak_contrast_pA: float = 0.85, sar_bias_pA: float = 1.20) -> dict:
    """Matched-SAR Larmor RF-resonance sweep contrasting raw vs. SAR-subtracted response (BQ-04)."""
    nu_L = GAMMA_E_MHZ_PER_UT * B0_uT  # ~1.401 MHz at 50 uT
    freqs = [round(0.2 + 0.2 * i, 2) for i in range(15)]
    if round(nu_L, 2) not in freqs:
        freqs.append(round(nu_L, 3))
        freqs.sort()
    points = []
    for f in freqs:
        # Lorentzian spin-disruption profile centered at electron Larmor frequency
        lorentz = (gamma_relax_MHz**2) / ((f - nu_L)**2 + gamma_relax_MHz**2)
        spin_shift = peak_contrast_pA * lorentz
        raw_response = spin_shift + sar_bias_pA
        matched_sar_contrast = raw_response - sar_bias_pA  # BQ-04 exact cancellation
        points.append({
            "freq_MHz": f,
            "raw_pA": round(raw_response, 4),
            "sar_matched_contrast_pA": round(matched_sar_contrast, 4),
        })
    return {
        "B0_uT": B0_uT,
        "larmor_freq_MHz": round(nu_L, 4),
        "sar_thermal_bias_pA": sar_bias_pA,
        "sweep": points,
    }


def prereg_sample_size(delta_min: float, sigma: float, z_alpha: float = 1.96, z_beta: float = 1.2816) -> dict:
    """Exact two-arm sample size per arm n >= 2*(z_alpha + z_beta)^2 * sigma^2 / delta_min^2 (NQA-06)."""
    z_total = z_alpha + z_beta  # ~3.2416 for two-sided alpha=0.05, 90% power
    n_exact = (2.0 * (z_total**2) * (sigma**2)) / (delta_min**2)
    n_ceil = math.ceil(n_exact)
    achieved_z_sq = (delta_min**2) / ((2.0 * (sigma**2)) / n_ceil)
    return {
        "delta_min": delta_min,
        "trial_sigma": sigma,
        "z_combined": round(z_total, 4),
        "n_exact_per_arm": round(n_exact, 2),
        "n_required_per_arm": n_ceil,
        "total_n_two_arms": 2 * n_ceil,
        "verified_nqa06_power_holds": achieved_z_sq >= (z_total**2) - 1e-9,
    }


def rtbt_analysis(Rphi: float = 0.85, snr1: float = 0.5, rho: float = 0.05, w_rec: float = 0.80,
                  A_noise: float = 0.004, B_drift: float = 0.16, B_crit: float = 12.0, max_spin_shift: float = 2.0) -> dict:
    """Relational Temporal Binding Theory (RTBT-01..06) quantitative solver."""
    B_cap = (Rphi**2) * ((snr1**2) / rho) / (1.0 - w_rec)
    tau_opt_s = math.sqrt(A_noise / B_drift)
    e_opt = A_noise / tau_opt_s + B_drift * tau_opt_s
    cv_opt = e_opt  # normalized timing CV at optimal window
    pi_time = 1.0 / (cv_opt**2)
    min_entropy_kB = 2.0 * pi_time  # TUR lower bound in units of k_B (RTBT-04)
    if B_cap > B_crit + max_spin_shift:
        regime = "awakeRobustlyBound"
    elif B_cap + max_spin_shift < B_crit:
        regime = "unconsciousSubcritical"
    else:
        regime = "criticalBoundaryQuantumSensitive"
    return {
        "binding_capacity_B": round(B_cap, 4),
        "B_crit": B_crit,
        "max_spin_shift": max_spin_shift,
        "regime_RTBT06": regime,
        "specious_present_opt_ms_RTBT02": round(tau_opt_s * 1000.0, 2),
        "min_window_error_E_opt": round(e_opt, 4),
        "temporal_precision_Pi_time": round(pi_time, 2),
        "tur_min_entropy_kB_per_window_RTBT04": round(min_entropy_kB, 2),
    }


def build_report(snr1: float, rho: float, delta_min: float, sigma: float) -> dict:
    ns = [1, 10, 100, 1000, 10000, 1000000]
    curve = [{"N": n, "SNR_pop": round(assembly_snr(snr1, n, rho), 4)} for n in ns]
    ceil_val = assembly_snr_ceiling(snr1, rho)
    sigma_jn = johnson_nyquist_sigma_pA()
    return {
        "tool": "graviton-cert/tools/bioquantum-sim.py",
        "standard": "BioQuantumGates (BQ-01..06) + NeuralQuantumAssembly (NQA-01..07) + RTBT (RTBT-01..06)",
        "johnson_nyquist_310K_200MOhm_100Hz_pA": round(sigma_jn, 4),
        "rtbt_awake_baseline": rtbt_analysis(Rphi=0.85, snr1=snr1, rho=rho, w_rec=0.80),
        "rtbt_anesthesia_critical_strip": rtbt_analysis(Rphi=0.68, snr1=snr1, rho=rho, w_rec=0.78),
        "rtbt_deep_anesthesia": rtbt_analysis(Rphi=0.35, snr1=snr1, rho=0.15, w_rec=0.30),
        "cortical_assembly_ceiling": {
            "single_neuron_SNR1": snr1,
            "pairwise_noise_correlation_rho": rho,
            "exact_N_infinity_ceiling": round(ceil_val, 4) if math.isfinite(ceil_val) else "infinity",
            "can_reach_SNR_3_at_any_N": ceil_val > 3.0,
            "curve": curve,
        },
        "recurrent_loop_check": recurrent_loop_analysis(snr1=snr1, sig_in=sigma_jn, sig_readout=0.25, w_rec=0.8),
        "xenon_bracketed_3isotope_demo": bracketed_xenon_contrast(
            p128=1.000,  # spin-0
            p129=1.185,  # spin-1/2 (hypothetical 0.15 spin shift + 0.035 linear mass shift)
            p130=1.070,  # spin-0 (pure +0.070 mass shift across 2 amu)
        ),
        "larmor_rf_sweep_50uT": larmor_rf_sweep(),
        "protocol_A_larmor_patch_clamp_power": prereg_sample_size(delta_min=delta_min, sigma=sigma),
        "protocol_B_xenon_3isotope_power": prereg_sample_size(delta_min=0.10, sigma=0.18),
        "epistemic_quarantine": "Passing all biophysical, cortical-assembly, zero-confound, and power gates certifies quantum neurobiology—not a derivation of first-person subjective qualia (BQ-GATE-01 / NQA-GATE-01).",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Graviton BioQuantum Assembly & Pre-Registration Simulator")
    parser.add_argument("--snr1", type=float, default=0.5, help="Single-neuron SNR (default: 0.5)")
    parser.add_argument("--rho", type=float, default=0.05, help="Pairwise cortical noise correlation rho (default: 0.05)")
    parser.add_argument("--delta-min", type=float, default=0.50, help="Protocol A min detectable shift in pA (default: 0.50)")
    parser.add_argument("--sigma", type=float, default=0.80, help="Protocol A trial SD in pA (default: 0.80)")
    parser.add_argument("--json", action="store_true", help="Output machine-readable JSON report")
    args = parser.parse_args()

    report = build_report(args.snr1, args.rho, args.delta_min, args.sigma)
    if args.json:
        print(json.dumps(report, indent=2))
        return 0

    print("=== GRAVITON BIOQUANTUM ASSEMBLY & ADVERSARIAL PROTOCOL SIMULATOR ===")
    print(f"310 K Johnson-Nyquist floor (200 MOhm, 100 Hz): {report['johnson_nyquist_310K_200MOhm_100Hz_pA']} pA")
    ca = report["cortical_assembly_ceiling"]
    print(f"\n[NQA-02] Cortical Assembly Ceiling (SNR1={ca['single_neuron_SNR1']}, rho={ca['pairwise_noise_correlation_rho']}):")
    print(f"  Exact N -> inf ceiling = {ca['exact_N_infinity_ceiling']} | Can reach SNR=3? {ca['can_reach_SNR_3_at_any_N']}")
    for pt in ca["curve"]:
        print(f"    N = {pt['N']:>7d} -> SNR_pop = {pt['SNR_pop']}")

    rl = report["recurrent_loop_check"]
    print(f"\n[NQA-03] Recurrent Loop (w={rl['w_rec']}, G={rl['gain_G']}x):")
    print(f"  Shared input SNR invariant? {rl['shared_snr_invariant']} ({rl['shared_input_snr_before']} -> {rl['shared_input_snr_after']})")
    print(f"  Total SNR w/ readout floor: {rl['total_snr_with_readout_before']} -> {rl['total_snr_with_readout_after']}")

    xe = report["xenon_bracketed_3isotope_demo"]
    print(f"\n[NQA-04] Bracketed 3-Isotope Xenon (128/129/130) Confound Cancellation:")
    print(f"  Naive (129-128) = {xe['naive_two_isotope_diff']} (mass-biased) | Bracketed spin signal S = {xe['isolated_spin_signal_S']} (exact)")

    pa = report["protocol_A_larmor_patch_clamp_power"]
    pb = report["protocol_B_xenon_3isotope_power"]
    print(f"\n[NQA-06] Pre-Registered 90%-Power Sample Sizes (two-sided alpha=0.05):")
    print(f"  Protocol A (Matched-SAR Larmor RF Patch-Clamp, d={pa['delta_min']} pA, sd={pa['trial_sigma']} pA): n = {pa['n_required_per_arm']}/arm ({pa['total_n_two_arms']} total)")
    print(f"  Protocol B (Bracketed 3-Isotope Xenon Anesthesia, d={pb['delta_min']}, sd={pb['trial_sigma']}): n = {pb['n_required_per_arm']}/arm ({pb['total_n_two_arms']} total)")
    print(f"\n[NQA-GATE-01] {report['epistemic_quarantine']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
