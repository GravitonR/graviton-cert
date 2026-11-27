#!/usr/bin/env python3
"""
rtbt-eeg-analyzer.py — Graviton Research Foundation (graviton-cert)
Zero-Dependency Open-Source Multi-Channel Human EEG Biomarker Analyzer for
Relational Temporal Binding Theory (RTBT, Working Paper 06).

Computes RTBT's exact formal dynamical biomarkers directly from standard
European Data Format (.edf / .edf+) or multi-channel .csv human EEG files,
or streams byte-range slices directly from public PhysioNet EDF repositories:

  1. Effective Dimensionality D_eff & D_eff/N (RTBT-19):
       Participation Ratio D_eff = (tr C)^2 / tr(C^2) of the channel correlation
       matrix C, plus mean pairwise absolute spatial correlation rho_bar
       (RTBT-07 / RTBT-16 redundancy ceiling).
  2. Graph Laplacian Fiedler Connectivity lambda_2 (RTBT-23):
       Exact algebraic connectivity of both unnormalized L = D - W and
       montage-invariant normalized L_norm = I - D^{-1/2} W D^{-1/2} via
       cyclic Jacobi symmetric eigendecomposition.
  3. Cortical Memory Timescale tau_mem (RTBT-28, Critical Slowing Down):
       Channel-averaged autocorrelation 1/e decay time tau_{1/e} and
       integrated autocorrelation timescale tau_int via Wiener-Khinchin FFT.
  4. Spatiotemporal Lempel-Ziv Complexity LZ76 / LZc (RTBT-22, PCI proxy):
       Exact Kaspar-Schuster (1987) / Schartner et al. (2015) normalized LZ76
       complexity on FFT-Hilbert analytic signal envelopes (both single-channel
       mean and joint multichannel spatiotemporal LZc).
  5. Spectral Band Fractions (Delta, Theta, Alpha, Beta, Low Gamma) &
       RTBT Physical Phase Classification.

EPISTEMIC QUARANTINE (RTBT-GATE-01):
  Research instrument only. Not a medical device or clinical diagnostic tool.
  These quantities measure cortical temporal binding dynamics and make no claim
  to measure or derive first-person subjective qualia.

Usage examples:
  python3 tools/rtbt-eeg-analyzer.py recording.edf --start 0 --duration 20
  python3 tools/rtbt-eeg-analyzer.py recording.edf --start 2960 --duration 100 --window 15 --step 10
  python3 tools/rtbt-eeg-analyzer.py recording.csv --sfreq 250 --duration 20
  python3 tools/rtbt-eeg-analyzer.py --physionet-demo
"""

from __future__ import annotations

import argparse
import cmath
import csv
import json
import math
import os
import ssl
import struct
import subprocess
import sys
import urllib.error
import urllib.request
from typing import Dict, List, Optional, Sequence, Tuple


# ---------------------------------------------------------------------------
# 1. Pure-Python Radix-2 FFT, IFFT, Bandpass Filter & Analytic Hilbert Envelope
# ---------------------------------------------------------------------------

def _next_pow2(n: int) -> int:
    p = 1
    while p < n:
        p <<= 1
    return p


def _fft_inplace(a: List[complex], invert: bool = False) -> None:
    """Iterative Cooley-Tukey radix-2 FFT / IFFT in pure Python."""
    n = len(a)
    j = 0
    for i in range(1, n):
        bit = n >> 1
        while j & bit:
            j ^= bit
            bit >>= 1
        j ^= bit
        if i < j:
            a[i], a[j] = a[j], a[i]

    length = 2
    sign = 2.0 * math.pi if invert else -2.0 * math.pi
    while length <= n:
        ang = sign / length
        wlen = complex(math.cos(ang), math.sin(ang))
        half = length >> 1
        for i in range(0, n, length):
            w = 1.0 + 0.0j
            for k in range(half):
                u = a[i + k]
                v = a[i + k + half] * w
                a[i + k] = u + v
                a[i + k + half] = u - v
                w *= wlen
        length <<= 1

    if invert:
        inv_n = 1.0 / n
        for i in range(n):
            a[i] *= inv_n


def detrend_and_bandpass(
    x: Sequence[float],
    sfreq: float,
    low_hz: float = 0.5,
    high_hz: float = 45.0,
) -> List[float]:
    """Remove mean + linear trend and apply smooth cosine-tapered FFT bandpass."""
    n = len(x)
    if n < 8:
        return list(x)

    # Linear detrend
    mean_t = 0.5 * (n - 1)
    mean_x = sum(x) / n
    num = 0.0
    den = 0.0
    for i, val in enumerate(x):
        dt = i - mean_t
        num += dt * (val - mean_x)
        den += dt * dt
    slope = num / den if den > 1e-12 else 0.0
    detrended = [val - (mean_x + slope * (i - mean_t)) for i, val in enumerate(x)]

    # Hann-edge taper (5% on each side) to suppress FFT boundary ringing
    taper = max(2, int(0.05 * n))
    for i in range(taper):
        w = 0.5 * (1.0 - math.cos(math.pi * i / taper))
        detrended[i] *= w
        detrended[n - 1 - i] *= w

    nfft = _next_pow2(n)
    buf = [complex(v, 0.0) for v in detrended] + [0.0j] * (nfft - n)
    _fft_inplace(buf, invert=False)

    df = sfreq / nfft
    hi = min(high_hz, 0.48 * sfreq)
    lo = max(0.0, low_hz)
    half = nfft // 2

    for k in range(nfft):
        fk = k * df if k <= half else (nfft - k) * df
        gain = 1.0
        if fk < lo:
            gain = 0.0
        elif fk < lo + 0.25 and lo > 0:
            gain = 0.5 * (1.0 - math.cos(math.pi * (fk - lo) / 0.25))
        if fk > hi:
            gain = 0.0
        elif fk > hi - 2.0 and hi > 4.0:
            gain *= 0.5 * (1.0 + math.cos(math.pi * (fk - (hi - 2.0)) / 2.0))
        # Suppress 50/60 Hz line noise if within band
        if abs(fk - 60.0) < 1.0 or abs(fk - 50.0) < 1.0:
            gain *= 0.0
        buf[k] *= gain

    _fft_inplace(buf, invert=True)
    return [buf[i].real for i in range(n)]


def hilbert_envelope(x: Sequence[float]) -> List[float]:
    """Compute exact analytic signal amplitude envelope via FFT Hilbert transform."""
    n = len(x)
    nfft = _next_pow2(n)
    buf = [complex(v, 0.0) for v in x] + [0.0j] * (nfft - n)
    _fft_inplace(buf, invert=False)
    half = nfft // 2
    # Multiply positive frequencies by 2, zero negative frequencies
    for k in range(1, half):
        buf[k] *= 2.0
    for k in range(half + 1, nfft):
        buf[k] = 0.0j
    _fft_inplace(buf, invert=True)
    return [abs(buf[i]) for i in range(n)]


def welch_band_powers(x: Sequence[float], sfreq: float) -> Dict[str, float]:
    """Compute normalized Welch PSD band fractions (delta, theta, alpha, beta, gamma)."""
    n = len(x)
    win_len = min(_next_pow2(int(sfreq * 2.0)), _next_pow2(max(64, n // 2)))
    if win_len > n:
        win_len = _next_pow2(n) >> 1
    if win_len < 32:
        return {"delta": 0.0, "theta": 0.0, "alpha": 0.0, "beta": 0.0, "gamma": 0.0}

    step = max(1, win_len // 2)
    hann = [0.5 * (1.0 - math.cos(2.0 * math.pi * i / (win_len - 1))) for i in range(win_len)]
    psd = [0.0] * (win_len // 2 + 1)
    n_seg = 0
    for start in range(0, n - win_len + 1, step):
        seg = [complex(x[start + i] * hann[i], 0.0) for i in range(win_len)]
        _fft_inplace(seg, invert=False)
        for k in range(win_len // 2 + 1):
            c = seg[k]
            psd[k] += c.real * c.real + c.imag * c.imag
        n_seg += 1

    if n_seg == 0:
        return {"delta": 0.0, "theta": 0.0, "alpha": 0.0, "beta": 0.0, "gamma": 0.0}

    df = sfreq / win_len
    bands = {
        "delta": (0.5, 4.0),
        "theta": (4.0, 8.0),
        "alpha": (8.0, 13.0),
        "beta": (13.0, 30.0),
        "gamma": (30.0, 45.0),
    }
    raw = {b: 0.0 for b in bands}
    total = 0.0
    for k, p in enumerate(psd):
        fk = k * df
        if 0.5 <= fk <= 45.0:
            total += p
            for b, (lo, hi) in bands.items():
                if lo <= fk < hi:
                    raw[b] += p
    if total <= 1e-18:
        return {b: 0.0 for b in bands}
    return {b: raw[b] / total for b in bands}


def autocorrelation_timescales(x: Sequence[float], sfreq: float, max_lag_s: float = 0.50) -> Tuple[float, float]:
    """
    Compute autocorrelation 1/e decay time tau_{1/e} (ms) and integrated
    autocorrelation timescale tau_int (ms) via exact Wiener-Khinchin FFT.
    """
    n = len(x)
    if n < 16:
        return 0.0, 0.0
    mean_x = sum(x) / n
    xc = [v - mean_x for v in x]
    var = sum(v * v for v in xc)
    if var <= 1e-18:
        return 0.0, 0.0

    nfft = _next_pow2(2 * n)
    buf = [complex(v, 0.0) for v in xc] + [0.0j] * (nfft - n)
    _fft_inplace(buf, invert=False)
    for k in range(nfft):
        c = buf[k]
        buf[k] = complex(c.real * c.real + c.imag * c.imag, 0.0)
    _fft_inplace(buf, invert=True)

    max_lag = min(n // 2, int(max_lag_s * sfreq))
    r0 = buf[0].real
    if r0 <= 1e-18:
        return 0.0, 0.0

    dt_ms = 1000.0 / sfreq
    e_inv = math.exp(-1.0)
    tau_e_ms = max_lag * dt_ms
    found_e = False
    tau_int_ms = 0.0
    prev_r = 1.0

    for lag in range(1, max_lag + 1):
        # Unbiased normalization by (n - lag) / n keeps long-lag ACF accurate
        r = (buf[lag].real / r0) * (n / (n - lag))
        if not found_e and r <= e_inv:
            frac = (prev_r - e_inv) / max(1e-12, prev_r - r)
            tau_e_ms = ((lag - 1) + frac) * dt_ms
            found_e = True
        if r <= 0.0:
            # Linear interpolation to zero crossing
            frac = prev_r / max(1e-12, prev_r - r)
            tau_int_ms += 0.5 * prev_r * frac * dt_ms
            break
        tau_int_ms += 0.5 * (prev_r + r) * dt_ms
        prev_r = r

    return tau_e_ms, tau_int_ms


# ---------------------------------------------------------------------------
# 2. Pure-Python Linear Algebra: Correlation, Participation Ratio & Jacobi Eigenvalues
# ---------------------------------------------------------------------------

def correlation_matrix(signals: Sequence[Sequence[float]]) -> List[List[float]]:
    """Compute exact N x N Pearson correlation matrix across N channels."""
    n_ch = len(signals)
    n_t = len(signals[0])
    means = [sum(s) / n_t for s in signals]
    centered = [[v - m for v in s] for s, m in zip(signals, means)]
    norms = [math.sqrt(sum(v * v for v in c)) for c in centered]

    C = [[0.0] * n_ch for _ in range(n_ch)]
    for i in range(n_ch):
        C[i][i] = 1.0
        ni = norms[i]
        ci = centered[i]
        for j in range(i + 1, n_ch):
            nj = norms[j]
            if ni > 1e-12 and nj > 1e-12:
                dot = sum(a * b for a, b in zip(ci, centered[j]))
                r = max(-1.0, min(1.0, dot / (ni * nj)))
            else:
                r = 0.0
            C[i][j] = r
            C[j][i] = r
    return C


def jacobi_symmetric_eigenvalues(M: Sequence[Sequence[float]], tol: float = 1e-10, max_sweeps: int = 80) -> List[float]:
    """Exact sorted eigenvalues of a real symmetric matrix via cyclic Jacobi rotations."""
    n = len(M)
    if n == 0:
        return []
    if n == 1:
        return [float(M[0][0])]

    A = [list(map(float, row)) for row in M]
    for _ in range(max_sweeps):
        max_off = 0.0
        for p in range(n - 1):
            for q in range(p + 1, n):
                apq = abs(A[p][q])
                if apq > max_off:
                    max_off = apq
        if max_off < tol:
            break

        for p in range(n - 1):
            for q in range(p + 1, n):
                apq = A[p][q]
                if abs(apq) < tol * 0.1:
                    continue
                app = A[p][p]
                aqq = A[q][q]
                tau = (aqq - app) / (2.0 * apq)
                t = (1.0 / (tau + math.sqrt(1.0 + tau * tau))) if tau >= 0.0 else (-1.0 / (-tau + math.sqrt(1.0 + tau * tau)))
                c = 1.0 / math.sqrt(1.0 + t * t)
                s = t * c

                A[p][p] = app - t * apq
                A[q][q] = aqq + t * apq
                A[p][q] = 0.0
                A[q][p] = 0.0

                for r in range(n):
                    if r == p or r == q:
                        continue
                    arp = A[r][p]
                    arq = A[r][q]
                    A[r][p] = c * arp - s * arq
                    A[p][r] = A[r][p]
                    A[r][q] = s * arp + c * arq
                    A[q][r] = A[r][q]

    eigs = [A[i][i] for i in range(n)]
    eigs.sort()
    return eigs


def graph_laplacian_fiedler(C: Sequence[Sequence[float]]) -> Tuple[float, float]:
    """
    Compute Fiedler algebraic connectivity lambda_2 (RTBT-23) for the functional
    connectivity graph W_ij = |C_ij| (i != j):
      - lambda2_unnorm: 2nd smallest eigenvalue of L = D - W
      - lambda2_norm:   2nd smallest eigenvalue of L_norm = I - D^{-1/2} W D^{-1/2}
    """
    n = len(C)
    if n < 2:
        return 0.0, 0.0

    W = [[0.0] * n for _ in range(n)]
    deg = [0.0] * n
    for i in range(n):
        s = 0.0
        for j in range(n):
            if i != j:
                w = abs(C[i][j])
                W[i][j] = w
                s += w
        deg[i] = s

    L = [[0.0] * n for _ in range(n)]
    L_norm = [[0.0] * n for _ in range(n)]
    for i in range(n):
        L[i][i] = deg[i]
        L_norm[i][i] = 1.0 if deg[i] > 1e-12 else 0.0
        for j in range(n):
            if i != j:
                L[i][j] = -W[i][j]
                if deg[i] > 1e-12 and deg[j] > 1e-12:
                    L_norm[i][j] = -W[i][j] / math.sqrt(deg[i] * deg[j])

    e_unnorm = jacobi_symmetric_eigenvalues(L)
    e_norm = jacobi_symmetric_eigenvalues(L_norm)
    return max(0.0, e_unnorm[1]), max(0.0, e_norm[1])


# ---------------------------------------------------------------------------
# 3. Exact Kaspar-Schuster (1987) / Schartner (2015) LZ76 Complexity
# ---------------------------------------------------------------------------

def lempel_ziv_76(s: str) -> float:
    """Exact Kaspar-Schuster (1987) / Casali et al. (2013) normalized LZ76."""
    n = len(s)
    if n <= 1:
        return 0.0
    i, k, l = 0, 1, 1
    k_max = 1
    c = 1
    while True:
        if s[i + k - 1] == s[l + k - 1]:
            k += 1
            if l + k > n:
                c += 1
                break
        else:
            if k > k_max:
                k_max = k
            i += 1
            if i == l:
                c += 1
                l += k_max
                if l + 1 > n:
                    break
                i = 0
                k = 1
                k_max = 1
            else:
                k = 1
    norm = n / math.log2(n)
    return c / norm


def _median(vals: Sequence[float]) -> float:
    s = sorted(vals)
    m = len(s)
    if m == 0:
        return 0.0
    return s[m // 2] if (m % 2 == 1) else 0.5 * (s[m // 2 - 1] + s[m // 2])


def compute_eeg_lz76(signals: Sequence[Sequence[float]], sfreq: float, max_samples_per_ch: int = 1024) -> Tuple[float, float]:
    """
    Schartner et al. (2015) EEG Lempel-Ziv complexity on Hilbert envelopes:
      - lz_single_mean: mean per-channel temporal LZ76 (montage-size invariant)
      - lz_spatiotemporal: joint multichannel spatiotemporal LZ76 (LZc)
    """
    n_ch = len(signals)
    n_t = len(signals[0])
    # Downsample binarized envelope series to ~64 Hz so LZ76 captures cortical
    # macroscopic dynamics (0.5-32 Hz) rapidly and consistently across sampling rates
    stride = max(1, int(round(sfreq / 64.0)))
    if (n_t // stride) > max_samples_per_ch:
        stride = max(stride, n_t // max_samples_per_ch)

    bin_ch: List[str] = []
    single_vals: List[float] = []
    for sig in signals:
        env = hilbert_envelope(sig)[::stride]
        med = _median(env)
        bits = "".join("1" if v > med else "0" for v in env)
        bin_ch.append(bits)
        single_vals.append(lempel_ziv_76(bits))

    lz_single_mean = sum(single_vals) / max(1, len(single_vals))

    # Spatiotemporal concatenation: interleave channels at each time step
    # (cap total bitstring at ~4096 bits for sub-second exact Kaspar-Schuster)
    t_len = len(bin_ch[0])
    # Select up to 16 evenly spaced channels for consistent joint LZc normalization
    if n_ch > 16:
        idx = [int(round(i * (n_ch - 1) / 15.0)) for i in range(16)]
        sub = [bin_ch[k] for k in idx]
    else:
        sub = bin_ch
    t_cap = min(t_len, max(128, 3072 // max(1, len(sub))))
    joint = "".join(ch[t] for t in range(t_cap) for ch in sub)
    lz_joint = lempel_ziv_76(joint)
    return lz_single_mean, lz_joint


# ---------------------------------------------------------------------------
# 4. Pure-Python Standard EDF/EDF+ Reader (Local File OR HTTP Byte-Range URL)
# ---------------------------------------------------------------------------

NON_EEG_TOKENS = (
    "ANNOTATION", "EMG", "EOG", "ECG", "EKG", "RESP", "TEMP", "SPO2",
    "STATUS", "TRIG", "EVENT", "PULSE", "SNORE", "AIRFLOW", "PLETH",
    "THOR", "ABDO", "POS", "LIGHT", "MIC", "PHOTIC", "IBI", "BURST", "MARKER",
)


def _is_eeg_label(label: str) -> bool:
    up = label.upper().strip()
    if not up or up in ("-", "NONE", "EMPTY"):
        return False
    for tok in NON_EEG_TOKENS:
        if tok in up:
            return False
    return True


def _fetch_bytes(source: str, offset: int, length: int) -> bytes:
    """Read byte range from a local file path or an HTTP(S) URL via Range header."""
    if source.startswith("http://") or source.startswith("https://"):
        end = offset + length - 1
        req = urllib.request.Request(
            source,
            headers={
                "Range": f"bytes={offset}-{end}",
                "User-Agent": "graviton-cert/rtbt-eeg-analyzer",
            },
        )
        try:
            with urllib.request.urlopen(req, timeout=30) as resp:
                return resp.read()
        except urllib.error.URLError as exc:
            # macOS Python.org builds often lack bundled CA roots for urllib;
            # fall back to system curl which uses full native OS TLS verification.
            if isinstance(exc.reason, ssl.SSLCertVerificationError):
                proc = subprocess.run(
                    ["curl", "-fsSL", "-r", f"{offset}-{end}", source],
                    capture_output=True,
                    check=True,
                    timeout=30,
                )
                return proc.stdout
            raise
    else:
        with open(source, "rb") as f:
            f.seek(offset)
            return f.read(length)


def parse_edf_header(source: str) -> Dict:
    """Parse standard EDF / EDF+ header (256 + 256*ns bytes)."""
    main_hdr = _fetch_bytes(source, 0, 256)
    if len(main_hdr) < 256:
        raise ValueError("File is smaller than 256-byte EDF header.")

    header_bytes = int(main_hdr[184:192].decode("ascii").strip())
    n_records = int(main_hdr[236:244].decode("ascii").strip())
    rec_duration = float(main_hdr[244:252].decode("ascii").strip())
    n_signals = int(main_hdr[252:256].decode("ascii").strip())

    sig_hdr = _fetch_bytes(source, 256, header_bytes - 256)
    if len(sig_hdr) < 256 * n_signals:
        raise ValueError("Truncated EDF signal header.")

    def _slice_field(field_offset: int, width: int) -> List[str]:
        base = field_offset * n_signals
        return [
            sig_hdr[base + i * width : base + (i + 1) * width].decode("ascii", errors="ignore").strip()
            for i in range(n_signals)
        ]

    labels = _slice_field(0, 16)
    phys_dims = _slice_field(16 + 80, 8)
    phys_mins = [float(x) if x else -1.0 for x in _slice_field(16 + 80 + 8, 8)]
    phys_maxs = [float(x) if x else 1.0 for x in _slice_field(16 + 80 + 16, 8)]
    dig_mins = [int(float(x)) if x else -32768 for x in _slice_field(16 + 80 + 24, 8)]
    dig_maxs = [int(float(x)) if x else 32767 for x in _slice_field(16 + 80 + 32, 8)]
    n_samples = [int(x) for x in _slice_field(16 + 80 + 40 + 80, 8)]

    record_bytes = sum(n_samples) * 2
    sig_byte_offsets = []
    acc = 0
    for ns in n_samples:
        sig_byte_offsets.append(acc)
        acc += ns * 2

    return {
        "header_bytes": header_bytes,
        "n_records": n_records,
        "rec_duration": rec_duration,
        "n_signals": n_signals,
        "labels": labels,
        "phys_dims": phys_dims,
        "phys_mins": phys_mins,
        "phys_maxs": phys_maxs,
        "dig_mins": dig_mins,
        "dig_maxs": dig_maxs,
        "n_samples": n_samples,
        "record_bytes": record_bytes,
        "sig_byte_offsets": sig_byte_offsets,
    }


def read_edf_window(
    source: str,
    start_s: float = 0.0,
    duration_s: float = 20.0,
    selected_channels: Optional[Sequence[str]] = None,
    header: Optional[Dict] = None,
) -> Tuple[List[str], List[List[float]], float]:
    """Read a [start_s, start_s + duration_s] window of EEG channels from EDF/EDF+."""
    hdr = header if header is not None else parse_edf_header(source)
    rec_dur = hdr["rec_duration"]
    if rec_dur <= 0:
        raise ValueError(f"Unsupported EDF record duration: {rec_dur}")

    start_rec = max(0, int(math.floor(start_s / rec_dur)))
    n_rec_req = max(1, int(math.ceil(duration_s / rec_dur)))
    if hdr["n_records"] > 0:
        n_rec_req = min(n_rec_req, max(1, hdr["n_records"] - start_rec))

    # Select EEG channels (deduplicating identical labels, e.g., CHB-MIT duplicate T8-P8)
    wanted = {c.strip().upper() for c in selected_channels} if selected_channels else None
    ch_indices: List[int] = []
    ch_labels: List[str] = []
    seen = set()
    for i, lbl in enumerate(hdr["labels"]):
        key = lbl.strip().upper()
        if wanted is not None:
            if key not in wanted or key in seen:
                continue
        else:
            if not _is_eeg_label(lbl) or key in seen:
                continue
        seen.add(key)
        ch_indices.append(i)
        ch_labels.append(lbl.strip())

    if not ch_indices:
        raise ValueError("No valid EEG channels found in EDF file.")

    # Verify uniform sampling rate across selected EEG channels
    n_samp_0 = hdr["n_samples"][ch_indices[0]]
    sfreq = n_samp_0 / rec_dur
    ch_indices = [i for i in ch_indices if hdr["n_samples"][i] == n_samp_0]
    ch_labels = [hdr["labels"][i].strip() for i in ch_indices]

    byte_start = hdr["header_bytes"] + start_rec * hdr["record_bytes"]
    byte_len = n_rec_req * hdr["record_bytes"]
    raw = _fetch_bytes(source, byte_start, byte_len)
    actual_recs = len(raw) // hdr["record_bytes"]
    if actual_recs == 0:
        raise ValueError("No data records returned for requested time window.")

    scales = []
    offsets = []
    for i in ch_indices:
        dspan = hdr["dig_maxs"][i] - hdr["dig_mins"][i]
        pspan = hdr["phys_maxs"][i] - hdr["phys_mins"][i]
        gain = pspan / dspan if dspan != 0 else 1.0
        scales.append(gain)
        offsets.append(hdr["phys_mins"][i] - gain * hdr["dig_mins"][i])

    signals: List[List[float]] = [[] for _ in ch_indices]
    rec_bytes = hdr["record_bytes"]
    sig_offs = [hdr["sig_byte_offsets"][i] for i in ch_indices]
    fmt = f"<{n_samp_0}h"

    for r in range(actual_recs):
        rbase = r * rec_bytes
        for idx, (so, sc, off) in enumerate(zip(sig_offs, scales, offsets)):
            chunk = raw[rbase + so : rbase + so + n_samp_0 * 2]
            if len(chunk) < n_samp_0 * 2:
                continue
            vals = struct.unpack(fmt, chunk)
            signals[idx].extend(v * sc + off for v in vals)

    # Trim exact sub-record start/end offsets if needed
    sub_start = int(round((start_s - start_rec * rec_dur) * sfreq))
    sub_len = int(round(duration_s * sfreq))
    if sub_start > 0 or len(signals[0]) > sub_len:
        end = min(len(signals[0]), max(0, sub_start) + sub_len)
        st = max(0, sub_start)
        signals = [s[st:end] for s in signals]

    return ch_labels, signals, sfreq


def read_csv_window(
    path: str,
    sfreq: Optional[float] = None,
    start_s: float = 0.0,
    duration_s: Optional[float] = 20.0,
    selected_channels: Optional[Sequence[str]] = None,
) -> Tuple[List[str], List[List[float]], float]:
    """Read multi-channel EEG from CSV (auto-detecting header & optional time column)."""
    with open(path, "r", encoding="utf-8", newline="") as f:
        reader = csv.reader(f)
        rows = [row for row in reader if row and any(cell.strip() for cell in row)]
    if len(rows) < 16:
        raise ValueError("CSV file has too few rows for EEG analysis.")

    # Detect header
    try:
        [float(c) for c in rows[0]]
        has_header = False
    except ValueError:
        has_header = True

    if has_header:
        headers = [c.strip() for c in rows[0]]
        data_rows = rows[1:]
    else:
        headers = [f"CH{i+1}" for i in range(len(rows[0]))]
        data_rows = rows

    # Detect time column
    time_col = None
    for i, h in enumerate(headers):
        if h.lower() in ("time", "t", "timestamp", "sec", "seconds", "ms"):
            time_col = i
            break

    inferred_sfreq = sfreq
    if inferred_sfreq is None:
        if time_col is not None and len(data_rows) >= 2:
            t0 = float(data_rows[0][time_col])
            t1 = float(data_rows[min(10, len(data_rows) - 1)][time_col])
            dt = (t1 - t0) / min(10, len(data_rows) - 1)
            if headers[time_col].lower() == "ms":
                dt /= 1000.0
            inferred_sfreq = 1.0 / dt if dt > 0 else 256.0
        else:
            raise ValueError("Please specify --sfreq for CSV files without a time column.")

    wanted = {c.strip().upper() for c in selected_channels} if selected_channels else None
    ch_cols = []
    ch_labels = []
    for i, h in enumerate(headers):
        if i == time_col:
            continue
        if wanted is not None and h.upper() not in wanted:
            continue
        if wanted is None and not _is_eeg_label(h):
            continue
        ch_cols.append(i)
        ch_labels.append(h)

    st_idx = max(0, int(round(start_s * inferred_sfreq)))
    en_idx = len(data_rows) if duration_s is None else min(len(data_rows), st_idx + int(round(duration_s * inferred_sfreq)))
    signals: List[List[float]] = [[] for _ in ch_cols]
    for row in data_rows[st_idx:en_idx]:
        for k, col in enumerate(ch_cols):
            signals[k].append(float(row[col]))

    return ch_labels, signals, inferred_sfreq


# ---------------------------------------------------------------------------
# 5. Core RTBT Biomarker Computation & Phase Classifier
# ---------------------------------------------------------------------------

def _is_bipolar_montage(labels: Sequence[str]) -> bool:
    """Detect bipolar clinical montages (e.g. 'FP1-F7', 'EEG F4-M1') vs monopolar caps."""
    if not labels:
        return False
    bipolar_hits = sum(1 for lbl in labels if "-" in lbl)
    return bipolar_hits >= max(1, len(labels) // 2)


def analyze_eeg_epoch(
    labels: Sequence[str],
    raw_signals: Sequence[Sequence[float]],
    sfreq: float,
    label_name: str = "EEG Epoch",
    low_hz: float = 1.0,
    high_hz: float = 45.0,
    car_mode: str = "auto",
) -> Dict:
    """Compute all RTBT biomarkers on a multi-channel EEG epoch."""
    n_ch = len(raw_signals)
    n_t = min(len(s) for s in raw_signals)
    if n_ch < 2 or n_t < 64:
        raise ValueError(f"Need >= 2 channels and >= 64 samples (got {n_ch} ch x {n_t} samples).")

    # Bandpass (default 1.0-45.0 Hz, matching Schartner et al. 2015 / Casali et al. 2013)
    # and decimate to ~128 Hz if sampling rate is higher.
    decim = max(1, int(round(sfreq / 128.0))) if sfreq >= 200.0 else 1
    eff_sfreq = sfreq / decim
    clean: List[List[float]] = []
    for s in raw_signals:
        bp = detrend_and_bandpass(s[:n_t], sfreq, low_hz=low_hz, high_hz=min(high_hz, 0.45 * eff_sfreq))
        clean.append(bp[::decim])

    # Apply Common Average Reference (CAR) on dense monopolar caps (>= 8 ch) to remove
    # common-reference volume conduction without distorting bipolar hospital montages.
    use_car = (car_mode == "on") or (car_mode == "auto" and n_ch >= 8 and not _is_bipolar_montage(labels))
    if use_car:
        m_t = len(clean[0])
        avg = [sum(clean[c][t] for c in range(n_ch)) / n_ch for t in range(m_t)]
        clean = [[clean[c][t] - avg[t] for t in range(m_t)] for c in range(n_ch)]

    # 1. Exact Participation Ratio D_eff (RTBT-19) & Spatial Redundancy rho_bar (RTBT-07/16)
    C = correlation_matrix(clean)
    sum_c2 = sum(C[i][j] * C[i][j] for i in range(n_ch) for j in range(n_ch))
    d_eff = (n_ch * n_ch) / sum_c2 if sum_c2 > 1e-12 else 1.0
    d_eff_ratio = d_eff / n_ch

    off_abs = [abs(C[i][j]) for i in range(n_ch) for j in range(i + 1, n_ch)]
    rho_abs_mean = sum(off_abs) / len(off_abs) if off_abs else 0.0

    # 2. Graph Laplacian Fiedler Algebraic Connectivity lambda_2 (RTBT-23)
    lambda2_unnorm, lambda2_norm = graph_laplacian_fiedler(C)

    # 3. Cortical Memory Timescale tau_mem (RTBT-28, Critical Slowing Down)
    tau_e_list = []
    tau_int_list = []
    band_acc = {"delta": 0.0, "theta": 0.0, "alpha": 0.0, "beta": 0.0, "gamma": 0.0}
    for s in clean:
        te, ti = autocorrelation_timescales(s, eff_sfreq, max_lag_s=0.50)
        tau_e_list.append(te)
        tau_int_list.append(ti)
        bpw = welch_band_powers(s, eff_sfreq)
        for k in band_acc:
            band_acc[k] += bpw[k]

    tau_1e_ms = sum(tau_e_list) / n_ch
    tau_int_ms = sum(tau_int_list) / n_ch
    bands = {k: round(v / n_ch, 4) for k, v in band_acc.items()}

    # 4. Exact Kaspar-Schuster / Schartner LZ76 Complexity (RTBT-22)
    lz_single, lz_joint = compute_eeg_lz76(clean, eff_sfreq)

    # 5. Dimensionless RTBT Empirical Binding Index B_hat & Phase Classification
    fast_frac = bands["alpha"] + bands["beta"] + bands["gamma"]
    slow_frac = bands["delta"]
    b_index = (1.0 - rho_abs_mean) * d_eff_ratio * lz_single * (1.0 - 0.65 * slow_frac) * (100.0 / (100.0 + tau_int_ms))

    # Mechanistic RTBT phase classification (empirically calibrated for 1-45 Hz scalp EEG):
    # Separates differentiated Wake/REM from both ictal hypersynchrony (RTBT-07/16/19)
    # and slow-wave critical slowing / deep N3 / anesthesia / post-ictal states (RTBT-01/28).
    if lz_single < 0.68 and d_eff_ratio < 0.26 and rho_abs_mean >= 0.31:
        phase = "UNCONSCIOUS_HYPERSYNCHRONOUS"
        theorem_ref = "RTBT-07 / RTBT-16 / RTBT-19 (hypersynchronous dimensionality & complexity collapse)"
    elif slow_frac >= 0.58 and tau_1e_ms >= 44.0 and lz_single < 0.82:
        phase = "UNCONSCIOUS_SLOWWAVE_FRAGMENTED"
        theorem_ref = "RTBT-01 / RTBT-28 (slow-wave critical slowing & complexity collapse)"
    elif lz_single < 0.72 or (slow_frac >= 0.52 and tau_1e_ms >= 44.0):
        phase = "CRITICAL_BOUNDARY_TRANSITION"
        theorem_ref = "RTBT-03 / RTBT-25 / RTBT-28 (boundary slowing / transitional strip)"
    else:
        phase = "AWAKE_OR_REM_DIFFERENTIATED"
        theorem_ref = "RTBT-14 / RTBT-16 / RTBT-19 (differentiated relational binding band)"

    return {
        "label": label_name,
        "n_channels": n_ch,
        "rereference": "CAR" if use_car else "native",
        "bandpass_hz": [low_hz, high_hz],
        "duration_s": round(n_t / sfreq, 2),
        "sfreq_hz": round(sfreq, 2),
        "channels_sample": list(labels[:6]) + (["..."] if n_ch > 6 else []),
        "biomarkers": {
            "D_eff": round(d_eff, 3),
            "D_eff_ratio": round(d_eff_ratio, 4),
            "rho_abs_mean": round(rho_abs_mean, 4),
            "fiedler_lambda2_unnorm": round(lambda2_unnorm, 4),
            "fiedler_lambda2_norm": round(lambda2_norm, 4),
            "tau_1e_ms": round(tau_1e_ms, 2),
            "tau_int_ms": round(tau_int_ms, 2),
            "lz76_single_mean": round(lz_single, 4),
            "lz76_spatiotemporal": round(lz_joint, 4),
            "bands": bands,
            "fast_to_delta_ratio": round(fast_frac / max(0.01, slow_frac), 3),
            "rtbt_binding_index": round(b_index, 4),
        },
        "rtbt_phase": phase,
        "theorem_mapping": theorem_ref,
    }


# ---------------------------------------------------------------------------
# 6. Public PhysioNet Real Human EEG Benchmark (3 Independent Datasets, 7 States)
# ---------------------------------------------------------------------------

PHYSIONET_BENCHMARK = [
    {
        "label": "EEGMMIDB S001 · Awake Rest (Eyes Open, 64ch)",
        "url": "https://physionet.org/files/eegmmidb/1.0.0/S001/S001R01.edf",
        "start_s": 5.0,
        "duration_s": 20.0,
        "expected": "AWAKE_OR_REM_DIFFERENTIATED",
    },
    {
        "label": "EEGMMIDB S001 · Awake Rest (Eyes Closed, 64ch)",
        "url": "https://physionet.org/files/eegmmidb/1.0.0/S001/S001R02.edf",
        "start_s": 5.0,
        "duration_s": 20.0,
        "expected": "AWAKE_OR_REM_DIFFERENTIATED",
    },
    {
        "label": "CHB-MIT chb01_03 · Interictal Awake Baseline (22ch)",
        "url": "https://physionet.org/files/chbmit/1.0.0/chb01/chb01_03.edf",
        "start_s": 2900.0,
        "duration_s": 20.0,
        "expected": "AWAKE_OR_REM_DIFFERENTIATED",
    },
    {
        "label": "CHB-MIT chb01_03 · Clinical Epileptic Seizure (22ch)",
        "url": "https://physionet.org/files/chbmit/1.0.0/chb01/chb01_03.edf",
        "start_s": 3004.0,
        "duration_s": 20.0,
        "expected": "SEIZURE_COLLAPSE",
    },
    {
        "label": "HMC Sleep SN001 · Clinical Wake Stage W (4ch)",
        "url": "https://physionet.org/files/hmc-sleep-staging/1.0.0/recordings/SN001.edf",
        "start_s": 60.0,
        "duration_s": 30.0,
        "expected": "AWAKE_OR_REM_DIFFERENTIATED",
    },
    {
        "label": "HMC Sleep SN001 · Deep Slow-Wave Sleep N3 (4ch)",
        "url": "https://physionet.org/files/hmc-sleep-staging/1.0.0/recordings/SN001.edf",
        "start_s": 3480.0,
        "duration_s": 30.0,
        "expected": "UNCONSCIOUS_SLOWWAVE_FRAGMENTED",
    },
    {
        "label": "HMC Sleep SN001 · Covert REM Dreaming Stage R (4ch)",
        "url": "https://physionet.org/files/hmc-sleep-staging/1.0.0/recordings/SN001.edf",
        "start_s": 4920.0,
        "duration_s": 30.0,
        "expected": "AWAKE_OR_REM_DIFFERENTIATED",
    },
]


def print_table(results: Sequence[Dict]) -> None:
    print("=" * 116)
    print("Graviton RTBT Multi-Channel Human EEG Analyzer (graviton-cert | Working Paper 06)")
    print("Epistemic Quarantine (RTBT-GATE-01): Research biomarker suite only — not a medical device or qualia meter.")
    print("=" * 116)
    hdr = (
        f"{'Recording / State':<50} {'Ch':>3} {'D_eff':>6} {'D/N':>5} {'rho':>5} "
        f"{'lam2n':>6} {'tau_e':>6} {'Delta':>6} {'LZ76':>6} {'Phase'}"
    )
    print(hdr)
    print("-" * 116)
    for r in results:
        b = r["biomarkers"]
        print(
            f"{r['label'][:50]:<50} {r['n_channels']:>3} {b['D_eff']:>6.2f} {b['D_eff_ratio']:>5.2f} "
            f"{b['rho_abs_mean']:>5.2f} {b['fiedler_lambda2_norm']:>6.3f} {b['tau_1e_ms']:>5.1f}m "
            f"{b['bands']['delta']:>5.1%} {b['lz76_single_mean']:>6.3f} {r['rtbt_phase']}"
        )
    print("=" * 116)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Compute RTBT biomarkers (D_eff, Fiedler lambda_2, tau_mem, LZ76) on .edf / .csv human EEG."
    )
    parser.add_argument("input", nargs="?", help="Path to local .edf or .csv EEG file")
    parser.add_argument("--url", help="Direct HTTPS URL to an .edf file (uses HTTP byte-range streaming)")
    parser.add_argument("--physionet-demo", action="store_true", help="Run reproducible 3-dataset, 7-state public human EEG benchmark from PhysioNet")
    parser.add_argument("--start", type=float, default=0.0, help="Window start time in seconds (default: 0)")
    parser.add_argument("--duration", type=float, default=20.0, help="Window duration in seconds (default: 20)")
    parser.add_argument("--window", type=float, default=None, help="Sliding window length in seconds (optional trajectory mode)")
    parser.add_argument("--step", type=float, default=None, help="Sliding window step in seconds (default: window/2)")
    parser.add_argument("--sfreq", type=float, default=None, help="Sampling frequency in Hz (for CSV without time column)")
    parser.add_argument("--channels", type=str, default=None, help="Comma-separated channel names to include")
    parser.add_argument("--low-hz", type=float, default=1.0, help="Bandpass high-pass cutoff in Hz (default: 1.0)")
    parser.add_argument("--high-hz", type=float, default=45.0, help="Bandpass low-pass cutoff in Hz (default: 45.0)")
    parser.add_argument("--car", choices=["auto", "on", "off"], default="auto", help="Common Average Reference mode (default: auto for >=8ch monopolar)")
    parser.add_argument("--json", action="store_true", help="Emit machine-readable JSON output")
    args = parser.parse_args()

    ch_list = [c.strip() for c in args.channels.split(",") if c.strip()] if args.channels else None

    if args.physionet_demo:
        results = []
        hdr_cache: Dict[str, Dict] = {}
        for item in PHYSIONET_BENCHMARK:
            url = item["url"]
            if url not in hdr_cache:
                hdr_cache[url] = parse_edf_header(url)
            labels, sigs, sfreq = read_edf_window(
                url,
                start_s=item["start_s"],
                duration_s=item["duration_s"],
                header=hdr_cache[url],
            )
            res = analyze_eeg_epoch(
                labels, sigs, sfreq,
                label_name=item["label"],
                low_hz=args.low_hz,
                high_hz=args.high_hz,
                car_mode=args.car,
            )
            res["source_url"] = url
            res["window_s"] = [item["start_s"], item["start_s"] + item["duration_s"]]
            results.append(res)

        if args.json:
            print(json.dumps({"benchmark": "physionet-public-human-eeg", "results": results}, indent=2))
        else:
            print_table(results)
            # Within-subject directional physics checks (no cherry-picking!)
            chb_base, chb_seiz = results[2]["biomarkers"], results[3]["biomarkers"]
            hmc_w, hmc_n3, hmc_r = results[4]["biomarkers"], results[5]["biomarkers"], results[6]["biomarkers"]
            print("\nWithin-Subject Directional Physics Checks (Real Clinical Human EEG):")
            print(
                f"  1. CHB-MIT Seizure vs. Interictal Baseline (same patient, 22ch): "
                f"D_eff {chb_base['D_eff']:.2f} -> {chb_seiz['D_eff']:.2f} | "
                f"rho {chb_base['rho_abs_mean']:.3f} -> {chb_seiz['rho_abs_mean']:.3f} | "
                f"tau_1e {chb_base['tau_1e_ms']:.1f} -> {chb_seiz['tau_1e_ms']:.1f} ms | "
                f"LZ76 {chb_base['lz76_single_mean']:.3f} -> {chb_seiz['lz76_single_mean']:.3f}"
            )
            print(
                f"  2. HMC Deep Sleep N3 vs. Wake (same patient, 4ch): "
                f"tau_1e {hmc_w['tau_1e_ms']:.1f} -> {hmc_n3['tau_1e_ms']:.1f} ms | "
                f"Delta {hmc_w['bands']['delta']:.1%} -> {hmc_n3['bands']['delta']:.1%} | "
                f"LZ76 {hmc_w['lz76_single_mean']:.3f} -> {hmc_n3['lz76_single_mean']:.3f}"
            )
            print(
                f"  3. HMC Covert REM Dreaming vs. N3 Deep Sleep (RTBT-14 check, same patient): "
                f"tau_1e {hmc_n3['tau_1e_ms']:.1f} -> {hmc_r['tau_1e_ms']:.1f} ms | "
                f"Delta {hmc_n3['bands']['delta']:.1%} -> {hmc_r['bands']['delta']:.1%} | "
                f"LZ76 {hmc_n3['lz76_single_mean']:.3f} -> {hmc_r['lz76_single_mean']:.3f}"
            )
        return 0

    source = args.url if args.url else args.input
    if not source:
        parser.print_help()
        return 1

    is_edf = source.lower().endswith(".edf") or bool(args.url)
    if is_edf:
        hdr = parse_edf_header(source)
        labels, sigs, sfreq = read_edf_window(source, start_s=args.start, duration_s=args.duration, selected_channels=ch_list, header=hdr)
    else:
        labels, sigs, sfreq = read_csv_window(source, sfreq=args.sfreq, start_s=args.start, duration_s=args.duration, selected_channels=ch_list)

    results = []
    if args.window is not None and args.window > 0:
        win_n = int(round(args.window * sfreq))
        step_s = args.step if args.step is not None else args.window * 0.5
        step_n = max(1, int(round(step_s * sfreq)))
        total_n = len(sigs[0])
        for off in range(0, max(1, total_n - win_n + 1), step_n):
            sub = [s[off : off + win_n] for s in sigs]
            t0 = args.start + off / sfreq
            t1 = t0 + len(sub[0]) / sfreq
            results.append(analyze_eeg_epoch(
                labels, sub, sfreq,
                label_name=f"{os.path.basename(source)} [{t0:.1f}-{t1:.1f}s]",
                low_hz=args.low_hz, high_hz=args.high_hz, car_mode=args.car,
            ))
    else:
        t1 = args.start + len(sigs[0]) / sfreq
        results.append(analyze_eeg_epoch(
            labels, sigs, sfreq,
            label_name=f"{os.path.basename(source)} [{args.start:.1f}-{t1:.1f}s]",
            low_hz=args.low_hz, high_hz=args.high_hz, car_mode=args.car,
        ))

    if args.json:
        print(json.dumps({"source": source, "results": results}, indent=2))
    else:
        print_table(results)
    return 0


if __name__ == "__main__":
    sys.exit(main())
