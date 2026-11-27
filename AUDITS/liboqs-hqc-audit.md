# Independent Post-Quantum Audit: `open-quantum-safe/liboqs` (`3ad27a3`)

**Audit Date:** November 26, 2026  
**Target Repository:** `https://github.com/open-quantum-safe/liboqs`  
**Exact Commit Audited:** `3ad27a3` (2026-11-24)  
**Audit Harness:** `graviton-cert v0.6.0` (`PostQuantumHQC.lean` `HQC-01`–`HQC-10` + `tools/pqc-audit.py`)

---

## Executive Summary

We audited the live **`src/kem/hqc`** and **`src/kem/ml_kem`** C implementations in `open-quantum-safe/liboqs` (`3ad27a3`) against Graviton's Lean 4 `PQCImplementationAcceptanceGate` (`HQC-01`–`HQC-10`) and automated static scanner `tools/pqc-audit.py`.

| Audit Check | Theorem Ref | Target (`liboqs 3ad27a3`) | Verdict |
| :--- | :---: | :--- | :---: |
| **ML-KEM Division-Free Arithmetic (Anti-KyberSlash)** | `HQC-09` | `src/kem/ml_kem/` | **PASS (0 findings)** |
| **HQC Implicit Rejection Full-Ciphertext Binding (`CVE-2025-48946`)** | `HQC-06` | `src/kem/hqc/pqc-hqc_hqc_common/hqc-kem.c` | **PASS (Remediated)** |
| **HQC Exact-Floor Barrett Multiplier (`PARAM_N_MU`)** | `HQC-09` | `src/kem/hqc/pqc-hqc_hqc-1_ref/parameters.h` | **PASS (`243079 = ⌊2³²/17669⌋`)** |
| **HQC Concatenated Code Padding Slack (`5 / 11 / 37` bits)** | `HQC-05` | `parameters.h` & `hqc-kem.c` | **PASS (Top bits bound into `K_bar`)** |
| **HQC AVX2 Reed–Muller Power-of-2 `/` and `%` Hygiene** | `HQC-09` / `HQC-GATE-03` | `pqc-hqc_hqc_avx256_common/reed_muller.c:224,232` | **LOW / HARDENING RECOMMENDED** |

---

## Detailed Findings

### 1. `CVE-2025-48946` Implicit Rejection — Confirmed Remediated (`HQC-06`)
In `src/kem/hqc/pqc-hqc_hqc_common/hqc-kem.c`, `hqc_kem_decaps_internal` computes:
```c
hash_j(K_bar, hash_ek_pke, sigma, c_pke_u, c_pke_v, salt);
result |= vect_compare((uint8_t *)c_pke_u, (uint8_t *)c_pke_prime_u, VEC_N_SIZE_BYTES);
result |= vect_compare((uint8_t *)c_pke_v, (uint8_t *)c_pke_prime_v, VEC_N1N2_SIZE_BYTES);
result |= vect_compare(salt, salt_prime, SALT_BYTES);
result -= 1;
for (size_t i = 0; i < SHARED_SECRET_BYTES_KEM; ++i) {
    K_prime[i] = (K_theta_prime[i] & result) ^ (K_bar[i] & ~result);
}
```
- **Assessment:** Matches `HQC-06` (`boundDecapKey`) and `HQC-09` (branchless bitwise `cmov` selection): `K_bar` binds `H(ek_pke)`, secret `sigma`, and the complete `(u, v, salt)` ciphertext including any unmasked trailing bits in the final byte of `u`. Malformed ciphertexts fail `vect_compare` and map injectively (under SHAKE256 collision resistance) to distinct rejection keys.

### 2. Barrett Multiplier Exact-Floor Discipline (`HQC-09`)
In `src/kem/hqc/pqc-hqc_hqc-1_ref/parameters.h`:
```c
#define PARAM_N_MU 243079ULL ///< floor(2^32 / PARAM_N)
```
- **Assessment:** Uses the exact floor `⌊2³² / 17669⌋ = 243079` rather than rounded `243080`, avoiding unsigned underflow on large inputs (the exact defect class caught in Lean 4 during `HQC-09` verification of ML-KEM Barrett reduction `20158` vs. `20159`).
- **Parameter Note:** `liboqs 3ad27a3` implements the updated HQC-1 weights (`PARAM_OMEGA = 67`, `PARAM_OMEGA_R = PARAM_OMEGA_E = 76`, `PARAM_N = 17669`, `PARAM_N1 = 46`, `PARAM_N2 = 384`, `PARAM_N1N2 = 17664`, exact 5-bit slack).

### 3. Low-Severity Hardening Finding: Secret `message / 16` and `message % 16` in AVX2 Reed–Muller Decoding (`HQC-GATE-03`)
`tools/pqc-audit.py` flagged two lines in `src/kem/hqc/pqc-hqc_hqc_avx256_common/reed_muller.c`:
```c
// Line 224 (size_t message — secret decoded byte)
int64_t message_mask = (-(int64_t)(i == message / 16)) >> 63;

// Line 232
int32_t message_mask = (-(int32_t)(i == message % 16)) >> (sizeof(int32_t) * 8 - 1);
```
- **Assessment:** Because `message` is unsigned (`size_t`) and `16` is a compile-time power of 2, standard optimizing compilers (`-O2`) lower `/ 16` to `>> 4` and `% 16` to `& 0xF` without emitting `div`/`idiv`. **However**, replacing them with explicit `message >> 4` and `message & 15U` removes dependence on compiler optimization flags (`-O0` / debug builds / non-standard toolchains), directly honoring `HQC-GATE-03` (constant-time codegen hygiene).

### 4. What This Audit Does *Not* Establish (Open Gates)
- Does **not** verify compiled x86_64/ARM64 machine-code disassembly across all compiler versions (`HQC-GATE-03`).
- Does **not** measure physical electromagnetic or power side-channel traces on embedded targets (`HQC-GATE-02`).
- Does **not** verify hybrid TLS combiner deployment or middlebox downgrade monitoring in downstream applications (`HQC-07`, `HQC-08`).
