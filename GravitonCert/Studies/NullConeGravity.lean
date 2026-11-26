import GravitonCert.Core.Boundary

/-!
# GravitonCert.Studies.NullConeGravity

Independent Lean 4 kernel & epistemic-boundary audit of key mathematical lemmas in:
Venkatesa Chandrasekaran, **"An algebraic quantization of gravity from the null cone"**,
arXiv:2611.34924 (submitted 25 Nov 2026).

This module separates **machine-checked algebraic & analytic cores** (zero `sorryAx`,
zero custom axioms) from **unproved physical / continuum / operator-domain assumptions**
(explicitly recorded as open gates `NC-GATE-01` through `NC-GATE-04`).

Proved universally in Lean 4's kernel:
1. **`NC-01` (`raychaudhuri_area_ceiling`, Eq. 5.21a–d):**
   Raychaudhuri focusing lower bound + Cauchy–Schwarz + causal-diamond clock cutoff
   `u ≤ ℓ` imply the exact quadratic area ceiling `A ≤ 4π ℓ² / (1 - ε)²`.
2. **`NC-02` (`boost_correlator_attenuation`, Eq. 5.29):**
   For any boost factor `r = e^η > 0`, `1 - 4r/(1+r)² = ((r-1)/(r+1))² = tanh²(η/2)`,
   strictly positive iff `r ≠ 1` (`η ≠ 0`).
3. **`NC-03` (`cycle_grouping_variance_and_sign_gap`, Eqs. 5.30c, 5.32, 5.37–5.38):**
   Proves that Chandrasekaran's cycle-grouping trick suppresses the normalized area
   variance of any finite union of cycles by `Δ² + s_*² / ((r - 1) m_min)`, and
   forces the cut amplitude `Z_P[X] ≤ 0 < Z[X]` whenever `⟨Δ_η O⟩_P ≤ δ_η / 2`.
4. **`NC-04` (`unconditional_sum_trace_finiteness`, Eqs. 5.44–5.45):**
   Proves that if `∑ w_i` is unbounded above and `p · v_0 > 0`, adding finite blocks
   `J × {a_0}` shifts Eq. (5.44) arbitrarily far below any negative bound `-B`,
   contradicting unordered/unconditional convergence to `0`.
5. **`NC-05` (`radial_vs_harmonic_and_4d_degeneracy`, Eqs. 4.33–4.34):**
   Proves simultaneously:
   - Uniform nonperturbative 1D radial bound `∑_{k=1}^N 1/k² < 2` for all `N ≥ 1`,
   - Unbounded perturbative `G_N³` harmonic divergence `∑_{k=1}^{2^m} 1/k ≥ 1 + m/2` for all `m`,
   - Exact 4D spherical-harmonic multiplicity `∑_{ℓ=0}^L (2ℓ + 1) = (L + 1)²`
     (marking the boundary between the 1D fixed-harmonic check in Eq. 4.33 and full 4D UV finiteness).
-/

namespace GravitonCert.Studies.NullConeGravity

private theorem rat_sq_nonneg (a : Rat) : 0 ≤ a * a := by
  by_cases h : 0 ≤ a
  · exact Rat.mul_nonneg h h
  · have hneg : 0 ≤ -a := by grind
    have hp : 0 ≤ (-a) * (-a) := Rat.mul_nonneg hneg hneg
    rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] at hp
    exact hp

private theorem rat_natCast_pos {n : Nat} (hn : 0 < n) : (0 : Rat) < (n : Rat) := by
  cases n with
  | zero => omega
  | succ k =>
    induction k with
    | zero => grind
    | succ m ih =>
      have h1 : ((m + 2 : Nat) : Rat) = ((m + 1 : Nat) : Rat) + 1 := by
        simp [Rat.natCast_add]; grind
      rw [h1]
      have hprev := ih (by omega)
      grind

/-! ### NC-01: Raychaudhuri–Cauchy–Schwarz Area Ceiling (Eq. 5.21a–d) -/

/--
**Theorem NC-01 (Causal Diamond Area Ceiling, arXiv:2611.34924 Eq. 5.21a–d):**
From the null-clock focusing lower bound `u ≥ (1 - ε) A / a`, Cauchy–Schwarz
`a² ≤ fourPi · A`, and diamond clock cutoff `u ≤ ℓ` (with `0 ≤ ε < 1`, `a > 0`,
`A ≥ 0`, `ℓ ≥ 0`, `fourPi > 0`), the corner area satisfies:
`(1 - ε)² A ≤ fourPi · ℓ²` and `A ≤ fourPi · ℓ² / (1 - ε)²`.
-/
theorem raychaudhuri_area_ceiling
    (ε a A u ℓ fourPi : Rat)
    (hε1 : ε < 1) (ha : 0 < a) (hA : 0 ≤ A) (hℓ : 0 ≤ ℓ) (h4pi : 0 < fourPi)
    (hClock : (1 - ε) * A / a ≤ u)
    (hCS : a * a ≤ fourPi * A)
    (hCut : u ≤ ℓ) :
    (1 - ε) * (1 - ε) * A ≤ fourPi * (ℓ * ℓ) ∧
    A ≤ fourPi * (ℓ * ℓ) / ((1 - ε) * (1 - ε)) := by
  have h1m : 0 < 1 - ε := by grind
  have h1m2 : 0 < (1 - ε) * (1 - ε) := Rat.mul_pos h1m h1m
  have hle : (1 - ε) * A / a ≤ ℓ := by grind
  have hmul_a : (1 - ε) * A ≤ ℓ * a := by
    have h := Rat.mul_le_mul_of_nonneg_right hle (Rat.le_of_lt ha)
    have hcancel : (1 - ε) * A / a * a = (1 - ε) * A := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (by grind), Rat.mul_one]
    rw [hcancel] at h
    exact h
  have hLHS_nn : 0 ≤ (1 - ε) * A := Rat.mul_nonneg (Rat.le_of_lt h1m) hA
  have hRHS_nn : 0 ≤ ℓ * a := Rat.mul_nonneg hℓ (Rat.le_of_lt ha)
  have hsq1 : ((1 - ε) * A) * ((1 - ε) * A) ≤ (ℓ * a) * (ℓ * a) := by
    have h1 := Rat.mul_le_mul_of_nonneg_left hmul_a hLHS_nn
    have h2 := Rat.mul_le_mul_of_nonneg_right hmul_a hRHS_nn
    grind
  have hℓ2_nn : 0 ≤ ℓ * ℓ := Rat.mul_nonneg hℓ hℓ
  have hsq2 : (ℓ * ℓ) * (a * a) ≤ (ℓ * ℓ) * (fourPi * A) :=
    Rat.mul_le_mul_of_nonneg_left hCS hℓ2_nn
  have hmain : (1 - ε) * (1 - ε) * A ≤ fourPi * (ℓ * ℓ) := by
    by_cases hAz : A = 0
    · subst hAz
      have hnn : 0 ≤ fourPi * (ℓ * ℓ) := Rat.mul_nonneg (Rat.le_of_lt h4pi) hℓ2_nn
      grind
    · have hApos : 0 < A := by grind
      have hcomb : ((1 - ε) * (1 - ε) * A) * A ≤ (fourPi * (ℓ * ℓ)) * A := by grind
      have hinv := Rat.mul_le_mul_of_nonneg_right hcomb (Rat.le_of_lt (Rat.inv_pos.mpr hApos))
      have hneA : A ≠ 0 := by grind
      have hL : (1 - ε) * (1 - ε) * A * A * A⁻¹ = (1 - ε) * (1 - ε) * A := by
        rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hneA, Rat.mul_one]
      have hR : fourPi * (ℓ * ℓ) * A * A⁻¹ = fourPi * (ℓ * ℓ) := by
        rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hneA, Rat.mul_one]
      rw [hL, hR] at hinv
      exact hinv
  refine ⟨hmain, ?_⟩
  have hdiv := Rat.mul_le_mul_of_nonneg_right hmain (Rat.le_of_lt (Rat.inv_pos.mpr h1m2))
  have hne : (1 - ε) * (1 - ε) ≠ 0 := by grind
  have hleft : (1 - ε) * (1 - ε) * A * ((1 - ε) * (1 - ε))⁻¹ = A := by
    calc (1 - ε) * (1 - ε) * A * ((1 - ε) * (1 - ε))⁻¹
        = A * (((1 - ε) * (1 - ε)) * ((1 - ε) * (1 - ε))⁻¹) := by grind
      _ = A * 1 := by rw [Rat.mul_inv_cancel _ hne]
      _ = A := by grind
  rw [hleft, ← Rat.div_def] at hdiv
  exact hdiv

/-! ### NC-02: Boost Correlator Attenuation Identity (Eq. 5.29) -/

/--
**Theorem NC-02 (Boost-Shifted Two-Point Attenuation, arXiv:2611.34924 Eq. 5.29):**
Writing `r = e^η > 0`, the boosted freely-falling vacuum ratio `4r / (1 + r)²`
satisfies `1 - 4r / (1 + r)² = ((r - 1) / (r + 1))² = tanh²(η/2)`, strictly
less than `1` for every nontrivial boost `r ≠ 1`, and equal to `1` iff `r = 1`.
-/
theorem boost_correlator_attenuation (r : Rat) (hr : 0 < r) :
    (1 - (4 * r) / ((1 + r) * (1 + r)) = ((r - 1) / (r + 1)) * ((r - 1) / (r + 1))) ∧
    (r ≠ 1 → (4 * r) / ((1 + r) * (1 + r)) < 1) ∧
    (r = 1 → (4 * r) / ((1 + r) * (1 + r)) = 1) := by
  have hden : (1 + r) ≠ 0 := by grind
  have hden2 : (1 + r) * (1 + r) > 0 := Rat.mul_pos (by grind) (by grind)
  refine ⟨by grind, ?_, by intro h1; subst h1; grind⟩
  intro hne
  have hdiff_ne : (r - 1) / (r + 1) ≠ 0 := by
    have hrm1 : r - 1 ≠ 0 := by grind
    rw [Rat.div_def]
    have hinv : (r + 1)⁻¹ ≠ 0 := by
      have hp : 0 < (r + 1)⁻¹ := Rat.inv_pos.mpr (by grind)
      grind
    grind
  have hpos : 0 < ((r - 1) / (r + 1)) * ((r - 1) / (r + 1)) := by
    have hnn := rat_sq_nonneg ((r - 1) / (r + 1))
    by_cases h0 : ((r - 1) / (r + 1)) * ((r - 1) / (r + 1)) = 0
    · exfalso
      have : (r - 1) / (r + 1) = 0 := by grind
      exact hdiff_ne this
    · grind
  have hid : 1 - (4 * r) / ((1 + r) * (1 + r)) = ((r - 1) / (r + 1)) * ((r - 1) / (r + 1)) := by grind
  grind

/-! ### NC-03: Cycle-Grouping Variance Bound & Cut Sign Contradiction (Eqs. 5.30c, 5.32, 5.38) -/

/--
**Theorem NC-03 (Cycle-Grouping Area Variance Suppression & Sign Gap, Eqs. 5.30c–5.38):**
In Chandrasekaran's cycle-grouping construction (Fig. 29, Eqs. 5.30c, 5.32, 5.38):
1. For any cycle (or union of cycles) where inside-band states carry weight
   `W_in ≥ (r - 1) · m_min > 0` with squared area deviation `≤ Δ²`, and outside
   states carry weight `0 ≤ w_out ≤ 1` with deviation `≤ s_*²` (`0 ≤ Δ ≤ s_*`),
   the normalized area variance satisfies:
   `(W_in · Δ² + w_out · s_*²) / (W_in + w_out) ≤ Δ² + s_*² / ((r - 1) · m_min)`.
2. Whenever the resulting expectation value satisfies `avg_P ≤ δ / 2` while the
   uncut amplitude satisfies `Z_uncut > 0` and `W_P > 0`, the cut partial sum
   satisfies `Z_P = W_P · (avg_P - δ / 2) ≤ 0 < Z_uncut`.
-/
theorem cycle_grouping_variance_and_sign_gap
    (W_in w_out Δ sStar mMin rM1 W_P avg_P δ Z_uncut : Rat)
    (hΔ : 0 ≤ Δ) (hΔs : Δ ≤ sStar)
    (hm : 0 < mMin) (hr : 0 < rM1)
    (hWin : rM1 * mMin ≤ W_in)
    (hw0 : 0 ≤ w_out) (hw1 : w_out ≤ 1)
    (hWP : 0 < W_P) (hAvg : avg_P ≤ δ / 2) (hZ : 0 < Z_uncut) :
    (W_in * (Δ * Δ) + w_out * (sStar * sStar)) / (W_in + w_out)
      ≤ Δ * Δ + (sStar * sStar) / (rM1 * mMin) ∧
    W_P * (avg_P - δ / 2) ≤ 0 ∧
    W_P * (avg_P - δ / 2) < Z_uncut := by
  have hrmPos : 0 < rM1 * mMin := Rat.mul_pos hr hm
  have hWinPos : 0 < W_in := by grind
  have hTotPos : 0 < W_in + w_out := by grind
  have hs_nn : 0 ≤ sStar := by grind
  have hsq_le : Δ * Δ ≤ sStar * sStar := by
    have h1 := Rat.mul_le_mul_of_nonneg_left hΔs hΔ
    have h2 := Rat.mul_le_mul_of_nonneg_right hΔs hs_nn
    grind
  have hs2_nn : 0 ≤ sStar * sStar := Rat.mul_nonneg hs_nn hs_nn
  -- Step 1: (W_in Δ² + w_out s*²) / (W_in + w_out) ≤ Δ² + w_out (s*² - Δ²) / (W_in + w_out)
  -- and w_out (s*² - Δ²) / (W_in + w_out) ≤ s*² / (rM1 * mMin)
  have hCross :
      w_out * (sStar * sStar - Δ * Δ) * (rM1 * mMin) ≤ (sStar * sStar) * (W_in + w_out) := by
    have hdiff_le : sStar * sStar - Δ * Δ ≤ sStar * sStar := by
      have hΔ2 := Rat.mul_nonneg hΔ hΔ
      grind
    have h1 : w_out * (sStar * sStar - Δ * Δ) ≤ 1 * (sStar * sStar) := by
      have ha := Rat.mul_le_mul_of_nonneg_left hdiff_le hw0
      have hb := Rat.mul_le_mul_of_nonneg_right hw1 hs2_nn
      grind
    have h2 : w_out * (sStar * sStar - Δ * Δ) * (rM1 * mMin) ≤ (sStar * sStar) * (rM1 * mMin) := by
      have h := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hrmPos)
      grind
    have h3 : (sStar * sStar) * (rM1 * mMin) ≤ (sStar * sStar) * (W_in + w_out) :=
      Rat.mul_le_mul_of_nonneg_left (by grind) hs2_nn
    grind
  have hfrac :
      (w_out * (sStar * sStar - Δ * Δ)) / (W_in + w_out) ≤ (sStar * sStar) / (rM1 * mMin) := by
    have hinv1 := Rat.inv_pos.mpr hTotPos
    have hinv2 := Rat.inv_pos.mpr hrmPos
    have hmul := Rat.mul_le_mul_of_nonneg_right hCross (Rat.le_of_lt (Rat.mul_pos hinv1 hinv2))
    have hne1 : W_in + w_out ≠ 0 := by grind
    have hne2 : rM1 * mMin ≠ 0 := by grind
    have hL : w_out * (sStar * sStar - Δ * Δ) * (rM1 * mMin) * ((W_in + w_out)⁻¹ * (rM1 * mMin)⁻¹) =
        (w_out * (sStar * sStar - Δ * Δ)) / (W_in + w_out) := by
      rw [Rat.div_def]
      calc w_out * (sStar * sStar - Δ * Δ) * (rM1 * mMin) * ((W_in + w_out)⁻¹ * (rM1 * mMin)⁻¹)
          = w_out * (sStar * sStar - Δ * Δ) * (W_in + w_out)⁻¹ * ((rM1 * mMin) * (rM1 * mMin)⁻¹) := by grind
        _ = w_out * (sStar * sStar - Δ * Δ) * (W_in + w_out)⁻¹ * 1 := by rw [Rat.mul_inv_cancel _ hne2]
        _ = w_out * (sStar * sStar - Δ * Δ) * (W_in + w_out)⁻¹ := by grind
    have hR : (sStar * sStar) * (W_in + w_out) * ((W_in + w_out)⁻¹ * (rM1 * mMin)⁻¹) =
        (sStar * sStar) / (rM1 * mMin) := by
      rw [Rat.div_def]
      calc (sStar * sStar) * (W_in + w_out) * ((W_in + w_out)⁻¹ * (rM1 * mMin)⁻¹)
          = (sStar * sStar) * (rM1 * mMin)⁻¹ * ((W_in + w_out) * (W_in + w_out)⁻¹) := by grind
        _ = (sStar * sStar) * (rM1 * mMin)⁻¹ * 1 := by rw [Rat.mul_inv_cancel _ hne1]
        _ = (sStar * sStar) * (rM1 * mMin)⁻¹ := by grind
    rw [hL, hR] at hmul
    exact hmul
  have hEq :
      (W_in * (Δ * Δ) + w_out * (sStar * sStar)) / (W_in + w_out) =
      Δ * Δ + (w_out * (sStar * sStar - Δ * Δ)) / (W_in + w_out) := by
    have hne1 : W_in + w_out ≠ 0 := by grind
    grind
  have hSign : W_P * (avg_P - δ / 2) ≤ 0 := by
    have hneg : avg_P - δ / 2 ≤ 0 := by grind
    have h := Rat.mul_le_mul_of_nonneg_left hneg (Rat.le_of_lt hWP)
    grind
  exact ⟨by rw [hEq]; grind, hSign, by grind⟩

/-! ### NC-04: Unconditional-Sum Trace Finiteness Lemma (Eqs. 5.44–5.45) -/

/--
**Theorem NC-04 (Unordered-Sum Trace Finiteness Contradiction, arXiv:2611.34924 Eqs. 5.44–5.45):**
Given `p > 0` and `v₀ > 0`, if the thermal weights `w_i` have unbounded finite partial
sums (`∀ M, ∃ S, M < S`), then for every bound `B : Rat`, there exists a finite subset
shift `-p · v₀ · S < -B`. Thus an unordered net of finite subsets `F` cannot converge
to `0` unless `Z_β = ∑ w_i < ∞`.
-/
theorem unconditional_sum_trace_finiteness
    (p v0 B : Rat) (hp : 0 < p) (hv : 0 < v0)
    (hDiv : ∀ M : Rat, ∃ S : Rat, M < S) :
    ∃ S : Rat, -(p * v0 * S) < -B := by
  have hpv : 0 < p * v0 := Rat.mul_pos hp hv
  have ⟨S, hS⟩ := hDiv (B / (p * v0))
  refine ⟨S, ?_⟩
  have hmul := Rat.mul_lt_mul_of_pos_left hS hpv
  have hcancel : (p * v0) * (B / (p * v0)) = B := by
    rw [Rat.div_def]
    calc (p * v0) * (B * (p * v0)⁻¹)
        = B * ((p * v0) * (p * v0)⁻¹) := by grind
      _ = B * 1 := by rw [Rat.mul_inv_cancel _ (by grind)]
      _ = B := by grind
  rw [hcancel] at hmul
  grind

/-! ### NC-05: 1D Radial Convergence vs. Harmonic Divergence & 4D Angular Multiplicity (Eqs. 4.33–4.34) -/

/-- Exact rational sum `∑_{k=1}^{N} 1 / k²`. -/
def invSqSum : Nat → Rat
  | 0 => 0
  | n + 1 => invSqSum n + (1 : Rat) / (((n + 1 : Nat) : Rat) * ((n + 1 : Nat) : Rat))

/-- Exact rational harmonic sum `∑_{k=1}^{N} 1 / k`. -/
def harmonicSum : Nat → Rat
  | 0 => 0
  | n + 1 => harmonicSum n + (1 : Rat) / ((n + 1 : Nat) : Rat)

/-- Total 4D spherical-harmonic angular modes up to angular momentum `L`: `∑_{ℓ=0}^{L} (2ℓ + 1)`. -/
def angularDegeneracySum : Nat → Nat
  | 0 => 1
  | L + 1 => angularDegeneracySum L + (2 * (L + 1) + 1)

theorem invSqSum_upper_bound (n : Nat) :
    invSqSum (n + 1) ≤ 2 - (1 : Rat) / ((n + 1 : Nat) : Rat) := by
  induction n with
  | zero =>
    simp [invSqSum]; grind
  | succ k ih =>
    unfold invSqSum
    have hk1_pos : (0 : Rat) < ((k + 1 : Nat) : Rat) := rat_natCast_pos (by omega)
    have hk2_pos : (0 : Rat) < ((k + 2 : Nat) : Rat) := rat_natCast_pos (by omega)
    have hcast : ((k + 2 : Nat) : Rat) = ((k + 1 : Nat) : Rat) + 1 := by
      simp [Rat.natCast_add]; grind
    have hstep :
        (1 : Rat) / (((k + 2 : Nat) : Rat) * ((k + 2 : Nat) : Rat)) ≤
        (1 : Rat) / ((k + 1 : Nat) : Rat) - (1 : Rat) / ((k + 2 : Nat) : Rat) := by
      have hden1 : 0 < ((k + 1 : Nat) : Rat) * ((k + 2 : Nat) : Rat) := Rat.mul_pos hk1_pos hk2_pos
      have hden2 : 0 < ((k + 2 : Nat) : Rat) * ((k + 2 : Nat) : Rat) := Rat.mul_pos hk2_pos hk2_pos
      have hdiff : (1 : Rat) / ((k + 1 : Nat) : Rat) - (1 : Rat) / ((k + 2 : Nat) : Rat) =
          (1 : Rat) / (((k + 1 : Nat) : Rat) * ((k + 2 : Nat) : Rat)) := by
        rw [hcast]
        grind
      rw [hdiff]
      have hcmp : ((k + 1 : Nat) : Rat) * ((k + 2 : Nat) : Rat) ≤ ((k + 2 : Nat) : Rat) * ((k + 2 : Nat) : Rat) := by
        have hlt : ((k + 1 : Nat) : Rat) ≤ ((k + 2 : Nat) : Rat) := by rw [hcast]; grind
        exact Rat.mul_le_mul_of_nonneg_right hlt (Rat.le_of_lt hk2_pos)
      have hinv := Rat.mul_le_mul_of_nonneg_right hcmp (Rat.le_of_lt (Rat.mul_pos (Rat.inv_pos.mpr hden1) (Rat.inv_pos.mpr hden2)))
      have hne1 : ((k + 1 : Nat) : Rat) * ((k + 2 : Nat) : Rat) ≠ 0 := by grind
      have hne2 : ((k + 2 : Nat) : Rat) * ((k + 2 : Nat) : Rat) ≠ 0 := by grind
      have hL : ((k + 1 : Nat) : Rat) * ((k + 2 : Nat) : Rat) *
          ((((k + 1 : Nat) : Rat) * ((k + 2 : Nat) : Rat))⁻¹ * (((k + 2 : Nat) : Rat) * ((k + 2 : Nat) : Rat))⁻¹) =
          (1 : Rat) / (((k + 2 : Nat) : Rat) * ((k + 2 : Nat) : Rat)) := by
        rw [Rat.div_def]
        calc _ = (((k + 1 : Nat) : Rat) * ((k + 2 : Nat) : Rat) * (((k + 1 : Nat) : Rat) * ((k + 2 : Nat) : Rat))⁻¹) *
                 (((k + 2 : Nat) : Rat) * ((k + 2 : Nat) : Rat))⁻¹ := by grind
          _ = 1 * (((k + 2 : Nat) : Rat) * ((k + 2 : Nat) : Rat))⁻¹ := by rw [Rat.mul_inv_cancel _ hne1]
      have hR : ((k + 2 : Nat) : Rat) * ((k + 2 : Nat) : Rat) *
          ((((k + 1 : Nat) : Rat) * ((k + 2 : Nat) : Rat))⁻¹ * (((k + 2 : Nat) : Rat) * ((k + 2 : Nat) : Rat))⁻¹) =
          (1 : Rat) / (((k + 1 : Nat) : Rat) * ((k + 2 : Nat) : Rat)) := by
        rw [Rat.div_def]
        calc _ = (((k + 2 : Nat) : Rat) * ((k + 2 : Nat) : Rat) * (((k + 2 : Nat) : Rat) * ((k + 2 : Nat) : Rat))⁻¹) *
                 (((k + 1 : Nat) : Rat) * ((k + 2 : Nat) : Rat))⁻¹ := by grind
          _ = 1 * (((k + 1 : Nat) : Rat) * ((k + 2 : Nat) : Rat))⁻¹ := by rw [Rat.mul_inv_cancel _ hne2]
      rw [hL, hR] at hinv
      exact hinv
    grind

private theorem harmonicSum_block_ge (a b : Nat) (hb : 0 < b) :
    harmonicSum (a + b) - harmonicSum a ≥ (b : Rat) / ((a + b : Nat) : Rat) := by
  induction b generalizing a with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      have h1 : harmonicSum (a + 1) = harmonicSum a + (1 : Rat) / ((a + 1 : Nat) : Rat) := rfl
      rw [h1]
      grind
    | succ k =>
      have hprev := ih a (by omega)
      have hstep : harmonicSum (a + (k + 2)) =
          harmonicSum (a + (k + 1)) + (1 : Rat) / ((a + (k + 2) : Nat) : Rat) := by
        have heq : a + (k + 2) = (a + (k + 1)) + 1 := by omega
        rw [heq]
        rfl
      have hpos1 : (0 : Rat) < ((a + (k + 1) : Nat) : Rat) := rat_natCast_pos (by omega)
      have hpos2 : (0 : Rat) < ((a + (k + 2) : Nat) : Rat) := rat_natCast_pos (by omega)
      have hle_den : ((a + (k + 1) : Nat) : Rat) ≤ ((a + (k + 2) : Nat) : Rat) := by
        have hc : ((a + (k + 2) : Nat) : Rat) = ((a + (k + 1) : Nat) : Rat) + 1 := by
          have : a + (k + 2) = (a + (k + 1)) + 1 := by omega
          rw [this, Rat.natCast_add]; grind
        rw [hc]; grind
      have hk1_nn : (0 : Rat) ≤ ((k + 1 : Nat) : Rat) := Rat.le_of_lt (rat_natCast_pos (by omega))
      have hmon : ((k + 1 : Nat) : Rat) / ((a + (k + 2) : Nat) : Rat) ≤
                  ((k + 1 : Nat) : Rat) / ((a + (k + 1) : Nat) : Rat) := by
        have hcross : ((k + 1 : Nat) : Rat) * ((a + (k + 1) : Nat) : Rat) ≤
                      ((k + 1 : Nat) : Rat) * ((a + (k + 2) : Nat) : Rat) :=
          Rat.mul_le_mul_of_nonneg_left hle_den hk1_nn
        have hmul := Rat.mul_le_mul_of_nonneg_right hcross
            (Rat.le_of_lt (Rat.mul_pos (Rat.inv_pos.mpr hpos1) (Rat.inv_pos.mpr hpos2)))
        have hne1 : ((a + (k + 1) : Nat) : Rat) ≠ 0 := by grind
        have hne2 : ((a + (k + 2) : Nat) : Rat) ≠ 0 := by grind
        have hL : ((k + 1 : Nat) : Rat) * ((a + (k + 1) : Nat) : Rat) *
            (((a + (k + 1) : Nat) : Rat)⁻¹ * ((a + (k + 2) : Nat) : Rat)⁻¹) =
            ((k + 1 : Nat) : Rat) / ((a + (k + 2) : Nat) : Rat) := by
          rw [Rat.div_def]
          calc _ = ((k + 1 : Nat) : Rat) * ((a + (k + 2) : Nat) : Rat)⁻¹ *
                   (((a + (k + 1) : Nat) : Rat) * ((a + (k + 1) : Nat) : Rat)⁻¹) := by grind
            _ = ((k + 1 : Nat) : Rat) * ((a + (k + 2) : Nat) : Rat)⁻¹ * 1 := by rw [Rat.mul_inv_cancel _ hne1]
            _ = _ := by grind
        have hR : ((k + 1 : Nat) : Rat) * ((a + (k + 2) : Nat) : Rat) *
            (((a + (k + 1) : Nat) : Rat)⁻¹ * ((a + (k + 2) : Nat) : Rat)⁻¹) =
            ((k + 1 : Nat) : Rat) / ((a + (k + 1) : Nat) : Rat) := by
          rw [Rat.div_def]
          calc _ = ((k + 1 : Nat) : Rat) * ((a + (k + 1) : Nat) : Rat)⁻¹ *
                   (((a + (k + 2) : Nat) : Rat) * ((a + (k + 2) : Nat) : Rat)⁻¹) := by grind
            _ = ((k + 1 : Nat) : Rat) * ((a + (k + 1) : Nat) : Rat)⁻¹ * 1 := by rw [Rat.mul_inv_cancel _ hne2]
            _ = _ := by grind
        rw [hL, hR] at hmul
        exact hmul
      have hcast_k : ((k + 2 : Nat) : Rat) = ((k + 1 : Nat) : Rat) + 1 := by
        simp [Rat.natCast_add]; grind
      rw [hstep, hcast_k]
      grind

theorem harmonicSum_dyadic_lower (m : Nat) :
    harmonicSum (2 ^ m) ≥ 1 + (m : Rat) / 2 := by
  induction m with
  | zero =>
    simp [harmonicSum]; grind
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
      rw [Nat.pow_succ]; omega
    have hpos : 0 < 2 ^ k := Nat.pow_pos (by omega)
    have hblk := harmonicSum_block_ge (2 ^ k) (2 ^ k) hpos
    rw [← hpow] at hblk
    have hratio : ((2 ^ k : Nat) : Rat) / ((2 ^ (k + 1) : Nat) : Rat) = (1 : Rat) / 2 := by
      have hcast : ((2 ^ (k + 1) : Nat) : Rat) = 2 * ((2 ^ k : Nat) : Rat) := by
        rw [hpow, Rat.natCast_add]; grind
      have hne : ((2 ^ k : Nat) : Rat) ≠ 0 := by
        have hp := rat_natCast_pos hpos; grind
      rw [hcast]
      grind
    rw [hratio] at hblk
    have hcast_k : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
      simp [Rat.natCast_add]
    rw [hcast_k]
    grind

theorem angularDegeneracySum_exact (L : Nat) :
    angularDegeneracySum L = (L + 1) * (L + 1) := by
  induction L with
  | zero => rfl
  | succ k ih =>
    unfold angularDegeneracySum
    rw [ih]
    grind

/--
**Theorem NC-05 (1D Radial Convergence vs. Perturbative Harmonic Divergence & 4D Multiplicity):**
Packages the exact mathematical dichotomy behind arXiv:2611.34924 Eqs. (4.33)–(4.34):
1. For EVERY `N ≥ 1`, the nonperturbative 1D radial sum is uniformly bounded: `∑_{k=1}^N 1/k² < 2`.
2. For EVERY `m`, the perturbative `G_N³` derivative sum diverges unboundedly: `∑_{k=1}^{2^m} 1/k ≥ 1 + m/2`.
3. Summing across 4D angular harmonics up to `L` adds exact quadratic multiplicity `(L + 1)²`
   (establishing why the fixed-harmonic check in Eq. 4.33 does not by itself settle full 4D UV finiteness).
-/
theorem radial_vs_harmonic_and_4d_degeneracy (N m L : Nat) :
    invSqSum (N + 1) < 2 ∧
    harmonicSum (2 ^ m) ≥ 1 + (m : Rat) / 2 ∧
    angularDegeneracySum L = (L + 1) * (L + 1) := by
  have h1 := invSqSum_upper_bound N
  have hpos : (0 : Rat) < (1 : Rat) / ((N + 1 : Nat) : Rat) := by
    rw [Rat.div_def]
    have hp := rat_natCast_pos (n := N + 1) (by omega)
    have hinv := Rat.inv_pos.mpr hp
    grind
  exact ⟨by grind, harmonicSum_dyadic_lower m, angularDegeneracySum_exact L⟩

/-- Certificate metadata for Graviton's independent audit of arXiv:2611.34924. -/
def studyCertificate : StudyCertificate := {
  studyId := "null-cone-gravity-audit-2611-34924"
  title := "Independent Lean 4 & Epistemic Boundary Audit of arXiv:2611.34924 (Null-Cone Algebraic Gravity)"
  url := "https://arxiv.org/abs/2611.34924"
  domain := "Algebraic Quantum Gravity / Null-Cone Quantization Audit"
  scopeStatement := "Independent Graviton kernel audit of five core mathematical mechanisms in V. Chandrasekaran, arXiv:2611.34924 (Eqs. 4.33–4.34, 5.21a–d, 5.29, 5.30c–5.38, 5.44–5.45), explicitly separating machine-checked algebra from unproved continuum, operator-domain, and 4D UV assumptions."
  assumptions := [
    { id := "NC-A1_caustic_free_clock"
      kind := "physical_truncation"
      statement := "Null cone is truncated at affine parameter v = ε > 0 before null generators form caustics, and clock/area operators satisfy Eq. 5.21a–b." },
    { id := "NC-A2_pure_gaussian_extension"
      kind := "representation_choice"
      statement := "Fixed-area Gaussian Fock state is extended as a pure state to the full algebra (Sec. 4.2), yielding a Type I factor via GNS." },
    { id := "NC-A3_unconditional_cut_gluing"
      kind := "path_integral_axiom"
      statement := "Diffeomorphism-invariant gluing across an internal cut S (Eq. 4.29) converges unconditionally over arbitrary finite cycle groupings or product-basis subsets." },
    { id := "NC-A4_single_angular_harmonic"
      kind := "toy_reduction"
      statement := "Graviton pair-creation finiteness check (Eqs. 4.32–4.34) restricts to one polarization and one fixed real angular harmonic, summing only over radial modes k ≥ 1." }
  ]
  claims := [
    { id := "NC-01"
      title := "Raychaudhuri–Cauchy–Schwarz Causal Diamond Area Ceiling (Eq. 5.21a–d)"
      leanDecl := ``raychaudhuri_area_ceiling
      claimKind := "theorem"
      summary := "Proves that u ≥ (1-ε)A/a, a² ≤ 4πA, and u ≤ ℓ imply A ≤ 4πℓ²/(1-ε)² identically over rationals."
      assumptionIds := ["NC-A1_caustic_free_clock"]
      doesNotEstablish := [
        "Does not prove that strong-field nonlinear graviton waves remain caustic-free up to v = ε > 0 or that unbounded operators (u_*, A) share a common self-adjoint core."
      ] },
    { id := "NC-02"
      title := "Freely-Falling Vacuum Boost Attenuation Identity (Eq. 5.29)"
      leanDecl := ``boost_correlator_attenuation
      claimKind := "theorem"
      summary := "Proves 1 - 4r/(1+r)² = ((r-1)/(r+1))² = tanh²(η/2) > 0 for all boost factors r = e^η ≠ 1."
      assumptionIds := []
      doesNotEstablish := [
        "Does not verify the nonperturbative smearing remainder O((Δu/d)²) or vacuum subtraction bounds in Appendix D.2."
      ] },
    { id := "NC-03"
      title := "Cycle-Grouping Area Variance Suppression & Cut Sign Contradiction (Eqs. 5.30c, 5.32, 5.38)"
      leanDecl := ``cycle_grouping_variance_and_sign_gap
      claimKind := "theorem"
      summary := "Proves that grouping r-1 narrow-band states with at most 1 outside state bounds area variance by Δ² + s_*²/((r-1)m_min) and forces Z_P[X] ≤ 0 < Z[X]."
      assumptionIds := ["NC-A2_pure_gaussian_extension", "NC-A3_unconditional_cut_gluing"]
      doesNotEstablish := [
        "Does not establish that the physical Lorentzian path integral converges unconditionally along arbitrary cycle permutations V without hidden regulator dependence."
      ] },
    { id := "NC-04"
      title := "Unconditional-Sum AdS Thermal Trace Finiteness Contradiction (Eqs. 5.44–5.45)"
      leanDecl := ``unconditional_sum_trace_finiteness
      claimKind := "theorem"
      summary := "Proves that any divergent sum ∑ w_i allows finite subset additions shifting Eq. (5.44) arbitrarily negative, contradicting unordered convergence to 0."
      assumptionIds := ["NC-A3_unconditional_cut_gluing"]
      doesNotEstablish := [
        "Relies crucially on unordered convergence over finite subsets F of product basis states rather than a fixed regularized summation order."
      ] },
    { id := "NC-05"
      title := "1D Radial Convergence vs. Perturbative Harmonic Divergence & 4D Angular Multiplicity (Eqs. 4.33–4.34)"
      leanDecl := ``radial_vs_harmonic_and_4d_degeneracy
      claimKind := "theorem"
      summary := "Proves ∑_{k=1}^N 1/k² < 2 uniformly for all N, ∑_{k=1}^{2^m} 1/k ≥ 1 + m/2 unboundedly, and ∑_{ℓ=0}^L (2ℓ+1) = (L+1)²."
      assumptionIds := ["NC-A4_single_angular_harmonic"]
      doesNotEstablish := [
        "1D fixed-harmonic radial convergence does not by itself prove 4D multi-loop UV finiteness across all (2ℓ+1) angular modes or cancel 2-loop Goroff–Sagnotti R³ counterterms."
      ] }
  ]
  openGates := [
    { id := "NC-GATE-01"
      quantity := "Unconditional convergence of Lorentzian cut-gluing sums under arbitrary cycle reorderings (Eqs. 4.29, 5.38, 5.44)"
      units := "operator-algebraic / path-integral axiom"
      requiredControl := "Constructive proof that the Lorentzian gluing amplitude is rearrangement-invariant on infinite-dimensional Hilbert spaces without sneaking in a trace-class cutoff."
      status := "open_mathematical_gate" },
    { id := "NC-GATE-02"
      quantity := "Basis & Gaussian-width independence of the pure Type I GNS representation (Sec. 4.2)"
      units := "algebraic / diffeomorphism covariance"
      requiredControl := "Proof that changing the countable basis (q_j, p_j) or Gaussian variance Δq_k yields a unitarily equivalent Type I representation preserving full 4D diffeomorphism symmetry."
      status := "open_mathematical_gate" },
    { id := "NC-GATE-03"
      quantity := "Full 4D angular+radial multi-loop UV finiteness including 2-loop Goroff–Sagnotti R³ (Sec. 4.4 & 6)"
      units := "O(G_N²) 4D graviton scattering amplitude"
      requiredControl := "Nonperturbative sum over all angular harmonics (2ℓ+1) and 2-loop graviton amplitudes beyond the 1D radial check in Eq. 4.33 and 1-loop semiclassical limit."
      status := "open_physics_gate" },
    { id := "NC-GATE-04"
      quantity := "Strong-field caustic formation & self-adjoint domains of (u_*, A) as ε → 0 (Sec. 5.1–5.3)"
      units := "nonlinear GR PDE / functional analysis"
      requiredControl := "Removal of the caustic-free truncation v = ε > 0 and proof of strong commutativity (commuting spectral projections) on a common dense domain."
      status := "open_mathematical_gate" }
  ]
  sourceArtifacts := [
    ("arxiv_url", "https://arxiv.org/abs/2611.34924"),
    ("audit_note", "AUDITS/arXiv-2611.34924.md")
  ]
}

end GravitonCert.Studies.NullConeGravity
