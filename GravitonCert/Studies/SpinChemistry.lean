import GravitonCert.Core.Boundary

/-!
# GravitonCert.Studies.SpinChemistry

Machine-checked formalization of Graviton Research Note 01:
*"Can a spin-dependent chemical signal reach a neuron?"*
<https://gravitonresearch.org/writing/spin-chemistry-neural-response/>

Proves in Lean 4's kernel:
1. Exact steady-state concentration and linear neuronal-current accounting,
2. SI unit invariance (μM / pA vs. mol·L⁻¹ / A),
3. Exact opposite-shift antisymmetry `Δy(-ΔΦ_S) = -Δy(ΔΦ_S)`,
4. **Universal Pathway Exclusion Theorem**: for *any* bounded biological
   parameters satisfying `G_max * F_max * B_Φ / k_min < δ_y`, the absolute
   neuronal current shift is strictly below the physiological threshold `δ_y`,
5. Exact instantiation on Graviton's illustrative exclusion scenario
   (`3.125 nM`, `0.1875 pA < 0.5 pA`), while quarantining the 4 unmeasured
   biological quantities as explicit `EmpiricalGate`s.
-/

namespace GravitonCert.Studies.SpinChemistry

/-- Exact absolute value on `Rat`. -/
def ratAbs (x : Rat) : Rat := if x < 0 then -x else x

theorem ratAbs_nonneg (x : Rat) : 0 ≤ ratAbs x := by
  unfold ratAbs
  grind

theorem ratAbs_mul (x y : Rat) : ratAbs (x * y) = ratAbs x * ratAbs y := by
  unfold ratAbs
  by_cases hx : x < 0 <;> by_cases hy : y < 0
  · have hpos : 0 < (-x) * (-y) := Rat.mul_pos (by grind) (by grind)
    have hxy : ¬ (x * y < 0) := by
      rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] at hpos
      grind
    simp only [hx, hy, hxy, ↓reduceIte]; grind
  · have hy0 : 0 ≤ y := by grind
    by_cases hyz : y = 0
    · subst hyz; simp [hx]
    · have hypos : 0 < y := by grind
      have hpos : 0 < (-x) * y := Rat.mul_pos (by grind) hypos
      have hxy : x * y < 0 := by rw [Rat.neg_mul] at hpos; grind
      simp only [hx, hy, hxy, ↓reduceIte]; grind
  · have hx0 : 0 ≤ x := by grind
    by_cases hxz : x = 0
    · subst hxz; simp [hy]
    · have hxpos : 0 < x := by grind
      have hpos : 0 < x * (-y) := Rat.mul_pos hxpos (by grind)
      have hxy : x * y < 0 := by rw [Rat.mul_neg] at hpos; grind
      simp only [hx, hy, hxy, ↓reduceIte]; grind
  · have hx0 : 0 ≤ x := by grind
    have hy0 : 0 ≤ y := by grind
    have hnn : 0 ≤ x * y := Rat.mul_nonneg hx0 hy0
    have hxy : ¬ (x * y < 0) := by grind
    simp only [hx, hy, hxy, ↓reduceIte]

theorem ratAbs_inv_of_pos {k : Rat} (hk : 0 < k) : ratAbs k⁻¹ = k⁻¹ := by
  have hk_inv_pos : 0 < k⁻¹ := Rat.inv_pos.mpr hk
  unfold ratAbs
  have hnot : ¬ (k⁻¹ < 0) := Rat.not_lt.mpr (Rat.le_of_lt hk_inv_pos)
  simp [hnot]

/-- Steady-state concentration shift `Δx = F_RP * ΔΦ_S / k_clear`. -/
def steadyConcShift (F_RP dPhi k_clear : Rat) : Rat :=
  (F_RP * dPhi) / k_clear

/-- Linearized neuronal membrane-current shift `Δŷ = g'(x_0) * Δx`. -/
def steadyCurrentShift (g_prime F_RP dPhi k_clear : Rat) : Rat :=
  g_prime * steadyConcShift F_RP dPhi k_clear

/--
**Theorem 1 (Reference Synthetic Accounting):**
With `F_RP = 0.20 μM/s`, `ΔΦ_S = 0.010`, `k_clear = 0.10 s⁻¹`, `g'(x_0) = 50 pA/μM`,
the linear kinetic model yields `Δx = 0.020 μM` (`20 nM`) and `Δŷ = 1.00 pA`.
-/
theorem reference_accounting_exact :
    steadyConcShift (1 / 5) (1 / 100) (1 / 10) = 1 / 50 ∧
    steadyConcShift (1 / 5) (1 / 100) (1 / 10) * 1000 = 20 ∧
    steadyCurrentShift 50 (1 / 5) (1 / 100) (1 / 10) = 1 := by
  unfold steadyCurrentShift steadyConcShift
  grind

/--
**Theorem 2 (SI Unit Invariance):**
Converting `F_RP` from `μM/s` to `mol/(L·s)` (`× 10⁻⁶`) and `g'` from `pA/μM`
to `A/(mol/L)` (`× 10⁻¹² / 10⁻⁶`) preserves the exact physical current (`1 pA = 10⁻¹² A`).
-/
theorem si_unit_invariance :
    let F_si : Rat := (1 / 5) * (1 / 1000000)
    let dPhi : Rat := 1 / 100
    let k_si : Rat := 1 / 10
    let g_si : Rat := (50 * (1 / 1000000000000)) / (1 / 1000000)
    steadyConcShift F_si dPhi k_si * 1000000000 = 20 ∧
    steadyCurrentShift g_si F_si dPhi k_si * 1000000000000 = 1 := by
  unfold steadyCurrentShift steadyConcShift
  grind

/--
**Theorem 3 (Opposite-Shift Antisymmetry):**
Within the linear response regime, reversing the yield shift `ΔΦ_S ↦ -ΔΦ_S`
reverses the predicted membrane-current change identically.
-/
theorem opposite_shift_antisymmetry (g_prime F_RP dPhi k_clear : Rat) :
    steadyCurrentShift g_prime F_RP (-dPhi) k_clear =
      - steadyCurrentShift g_prime F_RP dPhi k_clear := by
  unfold steadyCurrentShift steadyConcShift
  rw [Rat.mul_neg, Rat.div_def, Rat.div_def, Rat.neg_mul, Rat.mul_neg]

private theorem mul_le_mul_nonneg {a b c d : Rat}
    (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (hcd : c ≤ d) :
    a * c ≤ b * d := by
  have h1 : a * c ≤ b * c := Rat.mul_le_mul_of_nonneg_right hab hc
  have hb : 0 ≤ b := Rat.le_trans ha hab
  have h2 : b * c ≤ b * d := Rat.mul_le_mul_of_nonneg_left hcd hb
  exact Rat.le_trans h1 h2

/--
**Theorem 4 (Universal Pathway Exclusion Theorem):**
For *any* parameter tuple `(g', F_RP, ΔΦ_S, k_clear)` satisfying simultaneous bounds
`|g'| ≤ G_max`, `|F_RP| ≤ F_max`, `|ΔΦ_S| ≤ B_Φ`, and `0 < k_min ≤ k_clear`,
the absolute current shift satisfies:
`|Δŷ| ≤ G_max * F_max * B_Φ / k_min`.
Consequently, whenever `G_max * F_max * B_Φ / k_min < δ_y`, the pathway cannot
produce a physiologically meaningful current change `≥ δ_y`.
-/
theorem universal_pathway_exclusion
    (g_prime F_RP dPhi k_clear G_max F_max B_Phi k_min delta_y : Rat)
    (hk_min_pos : 0 < k_min)
    (hg : ratAbs g_prime ≤ G_max)
    (hF : ratAbs F_RP ≤ F_max)
    (hPhi : ratAbs dPhi ≤ B_Phi)
    (hk : k_min ≤ k_clear)
    (hBoundLt : (G_max * (F_max * B_Phi)) / k_min < delta_y) :
    ratAbs (steadyCurrentShift g_prime F_RP dPhi k_clear) < delta_y := by
  unfold steadyCurrentShift steadyConcShift
  have hk_pos : 0 < k_clear := by grind
  rw [Rat.div_def, ratAbs_mul, ratAbs_mul, ratAbs_mul, ratAbs_inv_of_pos hk_pos]
  -- Bound numerator: |g'| * (|F_RP| * |dPhi|) ≤ G_max * (F_max * B_Phi)
  have hFPhi : ratAbs F_RP * ratAbs dPhi ≤ F_max * B_Phi :=
    mul_le_mul_nonneg (ratAbs_nonneg F_RP) hF (ratAbs_nonneg dPhi) hPhi
  have hFPhi_nonneg : 0 ≤ ratAbs F_RP * ratAbs dPhi :=
    Rat.mul_nonneg (ratAbs_nonneg F_RP) (ratAbs_nonneg dPhi)
  have hNum : ratAbs g_prime * (ratAbs F_RP * ratAbs dPhi) ≤ G_max * (F_max * B_Phi) :=
    mul_le_mul_nonneg (ratAbs_nonneg g_prime) hg hFPhi_nonneg hFPhi
  -- Bound reciprocal: k_clear⁻¹ ≤ k_min⁻¹
  have hInv : k_clear⁻¹ ≤ k_min⁻¹ := by
    have hprod : k_min * k_clear⁻¹ ≤ k_clear * k_clear⁻¹ :=
      Rat.mul_le_mul_of_nonneg_right hk (Rat.le_of_lt (Rat.inv_pos.mpr hk_pos))
    rw [Rat.mul_inv_cancel k_clear (Rat.ne_of_gt hk_pos)] at hprod
    have hprod2 : k_min⁻¹ * (k_min * k_clear⁻¹) ≤ k_min⁻¹ * 1 :=
      Rat.mul_le_mul_of_nonneg_left hprod (Rat.le_of_lt (Rat.inv_pos.mpr hk_min_pos))
    rw [← Rat.mul_assoc, Rat.inv_mul_cancel k_min (Rat.ne_of_gt hk_min_pos),
        Rat.one_mul, Rat.mul_one] at hprod2
    exact hprod2
  -- Combine numerator and reciprocal bounds
  have hNum_nonneg : 0 ≤ ratAbs g_prime * (ratAbs F_RP * ratAbs dPhi) :=
    Rat.mul_nonneg (ratAbs_nonneg g_prime) hFPhi_nonneg
  have hInv_nonneg : 0 ≤ k_clear⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hk_pos)
  have hTotal :
      ratAbs g_prime * (ratAbs F_RP * ratAbs dPhi * k_clear⁻¹)
      ≤ (G_max * (F_max * B_Phi)) / k_min := by
    rw [← Rat.mul_assoc, Rat.div_def]
    exact mul_le_mul_nonneg hNum_nonneg hNum hInv_nonneg hInv
  grind

/--
**Theorem 5 (Graviton Research Note 01 Illustrative Exclusion Scenario):**
For any candidate satisfying `|g'| ≤ 60 pA/μM`, `|F_RP| ≤ 0.25 μM/s`,
`|ΔΦ_S| ≤ 0.001`, and `k_clear ≥ 0.08 s⁻¹`, the predicted current change is
strictly below `0.5 pA` (specifically `≤ 0.1875 pA`, concentration `≤ 3.125 nM`).
-/
theorem graviton_exclusion_scenario
    (g_prime F_RP dPhi k_clear : Rat)
    (hg : ratAbs g_prime ≤ 60)
    (hF : ratAbs F_RP ≤ 1 / 4)
    (hPhi : ratAbs dPhi ≤ 1 / 1000)
    (hk : 2 / 25 ≤ k_clear) :
    ratAbs (steadyCurrentShift g_prime F_RP dPhi k_clear) < 1 / 2 := by
  exact universal_pathway_exclusion
    g_prime F_RP dPhi k_clear 60 (1 / 4) (1 / 1000) (2 / 25) (1 / 2)
    (by grind) hg hF hPhi hk (by grind)

/-- Certificate metadata linking these Lean 4 theorems to `gravitonresearch.org`. -/
def studyCertificate : StudyCertificate := {
  studyId := "spin-chemistry-neural-response"
  title := "Research Note 01: Can a Spin-Dependent Chemical Signal Reach a Neuron?"
  url := "https://gravitonresearch.org/writing/spin-chemistry-neural-response/"
  domain := "Quantum Biology / Biophysical Kinetics"
  scopeStatement := "Exact linear steady-state accounting and universal exclusion bound under matched formation flux, first-order clearance, and local linear membrane-current calibration. Contains NO measured biological data."
  assumptions := [
    { id := "SC-A1_matched_flux"
      kind := "biological_idealization"
      statement := "Matched radical-pair formation flux F_RP and background production F_bg across control and perturbed steady states." },
    { id := "SC-A2_well_mixed_first_order"
      kind := "biological_idealization"
      statement := "First-order product clearance k_clear > 0 in a well-mixed cellular compartment without saturation." },
    { id := "SC-A3_local_linear_calibration"
      kind := "biological_idealization"
      statement := "Neuronal current y = g(x) is independently calibrated and locally linear with slope g'(x_0) over the relevant concentration interval." }
  ]
  claims := [
    { id := "SC-01"
      title := "Reference Synthetic Kinetic Accounting (20 nM, 1.00 pA)"
      leanDecl := ``reference_accounting_exact
      claimKind := "theorem"
      summary := "Exact rational verification that F_RP = 0.20 μM/s, ΔΦ_S = 0.010, k_clear = 0.10 s⁻¹, g' = 50 pA/μM yield Δx = 20 nM and Δŷ = 1.00 pA."
      assumptionIds := ["SC-A1_matched_flux", "SC-A2_well_mixed_first_order", "SC-A3_local_linear_calibration"]
      doesNotEstablish := [
        "Arbitrary synthetic demonstration inputs only; establishes neither achievable biological flux nor real neuronal sensitivity.",
        "Does not establish any link to conscious experience."
      ] },
    { id := "SC-02"
      title := "SI Unit Invariance (μM/pA vs. mol·L⁻¹/A)"
      leanDecl := ``si_unit_invariance
      claimKind := "theorem"
      summary := "Verifies dimensional consistency between biophysical units (μM, nM, pA) and SI units (mol/L, A)."
      assumptionIds := ["SC-A1_matched_flux", "SC-A2_well_mixed_first_order", "SC-A3_local_linear_calibration"]
      doesNotEstablish := [
        "Dimensional consistency does not validate physical plausibility."
      ] },
    { id := "SC-03"
      title := "Opposite-Shift Antisymmetry"
      leanDecl := ``opposite_shift_antisymmetry
      claimKind := "theorem"
      summary := "Proves Δŷ(-ΔΦ_S) = -Δŷ(ΔΦ_S) universally within the linear response model."
      assumptionIds := ["SC-A1_matched_flux", "SC-A2_well_mixed_first_order", "SC-A3_local_linear_calibration"]
      doesNotEstablish := [
        "Agreement with opposite-shift symmetry tests the shared-mediator model, not spin chemistry uniquely; selective molecular controls remain required."
      ] },
    { id := "SC-04"
      title := "Universal Pathway Exclusion Inequality"
      leanDecl := ``universal_pathway_exclusion
      claimKind := "exclusion_bound"
      summary := "Proves that for all bounded parameters with G_max * F_max * B_Φ / k_min < δ_y, the predicted current shift strictly satisfies |Δŷ| < δ_y."
      assumptionIds := ["SC-A1_matched_flux", "SC-A2_well_mixed_first_order", "SC-A3_local_linear_calibration"]
      doesNotEstablish := [
        "Excluding a single candidate pathway does not rule out nonlinear amplification, spatial microdomains, or other quantum contributions to biology."
      ] },
    { id := "SC-05"
      title := "Illustrative Exclusion Scenario (0.1875 pA < 0.5 pA)"
      leanDecl := ``graviton_exclusion_scenario
      claimKind := "exclusion_bound"
      summary := "Instantiates the universal exclusion bound on Graviton's scenario (G_max=60, F_max=0.25, B_Φ=0.001, k_min=0.08, δ_y=0.5)."
      assumptionIds := ["SC-A1_matched_flux", "SC-A2_well_mixed_first_order", "SC-A3_local_linear_calibration"]
      doesNotEstablish := [
        "These bounds are illustrative, not measured experimental confidence intervals."
      ] }
  ]
  openGates := [
    { id := "SC-GATE-01"
      quantity := "Candidate species, cell type, compartment, radical partners, and cofactor occupancy"
      units := "molecular_qualification"
      requiredControl := "Endogenous expression check (distinguished from engineered overexpression or added illumination)"
      status := "unmeasured" },
    { id := "SC-GATE-02"
      quantity := "Radical-pair formation flux F_RP and singlet-channel yield shift ΔΦ_S"
      units := "μM/s and dimensionless"
      requiredControl := "Selective spin perturbation preserving ordinary protein function and cellular health"
      status := "unmeasured" },
    { id := "SC-GATE-03"
      quantity := "First-order product clearance rate k_clear"
      units := "s⁻¹"
      requiredControl := "Matched steady-state and equilibration verification"
      status := "unmeasured" },
    { id := "SC-GATE-04"
      quantity := "Independent membrane-current calibration slope g'(x_0) and threshold δ_y"
      units := "pA/μM and pA"
      requiredControl := "Direct exogenous mediator titration prior to held-out spin perturbation test"
      status := "unmeasured" }
  ]
  sourceArtifacts := [
    ("protocol_url", "https://gravitonresearch.org/writing/spin-chemistry-neural-response/verify-response.py")
  ]
}

end GravitonCert.Studies.SpinChemistry
