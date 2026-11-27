import GravitonCert.Core.Boundary
import GravitonCert.Studies.SpinChemistry

/-!
# GravitonCert.Studies.BioQuantumGates

**Study 11 — Three Machine-Checked Biophysical Gates for Quantum Processes in Neural Dynamics (`BQ-01`–`BQ-06`):**
Extends Graviton Research Note 01 (`SpinChemistry.lean`, `SC-01`–`SC-05`) into a complete,
zero-dependency Lean 4 exclusion-and-survival atlas for quantum neurobiology:

1. **`BQ-01` (Gate 1 — 310 K Decoherence Timescale Separation):** Proves the >10¹⁰× gap
   excluding charge/ion superpositions (`τ ≤ 10⁻¹³ s` vs. `10⁻² s` neural integration),
   while separating spin-protected windows (radical-pair electron spins `~10⁻⁶ s` vs. `10⁻⁷ s`
   chemical step; `³¹P` nuclear spins `~10⁻¹ s`).
2. **`BQ-02` (Gate 2 — Johnson–Nyquist Thermal Current Floor & SNR Exclusion):** Proves
   exact squared thermal current noise `σ_I² = 4 k_B T Δf / R_m`, monotonicity in `R_m` and `Δf`,
   and strict SNR exclusion whenever `(Δŷ)² < SNR_min² · σ_I²`.
3. **`BQ-03` (Nanoscale Microdomain Amplification Ceiling — Closing `SC-04`'s Caveat):**
   Proves inverse-volume amplification `Δc = ΔN / V` and derives the exact maximum compartment
   volume `V_max = (|g'| · ΔN) / δ_y` above which even localized signals fail Gate 2.
4. **`BQ-04` (Gate 3 — Matched-SAR Larmor RF-Resonance Confound Cancellation):** Proves
   identically that subtracting off-resonance RF at matched SAR heating cancels 100% of
   classical thermal and pharmacological confounds, isolating pure spin-dependent signal.
5. **`BQ-05` (Nonlinear LIF Firing-Threshold Amplification vs. Sub-Threshold Exclusion):**
   Proves exact bifurcation boundary `|Δŷ| < I_crit - I_0` (strictly sub-threshold) vs.
   `Δŷ > I_crit - I_0` (threshold crossing).
6. **`BQ-06` (Executable `QuantumNeuralAcceptanceGate`):** Rejects candidates failing any
   of Gates 1–3 while explicitly quarantining the Hard Problem of subjective experience
   (`BQ-GATE-01`) and unmeasured wet-lab controls (`BQ-GATE-02`, `BQ-GATE-03`).

Compiles strictly against Lean 4's core kernel with zero `sorryAx` and zero custom axioms.
-/

namespace GravitonCert.Studies.BioQuantumGates

open GravitonCert
open GravitonCert.Studies.SpinChemistry

/-! ## 1. Gate 1: 310 K Decoherence Timescale Separation (`BQ-01`) -/

/-- Exact rational decoherence survival gate: `τ_decoh ≥ τ_op`. -/
def passesDecoherenceGate (tauDecoh tauOp : Rat) : Bool :=
  decide (tauOp ≤ tauDecoh)

/--
**Theorem BQ-01 (310 K Decoherence Timescale Separation):**
Comparing canonical 310 K timescales (in seconds):
- Neural integration timescale `τ_neural = 10⁻² s` (`10 ms`),
- Radical-pair chemical reaction timescale `τ_chem = 10⁻⁷ s` (`100 ns`),
- Charge/ion superposition decoherence `τ_charge ≤ 10⁻¹³ s` (Tegmark 310 K wall),
- Electron radical-pair spin coherence `τ_rp = 10⁻⁶ s` (`1 μs`),
- Shielded `³¹P` nuclear spin coherence `τ_nuc = 10⁻¹ s` (`100 ms`):
1. Every charge superposition with `0 < τ_charge ≤ 10⁻¹³ s` falls short of neural signaling by at least `10¹¹×`
   (`τ_neural / τ_charge ≥ 10¹¹`) and strictly fails Gate 1 against both `τ_neural` and `τ_chem`.
2. Both radical-pair electron spins (against `τ_chem`) and `³¹P` nuclear spins (against `τ_neural`)
   pass Gate 1 and advance to Gate 2.
-/
theorem thermal_decoherence_timescale_separation (tauCharge : Rat)
    (hPos : 0 < tauCharge) (hWall : tauCharge ≤ (1 : Rat) / 10000000000000) :
    let tauNeural : Rat := (1 : Rat) / 100
    let tauChem : Rat := (1 : Rat) / 10000000
    let tauRP : Rat := (1 : Rat) / 1000000
    let tauNuc : Rat := (1 : Rat) / 10
    ((100000000000 : Rat) ≤ tauNeural / tauCharge) ∧
    (passesDecoherenceGate tauCharge tauNeural = false) ∧
    (passesDecoherenceGate tauCharge tauChem = false) ∧
    (passesDecoherenceGate tauRP tauChem = true) ∧
    (passesDecoherenceGate tauNuc tauNeural = true) := by
  intro tauNeural tauChem tauRP tauNuc
  have hRatio : (100000000000 : Rat) ≤ tauNeural / tauCharge := by
    have hMul : (100000000000 : Rat) * tauCharge ≤ tauNeural := by
      dsimp only [tauNeural]; grind
    have hInv := Rat.inv_pos.mpr hPos
    have h1 := Rat.mul_le_mul_of_nonneg_right hMul (Rat.le_of_lt hInv)
    rw [Rat.mul_assoc, Rat.mul_inv_cancel tauCharge (Rat.ne_of_gt hPos), Rat.mul_one, ← Rat.div_def] at h1
    exact h1
  refine ⟨hRatio, ?_, ?_, ?_, ?_⟩
  · unfold passesDecoherenceGate; dsimp only [tauNeural]; simp only [decide_eq_false_iff_not]; grind
  · unfold passesDecoherenceGate; dsimp only [tauChem]; simp only [decide_eq_false_iff_not]; grind
  · unfold passesDecoherenceGate; dsimp only [tauRP, tauChem]; simp only [decide_eq_true_eq]; grind
  · unfold passesDecoherenceGate; dsimp only [tauNuc, tauNeural]; simp only [decide_eq_true_eq]; grind

/-! ## 2. Gate 2: Johnson–Nyquist Thermal Current Noise Floor & SNR Bound (`BQ-02`) -/

/-- Exact squared Johnson–Nyquist thermal current noise variance `σ_I² = 4 k_B T Δf / R_m`. -/
def thermalNoiseCurrentSq (kBT df Rm : Rat) : Rat :=
  (4 * kBT * df) / Rm

/--
**Theorem BQ-02 (Johnson–Nyquist Thermal Noise Monotonicity & SNR Exclusion):**
For thermal energy `k_B T > 0`, bandwidth `0 < Δf₁ < Δf₂`, membrane resistance `0 < R₁ < R₂`,
and minimum detection ratio `SNR_min > 0`:
1. Thermal noise variance is strictly positive: `0 < σ_I²`,
2. Higher membrane resistance strictly lowers thermal current noise (`σ_I²(R₂) < σ_I²(R₁)`),
3. Wider integration bandwidth strictly raises thermal current noise (`σ_I²(Δf₁) < σ_I²(Δf₂)`),
4. Whenever `(Δŷ)² < SNR_min² · σ_I²`, the signal falls strictly below the required SNR threshold
   (`(Δŷ)² / σ_I² < SNR_min²`).
-/
theorem johnson_nyquist_snr_exclusion_bound
    (kBT df1 df2 R1 R2 dY snrMin : Rat)
    (hkT : 0 < kBT) (hdf1 : 0 < df1) (hdf12 : df1 < df2)
    (hR1 : 0 < R1) (hR12 : R1 < R2) (_hSnr : 0 < snrMin) :
    (0 < thermalNoiseCurrentSq kBT df1 R1) ∧
    (thermalNoiseCurrentSq kBT df1 R2 < thermalNoiseCurrentSq kBT df1 R1) ∧
    (thermalNoiseCurrentSq kBT df1 R1 < thermalNoiseCurrentSq kBT df2 R1) ∧
    (dY * dY < (snrMin * snrMin) * thermalNoiseCurrentSq kBT df1 R1 →
      (dY * dY) / thermalNoiseCurrentSq kBT df1 R1 < snrMin * snrMin) := by
  have hNum1 : 0 < 4 * kBT * df1 := Rat.mul_pos (Rat.mul_pos (by grind) hkT) hdf1
  have hR2 : 0 < R2 := by grind
  have hSigPos : 0 < thermalNoiseCurrentSq kBT df1 R1 := by
    unfold thermalNoiseCurrentSq; rw [Rat.div_def]
    exact Rat.mul_pos hNum1 (Rat.inv_pos.mpr hR1)
  have hInvLt : R2⁻¹ < R1⁻¹ := by
    have h1 := Rat.mul_lt_mul_of_pos_right hR12 (Rat.mul_pos (Rat.inv_pos.mpr hR1) (Rat.inv_pos.mpr hR2))
    have hL : R1 * (R1⁻¹ * R2⁻¹) = R2⁻¹ := by
      rw [← Rat.mul_assoc, Rat.mul_inv_cancel R1 (Rat.ne_of_gt hR1), Rat.one_mul]
    have hR : R2 * (R1⁻¹ * R2⁻¹) = R1⁻¹ := by
      calc R2 * (R1⁻¹ * R2⁻¹) = R1⁻¹ * (R2 * R2⁻¹) := by grind
        _ = R1⁻¹ * 1 := by rw [Rat.mul_inv_cancel R2 (Rat.ne_of_gt hR2)]
        _ = R1⁻¹ := by grind
    rw [hL, hR] at h1
    exact h1
  refine ⟨hSigPos, ?_, ?_, ?_⟩
  · unfold thermalNoiseCurrentSq
    rw [Rat.div_def, Rat.div_def]
    exact Rat.mul_lt_mul_of_pos_left hInvLt hNum1
  · unfold thermalNoiseCurrentSq
    rw [Rat.div_def, Rat.div_def]
    have hNumLt : 4 * kBT * df1 < 4 * kBT * df2 :=
      Rat.mul_lt_mul_of_pos_left hdf12 (Rat.mul_pos (by grind) hkT)
    exact Rat.mul_lt_mul_of_pos_right hNumLt (Rat.inv_pos.mpr hR1)
  · intro hLt
    have hInv := Rat.inv_pos.mpr hSigPos
    have hMul := Rat.mul_lt_mul_of_pos_right hLt hInv
    have hRhs : snrMin * snrMin * thermalNoiseCurrentSq kBT df1 R1 * (thermalNoiseCurrentSq kBT df1 R1)⁻¹ = snrMin * snrMin := by
      rw [Rat.mul_assoc, Rat.mul_inv_cancel _ (Rat.ne_of_gt hSigPos), Rat.mul_one]
    rw [hRhs, ← Rat.div_def] at hMul
    exact hMul

/-! ## 3. Nanoscale Microdomain Amplification Ceiling (`BQ-03`, Closing `SC-04`'s Caveat) -/

/-- Local concentration shift `Δc = ΔN / V` for molecule shift `ΔN` in compartment volume `V`. -/
def localConcShift (dN V : Rat) : Rat := dN / V

/-- Exact maximum compartment volume `V_max = (|g'| · ΔN) / δ_y` capable of reaching threshold `δ_y`. -/
def maxMicrodomainVolume (gPrime dN deltaY : Rat) : Rat :=
  (ratAbs gPrime * dN) / deltaY

/--
**Theorem BQ-03 (Microdomain Inverse-Volume Amplification & Exact Exclusion Volume Ceiling):**
For positive molecule shift `ΔN > 0`, slope `g' ≠ 0`, and threshold `δ_y > 0`:
1. Shrinking compartment volume (`0 < V_micro < V_cell`) strictly amplifies local concentration
   (`Δc(V_cell) < Δc(V_micro)`).
2. **Exact Volume Exclusion Ceiling:** For *every* compartment volume `V > V_max = (|g'| · ΔN) / δ_y`,
   the localized current shift strictly fails threshold: `|g'| · (ΔN / V) < δ_y`.
   Conversely, for any `0 < V < V_max`, the localized shift strictly exceeds `δ_y`.
-/
theorem microdomain_volume_amplification_threshold
    (gPrime dN deltaY Vmicro Vcell V : Rat)
    (hdN : 0 < dN) (_hg : 0 < ratAbs gPrime) (hDelta : 0 < deltaY)
    (hVm : 0 < Vmicro) (hVmc : Vmicro < Vcell) (hV : 0 < V) :
    (localConcShift dN Vcell < localConcShift dN Vmicro) ∧
    (maxMicrodomainVolume gPrime dN deltaY < V → ratAbs gPrime * localConcShift dN V < deltaY) ∧
    (V < maxMicrodomainVolume gPrime dN deltaY → deltaY < ratAbs gPrime * localConcShift dN V) := by
  have hVc : 0 < Vcell := by grind
  have hInvLt : ∀ a b : Rat, 0 < a → a < b → b⁻¹ < a⁻¹ := by
    intro a b ha hab
    have hb : 0 < b := by grind
    have h1 := Rat.mul_lt_mul_of_pos_right hab (Rat.mul_pos (Rat.inv_pos.mpr ha) (Rat.inv_pos.mpr hb))
    have hL : a * (a⁻¹ * b⁻¹) = b⁻¹ := by
      rw [← Rat.mul_assoc, Rat.mul_inv_cancel a (Rat.ne_of_gt ha), Rat.one_mul]
    have hR : b * (a⁻¹ * b⁻¹) = a⁻¹ := by
      calc b * (a⁻¹ * b⁻¹) = a⁻¹ * (b * b⁻¹) := by grind
        _ = a⁻¹ * 1 := by rw [Rat.mul_inv_cancel b (Rat.ne_of_gt hb)]
        _ = a⁻¹ := by grind
    rw [hL, hR] at h1; exact h1
  refine ⟨?_, ?_, ?_⟩
  · unfold localConcShift; rw [Rat.div_def, Rat.div_def]
    exact Rat.mul_lt_mul_of_pos_left (hInvLt Vmicro Vcell hVm hVmc) hdN
  · intro hGt
    unfold maxMicrodomainVolume at hGt
    have hMul := Rat.mul_lt_mul_of_pos_right hGt hDelta
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel deltaY (Rat.ne_of_gt hDelta), Rat.mul_one] at hMul
    have hDiv := Rat.mul_lt_mul_of_pos_right hMul (Rat.inv_pos.mpr hV)
    have hRhs : V * deltaY * V⁻¹ = deltaY := by
      calc V * deltaY * V⁻¹ = deltaY * (V * V⁻¹) := by grind
        _ = deltaY * 1 := by rw [Rat.mul_inv_cancel V (Rat.ne_of_gt hV)]
        _ = deltaY := by grind
    rw [hRhs] at hDiv
    unfold localConcShift; rw [Rat.div_def, ← Rat.mul_assoc]
    exact hDiv
  · intro hLt
    unfold maxMicrodomainVolume at hLt
    have hMul := Rat.mul_lt_mul_of_pos_right hLt hDelta
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel deltaY (Rat.ne_of_gt hDelta), Rat.mul_one] at hMul
    have hDiv := Rat.mul_lt_mul_of_pos_right hMul (Rat.inv_pos.mpr hV)
    have hLhs : V * deltaY * V⁻¹ = deltaY := by
      calc V * deltaY * V⁻¹ = deltaY * (V * V⁻¹) := by grind
        _ = deltaY * 1 := by rw [Rat.mul_inv_cancel V (Rat.ne_of_gt hV)]
        _ = deltaY := by grind
    rw [hLhs] at hDiv
    unfold localConcShift; rw [Rat.div_def, ← Rat.mul_assoc]
    exact hDiv

/-! ## 4. Gate 3: Matched-SAR Larmor RF-Resonance Confound Cancellation (`BQ-04`) -/

/-- Observed neural response decomposed into spin-resonance signal + thermal heating + drug/background confound. -/
def observedResponse (spinSignal thermalSAR drugConfound : Rat) : Rat :=
  spinSignal + thermalSAR + drugConfound

/--
**Theorem BQ-04 (Matched-SAR Larmor RF-Resonance Confound Cancellation):**
Comparing on-resonance Larmor RF (`ν = ν_L`, signal `S_spin`) against off-resonance RF at
identical SAR heating (`P`, `S_spin_off = 0`) and identical pharmacological/cellular background (`C_drug`):
1. The matched-SAR contrast cancels **100%** of thermal heating and pharmacological confounds identically:
   `Y(S_spin, C_SAR, C_drug) - Y(0, C_SAR, C_drug) = S_spin`,
2. If no genuine spin-dependent mechanism is active (`S_spin = 0`), the matched-SAR contrast
   vanishes identically (`= 0`) regardless of how large the classical heating or drug effect is.
-/
theorem matched_sar_larmor_resonance_confound_cancellation
    (spinSignal thermalSAR drugConfound : Rat) :
    (observedResponse spinSignal thermalSAR drugConfound -
      observedResponse 0 thermalSAR drugConfound = spinSignal) ∧
    (observedResponse 0 thermalSAR drugConfound -
      observedResponse 0 thermalSAR drugConfound = 0) := by
  unfold observedResponse
  grind

/-! ## 5. Nonlinear LIF Firing-Threshold Amplification vs. Sub-Threshold Exclusion (`BQ-05`) -/

/--
**Theorem BQ-05 (Leaky Integrate-and-Fire Bifurcation Margin Theorem):**
For a neuron with baseline drive `I_0 < I_crit` (positive safety margin `M = I_crit - I_0 > 0`)
receiving a perturbation `Δŷ`:
1. If `|Δŷ| < M`, the neuron **strictly cannot cross threshold** (`I_0 + Δŷ < I_crit`),
2. If `Δŷ > M`, the neuron **strictly crosses threshold** (`I_crit < I_0 + Δŷ`),
quantifying the exact critical-margin window required for nonlinear firing amplification.
-/
theorem lif_firing_threshold_amplification_vs_exclusion (I0 Icrit dY : Rat)
    (hSub : I0 < Icrit) :
    let margin := Icrit - I0
    (ratAbs dY < margin → I0 + dY < Icrit) ∧
    (margin < dY → Icrit < I0 + dY) := by
  intro margin
  refine ⟨?_, ?_⟩
  · intro hLt
    unfold ratAbs at hLt
    by_cases h : dY < 0 <;> simp only [h, ↓reduceIte] at hLt <;> dsimp only [margin] at hLt <;> grind
  · intro hGt
    dsimp only [margin] at hGt; grind

/-! ## 6. Executable `QuantumNeuralAcceptanceGate` (`BQ-06`) -/

structure QuantumNeuralAcceptanceGate where
  passesGate1Decoherence : Bool
  passesGate2ThermalSNR : Bool
  passesGate3MatchedControl : Bool
  deriving DecidableEq, Repr

def passesQuantumNeuralGate (g : QuantumNeuralAcceptanceGate) : Bool :=
  g.passesGate1Decoherence && g.passesGate2ThermalSNR && g.passesGate3MatchedControl

/-- Naive charge superposition (fails Gate 1 Tegmark wall). -/
def chargeSuperpositionCandidate : QuantumNeuralAcceptanceGate :=
  { passesGate1Decoherence := false, passesGate2ThermalSNR := false, passesGate3MatchedControl := false }

/-- Bare epothilone B microtubule pharmacology without spin-selective control (fails Gate 3). -/
def uncontrolledDrugCandidate : QuantumNeuralAcceptanceGate :=
  { passesGate1Decoherence := true, passesGate2ThermalSNR := true, passesGate3MatchedControl := false }

/-- Qualified spin-chemical candidate passing all 3 biophysical gates (still quarantined from Hard Problem!). -/
def qualifiedSpinChemicalWitness : QuantumNeuralAcceptanceGate :=
  { passesGate1Decoherence := true, passesGate2ThermalSNR := true, passesGate3MatchedControl := true }

/--
**Theorem BQ-06 (Executable Three-Gate Quantum-to-Neural Acceptance Soundness):**
1. Naive charge superpositions (`Gate 1 = false`) and uncontrolled pharmacological claims
   (`Gate 3 = false`) are formally rejected,
2. Dropping *any* of the three gates causes rejection,
3. `qualifiedSpinChemicalWitness` passes all three biophysical gates (while leaving the Hard Problem
   of subjective qualia explicitly quarantined in `BQ-GATE-01`).
-/
theorem quantum_neural_acceptance_gate_soundness (g : QuantumNeuralAcceptanceGate) :
    (passesQuantumNeuralGate chargeSuperpositionCandidate = false) ∧
    (passesQuantumNeuralGate uncontrolledDrugCandidate = false) ∧
    (passesQuantumNeuralGate qualifiedSpinChemicalWitness = true) ∧
    (g.passesGate1Decoherence = false → passesQuantumNeuralGate g = false) ∧
    (g.passesGate2ThermalSNR = false → passesQuantumNeuralGate g = false) ∧
    (g.passesGate3MatchedControl = false → passesQuantumNeuralGate g = false) := by
  cases g with
  | mk a b c =>
    cases a <;> cases b <;> cases c <;> decide

/-! ## 7. Study Certificate Registration (`graviton-cert`) -/

def studyCertificate : StudyCertificate := {
  studyId := "bioquantum-neural-three-gates"
  title := "Working Paper 05: Three Machine-Checked Biophysical Gates for Quantum Processes in Neural Dynamics"
  url := "https://gravitonresearch.org/inquiry/quantum-consciousness/"
  domain := "Quantum Biology / Computational Neuroscience / Epistemic Gates"
  scopeStatement := "Zero-dependency Lean 4 formalization of Graviton's Three-Gate Standard for evaluating quantum-brain hypotheses: (1) 310 K decoherence timescale separation excluding charge superpositions while passing spin windows; (2) Johnson–Nyquist thermal noise SNR bounds and exact nanoscale microdomain volume ceilings closing SC-04's well-mixed caveat; (3) matched-SAR Larmor RF-resonance confound cancellation; and (4) nonlinear LIF firing-threshold margin bounds. Explicitly quarantines the Hard Problem of subjective experience and unmeasured wet-lab data."
  assumptions := [
    { id := "BQ-A1_310k_thermal_bath"
      kind := "physical_regime"
      statement := "Physiological mammalian brain temperature T ≈ 310 K with Johnson–Nyquist membrane resistance noise σ_I² = 4 k_B T Δf / R_m." },
    { id := "BQ-A2_additive_confound_model"
      kind := "biological_idealization"
      statement := "Local additive separation of spin-resonance response from matched-SAR thermal heating and background pharmacology in controlled RF contrast experiments." },
    { id := "BQ-A3_lif_threshold"
      kind := "biological_idealization"
      statement := "Sub-threshold leaky integrate-and-fire neuronal excitability margin M = I_crit - I_0 > 0." }
  ]
  claims := [
    { id := "BQ-01"
      title := "Gate 1: 310 K Decoherence Timescale Separation (>10¹¹× Charge Gap vs. Spin Windows)"
      leanDecl := ``thermal_decoherence_timescale_separation
      claimKind := "exclusion_bound"
      summary := "Proves charge superpositions (τ ≤ 10⁻¹³ s) fail 10 ms neural integration by ≥ 10¹¹×, while electron radical-pair spins (1 μs vs. 100 ns chemistry) and ³¹P nuclear spins pass Gate 1."
      assumptionIds := ["BQ-A1_310k_thermal_bath"]
      doesNotEstablish := [
        "Passing Gate 1 decoherence survival does not prove a spin mechanism actually couples to neural firing or consciousness."
      ] },
    { id := "BQ-02"
      title := "Gate 2: Johnson–Nyquist Thermal Current Floor & SNR Exclusion Bound"
      leanDecl := ``johnson_nyquist_snr_exclusion_bound
      claimKind := "exclusion_bound"
      summary := "Proves strict monotonicity of σ_I² = 4 k_B T Δf / R_m in R_m and Δf and strict SNR exclusion whenever (Δŷ)² < SNR_min² · σ_I²."
      assumptionIds := ["BQ-A1_310k_thermal_bath"]
      doesNotEstablish := [
        "Thermal noise is a lower bound; real neurons also exhibit synaptic background and ion-channel shot noise."
      ] },
    { id := "BQ-03"
      title := "Nanoscale Microdomain Inverse-Volume Amplification & Exact Exclusion Volume Ceiling"
      leanDecl := ``microdomain_volume_amplification_threshold
      claimKind := "theorem"
      summary := "Closes SC-04's well-mixed caveat by proving exact maximum microdomain volume V_max = (|g'| · ΔN) / δ_y above which localized shifts strictly fail threshold."
      assumptionIds := ["BQ-A1_310k_thermal_bath"]
      doesNotEstablish := [
        "Existence of a theoretical microdomain ceiling does not prove endogenous radical pairs actually form inside such a sub-volume in vivo."
      ] },
    { id := "BQ-04"
      title := "Gate 3: Matched-SAR Larmor RF-Resonance Confound Cancellation"
      leanDecl := ``matched_sar_larmor_resonance_confound_cancellation
      claimKind := "theorem"
      summary := "Proves identically that subtracting off-resonance RF at matched SAR power cancels 100% of classical thermal heating and drug confounds, isolating pure spin signal."
      assumptionIds := ["BQ-A2_additive_confound_model"]
      doesNotEstablish := [
        "Requires experimental verification that RF coil SAR is genuinely matched across frequencies (BQ-GATE-02)."
      ] },
    { id := "BQ-05"
      title := "Nonlinear LIF Firing-Threshold Amplification vs. Sub-Threshold Exclusion"
      leanDecl := ``lif_firing_threshold_amplification_vs_exclusion
      claimKind := "theorem"
      summary := "Proves a perturbation |Δŷ| < I_crit - I_0 strictly cannot trigger a spike, whereas Δŷ > I_crit - I_0 crosses firing threshold."
      assumptionIds := ["BQ-A3_lif_threshold"]
      doesNotEstablish := [
        "Threshold crossing in a single neuron does not establish a causal role in subjective conscious experience."
      ] },
    { id := "BQ-06"
      title := "Executable Three-Gate QuantumNeuralAcceptanceGate & Confound Rejection"
      leanDecl := ``quantum_neural_acceptance_gate_soundness
      claimKind := "theorem"
      summary := "Purely constructive gate formally rejecting naive charge superpositions and uncontrolled pharmacology while certifying the 3-gate biophysical standard."
      assumptionIds := ["BQ-A1_310k_thermal_bath", "BQ-A2_additive_confound_model", "BQ-A3_lif_threshold"]
      doesNotEstablish := [
        "Passing all three biophysical gates proves genuine quantum neurobiology, NOT a solution to the Hard Problem of consciousness (BQ-GATE-01)."
      ] }
  ]
  openGates := [
    { id := "BQ-GATE-01"
      quantity := "Explanatory bridge from biophysical neural dynamics (classical or quantum) to subjective qualia (Hard Problem)"
      units := "foundational / philosophical boundary"
      requiredControl := "Explicit distinction between third-person neural correlates/modulators and first-person phenomenal experience"
      status := "open_theoretical_obligation" },
    { id := "BQ-GATE-02"
      quantity := "Pre-registered matched-SAR Larmor RF-resonance patch-clamp experiment on primary cortical/hippocampal neurons"
      units := "pA current contrast at matched SAR (W/kg)"
      requiredControl := "Blinded on-resonance (1.4 MHz at 50 μT) vs. off-resonance RF with matched heating and exogenous ROS calibration"
      status := "open_experimental_gate" },
    { id := "BQ-GATE-03"
      quantity := "Blinded nuclear-spin isotope replication (¹²⁹Xe/¹³¹Xe vs. ¹³²Xe/¹³⁴Xe) and endogenous in vivo Posner / microtubule controls"
      units := "anesthetic MAC / LORR delta under matched classical controls"
      requiredControl := "Multi-lab adversarial replication separating nuclear-spin effects from mass/pharmacokinetic/structural confounds"
      status := "open_experimental_gate" }
  ]
  sourceArtifacts := [
    ("working_paper_05_tex", "paper/bioquantum-main.tex"),
    ("quantum_consciousness_inquiry", "https://gravitonresearch.org/inquiry/quantum-consciousness/")
  ]
}

end GravitonCert.Studies.BioQuantumGates
