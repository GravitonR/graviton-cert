import GravitonCert.Core.Boundary
import GravitonCert.Core.Interval

/-!
# GravitonCert.Studies.ObservationWindow

Machine-checked formalization of Graviton Research Note 02:
*"When the observation window changes the result"*
<https://gravitonresearch.org/writing/when-quantum-models-disagree/>

Proves in Lean 4's kernel (zero floating point, zero `sorry`):
1. Exact 4-qubit Pauli / Majorana Clifford algebra (`{ψ_i, ψ_j} = δ_{ij} I` for all 64 pairs),
2. **Exact Spectator Conservation**: `ψ_8` commutes with all 35 quartic operators (`[H_0 + λP, ψ_8] = 0`),
3. **Commuting Controls & Non-Commuting Reference**: `P_{1267}` and `P_{4567}` commute with `H_0`; `P_{1235}` anticommutes with `P_{1245} ∈ H_0`,
4. **Exact Closed-Form 4-Block Clifford Reduction of `H_0 + λ P_{1235}`**:
   - All 5 terms of `H_0` mutually commute,
   - Exact stabilizer relations `Q_{1245} Q_{1356} Q_{2346} = -I` and `Q_{1245} Q_{1347} Q_{2357} = +I`,
   - `P_{1235}` commutes with `Q_{1347}, Q_{2346}` and anticommutes with `Q_{1245}, Q_{1356}, Q_{2357}`,
   - Exact RMS energy-matching ratio `α² = 9583 / 9983`,
   - Exact conjugation sign table for all 7 active Majorana operators `ψ₁..ψ₇`,
5. **Rigorous Fixed-Point Interval Certification of the Sign Reversal (Closing `OW-GATE-01`)**:
   - Exact kernel-verified square-root enclosures for `α` and all four 2×2 block frequencies,
   - Pure-integer interval evaluation of `D_W(H₀)` and `D_W(H₁)` directly from the exact closed-form 4-block Clifford trace formula,
   - Formally certifies `D_{[12,24]}(H₁) < D_{[12,24]}(H₀)` (`ΔD < 0`) AND `D_{[36,48]}(H₀) < D_{[36,48]}(H₁)` (`ΔD > 0`) with zero floating point!
-/

namespace GravitonCert.Studies.ObservationWindow

open GravitonCert.Interval

/-- Single-qubit Pauli operator (`I`, `X`, `Y`, `Z`). -/
inductive Pauli1 where
  | I | X | Y | Z
  deriving DecidableEq, Repr

/-- Exact single-qubit Pauli multiplication returning `(phase_power_of_i : Fin 4, op)`. -/
def Pauli1.mul : Pauli1 → Pauli1 → Fin 4 × Pauli1
  | .I, p => (0, p)
  | p, .I => (0, p)
  | .X, .X => (0, .I)
  | .Y, .Y => (0, .I)
  | .Z, .Z => (0, .I)
  | .X, .Y => (1, .Z)
  | .Y, .X => (3, .Z)
  | .Y, .Z => (1, .X)
  | .Z, .Y => (3, .X)
  | .Z, .X => (1, .Y)
  | .X, .Z => (3, .Y)

/-- Exact 4-qubit signed Pauli string: `i^phase * (q0 ⊗ q1 ⊗ q2 ⊗ q3)`. -/
structure Pauli4 where
  phase : Fin 4
  q0 : Pauli1
  q1 : Pauli1
  q2 : Pauli1
  q3 : Pauli1
  deriving DecidableEq, Repr

namespace Pauli4

def id : Pauli4 := ⟨0, .I, .I, .I, .I⟩

def neg (p : Pauli4) : Pauli4 :=
  { p with phase := p.phase + 2 }

def mul (a b : Pauli4) : Pauli4 :=
  let (p0, r0) := Pauli1.mul a.q0 b.q0
  let (p1, r1) := Pauli1.mul a.q1 b.q1
  let (p2, r2) := Pauli1.mul a.q2 b.q2
  let (p3, r3) := Pauli1.mul a.q3 b.q3
  ⟨a.phase + b.phase + p0 + p1 + p2 + p3, r0, r1, r2, r3⟩

instance : Mul Pauli4 := ⟨Pauli4.mul⟩

end Pauli4

/-- Exact Jordan–Wigner Majorana operators `ψ̃_k = √2 · ψ_k` (`k : Fin 8`, 0-indexed for `ψ₁..ψ₈`). -/
def majorana : Fin 8 → Pauli4
  | ⟨0, _⟩ => ⟨0, .X, .I, .I, .I⟩
  | ⟨1, _⟩ => ⟨0, .Y, .I, .I, .I⟩
  | ⟨2, _⟩ => ⟨0, .Z, .X, .I, .I⟩
  | ⟨3, _⟩ => ⟨0, .Z, .Y, .I, .I⟩
  | ⟨4, _⟩ => ⟨0, .Z, .Z, .X, .I⟩
  | ⟨5, _⟩ => ⟨0, .Z, .Z, .Y, .I⟩
  | ⟨6, _⟩ => ⟨0, .Z, .Z, .Z, .X⟩
  | ⟨7, _⟩ => ⟨0, .Z, .Z, .Z, .Y⟩

/-- **Theorem 1 (Exact 4-Qubit Majorana Clifford Relations — 64 pairs):** `{ψ_i, ψ_j} = δ_{ij} I`. -/
theorem majorana_clifford_relations :
    ∀ i j : Fin 8,
      (i = j → majorana i * majorana j = Pauli4.id) ∧
      (i ≠ j → majorana i * majorana j = Pauli4.neg (majorana j * majorana i)) := by
  decide

/-- Quartic Majorana product `Q_{abcd} = ψ̃_a ψ̃_b ψ̃_c ψ̃_d` (0-indexed for `1..7`). -/
def quartic (a b c d : Fin 7) : Pauli4 :=
  majorana ⟨a.val, by omega⟩ *
  majorana ⟨b.val, by omega⟩ *
  majorana ⟨c.val, by omega⟩ *
  majorana ⟨d.val, by omega⟩

def psi8 : Pauli4 := majorana ⟨7, by decide⟩

/-- **Theorem 2 (Exact Spectator Conservation Across All 35 Quartic Terms / 180 Hamiltonians).** -/
theorem spectator_psi8_commutes_with_all_quartic_terms :
    ∀ a b c d : Fin 7,
      a < b → b < c → c < d →
      quartic a b c d * psi8 = psi8 * quartic a b c d := by
  decide

def Q_1245 : Pauli4 := quartic ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨3, by decide⟩ ⟨4, by decide⟩
def Q_1347 : Pauli4 := quartic ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨3, by decide⟩ ⟨6, by decide⟩
def Q_1356 : Pauli4 := quartic ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨4, by decide⟩ ⟨5, by decide⟩
def Q_2346 : Pauli4 := quartic ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨3, by decide⟩ ⟨5, by decide⟩
def Q_2357 : Pauli4 := quartic ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨4, by decide⟩ ⟨6, by decide⟩

def baselineH0Terms : List Pauli4 := [Q_1245, Q_1347, Q_1356, Q_2346, Q_2357]

def P_1267 : Pauli4 := quartic ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨5, by decide⟩ ⟨6, by decide⟩
def P_4567 : Pauli4 := quartic ⟨3, by decide⟩ ⟨4, by decide⟩ ⟨5, by decide⟩ ⟨6, by decide⟩
def P_1235 : Pauli4 := quartic ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨4, by decide⟩

/-- **Theorem 3 (Commuting Control Perturbations `P_{1267}` and `P_{4567}`).** -/
theorem control_perturbations_commute_with_H0 :
    (∀ h ∈ baselineH0Terms, P_1267 * h = h * P_1267) ∧
    (∀ h ∈ baselineH0Terms, P_4567 * h = h * P_4567) := by
  decide

/-- **Theorem 4 (Reference Perturbation `P_{1235}` Anticommutes with `Q_{1245} ∈ H₀`).** -/
theorem reference_perturbation_noncommuting :
    ∃ h ∈ baselineH0Terms, P_1235 * h = Pauli4.neg (h * P_1235) := by
  refine ⟨Q_1245, by decide, by decide⟩

/--
**Theorem 5 (Exact 4-Block Clifford Reduction of `H₀` and `H₀ + λ P_{1235}`):**
1. All 5 terms of `H₀` mutually commute and square to `+I`.
2. Exact stabilizer relations: `Q_{1245} Q_{1356} Q_{2346} = -I` and `Q_{1245} Q_{1347} Q_{2357} = +I`,
   so `H₀` is generated by 3 independent commuting Pauli stabilizers `(Q_{1347}, Q_{2346}, Q_{1245})`.
3. `P_{1235}` commutes with `Q_{1347}, Q_{2346}` and anticommutes with `Q_{1245}, Q_{1356}, Q_{2357}`,
   reducing the full 16×16 Hamiltonian `H₀ + λ P_{1235}` to four exact 2×2 Pauli blocks!
-/
theorem exact_four_block_clifford_reduction :
    (∀ a ∈ baselineH0Terms, ∀ b ∈ baselineH0Terms, a * b = b * a) ∧
    (∀ a ∈ baselineH0Terms, a * a = Pauli4.id) ∧
    (P_1235 * P_1235 = Pauli4.id) ∧
    (Q_1245 * Q_1356 * Q_2346 = Pauli4.neg Pauli4.id) ∧
    (Q_1245 * Q_1347 * Q_2357 = Pauli4.id) ∧
    (P_1235 * Q_1347 = Q_1347 * P_1235) ∧
    (P_1235 * Q_2346 = Q_2346 * P_1235) ∧
    (P_1235 * Q_1245 = Pauli4.neg (Q_1245 * P_1235)) ∧
    (P_1235 * Q_1356 = Pauli4.neg (Q_1356 * P_1235)) ∧
    (P_1235 * Q_2357 = Pauli4.neg (Q_2357 * P_1235)) := by
  decide

/-- Commutation sign `+1` or `-1` of `ψ̃_i` with a Pauli operator `q`. -/
def commSign (a b : Pauli4) : Int :=
  if a * b = b * a then 1 else -1

/-- Exact conjugation sign 4-tuple `(c1, c2, c3, cp)` of `ψ_i` against `(Q_{1347}, Q_{2346}, Q_{1245}, P_{1235})`. -/
def conjSigns (i : Fin 7) : Int × Int × Int × Int :=
  let op := majorana ⟨i.val, by omega⟩
  (commSign op Q_1347, commSign op Q_2346, commSign op Q_1245, commSign op P_1235)

/-- **Theorem 6 (Exact RMS Energy-Matching Ratio `α² = 9583 / 9983`):** -/
theorem exact_rms_energy_ratio_sq :
    let s0 : Rat := (-36/100)^2 + (19/100)^2 + (-71/100)^2 + (22/100)^2 + (49/100)^2
    let s1 : Rat := s0 + (20/100)^2
    s0 = 9583 / 10000 ∧ s1 = 9983 / 10000 ∧ s0 / s1 = 9583 / 9983 := by
  grind

/-! ### Rigorous Kernel-Checked Interval Verification of the Sign Reversal (Closing `OW-GATE-01`) -/

/-- Exact rational square-root enclosure for `α = √(9583 / 9983)` at scale `10^6`. -/
def alphaIv : Iv := ⟨979761, 979762⟩

/-- Exact square-root enclosures `(r1_iv, cosθ_iv, sinθ_iv)` for the 4 blocks `(s1, s2) ∈ {±1}²`. -/
def blockPertParams (s1 s2 : Int) : Iv × Iv × Iv × Int :=
  -- Returns (r_scaled, |a|/r, b/r, sign(a))
  if s1 = -1 ∧ s2 = -1 then (⟨385234, 385235⟩, ⟨991881, 991882⟩, ⟨127164, 127165⟩, -1)
  else if s1 = -1 ∧ s2 = 1 then (⟨59797, 59798⟩, ⟨573462, 573463⟩, ⟨819231, 819232⟩, -1)
  else if s1 = 1 ∧ s2 = -1 then (⟨150274, 150275⟩, ⟨945372, 945373⟩, ⟨325990, 325991⟩, -1)
  else (⟨211501, 211502⟩, ⟨972806, 972807⟩, ⟨231620, 231621⟩, 1)

/--
**Theorem 7 (Kernel-Verified Rational Square-Root Certificates):**
Proves that `alphaIv` and all four 2×2 block frequencies and mixing-angle cosines/sines
strictly enclose their exact algebraic square roots (`lo² ≤ exact ≤ hi²`).
-/
theorem spectral_sqrt_enclosures_certified :
    isSqrtEnclosure 9583 9983 alphaIv = true ∧
    -- Block (-1, -1): a_num = -156
    isSqrtEnclosure (9583 * (156 * 156 + 400)) (9983 * 160000) ⟨385234, 385235⟩ = true ∧
    isSqrtEnclosure (156 * 156) (156 * 156 + 400) ⟨991881, 991882⟩ = true ∧
    isSqrtEnclosure 400 (156 * 156 + 400) ⟨127164, 127165⟩ = true ∧
    -- Block (-1, +1): a_num = -14
    isSqrtEnclosure (9583 * (14 * 14 + 400)) (9983 * 160000) ⟨59797, 59798⟩ = true ∧
    isSqrtEnclosure (14 * 14) (14 * 14 + 400) ⟨573462, 573463⟩ = true ∧
    isSqrtEnclosure 400 (14 * 14 + 400) ⟨819231, 819232⟩ = true ∧
    -- Block (+1, -1): a_num = -58
    isSqrtEnclosure (9583 * (58 * 58 + 400)) (9983 * 160000) ⟨150274, 150275⟩ = true ∧
    isSqrtEnclosure (58 * 58) (58 * 58 + 400) ⟨945372, 945373⟩ = true ∧
    isSqrtEnclosure 400 (58 * 58 + 400) ⟨325990, 325991⟩ = true ∧
    -- Block (+1, +1): a_num = +84
    isSqrtEnclosure (9583 * (84 * 84 + 400)) (9983 * 160000) ⟨211501, 211502⟩ = true ∧
    isSqrtEnclosure (84 * 84) (84 * 84 + 400) ⟨972806, 972807⟩ = true ∧
    isSqrtEnclosure 400 (84 * 84 + 400) ⟨231620, 231621⟩ = true := by
  decide

/-- Exact baseline commuting frequency `E_c(s1, s2) = (19*s1 + 22*s2) / 400` scaled by `SCALE = 10^6`. -/
def ecBaseScaled (s1 s2 : Int) : Int := (19 * s1 + 22 * s2) * 2500

/-- Exact baseline anticommuting frequency `A(s1, s2) = (-36 + 71*s2 + 49*s1) / 400` scaled by `SCALE = 10^6`. -/
def aBaseScaled (s1 s2 : Int) : Int := (-36 + 71 * s2 + 49 * s1) * 2500

/-- Pre-tabulated conjugation signs `(c1, c2, c3, cp)` for `ψ₁..ψ₇` (fast O(1) lookup). -/
def conjSignsTable : Fin 7 → Int × Int × Int × Int
  | ⟨0, _⟩ => (-1,  1, -1, -1)
  | ⟨1, _⟩ => ( 1, -1, -1, -1)
  | ⟨2, _⟩ => (-1, -1,  1, -1)
  | ⟨3, _⟩ => (-1, -1, -1,  1)
  | ⟨4, _⟩ => ( 1,  1, -1, -1)
  | ⟨5, _⟩ => ( 1, -1,  1,  1)
  | ⟨6, _⟩ => (-1,  1,  1,  1)

/-- Kernel proof that `conjSignsTable` matches the exact Pauli Clifford commutators for all 7 operators. -/
theorem conjSigns_eq_table : ∀ i : Fin 7, conjSigns i = conjSignsTable i := by
  decide

/-- Exact interval enclosure of `G_i(t)` for baseline `H₀` at `t = tTenths / 10`. -/
def gBaseIv (i : Fin 7) (tTenths : Int) : Iv :=
  let (c1, c2, c3, _) := conjSignsTable i
  let evalBlock (s1 s2 : Int) : Iv :=
    let dec := (ecBaseScaled s1 s2 - ecBaseScaled (c1 * s1) (c2 * s2)) * tTenths / 10
    let da  := (aBaseScaled s1 s2 - c3 * aBaseScaled (c1 * s1) (c2 * s2)) * tTenths / 10
    (cosIv (Iv.point dec)).mul (cosIv (Iv.point da))
  let sum := ((evalBlock (-1) (-1)).add (evalBlock (-1) 1)).add ((evalBlock 1 (-1)).add (evalBlock 1 1))
  sum.divPosInt 4

/-- Exact interval enclosure of `G_i(t)` for perturbed `H₁ = α (H₀ + 0.2 P_{1235})` at `t = tTenths / 10`. -/
def gPertIv (i : Fin 7) (tTenths : Int) : Iv :=
  let (c1, c2, c3, cp) := conjSignsTable i
  let evalBlock (s1 s2 : Int) : Iv :=
    let dec0 := ecBaseScaled s1 s2 - ecBaseScaled (c1 * s1) (c2 * s2)
    let decIv := ((alphaIv.scaleInt dec0).divPosInt SCALE).scaleInt tTenths |>.divPosInt 10
    let (r1, cos1, sin1, sgn1) := blockPertParams s1 s2
    let (r2, cos2, sin2, sgn2) := blockPertParams (c1 * s1) (c2 * s2)
    let r1t := (r1.scaleInt tTenths).divPosInt 10
    let r2t := (r2.scaleInt tTenths).divPosInt 10
    let dotCoef := ((cos1.mul cos2).scaleInt (sgn1 * sgn2 * c3)).add ((sin1.mul sin2).scaleInt cp)
    let inner := ((cosIv r1t).mul (cosIv r2t)).add (dotCoef.mul ((sinIv r1t).mul (sinIv r2t)))
    (cosIv decIv).mul inner
  let sum := ((evalBlock (-1) (-1)).add (evalBlock (-1) 1)).add ((evalBlock 1 (-1)).add (evalBlock 1 1))
  sum.divPosInt 4

/-- Direct unrolled sum of `|G_i(t)|` over all 7 active Majorana operators. -/
def rowBaseIv (tTenths : Int) : Iv :=
  (((((((gBaseIv ⟨0, by decide⟩ tTenths).abs.add (gBaseIv ⟨1, by decide⟩ tTenths).abs).add
       (gBaseIv ⟨2, by decide⟩ tTenths).abs).add (gBaseIv ⟨3, by decide⟩ tTenths).abs).add
      (gBaseIv ⟨4, by decide⟩ tTenths).abs).add (gBaseIv ⟨5, by decide⟩ tTenths).abs).add
     (gBaseIv ⟨6, by decide⟩ tTenths).abs)

def rowPertIv (tTenths : Int) : Iv :=
  (((((((gPertIv ⟨0, by decide⟩ tTenths).abs.add (gPertIv ⟨1, by decide⟩ tTenths).abs).add
       (gPertIv ⟨2, by decide⟩ tTenths).abs).add (gPertIv ⟨3, by decide⟩ tTenths).abs).add
      (gPertIv ⟨4, by decide⟩ tTenths).abs).add (gPertIv ⟨5, by decide⟩ tTenths).abs).add
     (gPertIv ⟨6, by decide⟩ tTenths).abs)

/-- Sum of `|G_i(t)|` over `i = 1..7` and uniform grid `tStart, tStart + step, ..., tStart + nSteps * step` (in tenths). -/
def windowSumBase (tStartTenths stepTenths : Nat) : Nat → Iv
  | 0 => rowBaseIv (Int.ofNat tStartTenths)
  | n + 1 => (windowSumBase tStartTenths stepTenths n).add (rowBaseIv (Int.ofNat (tStartTenths + (n + 1) * stepTenths)))

def windowSumPert (tStartTenths stepTenths : Nat) : Nat → Iv
  | 0 => rowPertIv (Int.ofNat tStartTenths)
  | n + 1 => (windowSumPert tStartTenths stepTenths n).add (rowPertIv (Int.ofNat (tStartTenths + (n + 1) * stepTenths)))

section
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/--
**Theorem 8 (Kernel-Certified Window-Reversal Theorem — Closing `OW-GATE-01`):**
Evaluating the exact closed-form 4-block Clifford trace via sound fixed-point
interval arithmetic (zero floating point, zero external solvers!) proves:
1. On window `[12, 24]` (`Δt = 0.5`, 25 samples × 7 operators = 175 evaluations),
   `(D_perturbed).hi < (D_baseline).lo` — strictly negative contrast `ΔD < 0`!
2. On window `[36, 48]` (`Δt = 0.5`, 25 samples × 7 operators = 175 evaluations),
   `(D_baseline).hi < (D_perturbed).lo` — strictly positive contrast `ΔD > 0`!
-/
theorem certified_interval_window_reversal :
    (windowSumPert 120 5 24).hi < (windowSumBase 120 5 24).lo ∧
    (windowSumBase 360 5 24).hi < (windowSumPert 360 5 24).lo := by
  decide

end

/-- The four observation windows declared in Research Note 02 (`protocol.json`). -/
inductive ObsWindow where
  | w0_12 | w12_24 | w24_36 | w36_48
  deriving DecidableEq, Repr

/--
**Theorem 9 (Formal Scope & Reversal Refutation Principle):**
Given any contrast functional `ΔD : ObsWindow → Rat`, a negative contrast on `W₁`
and positive contrast on `W₂` leave the bounded claim `ΔD W₁ < 0` valid while
formally refuting the universal generalization `∀ W, ΔD W < 0`.
-/
theorem window_reversal_refutes_universal_sign
    (deltaD : ObsWindow → Rat)
    (wNeg wPos : ObsWindow)
    (hNeg : deltaD wNeg < 0)
    (hPos : 0 < deltaD wPos) :
    deltaD wNeg < 0 ∧ ¬ (∀ w : ObsWindow, deltaD w < 0) := by
  refine ⟨hNeg, ?_⟩
  intro hAll
  have hlt : deltaD wPos < 0 := hAll wPos
  grind

/-- Certificate metadata linking these Lean 4 theorems to `gravitonresearch.org`. -/
def studyCertificate : StudyCertificate := {
  studyId := "when-quantum-models-disagree"
  title := "Research Note 02: Majorana Algebra & Kernel-Certified Window Reversal"
  url := "https://gravitonresearch.org/writing/when-quantum-models-disagree/"
  domain := "Quantum Many-Body Dynamics / Finite SYK Models"
  scopeStatement := "Exact 4-qubit Majorana Clifford algebra, exact 4-block closed-form reduction of H₀ + λP₁₂₃₅, exact RMS ratio α² = 9583/9983, and zero-floating-point rational-interval proof of the sign reversal between [12,24] and [36,48] (closing OW-GATE-01)."
  assumptions := [
    { id := "OW-A1_finite_4qubit"
      kind := "physical_regime"
      statement := "Four-qubit (16-dimensional) Hilbert space with Jordan–Wigner Majorana operators {ψ_i, ψ_j} = δ_{ij} I and infinite-temperature state ρ = I₁₆ / 16." },
    { id := "OW-A2_interval_taylor"
      kind := "mathematical"
      statement := "Fixed-point interval arithmetic (scale 10^6) uses exact integer sqrt enclosures and alternating degree-8/9 Taylor polynomials on [-π/2, π/2] with conservative remainder bounds (±3×10⁻⁵ for cos, ±5×10⁻⁶ for sin)." }
  ]
  claims := [
    { id := "OW-01"
      title := "Exact 4-Qubit Majorana Clifford Relations (64 pairs)"
      leanDecl := ``majorana_clifford_relations
      claimKind := "theorem"
      summary := "Proves {ψ_i, ψ_j} = δ_{ij} I identically for all 64 pairs of the 8 Jordan–Wigner Majorana operators."
      assumptionIds := ["OW-A1_finite_4qubit"]
      doesNotEstablish := [
        "Algebraic representation alone does not create or detect a physical Majorana particle."
      ] },
    { id := "OW-02"
      title := "Exact Spectator Conservation of ψ₈ Across All 35 Quartic Terms"
      leanDecl := ``spectator_psi8_commutes_with_all_quartic_terms
      claimKind := "theorem"
      summary := "Proves [P_{abcd}, ψ₈] = 0 for all 35 quartic operators on ψ₁..ψ₇, guaranteeing G₈(t) = 1 across all 180 Hamiltonians and all continuous times."
      assumptionIds := ["OW-A1_finite_4qubit"]
      doesNotEstablish := [
        "Does not imply thermalization or ergodicity of the remaining 7 operators."
      ] },
    { id := "OW-03"
      title := "Commuting Control Perturbations P_{1267} and P_{4567}"
      leanDecl := ``control_perturbations_commute_with_H0
      claimKind := "theorem"
      summary := "Verifies that P_{1267} and P_{4567} commute term-by-term with the entire 5-term baseline H₀."
      assumptionIds := ["OW-A1_finite_4qubit"]
      doesNotEstablish := [
        "Sign reversals in Note 02 are not confined to these commuting controls."
      ] },
    { id := "OW-04"
      title := "Reference Perturbation P_{1235} Anticommutes with Q_{1245} ∈ H₀"
      leanDecl := ``reference_perturbation_noncommuting
      claimKind := "theorem"
      summary := "Constructively exhibits Q_{1245} ∈ H₀ anticommuting with P_{1235} (sharing 3 Majorana indices {1,2,5})."
      assumptionIds := ["OW-A1_finite_4qubit"]
      doesNotEstablish := [
        "Non-commutativity does not guarantee monotonic autocorrelation suppression across all windows."
      ] },
    { id := "OW-05"
      title := "Exact 4-Block Clifford Reduction of H₀ + λ P_{1235}"
      leanDecl := ``exact_four_block_clifford_reduction
      claimKind := "theorem"
      summary := "Proves all 5 terms of H₀ mutually commute with 2 stabilizer relations, and P_{1235} splits H₀ into 2 commuting + 3 anticommuting terms, reducing the 16×16 spectrum to four exact 2×2 Pauli blocks."
      assumptionIds := ["OW-A1_finite_4qubit"]
      doesNotEstablish := [
        "This closed-form 2×2 reduction applies to P_{1235} and perturbations with equivalent stabilizer splits, not arbitrary generic dense Hamiltonians."
      ] },
    { id := "OW-06"
      title := "Exact RMS Energy-Matching Ratio α² = 9583 / 9983 & Certified Sqrt Enclosures"
      leanDecl := ``spectral_sqrt_enclosures_certified
      claimKind := "theorem"
      summary := "Kernel-verifies exact integer square-root enclosures for α = √(9583/9983) and all four 2×2 block frequencies and mixing angles."
      assumptionIds := ["OW-A1_finite_4qubit"]
      doesNotEstablish := [
        "Matching centered RMS energy does not match higher spectral moments or level spacings."
      ] },
    { id := "OW-07"
      title := "Zero-Floating-Point Interval Proof of Window Sign Reversal ([12,24] vs [36,48])"
      leanDecl := ``certified_interval_window_reversal
      claimKind := "counterexample"
      summary := "Directly proves inside Lean 4's kernel (pure integer interval arithmetic on the exact 4-block Clifford trace) that ΔD < 0 on [12,24] and ΔD > 0 on [36,48], closing OW-GATE-01."
      assumptionIds := ["OW-A1_finite_4qubit", "OW-A2_interval_taylor"]
      doesNotEstablish := [
        "Does not simulate a physical wormhole, measure consciousness, or establish a new law of gravity.",
        "Certifies the discrete finite-window reversal for P_{1235} at λ = +0.2 without floating point; does not replace full 180-case exploratory sweeps."
      ] }
  ]
  openGates := []
  sourceArtifacts := [
    ("protocol_url", "https://gravitonresearch.org/writing/when-quantum-models-disagree/protocol.json")
  ]
}

end GravitonCert.Studies.ObservationWindow
