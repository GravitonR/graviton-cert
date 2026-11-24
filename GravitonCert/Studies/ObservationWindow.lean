import GravitonCert.Core.Boundary

/-!
# GravitonCert.Studies.ObservationWindow

Machine-checked formalization of the exact 4-qubit Majorana algebra and
falsification logic underlying Graviton Research Note 02:
*"When the observation window changes the result"*
<https://gravitonresearch.org/writing/when-quantum-models-disagree/>

Proves in Lean 4's kernel (zero floating point, zero `sorry`):
1. Exact 4-qubit Pauli / Majorana Clifford algebra (`{ψ_i, ψ_j} = δ_{ij} I` for all 64 pairs),
2. **Exact Spectator Conservation Theorem**: `ψ_8` commutes with *every* quartic
   operator `P_{abcd}` (`1 ≤ a < b < c < d ≤ 7`)—hence `[H_0 + λP, ψ_8] = 0` for
   all 180 Hamiltonians and all couplings `λ`,
3. **Commuting Control Verification**: both control perturbations `P_{1267}` and
   `P_{4567}` commute with every term of the 5-term baseline `H_0`,
4. **Non-Commuting Reference Verification**: the reference perturbation `P_{1235}`
   does *not* commute with `H_0`,
5. **Formal Window-Reversal Refutation**: proves how a verified reversal witness
   (`ΔD(W₁) < 0 ∧ ΔD(W₂) > 0`) formally refutes the universal negative-contrast
   generalization while leaving the bounded-window result intact.
-/

namespace GravitonCert.Studies.ObservationWindow

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
  | .X, .Y => (1, .Z)  -- X Y = +i Z
  | .Y, .X => (3, .Z)  -- Y X = -i Z
  | .Y, .Z => (1, .X)  -- Y Z = +i X
  | .Z, .Y => (3, .X)  -- Z Y = -i X
  | .Z, .X => (1, .Y)  -- Z X = +i Y
  | .X, .Z => (3, .Y)  -- X Z = -i Y

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

/--
Exact Jordan–Wigner Majorana operators `ψ̃_k = √2 · ψ_k` (`k : Fin 8`, 0-indexed for `ψ₁..ψ₈`)
matching Research Note 02's exact convention:
`ψ̃_{2j-1} = Z^{⊗(j-1)} ⊗ X ⊗ I^{⊗(4-j)}`, `ψ̃_{2j} = Z^{⊗(j-1)} ⊗ Y ⊗ I^{⊗(4-j)}`.
-/
def majorana : Fin 8 → Pauli4
  | ⟨0, _⟩ => ⟨0, .X, .I, .I, .I⟩ -- ψ̃₁
  | ⟨1, _⟩ => ⟨0, .Y, .I, .I, .I⟩ -- ψ̃₂
  | ⟨2, _⟩ => ⟨0, .Z, .X, .I, .I⟩ -- ψ̃₃
  | ⟨3, _⟩ => ⟨0, .Z, .Y, .I, .I⟩ -- ψ̃₄
  | ⟨4, _⟩ => ⟨0, .Z, .Z, .X, .I⟩ -- ψ̃₅
  | ⟨5, _⟩ => ⟨0, .Z, .Z, .Y, .I⟩ -- ψ̃₆
  | ⟨6, _⟩ => ⟨0, .Z, .Z, .Z, .X⟩ -- ψ̃₇
  | ⟨7, _⟩ => ⟨0, .Z, .Z, .Z, .Y⟩ -- ψ̃₈ (spectator)

/--
**Theorem 1 (Exact 4-Qubit Majorana Clifford Algebra):**
For all 64 pairs `(i, j) : Fin 8 × Fin 8`:
- `ψ̃_i · ψ̃_i = I` (equivalently `{ψ_i, ψ_i} = I`), and
- for `i ≠ j`, `ψ̃_i · ψ̃_j = - (ψ̃_j · ψ̃_i)` (equivalently `{ψ_i, ψ_j} = 0`).
-/
theorem majorana_clifford_relations :
    ∀ i j : Fin 8,
      (i = j → majorana i * majorana j = Pauli4.id) ∧
      (i ≠ j → majorana i * majorana j = Pauli4.neg (majorana j * majorana i)) := by
  decide

/-- Quartic Majorana product `P_{a b c d} = ψ̃_a ψ̃_b ψ̃_c ψ̃_d` (using 1-based indices `1..7`). -/
def quartic (a b c d : Fin 7) : Pauli4 :=
  majorana ⟨a.val, by omega⟩ *
  majorana ⟨b.val, by omega⟩ *
  majorana ⟨c.val, by omega⟩ *
  majorana ⟨d.val, by omega⟩

/-- The spectator operator `ψ̃₈`. -/
def psi8 : Pauli4 := majorana ⟨7, by decide⟩

/--
**Theorem 2 (Exact Spectator Conservation Across All 35 Quartic Terms / 180 Hamiltonians):**
Every quartic operator `P_{abcd}` formed from `ψ₁..ψ₇` commutes identically with `ψ₈`.
Therefore `[H_0 + λ P, ψ₈] = 0` for every perturbation in Note 02's 180-Hamiltonian sweep
and every real coupling `λ`, guaranteeing `G₈(t) = 1` for all continuous times `t`.
-/
theorem spectator_psi8_commutes_with_all_quartic_terms :
    ∀ a b c d : Fin 7,
      a < b → b < c → c < d →
      quartic a b c d * psi8 = psi8 * quartic a b c d := by
  decide

/-- Exact count of strictly increasing 4-element subsets of `{1..7}` is 35 (5 in `H₀` + 30 perturbations). -/
def allQuarticIndices : List (Fin 7 × Fin 7 × Fin 7 × Fin 7) :=
  (List.finRange 7).flatMap fun a =>
  (List.finRange 7).flatMap fun b =>
  (List.finRange 7).flatMap fun c =>
  (List.finRange 7).filterMap fun d =>
    if a < b ∧ b < c ∧ c < d then some (a, b, c, d) else none

theorem perturbation_family_count_exact :
    allQuarticIndices.length = 35 ∧ allQuarticIndices.length - 5 = 30 := by
  decide

/-- The five quartic operators in the Kobrin–Schuster–Yao baseline Hamiltonian `H₀` (0-indexed for `1..7`). -/
def baselineH0Terms : List Pauli4 :=
  [ quartic ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨3, by decide⟩ ⟨4, by decide⟩, -- P_{1245}
    quartic ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨3, by decide⟩ ⟨6, by decide⟩, -- P_{1347}
    quartic ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨4, by decide⟩ ⟨5, by decide⟩, -- P_{1356}
    quartic ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨3, by decide⟩ ⟨5, by decide⟩, -- P_{2346}
    quartic ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨4, by decide⟩ ⟨6, by decide⟩  -- P_{2357}
  ]

def P_1267 : Pauli4 := quartic ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨5, by decide⟩ ⟨6, by decide⟩
def P_4567 : Pauli4 := quartic ⟨3, by decide⟩ ⟨4, by decide⟩ ⟨5, by decide⟩ ⟨6, by decide⟩
def P_1235 : Pauli4 := quartic ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨4, by decide⟩

/--
**Theorem 3 (Commuting Control Perturbations):**
Both control additions `P_{1267}` and `P_{4567}` commute term-by-term with
the entire 5-term baseline Hamiltonian `H₀`.
-/
theorem control_perturbations_commute_with_H0 :
    (∀ h ∈ baselineH0Terms, P_1267 * h = h * P_1267) ∧
    (∀ h ∈ baselineH0Terms, P_4567 * h = h * P_4567) := by
  decide

/--
**Theorem 4 (Reference Perturbation Non-Commutativity):**
The reference perturbation `P_{1235}` does *not* commute with `H₀`
(specifically, it shares 3 Majorana indices `{1, 2, 5}` with `P_{1245} ∈ H₀`
and therefore anticommutes with `P_{1245}`).
-/
theorem reference_perturbation_noncommuting :
    ∃ h ∈ baselineH0Terms, P_1235 * h = Pauli4.neg (h * P_1235) := by
  refine ⟨quartic ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨3, by decide⟩ ⟨4, by decide⟩, ?_, ?_⟩
  · decide
  · decide

/-- The four observation windows declared in Research Note 02 (`protocol.json`). -/
inductive ObsWindow where
  | w0_12 | w12_24 | w24_36 | w36_48
  deriving DecidableEq, Repr

/--
**Theorem 5 (Formal Scope & Reversal Refutation Principle):**
Given any contrast functional `ΔD : ObsWindow → Rat`, if a reference window `W₁`
exhibits a negative contrast (`ΔD W₁ < 0`) while another window `W₂` exhibits a
positive contrast (`ΔD W₂ > 0`), then:
1. The bounded-window claim `ΔD W₁ < 0` remains valid, AND
2. The universal window-independent generalization `∀ W, ΔD W < 0` is provably false.
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

/-- Recorded primary-grid contrasts for `P_{1235}` at `λ = +0.2` from Note 02. -/
def referenceContrastP1235 : ObsWindow → Rat
  | .w12_24 => -36111 / 1000000
  | .w36_48 =>   6218 / 1000000
  | .w0_12  => -1 / 1000  -- illustrative placeholder; only w12_24 and w36_48 are used below
  | .w24_36 => -1 / 1000

theorem reference_P1235_reversal_refutes_global_claim :
    referenceContrastP1235 .w12_24 < 0 ∧
    ¬ (∀ w : ObsWindow, referenceContrastP1235 w < 0) := by
  exact window_reversal_refutes_universal_sign
    referenceContrastP1235 .w12_24 .w36_48
    (by unfold referenceContrastP1235; grind)
    (by unfold referenceContrastP1235; grind)

/-- Certificate metadata linking these Lean 4 theorems to `gravitonresearch.org`. -/
def studyCertificate : StudyCertificate := {
  studyId := "when-quantum-models-disagree"
  title := "Research Note 02: Majorana Algebra & Observation-Window Reversal"
  url := "https://gravitonresearch.org/writing/when-quantum-models-disagree/"
  domain := "Quantum Many-Body Dynamics / Finite SYK Models"
  scopeStatement := "Exact algebraic verification of the 4-qubit Majorana Clifford algebra, spectator conservation across all 35 quartic terms, commuting controls, and logical refutation of universal sign invariance from a verified window reversal."
  assumptions := [
    { id := "OW-A1_finite_4qubit"
      kind := "physical_regime"
      statement := "Four-qubit (16-dimensional) Hilbert space with Jordan–Wigner Majorana operators {ψ_i, ψ_j} = δ_{ij} I and infinite-temperature state ρ = I₁₆ / 16." },
    { id := "OW-A2_numerical_witness"
      kind := "numerical_discretization"
      statement := "Recorded contrast values (-0.036111 on [12,24], +0.006218 on [36,48]) come from Note 02's cross-checked Δt = 0.1 / 0.05 / 0.025 sweep (not yet replaced by Lean interval-arithmetic matrix exponentials)." }
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
      title := "Exact Count of 30 Perturbations + Commuting Controls P_{1267}, P_{4567}"
      leanDecl := ``control_perturbations_commute_with_H0
      claimKind := "theorem"
      summary := "Verifies that P_{1267} and P_{4567} commute term-by-term with the entire 5-term baseline H₀."
      assumptionIds := ["OW-A1_finite_4qubit"]
      doesNotEstablish := [
        "Sign reversals in Note 02 are not confined to these commuting controls."
      ] },
    { id := "OW-04"
      title := "Reference Perturbation P_{1235} Does Not Commute with H₀"
      leanDecl := ``reference_perturbation_noncommuting
      claimKind := "theorem"
      summary := "Constructively exhibits P_{1245} ∈ H₀ anticommuting with P_{1235} (sharing 3 Majorana indices {1,2,5})."
      assumptionIds := ["OW-A1_finite_4qubit"]
      doesNotEstablish := [
        "Non-commutativity does not guarantee monotonic autocorrelation suppression across all windows."
      ] },
    { id := "OW-05"
      title := "Window Reversal Refutes Global Negative-Contrast Generalization"
      leanDecl := ``reference_P1235_reversal_refutes_global_claim
      claimKind := "counterexample"
      summary := "Formally proves that opposite signs on [12,24] and [36,48] refute ∀ W, ΔD(W) < 0 while preserving the bounded-window result."
      assumptionIds := ["OW-A1_finite_4qubit", "OW-A2_numerical_witness"]
      doesNotEstablish := [
        "Does not simulate a physical wormhole, measure consciousness, or establish a new law of gravity.",
        "Continuous-time interval-arithmetic verification of the matrix exponential trace remains an open formalization upgrade."
      ] }
  ]
  openGates := [
    { id := "OW-GATE-01"
      quantity := "Continuous-time interval-arithmetic certificate for Tr[e^{iHt} ψ_i e^{-iHt} ψ_i]"
      units := "formal_numerics"
      requiredControl := "Replace floating-point ΔD witnesses with LeanCert/rational Taylor remainder enclosures"
      status := "planned_v0.2_upgrade" }
  ]
  sourceArtifacts := [
    ("protocol_url", "https://gravitonresearch.org/writing/when-quantum-models-disagree/protocol.json")
  ]
}

end GravitonCert.Studies.ObservationWindow
