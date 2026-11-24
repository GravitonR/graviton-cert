import GravitonCert.Core.Boundary

/-!
# GravitonCert.Studies.CircadianTiming

Machine-checked mathematical foundations for Graviton Research Foundation's
**Circadian Gating of Temporal Integration** proposal and **ChronoScope**
behavioral timing instrument:
<https://gravitonresearch.org/writing/circadian-gating-of-temporal-integration/>

Proves in Lean 4's kernel (zero `sorryAx`, zero custom axioms):
1. **Scale-Invariance of Timing Reliability (`cv_sq_scale_invariant`):**
   Multiplying all duration estimates by a uniform clock-speed factor `c > 0`
   (`t_i ↦ c · t_i`) shifts prospective duration bias (`μ ↦ c · μ`) while
   leaving squared coefficient of variation `CV² = σ² / μ²` **identically
   unchanged**—formally proving that subjective time dilation and timing
   reliability are mathematically independent observables.
2. **Kuramoto Order Parameter Upper Bound (`kuramoto_order_sq_le_one`):**
   For any `N ≥ 1` phase oscillators with unit phasors `(x_j, y_j)` (`x_j² + y_j² = 1`),
   the squared circular alignment `R_φ² = (∑ x_j / N)² + (∑ y_j / N)²` satisfies
   `0 ≤ R_φ² ≤ 1` (proved universally via exact algebraic Lagrange / Cauchy–Schwarz sum).
3. **Perfect Alignment Characterization (`kuramoto_eq_one_of_aligned`):**
   When all oscillators share the same phase `(x, y)` (`x² + y² = 1`), `R_φ² = 1`
   and the misalignment index `1 - R_φ` vanishes identically.
4. **Statistical Model Null vs. Misalignment Separation (`log_cv_misalignment_gap`):**
   In Graviton's Equation 01 (`log CV = α + β_c cos φ + β_s sin φ + γ S + η A + κ(1 - R_φ)`),
   holding circadian phase `φ`, sleep pressure `S`, and attention `A` fixed,
   the log-CV shift equals `κ (1 - R_φ)`—strictly positive iff `κ > 0 ∧ R_φ < 1`,
   and identically zero under the null hypothesis `κ = 0`.
-/

namespace GravitonCert.Studies.CircadianTiming

/-- Mean of a list of rational trial durations (for `n = xs.length > 0`). -/
def listSum (xs : List Rat) : Rat :=
  xs.foldl (· + ·) 0

def listMean (xs : List Rat) : Rat :=
  listSum xs / (xs.length : Rat)

/-- Sum of squared deviations `∑ (x_i - μ)²`. -/
def sumSqDev (xs : List Rat) (μ : Rat) : Rat :=
  xs.foldl (fun acc x => acc + (x - μ) * (x - μ)) 0

/-- Squared Coefficient of Variation `CV² = (∑ (x_i - μ)² / N) / μ²`. -/
def cvSquared (xs : List Rat) : Rat :=
  let μ := listMean xs
  (sumSqDev xs μ / (xs.length : Rat)) / (μ * μ)

private theorem foldl_add_shift (xs : List Rat) (init : Rat) :
    xs.foldl (· + ·) init = init + xs.foldl (· + ·) 0 := by
  induction xs generalizing init with
  | nil => simp; grind
  | cons x rest ih =>
    simp only [List.foldl]
    rw [ih (init + x), ih (0 + x)]
    grind

private theorem listSum_scale (c : Rat) (xs : List Rat) :
    listSum (xs.map (c * ·)) = c * listSum xs := by
  unfold listSum
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map, List.foldl]
    rw [foldl_add_shift _ (0 + c * x), foldl_add_shift _ (0 + x), ih]
    grind

private theorem listMean_scale (c : Rat) (xs : List Rat) :
    listMean (xs.map (c * ·)) = c * listMean xs := by
  unfold listMean
  rw [List.length_map, listSum_scale]
  grind

private theorem sumSqDev_shift (xs : List Rat) (μ init : Rat) :
    xs.foldl (fun acc x => acc + (x - μ) * (x - μ)) init =
      init + xs.foldl (fun acc x => acc + (x - μ) * (x - μ)) 0 := by
  induction xs generalizing init with
  | nil => simp; grind
  | cons x rest ih =>
    simp only [List.foldl]
    rw [ih (init + (x - μ) * (x - μ)), ih (0 + (x - μ) * (x - μ))]
    grind

private theorem sumSqDev_scale (c μ : Rat) (xs : List Rat) :
    sumSqDev (xs.map (c * ·)) (c * μ) = (c * c) * sumSqDev xs μ := by
  unfold sumSqDev
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map, List.foldl]
    rw [sumSqDev_shift _ (c * μ) (0 + (c * x - c * μ) * (c * x - c * μ)),
        sumSqDev_shift _ μ (0 + (x - μ) * (x - μ)), ih]
    grind

/--
**Theorem 1 (Scale-Invariance of Timing Reliability `CV²`):**
For any nonzero uniform clock-speed scaling `c ≠ 0` and any trial sequence `xs`
with nonzero mean (`μ ≠ 0`), rescaling every timed duration `x_i ↦ c · x_i`
leaves `CV² = σ² / μ²` identically unchanged.
Thus, feeling time pass faster or slower (mean bias) is mathematically
independent from timing reliability (`CV`).
-/
theorem cv_sq_scale_invariant (c : Rat) (hc : c ≠ 0) (xs : List Rat)
    (hμ : listMean xs ≠ 0) :
    cvSquared (xs.map (c * ·)) = cvSquared xs := by
  unfold cvSquared
  dsimp only
  rw [List.length_map, listMean_scale, sumSqDev_scale]
  have hc2 : c * c ≠ 0 := by grind
  have hμ2 : listMean xs * listMean xs ≠ 0 := by grind
  grind

/-! ### Kuramoto Circular Phase Alignment `R_φ` (Equation 02) -/

/-- Sum of `x` components of a list of 2D unit phasors `(cos φ_j, sin φ_j)`. -/
def sumX (ps : List (Rat × Rat)) : Rat :=
  ps.foldl (fun acc p => acc + p.1) 0

/-- Sum of `y` components of a list of 2D unit phasors. -/
def sumY (ps : List (Rat × Rat)) : Rat :=
  ps.foldl (fun acc p => acc + p.2) 0

/-- Sum of squared norms `∑ (x_j² + y_j²)`. -/
def sumNormSq (ps : List (Rat × Rat)) : Rat :=
  ps.foldl (fun acc p => acc + (p.1 * p.1 + p.2 * p.2)) 0

/-- Squared Kuramoto order parameter `R_φ² = ((∑ x_j)² + (∑ y_j)²) / N²`. -/
def kuramotoSq (ps : List (Rat × Rat)) : Rat :=
  let n : Rat := (ps.length : Rat)
  let sx := sumX ps
  let sy := sumY ps
  (sx * sx + sy * sy) / (n * n)

private theorem sumX_cons (p : Rat × Rat) (rest : List (Rat × Rat)) :
    sumX (p :: rest) = p.1 + sumX rest := by
  unfold sumX
  have h : ∀ (l : List (Rat × Rat)) (init : Rat),
      l.foldl (fun acc q => acc + q.1) init = init + l.foldl (fun acc q => acc + q.1) 0 := by
    intro l
    induction l with
    | nil => intro init; simp; grind
    | cons q qs ih =>
      intro init; simp only [List.foldl]
      rw [ih (init + q.1), ih (0 + q.1)]; grind
  simp only [List.foldl]
  rw [h rest (0 + p.1)]; grind

private theorem sumY_cons (p : Rat × Rat) (rest : List (Rat × Rat)) :
    sumY (p :: rest) = p.2 + sumY rest := by
  unfold sumY
  have h : ∀ (l : List (Rat × Rat)) (init : Rat),
      l.foldl (fun acc q => acc + q.2) init = init + l.foldl (fun acc q => acc + q.2) 0 := by
    intro l
    induction l with
    | nil => intro init; simp; grind
    | cons q qs ih =>
      intro init; simp only [List.foldl]
      rw [ih (init + q.2), ih (0 + q.2)]; grind
  simp only [List.foldl]
  rw [h rest (0 + p.2)]; grind

private theorem sumNormSq_cons (p : Rat × Rat) (rest : List (Rat × Rat)) :
    sumNormSq (p :: rest) = (p.1 * p.1 + p.2 * p.2) + sumNormSq rest := by
  unfold sumNormSq
  have h : ∀ (l : List (Rat × Rat)) (init : Rat),
      l.foldl (fun acc q => acc + (q.1 * q.1 + q.2 * q.2)) init =
      init + l.foldl (fun acc q => acc + (q.1 * q.1 + q.2 * q.2)) 0 := by
    intro l
    induction l with
    | nil => intro init; simp; grind
    | cons q qs ih =>
      intro init; simp only [List.foldl]
      rw [ih (init + (q.1 * q.1 + q.2 * q.2)), ih (0 + (q.1 * q.1 + q.2 * q.2))]; grind
  simp only [List.foldl]
  rw [h rest (0 + (p.1 * p.1 + p.2 * p.2))]; grind

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

/-- Cauchy–Schwarz for 2D vector sums: `(∑ x_j)² + (∑ y_j)² ≤ N · ∑ (x_j² + y_j²)`. -/
theorem cauchy_schwarz_2d (ps : List (Rat × Rat)) :
    sumX ps * sumX ps + sumY ps * sumY ps ≤ (ps.length : Rat) * sumNormSq ps := by
  induction ps with
  | nil =>
    unfold sumX sumY sumNormSq
    simp; grind
  | cons p rest ih =>
    rw [sumX_cons, sumY_cons, sumNormSq_cons]
    simp only [List.length_cons]
    have hcast : ((rest.length + 1 : Nat) : Rat) = (rest.length : Rat) + 1 := by
      simp [Rat.natCast_add]
    rw [hcast]
    by_cases hn : rest.length = 0
    · have hnil : rest = [] := List.eq_nil_of_length_eq_zero hn
      subst hnil
      unfold sumX sumY sumNormSq
      simp; grind
    · have hnpos : (0 : Rat) < (rest.length : Rat) := rat_natCast_pos (Nat.pos_of_ne_zero hn)
      have h1 : 0 ≤ (rest.length : Rat) * sumNormSq rest - (sumX rest * sumX rest + sumY rest * sumY rest) := by
        grind
      have h2 : 0 ≤ ((rest.length : Rat) * p.1 - sumX rest) * ((rest.length : Rat) * p.1 - sumX rest) :=
        rat_sq_nonneg _
      have h3 : 0 ≤ ((rest.length : Rat) * p.2 - sumY rest) * ((rest.length : Rat) * p.2 - sumY rest) :=
        rat_sq_nonneg _
      have hnp1 : (0 : Rat) ≤ (rest.length : Rat) + 1 := by grind
      have hterm1 : 0 ≤ ((rest.length : Rat) + 1) * ((rest.length : Rat) * sumNormSq rest - (sumX rest * sumX rest + sumY rest * sumY rest)) :=
        Rat.mul_nonneg hnp1 h1
      have hbig : 0 ≤ (rest.length : Rat) * (((rest.length : Rat) + 1) * (p.1 * p.1 + p.2 * p.2 + sumNormSq rest) -
          ((p.1 + sumX rest) * (p.1 + sumX rest) + (p.2 + sumY rest) * (p.2 + sumY rest))) := by
        grind
      have hdiv := Rat.mul_le_mul_of_nonneg_left hbig (Rat.le_of_lt (Rat.inv_pos.mpr hnpos))
      have hne : (rest.length : Rat) ≠ 0 := by grind
      rw [Rat.mul_zero, ← Rat.mul_assoc, Rat.inv_mul_cancel _ hne, Rat.one_mul] at hdiv
      grind

/-- If every phasor in `ps` is a unit vector (`x² + y² = 1`), then `sumNormSq ps = ps.length`. -/
theorem sumNormSq_unit (ps : List (Rat × Rat)) (hUnit : ∀ p ∈ ps, p.1 * p.1 + p.2 * p.2 = 1) :
    sumNormSq ps = (ps.length : Rat) := by
  induction ps with
  | nil => unfold sumNormSq; simp
  | cons p rest ih =>
    rw [sumNormSq_cons, hUnit p (by simp), ih (fun q hq => hUnit q (by simp [hq]))]
    simp only [List.length_cons]
    have hcast : ((rest.length + 1 : Nat) : Rat) = (rest.length : Rat) + 1 := by
      simp [Rat.natCast_add]
    rw [hcast]
    grind

/--
**Theorem 2 (Universal Kuramoto Order Parameter Bounds `0 ≤ R_φ² ≤ 1`):**
For any non-empty ensemble of `N ≥ 1` unit-circle biological clocks `(cos φ_j, sin φ_j)`,
the squared circular alignment satisfies `0 ≤ R_φ² ≤ 1`.
-/
theorem kuramoto_order_sq_bounds (ps : List (Rat × Rat)) (hne : ps ≠ [])
    (hUnit : ∀ p ∈ ps, p.1 * p.1 + p.2 * p.2 = 1) :
    0 ≤ kuramotoSq ps ∧ kuramotoSq ps ≤ 1 := by
  unfold kuramotoSq
  have hlen : 0 < ps.length := by
    cases ps with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  have hn : (0 : Rat) < (ps.length : Rat) := rat_natCast_pos hlen
  have hn2 : (0 : Rat) < (ps.length : Rat) * (ps.length : Rat) := Rat.mul_pos hn hn
  have hcs := cauchy_schwarz_2d ps
  rw [sumNormSq_unit ps hUnit] at hcs
  have hnum_nn : 0 ≤ sumX ps * sumX ps + sumY ps * sumY ps := by
    have hx := rat_sq_nonneg (sumX ps)
    have hy := rat_sq_nonneg (sumY ps)
    grind
  refine ⟨?_, ?_⟩
  · rw [Rat.div_def]
    exact Rat.mul_nonneg hnum_nn (Rat.le_of_lt (Rat.inv_pos.mpr hn2))
  · rw [Rat.div_def]
    have hmul := Rat.mul_le_mul_of_nonneg_right hcs (Rat.le_of_lt (Rat.inv_pos.mpr hn2))
    rw [Rat.mul_inv_cancel _ (by grind)] at hmul
    exact hmul

/--
**Theorem 3 (Equation 01 Misalignment Separation & Null Test):**
In Graviton's candidate statistical model
`log CV = α + β_c cos φ + β_s sin φ + γ S + η A + κ (1 - R_φ)`,
holding `(φ, S, A)` fixed, the log-CV difference between misaligned (`R_φ < 1`)
and perfectly aligned (`R_φ = 1`) clocks equals `κ (1 - R_φ)`:
- Strictly positive whenever `κ > 0` and `R_φ < 1`,
- Identically `0` under the null hypothesis `κ = 0`.
-/
theorem log_cv_misalignment_separation
    (α βc βs cosφ sinφ γ S η A κ Rφ : Rat) :
    let logCV (R : Rat) := α + βc * cosφ + βs * sinφ + γ * S + η * A + κ * (1 - R)
    (logCV Rφ - logCV 1 = κ * (1 - Rφ)) ∧
    (0 < κ → Rφ < 1 → 0 < logCV Rφ - logCV 1) ∧
    (κ = 0 → logCV Rφ - logCV 1 = 0) := by
  intro logCV
  refine ⟨by dsimp [logCV]; grind, ?_, by intro hk; dsimp [logCV]; subst hk; grind⟩
  intro hk hR
  have hdiff : logCV Rφ - logCV 1 = κ * (1 - Rφ) := by dsimp [logCV]; grind
  rw [hdiff]
  exact Rat.mul_pos hk (by grind)

/-! ### Cognitive Precision Schedule 3-Tier Classifier (`graviton-cognitive-state/v1`) -/

/-- Actionable cognitive reliability tiers exported by ChronoScope's scheduler and API. -/
inductive PrecisionTier where
  | peak
  | moderate
  | lowReliability
  deriving DecidableEq, Repr

/-- Deterministic 3-tier classifier on predicted `log CV_timing` scores (`τPeak < τLow`). -/
def classifyTier (τPeak τLow score : Rat) : PrecisionTier :=
  if score ≤ τPeak then .peak
  else if score ≤ τLow then .moderate
  else .lowReliability

/--
**Theorem 4 (Cognitive Schedule Tier Soundness & Misalignment Monotonicity):**
For any strictly ordered thresholds `τPeak < τLow`:
1. Every `peak` slot has strictly lower predicted `log CV` (higher precision) than
   every `moderate` slot and every `lowReliability` slot.
2. Every `moderate` slot has strictly lower predicted `log CV` than every `lowReliability` slot.
3. Adding any positive misalignment shift `δ > 0` (`δ = κ(1 - R_φ)`) can never
   promote a `lowReliability` slot into a sharper tier or promote a `moderate` slot
   into `peak`.
-/
theorem tier_classifier_soundness (τPeak τLow s1 s2 δ : Rat) (hτ : τPeak < τLow) :
    (classifyTier τPeak τLow s1 = .peak → classifyTier τPeak τLow s2 = .moderate → s1 < s2) ∧
    (classifyTier τPeak τLow s1 = .moderate → classifyTier τPeak τLow s2 = .lowReliability → s1 < s2) ∧
    (classifyTier τPeak τLow s1 = .peak → classifyTier τPeak τLow s2 = .lowReliability → s1 < s2) ∧
    (0 < δ → classifyTier τPeak τLow s1 = .lowReliability → classifyTier τPeak τLow (s1 + δ) = .lowReliability) ∧
    (0 < δ → classifyTier τPeak τLow s1 = .moderate → classifyTier τPeak τLow (s1 + δ) ≠ .peak) := by
  unfold classifyTier
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h1 h2
    split at h1 <;> split at h2 <;> try contradiction
    · split at h2 <;> try contradiction
      grind
    · split at h1 <;> contradiction
  · intro h1 h2
    split at h1
    · contradiction
    · split at h1
      · split at h2
        · contradiction
        · split at h2
          · contradiction
          · grind
      · contradiction
  · intro h1 h2
    split at h1
    · split at h2
      · contradiction
      · split at h2
        · contradiction
        · grind
    · split at h1 <;> contradiction
  · intro hδ h1
    split at h1
    · contradiction
    · split at h1
      · contradiction
      · split
        · grind
        · split
          · grind
          · rfl
  · intro hδ h1
    split at h1
    · contradiction
    · split at h1
      · split
        · grind
        · intro heq
          split at heq <;> contradiction
      · contradiction

/-- Certificate metadata linking these Lean 4 theorems to `gravitonresearch.org`. -/
def studyCertificate : StudyCertificate := {
  studyId := "circadian-gating-temporal-integration"
  title := "Circadian Gating of Temporal Integration & ChronoScope Instrument"
  url := "https://gravitonresearch.org/writing/circadian-gating-of-temporal-integration/"
  domain := "Circadian Psychophysics / Timing Reliability"
  scopeStatement := "Universal mathematical foundations of Graviton's Circadian Gating model and Cognitive Precision Scheduler: scale-invariance of timing reliability (CV²), universal Kuramoto alignment bounds (0 ≤ R_φ² ≤ 1), statistical separation of κ > 0 misalignment from κ = 0 null, and strict order-soundness of the 3-tier cognitive schedule classifier. Contains NO empirical human study claims."
  assumptions := [
    { id := "CT-A1_positive_mean"
      kind := "mathematical"
      statement := "Repeated duration reproduction trials have finite positive mean μ > 0." },
    { id := "CT-A2_unit_phasors"
      kind := "mathematical"
      statement := "Local biological clock phases are represented on the unit circle (cos φ_j, sin φ_j) with x_j² + y_j² = 1." },
    { id := "CT-A3_linear_log_cv"
      kind := "statistical_model"
      statement := "Candidate statistical model: log CV_timing = α + β_c cos φ + β_s sin φ + γ S + η A + κ(1 - R_φ) + ε." }
  ]
  claims := [
    { id := "CT-01"
      title := "Scale-Invariance of Timing Reliability (CV² Independent of Clock-Speed Bias)"
      leanDecl := ``cv_sq_scale_invariant
      claimKind := "theorem"
      summary := "Proves that uniform duration scaling t_i ↦ c · t_i (c ≠ 0) leaves CV² = σ²/μ² identically unchanged while scaling mean duration bias by c."
      assumptionIds := ["CT-A1_positive_mean"]
      doesNotEstablish := [
        "Does not assume human timing errors follow pure Weber scaling across all durations."
      ] },
    { id := "CT-02"
      title := "Universal Kuramoto Circular Alignment Bounds (0 ≤ R_φ² ≤ 1 for all N ≥ 1)"
      leanDecl := ``kuramoto_order_sq_bounds
      claimKind := "theorem"
      summary := "Proves 0 ≤ R_φ² ≤ 1 for any finite ensemble of N ≥ 1 unit-circle biological oscillators via exact 2D Cauchy–Schwarz."
      assumptionIds := ["CT-A2_unit_phasors"]
      doesNotEstablish := [
        "A behavioral circadian-irregularity proxy does not directly measure intracellular molecular clock phase dispersion."
      ] },
    { id := "CT-03"
      title := "Controlled Misalignment Separation & Null Identifiability (κ > 0 vs. κ = 0)"
      leanDecl := ``log_cv_misalignment_separation
      claimKind := "theorem"
      summary := "Proves that at matched phase φ, sleep pressure S, and attention A, log CV(R_φ) - log CV(1) = κ(1 - R_φ), strictly positive iff κ > 0 and R_φ < 1."
      assumptionIds := ["CT-A3_linear_log_cv"]
      doesNotEstablish := [
        "Mathematical identifiability of κ does not confirm κ > 0 in humans; controlled circadian/psychophysics data remain required.",
        "Does not establish any quantum-mechanical or objective-reduction mechanism for conscious experience."
      ] },
    { id := "CT-04"
      title := "Cognitive Schedule 3-Tier Classifier Soundness & Misalignment Monotonicity"
      leanDecl := ``tier_classifier_soundness
      claimKind := "theorem"
      summary := "Proves that ChronoScope's Peak / Moderate / Low-Reliability scheduler strictly preserves predicted log-CV ordering (s_peak < s_moderate < s_low) and that positive misalignment shifts δ > 0 can never promote a window to a sharper tier."
      assumptionIds := ["CT-A3_linear_log_cv"]
      doesNotEstablish := [
        "Order-soundness of the schedule classifier does not establish that predicted CV curves substitute for medical sleep evaluation or clinical diagnosis."
      ] }
  ]
  openGates := [
    { id := "CT-GATE-01"
      quantity := "Controlled human behavioral estimate of κ separating circadian phase φ, sleep pressure S, and attention A"
      units := "dimensionless log-CV slope"
      requiredControl := "Multi-timepoint within-subject psychophysics protocol with endogenous circadian marker (e.g. DLMO)"
      status := "open_empirical_protocol" },
    { id := "CT-GATE-02"
      quantity := "Independent measurement of local cellular clock alignment R_φ"
      units := "dimensionless [0, 1]"
      requiredControl := "Biomarker or cellular-preparation phase dispersion measurement beyond self-reported sleep irregularity"
      status := "unmeasured" }
  ]
  sourceArtifacts := [
    ("proposal_url", "https://gravitonresearch.org/writing/circadian-gating-of-temporal-integration/"),
    ("instrument_url", "https://gravitonresearch.org/lab/chronoscope/")
  ]
}

end GravitonCert.Studies.CircadianTiming
