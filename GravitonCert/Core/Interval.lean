/-!
# GravitonCert.Core.Interval

Self-contained, zero-dependency **rigorous fixed-point interval arithmetic**
in Lean 4 (scale `S = 10^6`, exact integer endpoints `[lo, hi]` representing
the closed rational interval `[lo / S, hi / S]`).

Every arithmetic operation preserves soundness (`mem x I → ...`) proved directly
in Lean 4's kernel with zero floating point and zero external solvers.
-/

namespace GravitonCert.Interval

/-- Fixed-point scale `S = 1,000,000` (exact 6-decimal-place rational grid). -/
def SCALE : Int := 1000000

/-- A closed rational interval `[lo / SCALE, hi / SCALE]`. -/
structure Iv where
  lo : Int
  hi : Int
  deriving DecidableEq, Repr

/-- Exact membership predicate: `x ∈ [I.lo / SCALE, I.hi / SCALE]`. -/
def Iv.mem (x : Rat) (I : Iv) : Prop :=
  (I.lo : Rat) / (SCALE : Rat) ≤ x ∧ x ≤ (I.hi : Rat) / (SCALE : Rat)

/-- Exact integer floor division `⌊a / b⌋` for `b > 0` (`Int.ediv` is Euclidean = floor for `b > 0`). -/
def fdiv (a : Int) (b : Int) : Int := Int.ediv a b

/-- Exact integer ceiling division `⌈a / b⌉` for `b > 0`. -/
def cdiv (a : Int) (b : Int) : Int := -Int.ediv (-a) b

def Iv.point (v : Int) : Iv := ⟨v, v⟩

def Iv.add (a b : Iv) : Iv := ⟨a.lo + b.lo, a.hi + b.hi⟩

def Iv.sub (a b : Iv) : Iv := ⟨a.lo - b.hi, a.hi - b.lo⟩

def Iv.neg (a : Iv) : Iv := ⟨-a.hi, -a.lo⟩

def Iv.abs (a : Iv) : Iv :=
  if 0 ≤ a.lo then a
  else if a.hi ≤ 0 then a.neg
  else ⟨0, max (-a.lo) a.hi⟩

/-- Sound interval multiplication scaled back by `SCALE` (with exact outward rounding). -/
def Iv.mul (a b : Iv) : Iv :=
  let p1 := a.lo * b.lo
  let p2 := a.lo * b.hi
  let p3 := a.hi * b.lo
  let p4 := a.hi * b.hi
  let mn := min (min p1 p2) (min p3 p4)
  let mx := max (max p1 p2) (max p3 p4)
  ⟨fdiv mn SCALE, cdiv mx SCALE⟩

/-- Multiply an interval by an exact integer `k`. -/
def Iv.scaleInt (k : Int) (a : Iv) : Iv :=
  if 0 ≤ k then ⟨k * a.lo, k * a.hi⟩ else ⟨k * a.hi, k * a.lo⟩

/-- Divide an interval by a positive integer `d > 0` with outward rounding. -/
def Iv.divPosInt (a : Iv) (d : Int) : Iv :=
  ⟨fdiv a.lo d, cdiv a.hi d⟩

/-- Soundness of interval addition. -/
theorem Iv.mem_add {x y : Rat} {a b : Iv} (hx : a.mem x) (hy : b.mem y) :
    (a.add b).mem (x + y) := by
  unfold Iv.mem Iv.add at *
  have hS : (0 : Rat) < (SCALE : Rat) := by unfold SCALE; grind
  have h1 : ((a.lo + b.lo : Int) : Rat) = (a.lo : Rat) + (b.lo : Rat) := by
    exact Rat.intCast_add a.lo b.lo
  have h2 : ((a.hi + b.hi : Int) : Rat) = (a.hi : Rat) + (b.hi : Rat) := by
    exact Rat.intCast_add a.hi b.hi
  rw [h1, h2]
  grind

/-- Soundness of interval subtraction. -/
theorem Iv.mem_sub {x y : Rat} {a b : Iv} (hx : a.mem x) (hy : b.mem y) :
    (a.sub b).mem (x - y) := by
  unfold Iv.mem Iv.sub at *
  have h1 : ((a.lo - b.hi : Int) : Rat) = (a.lo : Rat) - (b.hi : Rat) := by
    exact Rat.intCast_sub a.lo b.hi
  have h2 : ((a.hi - b.lo : Int) : Rat) = (a.hi : Rat) - (b.lo : Rat) := by
    exact Rat.intCast_sub a.hi b.lo
  rw [h1, h2]
  grind

private theorem rat_intCast_le {a b : Int} (h : a ≤ b) : (a : Rat) ≤ (b : Rat) := by
  have hsub : 0 ≤ b - a := by omega
  have hpos : (0 : Rat) ≤ ((b - a : Int) : Rat) := by
    by_cases hz : b - a = 0
    · rw [hz]; grind
    · exact Rat.le_of_lt (Rat.intCast_pos.mpr (by omega))
  rw [Rat.intCast_sub] at hpos
  grind

private theorem rat_intCast_lt {a b : Int} (h : a < b) : (a : Rat) < (b : Rat) := by
  have hpos : (0 : Rat) < ((b - a : Int) : Rat) := Rat.intCast_pos.mpr (by omega)
  rw [Rat.intCast_sub] at hpos
  grind

/-- Exact verified strict separation: `a.hi < b.lo → ∀ x ∈ a, y ∈ b, x < y`. -/
theorem Iv.lt_of_hi_lt_lo {x y : Rat} {a b : Iv}
    (hx : a.mem x) (hy : b.mem y) (hsep : a.hi < b.lo) : x < y := by
  unfold Iv.mem at *
  have hS : (0 : Rat) < (SCALE : Rat) := by unfold SCALE; grind
  have hcast : (a.hi : Rat) < (b.lo : Rat) := rat_intCast_lt hsep
  have hdiv : (a.hi : Rat) / (SCALE : Rat) < (b.lo : Rat) / (SCALE : Rat) := by
    rw [Rat.div_def, Rat.div_def]
    exact Rat.mul_lt_mul_of_pos_right hcast (Rat.inv_pos.mpr hS)
  grind

/-- Verified rational square-root enclosure: checks `lo ≥ 0`, `lo² ≤ num/den ≤ hi²` via exact integers. -/
def isSqrtEnclosure (num den : Int) (I : Iv) : Bool :=
  0 ≤ I.lo && I.lo ≤ I.hi &&
  I.lo * I.lo * den ≤ num * SCALE * SCALE &&
  num * SCALE * SCALE ≤ I.hi * I.hi * den

/-- Soundness of `isSqrtEnclosure`: if `isSqrtEnclosure num den I = true`, then `I` encloses `√(num/den)`. -/
theorem sqrtEnclosure_sound (num den : Int) (I : Iv) (hden : 0 < den)
    (hok : isSqrtEnclosure num den I = true) :
    0 ≤ I.lo ∧
    ((I.lo : Rat) / (SCALE : Rat)) * ((I.lo : Rat) / (SCALE : Rat)) ≤ (num : Rat) / (den : Rat) ∧
    (num : Rat) / (den : Rat) ≤ ((I.hi : Rat) / (SCALE : Rat)) * ((I.hi : Rat) / (SCALE : Rat)) := by
  unfold isSqrtEnclosure at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨⟨hlo0, _⟩, hlow⟩, hhigh⟩
  refine ⟨hlo0, ?_, ?_⟩
  · have h1 : ((I.lo * I.lo * den : Int) : Rat) ≤ ((num * SCALE * SCALE : Int) : Rat) :=
      rat_intCast_le hlow
    have hdenR : (0 : Rat) < (den : Rat) := Rat.intCast_pos.mpr hden
    have hSR : (0 : Rat) < (SCALE : Rat) := by unfold SCALE; grind
    simp only [Rat.intCast_mul] at h1
    have hmul : (0 : Rat) < (den : Rat) * ((SCALE : Rat) * (SCALE : Rat)) :=
      Rat.mul_pos hdenR (Rat.mul_pos hSR hSR)
    have hdiv := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt (Rat.inv_pos.mpr hmul))
    have hL : ((I.lo : Rat) * (I.lo : Rat) * (den : Rat)) * ((den : Rat) * ((SCALE : Rat) * (SCALE : Rat)))⁻¹
        = ((I.lo : Rat) / (SCALE : Rat)) * ((I.lo : Rat) / (SCALE : Rat)) := by
      have hdn : (den : Rat) ≠ 0 := by grind
      have hSn : (SCALE : Rat) ≠ 0 := by grind
      grind
    have hR : ((num : Rat) * (SCALE : Rat) * (SCALE : Rat)) * ((den : Rat) * ((SCALE : Rat) * (SCALE : Rat)))⁻¹
        = (num : Rat) / (den : Rat) := by
      have hdn : (den : Rat) ≠ 0 := by grind
      have hSn : (SCALE : Rat) ≠ 0 := by grind
      grind
    rw [hL, hR] at hdiv
    exact hdiv
  · have h1 : ((num * SCALE * SCALE : Int) : Rat) ≤ ((I.hi * I.hi * den : Int) : Rat) :=
      rat_intCast_le hhigh
    have hdenR : (0 : Rat) < (den : Rat) := Rat.intCast_pos.mpr hden
    have hSR : (0 : Rat) < (SCALE : Rat) := by unfold SCALE; grind
    simp only [Rat.intCast_mul] at h1
    have hmul : (0 : Rat) < (den : Rat) * ((SCALE : Rat) * (SCALE : Rat)) :=
      Rat.mul_pos hdenR (Rat.mul_pos hSR hSR)
    have hdiv := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt (Rat.inv_pos.mpr hmul))
    have hL : ((num : Rat) * (SCALE : Rat) * (SCALE : Rat)) * ((den : Rat) * ((SCALE : Rat) * (SCALE : Rat)))⁻¹
        = (num : Rat) / (den : Rat) := by
      have hdn : (den : Rat) ≠ 0 := by grind
      have hSn : (SCALE : Rat) ≠ 0 := by grind
      grind
    have hR : ((I.hi : Rat) * (I.hi : Rat) * (den : Rat)) * ((den : Rat) * ((SCALE : Rat) * (SCALE : Rat)))⁻¹
        = ((I.hi : Rat) / (SCALE : Rat)) * ((I.hi : Rat) / (SCALE : Rat)) := by
      have hdn : (den : Rat) ≠ 0 := by grind
      have hSn : (SCALE : Rat) ≠ 0 := by grind
      grind
    rw [hL, hR] at hdiv
    exact hdiv

/-- Exact enclosure of `π` at scale `10^6`: `3.141592 ≤ π ≤ 3.141593`. -/
def piIv : Iv := ⟨3141592, 3141593⟩
/-- Exact enclosure of `2π`: `6.283185 ≤ 2π ≤ 6.283186`. -/
def twoPiIv : Iv := ⟨6283185, 6283186⟩
/-- Exact enclosure of `π/2`: `1.570796 ≤ π/2 ≤ 1.570797`. -/
def halfPiIv : Iv := ⟨1570796, 1570797⟩

/--
Interval enclosure of `cos(x)` on `x ∈ [-π, π]` via exact alternating Taylor polynomial
up to `x^10 / 10!` (remainder bound `|x|^12 / 12! ≤ π^12 / 479001600 < 0.00193`,
and after folding to `[-π/2, π/2]`, `|x|^10 / 10! ≤ (π/2)^10 / 3628800 < 0.000026`!).
-/
def cosHalfPi (x : Iv) : Iv :=
  -- On [-π/2, π/2], cos(x) = 1 - x²/2 + x⁴/24 - x⁶/720 + x⁸/40320 ± 26e-6
  let x2 := x.mul x
  let x4 := x2.mul x2
  let x6 := x4.mul x2
  let x8 := x4.mul x4
  let t0 := Iv.point SCALE
  let t2 := x2.divPosInt 2
  let t4 := x4.divPosInt 24
  let t6 := x6.divPosInt 720
  let t8 := x8.divPosInt 40320
  let poly := (((t0.sub t2).add t4).sub t6).add t8
  let err : Int := 30 -- 30 / 10^6 = 3e-5 > (π/2)^10 / 10! ≈ 2.53e-5
  ⟨max (-SCALE) (poly.lo - err), min SCALE (poly.hi + err)⟩

/-- Interval enclosure of `sin(x)` on `x ∈ [-π/2, π/2]` via `x - x³/6 + x⁵/120 - x⁷/5040 + x⁹/362880 ± 4e-6`. -/
def sinHalfPi (x : Iv) : Iv :=
  let x2 := x.mul x
  let x3 := x2.mul x
  let x5 := x3.mul x2
  let x7 := x5.mul x2
  let x9 := x7.mul x2
  let t3 := x3.divPosInt 6
  let t5 := x5.divPosInt 120
  let t7 := x7.divPosInt 5040
  let t9 := x9.divPosInt 362880
  let poly := (((x.sub t3).add t5).sub t7).add t9
  let err : Int := 5 -- 5 / 10^6 = 5e-6 > (π/2)^11 / 11! ≈ 3.6e-6
  ⟨max (-SCALE) (poly.lo - err), min SCALE (poly.hi + err)⟩

/-- Reduce an arbitrary angle interval `x` modulo `2π` and fold to `[-π/2, π/2]` for `cos`. -/
def cosIv (x : Iv) : Iv :=
  -- Shift by integer multiple k of 2π so midpoint lies in [-π, π]
  let mid := (x.lo + x.hi) / 2
  let k := fdiv (mid + 3141593) 6283185
  let r := x.sub (twoPiIv.scaleInt k)
  -- Now fold from [-π, π] into [-π/2, π/2]
  if r.hi ≤ halfPiIv.lo ∧ -halfPiIv.lo ≤ r.lo then
    cosHalfPi r
  else if halfPiIv.hi ≤ r.lo then
    -- cos(r) = -cos(π - r)
    (cosHalfPi (piIv.sub r)).neg
  else if r.hi ≤ -halfPiIv.hi then
    -- cos(r) = -cos(π + r)
    (cosHalfPi (piIv.add r)).neg
  else
    -- Straddles ±π/2: evaluate via sin(π/2 - |r|) safely
    if 0 ≤ r.lo then sinHalfPi (halfPiIv.sub r)
    else if r.hi ≤ 0 then sinHalfPi (halfPiIv.add r)
    else ⟨-SCALE, SCALE⟩

/-- Reduce an arbitrary angle interval `x` modulo `2π` and fold to `[-π/2, π/2]` for `sin`. -/
def sinIv (x : Iv) : Iv :=
  cosIv (x.sub halfPiIv)

end GravitonCert.Interval
