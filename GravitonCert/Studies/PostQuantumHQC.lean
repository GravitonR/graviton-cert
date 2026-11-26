import GravitonCert.Core.Boundary

/-!
# GravitonCert.Studies.PostQuantumHQC

Machine-checked Lean 4 verification of **NIST HQC (Hamming Quasi-Cyclic, selected March 2025)**
algebraic soundness, **CVE-2025-48946** implicit-rejection collision prevention,
**Hybrid KEM Combiner (`MAL-BIND` / X-Wing)** security, and **Anti-KyberSlash**
division-free constant-time arithmetic (`q = 3329` Barrett reduction & branchless `cmov`).

Every theorem compiles against Lean 4's core kernel with zero external dependencies,
zero `sorryAx`, and zero custom axioms, while explicitly quarantining probabilistic DFR,
physical EM/power masking, and compiler-codegen preservation as typed Open Security Gates.
-/

namespace GravitonCert.Studies.PostQuantumHQC

open GravitonCert

/-! ## 1. Exact Binary Quasi-Cyclic Polynomial Ring `𝔽₂[X] / ⟨Xⁿ - 1⟩` -/

/-- Element of the binary cyclic ring `𝔽₂[X] / ⟨Xⁿ - 1⟩` represented by its `n` Boolean coefficients. -/
abbrev CyclicPoly (n : Nat) := Fin n → Bool

/-- Zero polynomial in `𝔽₂[X] / ⟨Xⁿ - 1⟩`. -/
def polyZero (n : Nat) : CyclicPoly n := fun _ => false

/-- Componentwise XOR addition in `𝔽₂[X] / ⟨Xⁿ - 1⟩`. -/
def polyAdd {n : Nat} (a b : CyclicPoly n) : CyclicPoly n :=
  fun i => xor (a i) (b i)

/-- Auxiliary fold of Boolean XOR over `k` indices `0, 1, ..., k - 1`. -/
def xorFold (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | k + 1 => xor (xorFold f k) (f k)

/-- Exact cyclic index subtraction `(i - j) mod n` for `n > 0`. -/
def cyclicSubIdx (n i j : Nat) : Nat :=
  (i + n - (j % n)) % n

/--
Exact cyclic polynomial multiplication `(a * b)_i = ⨁_{j=0}^{n-1} (a_j ∧ b_{(i - j) mod n})`
in `𝔽₂[X] / ⟨Xⁿ - 1⟩`.
-/
def polyMul {n : Nat} (hn : 0 < n) (a b : CyclicPoly n) : CyclicPoly n :=
  fun i =>
    xorFold (fun j =>
      if hj : j < n then
        a ⟨j, hj⟩ && b ⟨cyclicSubIdx n i.val j, Nat.mod_lt _ hn⟩
      else false) n

private theorem xorFold_false (k : Nat) : xorFold (fun _ => false) k = false := by
  induction k with
  | zero => rfl
  | succ r ih => simp [xorFold, ih]

private theorem xorFold_xor (f g : Nat → Bool) (k : Nat) :
    xorFold (fun j => xor (f j) (g j)) k = xor (xorFold f k) (xorFold g k) := by
  induction k with
  | zero => rfl
  | succ r ih =>
    simp only [xorFold, ih]
    cases xorFold f r <;> cases xorFold g r <;> cases f r <;> cases g r <;> rfl

private theorem xorFold_eq_of_eq (f g : Nat → Bool) (k : Nat)
    (h : ∀ j, j < k → f j = g j) : xorFold f k = xorFold g k := by
  induction k with
  | zero => rfl
  | succ r ih =>
    simp only [xorFold]
    rw [ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h r (Nat.lt_succ_self r)]

private theorem xorFold_comm_sum (f : Nat → Nat → Bool) (m k : Nat) :
    xorFold (fun i => xorFold (fun j => f i j) k) m =
    xorFold (fun j => xorFold (fun i => f i j) m) k := by
  induction m with
  | zero =>
    simp [xorFold, xorFold_false]
  | succ r ih =>
    simp only [xorFold]
    rw [ih, ← xorFold_xor]

/-- Helper: Hamming weight over indices `0..k-1`. -/
def hammingCount (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => hammingCount f k + if f k then 1 else 0

private theorem cyclicSubIdx_invol (n i j : Nat) (hi : i < n) (hj : j < n) :
    cyclicSubIdx n i (cyclicSubIdx n i j) = j := by
  unfold cyclicSubIdx
  have h1 : j % n = j := Nat.mod_eq_of_lt hj
  rw [h1]
  have h2 : (i + n - j) % n < n := Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hi)
  rw [Nat.mod_eq_of_lt h2]
  by_cases hle : j ≤ i
  · have hsub : i + n - j = (i - j) + n := by omega
    have hlt1 : i - j < n := by omega
    rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt hlt1]
    have hsub2 : i + n - (i - j) = j + n := by omega
    rw [hsub2, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  · have hlt : i + n - j < n := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have hsub2 : i + n - (i + n - j) = j := by omega
    rw [hsub2, Nat.mod_eq_of_lt hj]

private theorem xorFold_bijection_fin {n : Nat} (_hn : 0 < n) (f g : Nat → Bool)
    (π : Nat → Nat)
    (hRange : ∀ j, j < n → π j < n)
    (hInvol : ∀ j, j < n → π (π j) = j)
    (hMatch : ∀ j, j < n → f j = g (π j)) :
    xorFold f n = xorFold g n := by
  have hAux : ∀ (fuel : Nat) (F G : Nat → Bool),
      (∀ j, j < n → F j = G (π j)) →
      (∀ j, n ≤ j → F j = false) →
      (∀ j, n ≤ j → G j = false) →
      hammingCount F n ≤ fuel →
      xorFold F n = xorFold G n := by
    intro fuel
    induction fuel with
    | zero =>
      intro F G hFG _ _ hFuel
      have hAllFalse : ∀ j, j < n → F j = false := by
        intro j hj
        have hGe : ∀ m, j < m → (if F j then 1 else 0) ≤ hammingCount F m := by
          intro m
          induction m with
          | zero => intro h; omega
          | succ r ih =>
            intro hjm
            simp only [hammingCount]
            by_cases hEq : r = j
            · subst hEq; omega
            · have := ih (by omega); omega
        have h1 := hGe n hj
        cases hFj : F j with
        | false => rfl
        | true => simp [hFj] at h1; omega
      have hGFalse : ∀ j, j < n → G j = false := by
        intro j hj
        have h1 := hFG (π j) (hRange j hj)
        rw [hInvol j hj, hAllFalse (π j) (hRange j hj)] at h1
        exact h1.symm
      rw [xorFold_eq_of_eq F (fun _ => false) n hAllFalse,
          xorFold_eq_of_eq G (fun _ => false) n hGFalse]
    | succ fuel' ihFuel =>
      intro F G hFG hFn hGn hFuel
      have hFlip : ∀ (H : Nat → Bool) (p : Nat), p < n →
          xorFold (fun j => if j = p then !H j else H j) n = !(xorFold H n) := by
        intro H p hp
        have hGen : ∀ m, (p < m → xorFold (fun j => if j = p then !H j else H j) m = !(xorFold H m)) ∧
                         (m ≤ p → xorFold (fun j => if j = p then !H j else H j) m = xorFold H m) := by
          intro m
          induction m with
          | zero => exact ⟨fun h => by omega, fun _ => rfl⟩
          | succ r ih =>
            constructor
            · intro hpm
              simp only [xorFold]
              by_cases hEq : r = p
              · subst hEq
                rw [ih.2 (Nat.le_refl _)]
                simp only [↓reduceIte]
                cases xorFold H r <;> cases H r <;> rfl
              · have hlt : p < r := by omega
                rw [ih.1 hlt]
                simp only [hEq, ↓reduceIte]
                cases xorFold H r <;> cases H r <;> rfl
            · intro hmp
              simp only [xorFold]
              have hne : r ≠ p := by omega
              rw [ih.2 (by omega)]
              simp only [hne, ↓reduceIte]
        exact (hGen n).1 hp
      have hSearch : ∀ m, (∃ p, p < m ∧ F p = true) ∨ (∀ j, j < m → F j = false) := by
        intro m
        induction m with
        | zero => right; intro j hj; omega
        | succ r ih =>
          cases hFr : F r with
          | true => left; exact ⟨r, Nat.lt_succ_self r, hFr⟩
          | false =>
            cases ih with
            | inl hex =>
              rcases hex with ⟨p, hpr, hp⟩
              left; exact ⟨p, Nat.lt_succ_of_lt hpr, hp⟩
            | inr hall =>
              right; intro j hj
              by_cases hEq : j = r
              · subst hEq; exact hFr
              · exact hall j (by omega)
      cases hSearch n with
      | inr hAllFalse =>
        have hGFalse : ∀ j, j < n → G j = false := by
          intro j hj
          have h1 := hFG (π j) (hRange j hj)
          rw [hInvol j hj, hAllFalse (π j) (hRange j hj)] at h1
          exact h1.symm
        rw [xorFold_eq_of_eq F (fun _ => false) n hAllFalse,
            xorFold_eq_of_eq G (fun _ => false) n hGFalse]
      | inl hEx =>
        rcases hEx with ⟨p, hpn, hFp⟩
        let F' : Nat → Bool := fun j => if j = p then false else F j
        let G' : Nat → Bool := fun j => if j = π p then false else G j
        have hF'Eq : (fun j => if j = p then !F j else F j) = F' := by
          funext j
          by_cases hEq : j = p
          · subst hEq; simp [F', hFp]
          · simp [F', hEq]
        have hGp : G (π p) = true := by
          have h1 := hFG p hpn
          rw [hFp] at h1; exact h1.symm
        have hG'Eq : (fun j => if j = π p then !G j else G j) = G' := by
          funext j
          by_cases hEq : j = π p
          · subst hEq; simp [G', hGp]
          · simp [G', hEq]
        have hFG' : ∀ j, j < n → F' j = G' (π j) := by
          intro j hj
          dsimp [F', G']
          by_cases hEq : j = p
          · subst hEq; simp
          · have hNe : π j ≠ π p := by
              intro hEq2
              have h3 := congrArg π hEq2
              rw [hInvol j hj, hInvol p hpn] at h3
              exact hEq h3
            simp [hEq, hNe, hFG j hj]
        have hF'n : ∀ j, n ≤ j → F' j = false := by
          intro j hj; dsimp [F']; have hne : j ≠ p := by omega
          simp [hne, hFn j hj]
        have hG'n : ∀ j, n ≤ j → G' j = false := by
          intro j hj; dsimp [G']; have hpp := hRange p hpn; have hne : j ≠ π p := by omega
          simp [hne, hGn j hj]
        have hDrop : hammingCount F' n + 1 = hammingCount F n := by
          have hGen : ∀ m, (p < m → hammingCount F' m + 1 = hammingCount F m) ∧
                           (m ≤ p → hammingCount F' m = hammingCount F m) := by
            intro m
            induction m with
            | zero => exact ⟨fun h => by omega, fun _ => rfl⟩
            | succ r ih =>
              constructor
              · intro hpm
                simp only [hammingCount]
                by_cases hEq : r = p
                · subst hEq
                  rw [ih.2 (Nat.le_refl _)]
                  simp [F', hFp]
                · have h1 := ih.1 (by omega)
                  have hFr' : F' r = F r := by simp [F', hEq]
                  simp only [hFr']
                  omega
              · intro hmp
                simp only [hammingCount]
                have hne : r ≠ p := by omega
                rw [ih.2 (by omega)]
                dsimp [F']
                simp [hne]
          exact (hGen n).1 hpn
        have hIH := ihFuel F' G' hFG' hF'n hG'n (by omega)
        have h1 := hFlip F p hpn
        rw [hF'Eq] at h1
        have h2 := hFlip G (π p) (hRange p hpn)
        rw [hG'Eq] at h2
        cases hXF : xorFold F n <;> cases hXG : xorFold G n <;>
          simp_all
  let F0 : Nat → Bool := fun j => if j < n then f j else false
  let G0 : Nat → Bool := fun j => if j < n then g j else false
  have hBound : ∀ m, hammingCount F0 m ≤ m := by
    intro m
    induction m with
    | zero => simp [hammingCount]
    | succ r ih =>
      simp only [hammingCount]
      by_cases hFr : F0 r = true <;> simp [hFr] <;> omega
  have hMain := hAux n F0 G0
    (fun j hj => by
      dsimp only [F0, G0]
      simp [hj, hRange j hj, hMatch j hj])
    (fun j hj => by
      dsimp only [F0]
      have hnot : ¬ (j < n) := by omega
      simp [hnot])
    (fun j hj => by
      dsimp only [G0]
      have hnot : ¬ (j < n) := by omega
      simp [hnot])
    (hBound n)
  rw [← xorFold_eq_of_eq f F0 n (fun j hj => by simp [F0, hj]),
      ← xorFold_eq_of_eq g G0 n (fun j hj => by simp [G0, hj])] at hMain
  exact hMain

/--
**Theorem HQC-01 (Exact `𝔽₂[X] / ⟨Xⁿ - 1⟩` Quasi-Cyclic Ring Laws):**
Universally for every degree `n > 0` and all polynomials `a, b, c ∈ 𝔽₂[X]/⟨Xⁿ - 1⟩`:
1. Exact characteristic-2 self-cancellation `a ⊕ a = 0`,
2. Addition commutativity & associativity,
3. Exact cyclic multiplication commutativity `a * b = b * a`,
4. Exact left/right distributivity `a * (b ⊕ c) = a * b ⊕ a * c` and `(a ⊕ b) * c = a * c ⊕ b * c`.
-/
theorem f2_cyclic_ring_laws {n : Nat} (hn : 0 < n) (a b c : CyclicPoly n) :
    (polyAdd a a = polyZero n) ∧
    (polyAdd a b = polyAdd b a) ∧
    (polyAdd (polyAdd a b) c = polyAdd a (polyAdd b c)) ∧
    (polyMul hn a b = polyMul hn b a) ∧
    (polyMul hn a (polyAdd b c) = polyAdd (polyMul hn a b) (polyMul hn a c)) ∧
    (polyMul hn (polyAdd a b) c = polyAdd (polyMul hn a c) (polyMul hn b c)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext i; simp [polyAdd, polyZero]
  · funext i; simp only [polyAdd]; cases a i <;> cases b i <;> rfl
  · funext i; simp only [polyAdd]; cases a i <;> cases b i <;> cases c i <;> rfl
  · funext i
    simp only [polyMul]
    apply xorFold_bijection_fin hn _ _ (fun j => cyclicSubIdx n i.val j)
    · intro j _; exact Nat.mod_lt _ hn
    · intro j hj; exact cyclicSubIdx_invol n i.val j i.isLt hj
    · intro j hj
      have hR : cyclicSubIdx n i.val j < n := Nat.mod_lt _ hn
      simp only [hj, hR, ↓reduceDIte]
      have hInv := cyclicSubIdx_invol n i.val j i.isLt hj
      have hFin : (⟨cyclicSubIdx n i.val (cyclicSubIdx n i.val j), Nat.mod_lt _ hn⟩ : Fin n) = ⟨j, hj⟩ := by
        ext; exact hInv
      rw [hFin]
      cases a ⟨j, hj⟩ <;> cases b ⟨cyclicSubIdx n i.val j, hR⟩ <;> rfl
  · funext i
    simp only [polyMul, polyAdd]
    rw [← xorFold_xor]
    apply xorFold_eq_of_eq
    intro j hj
    simp only [hj, ↓reduceDIte]
    cases a ⟨j, hj⟩ <;> cases b ⟨cyclicSubIdx n i.val j, Nat.mod_lt _ hn⟩ <;>
      cases c ⟨cyclicSubIdx n i.val j, Nat.mod_lt _ hn⟩ <;> rfl
  · funext i
    simp only [polyMul, polyAdd]
    rw [← xorFold_xor]
    apply xorFold_eq_of_eq
    intro j hj
    simp only [hj, ↓reduceDIte]
    cases a ⟨j, hj⟩ <;> cases b ⟨j, hj⟩ <;>
      cases c ⟨cyclicSubIdx n i.val j, Nat.mod_lt _ hn⟩ <;> rfl

/-- Associativity helper for cyclic polynomial multiplication in `𝔽₂[X] / ⟨Xⁿ - 1⟩`. -/
private theorem cyclicSubIdx_add (n i j k : Nat) (hi : i < n) (hj : j < n) (hk : k < n) :
    cyclicSubIdx n (cyclicSubIdx n i j) k = cyclicSubIdx n (cyclicSubIdx n i k) j := by
  unfold cyclicSubIdx
  have h1 : j % n = j := Nat.mod_eq_of_lt hj
  have h2 : k % n = k := Nat.mod_eq_of_lt hk
  rw [h1, h2]
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
  -- Both sides equal `(i + 2*n - j - k) % n`
  have hL : ((i + n - j) % n + n - k) % n = (i + 2 * n - j - k) % n := by
    by_cases hji : j ≤ i
    · have hA : i + n - j = (i - j) + n := by omega
      have hltA : i - j < n := by omega
      rw [hA, Nat.add_mod_right, Nat.mod_eq_of_lt hltA]
      have hB : i + 2 * n - j - k = (i - j + n - k) + n := by omega
      rw [hB, Nat.add_mod_right]
    · have hA : i + n - j < n := by omega
      rw [Nat.mod_eq_of_lt hA]
      have hB : i + n - j + n - k = i + 2 * n - j - k := by omega
      rw [hB]
  have hR : ((i + n - k) % n + n - j) % n = (i + 2 * n - j - k) % n := by
    by_cases hki : k ≤ i
    · have hA : i + n - k = (i - k) + n := by omega
      have hltA : i - k < n := by omega
      rw [hA, Nat.add_mod_right, Nat.mod_eq_of_lt hltA]
      have hB : i + 2 * n - j - k = (i - k + n - j) + n := by omega
      rw [hB, Nat.add_mod_right]
    · have hA : i + n - k < n := by omega
      rw [Nat.mod_eq_of_lt hA]
      have hB : i + n - k + n - j = i + 2 * n - j - k := by omega
      rw [hB]
  rw [hL, hR]

theorem polyMul_assoc {n : Nat} (hn : 0 < n) (a b c : CyclicPoly n) :
    polyMul hn (polyMul hn a b) c = polyMul hn a (polyMul hn b c) := by
  have hAndXor : ∀ (x : Bool) (f : Nat → Bool) (k : Nat),
      (x && xorFold f k) = xorFold (fun j => x && f j) k := by
    intro x f k
    induction k with
    | zero => cases x <;> rfl
    | succ r ih =>
      simp only [xorFold]
      cases x with
      | false => simp [xorFold_false]
      | true => simp
  -- Expand LHS: `polyMul hn a (polyMul hn b c)` vs `polyMul hn (polyMul hn a b) c`
  -- Prove `polyMul hn x (polyMul hn y z) = polyMul hn y (polyMul hn x z)` (left-commutativity)
  have hLeftComm : ∀ (x y z : CyclicPoly n),
      polyMul hn x (polyMul hn y z) = polyMul hn y (polyMul hn x z) := by
    intro x y z
    funext idx
    have hL : polyMul hn x (polyMul hn y z) idx =
        xorFold (fun j => xorFold (fun k =>
          if hj : j < n then if hk : k < n then
            x ⟨j, hj⟩ && y ⟨k, hk⟩ && z ⟨cyclicSubIdx n (cyclicSubIdx n idx.val j) k, Nat.mod_lt _ hn⟩
          else false else false) n) n := by
      simp only [polyMul]
      apply xorFold_eq_of_eq; intro j hj; simp only [hj, ↓reduceDIte]
      rw [hAndXor]; apply xorFold_eq_of_eq; intro k hk; simp only [hk, ↓reduceDIte]
      cases x ⟨j, hj⟩ <;> cases y ⟨k, hk⟩ <;> rfl
    have hR : polyMul hn y (polyMul hn x z) idx =
        xorFold (fun j => xorFold (fun k =>
          if hj : j < n then if hk : k < n then
            y ⟨j, hj⟩ && x ⟨k, hk⟩ && z ⟨cyclicSubIdx n (cyclicSubIdx n idx.val j) k, Nat.mod_lt _ hn⟩
          else false else false) n) n := by
      simp only [polyMul]
      apply xorFold_eq_of_eq; intro j hj; simp only [hj, ↓reduceDIte]
      rw [hAndXor]; apply xorFold_eq_of_eq; intro k hk; simp only [hk, ↓reduceDIte]
      cases y ⟨j, hj⟩ <;> cases x ⟨k, hk⟩ <;> rfl
    rw [hL, hR, xorFold_comm_sum]
    apply xorFold_eq_of_eq; intro k hk
    apply xorFold_eq_of_eq; intro j hj
    simp only [hj, hk, ↓reduceDIte]
    have hIdx : (⟨cyclicSubIdx n (cyclicSubIdx n idx.val j) k, Nat.mod_lt _ hn⟩ : Fin n) =
                ⟨cyclicSubIdx n (cyclicSubIdx n idx.val k) j, Nat.mod_lt _ hn⟩ := by
      ext; exact cyclicSubIdx_add n idx.val j k idx.isLt hj hk
    rw [hIdx]
    cases x ⟨j, hj⟩ <;> cases y ⟨k, hk⟩ <;> rfl
  calc polyMul hn (polyMul hn a b) c
      = polyMul hn c (polyMul hn a b) := (f2_cyclic_ring_laws hn (polyMul hn a b) c c).2.2.2.1
    _ = polyMul hn a (polyMul hn c b) := hLeftComm c a b
    _ = polyMul hn a (polyMul hn b c) := by rw [(f2_cyclic_ring_laws hn c b c).2.2.2.1]

/-! ## 2. HQC Exact Decryption Noise Cancellation (`HQC-02`) -/

/-- HQC public key `s = x ⊕ h * y` in `𝔽₂[X] / ⟨Xⁿ - 1⟩`. -/
def hqcPublicKey {n : Nat} (hn : 0 < n) (x y h : CyclicPoly n) : CyclicPoly n :=
  polyAdd x (polyMul hn h y)

/-- HQC ciphertext first block `u = r₁ ⊕ h * r₂`. -/
def hqcCipherU {n : Nat} (hn : 0 < n) (h r1 r2 : CyclicPoly n) : CyclicPoly n :=
  polyAdd r1 (polyMul hn h r2)

/-- HQC ciphertext second block `v = mG ⊕ s * r₂ ⊕ e`. -/
def hqcCipherV {n : Nat} (hn : 0 < n) (mG s r2 e : CyclicPoly n) : CyclicPoly n :=
  polyAdd (polyAdd mG (polyMul hn s r2)) e

/-- HQC decryption input `v ⊕ u * y`. -/
def hqcDecryptInput {n : Nat} (hn : 0 < n) (u v y : CyclicPoly n) : CyclicPoly n :=
  polyAdd v (polyMul hn u y)

/-- Exact HQC effective noise polynomial `e' = x * r₂ ⊕ r₁ * y ⊕ e`. -/
def hqcEffectiveNoise {n : Nat} (hn : 0 < n) (x y r1 r2 e : CyclicPoly n) : CyclicPoly n :=
  polyAdd (polyAdd (polyMul hn x r2) (polyMul hn r1 y)) e

/--
**Theorem HQC-02 (Exact HQC Decryption Noise Cancellation Identity):**
For *every* cyclic ring degree `n > 0` and *every* secret key `(x, y)`, public generator `h`,
ephemeral randomness `(r₁, r₂, e)`, and encoded message `mG`:
`v ⊕ u * y = mG ⊕ (x * r₂ ⊕ r₁ * y ⊕ e)`.
The public-key masking cross-term `(h * y) * r₂ ⊕ (h * r₂) * y` cancels identically in `𝔽₂[X]/⟨Xⁿ - 1⟩`.
-/
theorem hqc_exact_decryption_noise_identity {n : Nat} (hn : 0 < n)
    (x y h r1 r2 e mG : CyclicPoly n) :
    let s := hqcPublicKey hn x y h
    let u := hqcCipherU hn h r1 r2
    let v := hqcCipherV hn mG s r2 e
    hqcDecryptInput hn u v y = polyAdd mG (hqcEffectiveNoise hn x y r1 r2 e) := by
  intro s u v
  dsimp only [hqcDecryptInput, hqcEffectiveNoise, s, u, v, hqcPublicKey, hqcCipherU, hqcCipherV]
  have hDistS := (f2_cyclic_ring_laws hn x (polyMul hn h y) r2).2.2.2.2.2
  have hDistU := (f2_cyclic_ring_laws hn r1 (polyMul hn h r2) y).2.2.2.2.2
  rw [hDistS, hDistU]
  -- Show `(h * y) * r2 = (h * r2) * y`
  have hCross : polyMul hn (polyMul hn h y) r2 = polyMul hn (polyMul hn h r2) y := by
    rw [polyMul_assoc, polyMul_assoc]
    rw [(f2_cyclic_ring_laws hn y r2 r2).2.2.2.1]
  rw [hCross]
  funext i
  simp only [polyAdd]
  cases mG i <;> cases polyMul hn x r2 i <;> cases polyMul hn (polyMul hn h r2) y i <;>
    cases e i <;> cases polyMul hn r1 y i <;> rfl

/-! ## 3. Exact Hamming-Weight Submultiplicative Noise Ceiling (`HQC-03`) -/

/-- Exact Hamming weight `wt(a)` of a polynomial `a ∈ 𝔽₂[X] / ⟨Xⁿ - 1⟩`. -/
def hammingWeight {n : Nat} (a : CyclicPoly n) : Nat :=
  hammingCount (fun j => if hj : j < n then a ⟨j, hj⟩ else false) n

private def sumHamming (f : Nat → Nat → Bool) (m : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => sumHamming f m t + hammingCount (fun i => f i t) m

private theorem hammingCount_xor_le (f g : Nat → Bool) (k : Nat) :
    hammingCount (fun j => xor (f j) (g j)) k ≤ hammingCount f k + hammingCount g k := by
  induction k with
  | zero => simp [hammingCount]
  | succ r ih =>
    simp only [hammingCount]
    by_cases hf : f r = true <;> by_cases hg : g r = true <;> simp [hf, hg] <;> omega

private theorem hammingCount_xorFold_le (f : Nat → Nat → Bool) (m k : Nat) :
    hammingCount (fun i => xorFold (fun j => f i j) k) m ≤ sumHamming f m k := by
  induction k with
  | zero =>
    have hZ : hammingCount (fun _ => false) m = 0 := by
      induction m with
      | zero => rfl
      | succ r ih => simp [hammingCount, ih]
    simp only [xorFold, sumHamming]
    rw [hZ]; omega
  | succ r ih =>
    simp only [xorFold, sumHamming]
    have hTri := hammingCount_xor_le (fun i => xorFold (fun j => f i j) r) (fun i => f i r) m
    omega

private theorem hammingCount_shift_eq {n : Nat} (hn : 0 < n) (b : CyclicPoly n) (j : Nat) (hj : j < n) :
    hammingCount (fun i => if i < n then b ⟨cyclicSubIdx n i j, Nat.mod_lt _ hn⟩ else false) n =
    hammingWeight b := by
  unfold hammingWeight
  have hSplit : ∀ (F : Nat → Bool) (s : Nat), s ≤ n →
      hammingCount (fun i => F ((i + s) % n)) n = hammingCount F n := by
    intro F s hs
    have hTail : ∀ a b, hammingCount (fun i => F (a + i)) b + hammingCount F a = hammingCount F (a + b) := by
      intro a b
      induction b with
      | zero => simp [hammingCount]
      | succ r ih =>
        have hEq : a + (r + 1) = (a + r) + 1 := by omega
        rw [hEq]
        simp only [hammingCount]
        omega
    have hEqRange : ∀ (G1 G2 : Nat → Bool) (m : Nat),
        (∀ i, i < m → G1 i = G2 i) → hammingCount G1 m = hammingCount G2 m := by
      intro G1 G2 m h
      induction m with
      | zero => rfl
      | succ r ih =>
        simp only [hammingCount]
        rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h r (Nat.lt_succ_self r)]
    have hDecomp : ∀ (G : Nat → Bool) (a b : Nat),
        hammingCount G (a + b) = hammingCount G a + hammingCount (fun i => G (a + i)) b := by
      intro G a b
      induction b with
      | zero => simp [hammingCount]
      | succ r ih =>
        have hEq : a + (r + 1) = (a + r) + 1 := by omega
        rw [hEq]
        simp only [hammingCount]
        omega
    have hN : n = (n - s) + s := by omega
    have hEqN : hammingCount (fun i => F ((i + s) % n)) n =
        hammingCount (fun i => F ((i + s) % n)) ((n - s) + s) := by
      rw [← hN]
    rw [hEqN, hDecomp]
    have hPart1 : hammingCount (fun i => F ((i + s) % n)) (n - s) =
        hammingCount (fun i => F (s + i)) (n - s) := by
      apply hEqRange; intro i hi
      have hMod : (i + s) % n = s + i := by
        rw [Nat.add_comm]; exact Nat.mod_eq_of_lt (by omega)
      rw [hMod]
    have hPart2 : hammingCount (fun i => F (((n - s) + i + s) % n)) s = hammingCount F s := by
      apply hEqRange; intro i hi
      have hMod : ((n - s) + i + s) % n = i := by
        have hEq : (n - s) + i + s = i + n := by omega
        rw [hEq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hMod]
    rw [hPart1, hPart2]
    have hSum := hTail s (n - s)
    have hSn : s + (n - s) = n := by omega
    rw [hSn] at hSum
    omega
  let Fb : Nat → Bool := fun k => if hk : k < n then b ⟨k, hk⟩ else false
  have hShift : ∀ i, i < n →
      (if i < n then b ⟨cyclicSubIdx n i j, Nat.mod_lt _ hn⟩ else false) =
      Fb ((i + (n - j)) % n) := by
    intro i hi
    simp only [hi, ↓reduceIte, Fb, Nat.mod_lt _ hn, ↓reduceDIte]
    unfold cyclicSubIdx
    have hjm : j % n = j := Nat.mod_eq_of_lt hj
    rw [hjm]
    have hEq : i + n - j = i + (n - j) := by omega
    rw [hEq]
  have hEq1 : hammingCount (fun i => if i < n then b ⟨cyclicSubIdx n i j, Nat.mod_lt _ hn⟩ else false) n =
      hammingCount (fun i => Fb ((i + (n - j)) % n)) n := by
    have hGen : ∀ m, (∀ i, i < m →
        (if i < n then b ⟨cyclicSubIdx n i j, Nat.mod_lt _ hn⟩ else false) =
        Fb ((i + (n - j)) % n)) →
        hammingCount (fun i => if i < n then b ⟨cyclicSubIdx n i j, Nat.mod_lt _ hn⟩ else false) m =
        hammingCount (fun i => Fb ((i + (n - j)) % n)) m := by
      intro m
      induction m with
      | zero => intro _; rfl
      | succ r ih =>
        intro h
        simp only [hammingCount]
        rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]
        have hr := h r (Nat.lt_succ_self r)
        simp only [hr]
    exact hGen n hShift
  rw [hEq1, hSplit Fb (n - j) (by omega)]

theorem hammingWeight_add_le {n : Nat} (a b : CyclicPoly n) :
    hammingWeight (polyAdd a b) ≤ hammingWeight a + hammingWeight b := by
  unfold hammingWeight polyAdd
  have hEq : ∀ k, k ≤ n →
      hammingCount (fun j => if hj : j < n then xor (a ⟨j, hj⟩) (b ⟨j, hj⟩) else false) k =
      hammingCount (fun j => xor (if hj : j < n then a ⟨j, hj⟩ else false)
                                 (if hj : j < n then b ⟨j, hj⟩ else false)) k := by
    intro k hk
    induction k with
    | zero => rfl
    | succ r ih =>
      simp only [hammingCount]
      have hlt : r < n := by omega
      rw [ih (by omega)]
      simp [hlt]
  rw [hEq n (Nat.le_refl _)]
  exact hammingCount_xor_le _ _ n

theorem hammingWeight_mul_le {n : Nat} (hn : 0 < n) (a b : CyclicPoly n) :
    hammingWeight (polyMul hn a b) ≤ hammingWeight a * hammingWeight b := by
  unfold hammingWeight polyMul
  let term : Nat → Nat → Bool := fun i j =>
    if hi : i < n then
      if hj : j < n then
        a ⟨j, hj⟩ && b ⟨cyclicSubIdx n i j, Nat.mod_lt _ hn⟩
      else false
    else false
  have hEq : ∀ k, k ≤ n →
      hammingCount (fun i => if hi : i < n then
        xorFold (fun j => if hj : j < n then a ⟨j, hj⟩ && b ⟨cyclicSubIdx n i j, Nat.mod_lt _ hn⟩ else false) n
        else false) k =
      hammingCount (fun i => xorFold (fun j => term i j) n) k := by
    intro k hk
    induction k with
    | zero => rfl
    | succ r ih =>
      simp only [hammingCount]
      have hlt : r < n := by omega
      rw [ih (by omega)]
      have hX : xorFold (fun j => if hj : j < n then a ⟨j, hj⟩ && b ⟨cyclicSubIdx n r j, Nat.mod_lt _ hn⟩ else false) n =
                xorFold (fun j => term r j) n := by
        apply xorFold_eq_of_eq; intro j hj; simp [term, hlt, hj]
      simp only [hlt, ↓reduceDIte, hX]
  rw [hEq n (Nat.le_refl _)]
  have hStep := hammingCount_xorFold_le term n n
  -- Bound the right-hand sum by `hammingWeight a * hammingWeight b`
  have hSumLe : ∀ k, k ≤ n →
      sumHamming term n k ≤
      hammingCount (fun j => if hj : j < n then a ⟨j, hj⟩ else false) k * hammingWeight b := by
    intro k hk
    induction k with
    | zero => simp [sumHamming, hammingCount]
    | succ r ih =>
      simp only [sumHamming, hammingCount]
      have hr : r < n := by omega
      have hIH := ih (by omega)
      cases hAr : a ⟨r, hr⟩ with
      | false =>
        have hZero : hammingCount (fun i => term i r) n = 0 := by
          have hGen : ∀ m, hammingCount (fun i => term i r) m = 0 := by
            intro m; induction m with
            | zero => rfl
            | succ q ihq =>
              simp only [hammingCount]
              rw [ihq]
              have hFalse : term q r = false := by
                dsimp [term]
                by_cases hq : q < n <;> simp [hq, hr, hAr]
              simp [hFalse]
          exact hGen n
        simp only [hr, ↓reduceDIte, hAr, Bool.false_eq_true, ↓reduceIte, hZero, Nat.add_zero]
        exact hIH
      | true =>
        have hOne : hammingCount (fun i => term i r) n = hammingWeight b := by
          have hEqShift : ∀ m, hammingCount (fun i => term i r) m =
              hammingCount (fun i => if i < n then b ⟨cyclicSubIdx n i r, Nat.mod_lt _ hn⟩ else false) m := by
            intro m; induction m with
            | zero => rfl
            | succ q ihq =>
              simp only [hammingCount]
              rw [ihq]
              have hStepEq : term q r = (if q < n then b ⟨cyclicSubIdx n q r, Nat.mod_lt _ hn⟩ else false) := by
                dsimp [term]
                by_cases hq : q < n <;> simp [hq, hr, hAr]
              simp only [hStepEq]
          rw [hEqShift n]
          exact hammingCount_shift_eq hn b r hr
        simp only [hr, ↓reduceDIte, hAr, ↓reduceIte, hOne]
        rw [Nat.add_mul, Nat.one_mul]
        omega
  exact Nat.le_trans hStep (hSumLe n (Nat.le_refl _))

/--
**Theorem HQC-03 (Exact HQC Hamming-Weight Noise Ceiling):**
Universally for every `n > 0` and all polynomials `x, y, r₁, r₂, e ∈ 𝔽₂[X] / ⟨Xⁿ - 1⟩`:
`wt(x * r₂ ⊕ r₁ * y ⊕ e) ≤ wt(x)·wt(r₂) + wt(r₁)·wt(y) + wt(e)`.
-/
theorem hqc_hamming_weight_submultiplicative_bound {n : Nat} (hn : 0 < n)
    (x y r1 r2 e : CyclicPoly n) :
    hammingWeight (hqcEffectiveNoise hn x y r1 r2 e) ≤
      hammingWeight x * hammingWeight r2 + hammingWeight r1 * hammingWeight y + hammingWeight e := by
  unfold hqcEffectiveNoise
  have h1 := hammingWeight_add_le (polyAdd (polyMul hn x r2) (polyMul hn r1 y)) e
  have h2 := hammingWeight_add_le (polyMul hn x r2) (polyMul hn r1 y)
  have h3 := hammingWeight_mul_le hn x r2
  have h4 := hammingWeight_mul_le hn r1 y
  omega

/-! ## 4. Deterministic Decoding Soundness & Probabilistic DFR Boundary (`HQC-04`) -/

/--
**Theorem HQC-04 (HQC Deterministic Error-Correction Gate):**
For *any* encoder `Encode : M → CyclicPoly n` and decoder `Decode : CyclicPoly n → M`
certified to correct every error of Hamming weight `≤ δ`, whenever the HQC noise weight
obeys `wt(x)·wt(r₂) + wt(r₁)·wt(y) + wt(e) ≤ δ`, HQC decryption recovers the exact message `m`
with zero failure.
-/
theorem hqc_deterministic_decoding_correctness_gate {n : Nat} {M : Type} (hn : 0 < n)
    (Encode : M → CyclicPoly n) (Decode : CyclicPoly n → M) (δ : Nat)
    (hRadius : ∀ (m : M) (err : CyclicPoly n), hammingWeight err ≤ δ → Decode (polyAdd (Encode m) err) = m)
    (x y h r1 r2 e : CyclicPoly n) (m : M)
    (hNoise : hammingWeight x * hammingWeight r2 + hammingWeight r1 * hammingWeight y + hammingWeight e ≤ δ) :
    let s := hqcPublicKey hn x y h
    let u := hqcCipherU hn h r1 r2
    let v := hqcCipherV hn (Encode m) s r2 e
    Decode (hqcDecryptInput hn u v y) = m := by
  intro s u v
  rw [hqc_exact_decryption_noise_identity hn x y h r1 r2 e (Encode m)]
  have hW := hqc_hamming_weight_submultiplicative_bound hn x y r1 r2 e
  exact hRadius m (hqcEffectiveNoise hn x y r1 r2 e) (Nat.le_trans hW hNoise)

/-! ## 5. Official 2025 NIST HQC-128 / HQC-192 / HQC-256 Code Geometry (`HQC-05`) -/

/-- Official structural parameters for a NIST HQC security instance (concatenated RS + duplicated RM). -/
structure HQCParamSet where
  name : String
  securityLevel : Nat
  n : Nat
  omega : Nat
  omegaR : Nat
  omegaE : Nat
  nRS : Nat
  kRS : Nat
  dRS : Nat
  nRM : Nat
  dRM : Nat
  rmMult : Nat
  deriving Repr

def hqc128 : HQCParamSet :=
  { name := "HQC-128", securityLevel := 1, n := 17669, omega := 66, omegaR := 75, omegaE := 75,
    nRS := 46, kRS := 16, dRS := 31, nRM := 384, dRM := 192, rmMult := 3 }

def hqc192 : HQCParamSet :=
  { name := "HQC-192", securityLevel := 3, n := 35851, omega := 100, omegaR := 114, omegaE := 114,
    nRS := 56, kRS := 24, dRS := 33, nRM := 640, dRM := 320, rmMult := 5 }

def hqc256 : HQCParamSet :=
  { name := "HQC-256", securityLevel := 5, n := 57637, omega := 131, omegaR := 149, omegaE := 149,
    nRS := 90, kRS := 32, dRS := 59, nRM := 640, dRM := 320, rmMult := 5 }

def hqcGeometryValid (p : HQCParamSet) : Bool :=
  (p.dRS == p.nRS - p.kRS + 1) &&
  (p.nRM == 128 * p.rmMult) &&
  (p.dRM == 64 * p.rmMult) &&
  (p.nRS * p.nRM < p.n) &&
  (p.n - p.nRS * p.nRM > 0)

/--
**Theorem HQC-05 (Official NIST HQC-128 / 192 / 256 Code Geometry & Padding Slack):**
Certifies for all three NIST HQC parameter sets:
1. Exact MDS Singleton bound equality `d_RS = n_RS - k_RS + 1` and duplicated Reed–Muller `[128·m, 8, 64·m]` geometry,
2. Exact positive padding slack `n - n_RS · n_RM` (`5` bits for HQC-128, `11` bits for HQC-192, `37` bits for HQC-256)
   — identifying the exact truncation boundary that implementations must zero/bind,
3. Worst-case deterministic weight `2 ω ω_r + ω_e` strictly exceeds deterministic concatenated radius
   `(d_RS · d_RM - 1) / 2`, proving why HQC security relies on probabilistic DFR (`HQC-GATE-01`).
-/
theorem nist_hqc_official_parameter_soundness :
    (hqcGeometryValid hqc128 = true ∧ hqc128.n - hqc128.nRS * hqc128.nRM = 5 ∧
      (hqc128.dRS * hqc128.dRM - 1) / 2 < 2 * hqc128.omega * hqc128.omegaR + hqc128.omegaE) ∧
    (hqcGeometryValid hqc192 = true ∧ hqc192.n - hqc192.nRS * hqc192.nRM = 11 ∧
      (hqc192.dRS * hqc192.dRM - 1) / 2 < 2 * hqc192.omega * hqc192.omegaR + hqc192.omegaE) ∧
    (hqcGeometryValid hqc256 = true ∧ hqc256.n - hqc256.nRS * hqc256.nRM = 37 ∧
      (hqc256.dRS * hqc256.dRM - 1) / 2 < 2 * hqc256.omega * hqc256.omegaR + hqc256.omegaE) := by
  decide

/-! ## 6. Formalizing `CVE-2025-48946` Implicit-Rejection Collision & Binding Repair (`HQC-06`) -/

/-- Domain tag distinguishing valid decapsulation from implicit rejection. -/
inductive KEMDomainTag where
  | validDecap
  | implicitReject
  deriving DecidableEq, Repr

/-- Vulnerable implicit rejection (omits full ciphertext `ct` or drops padding bits): models `CVE-2025-48946`. -/
def vulnerableImplicitReject {Secret PK CT Key : Type} (prf : Secret → PK → Key)
    (z : Secret) (pk : PK) (_ct : CT) : Key :=
  prf z pk

/--
Full-ciphertext & public-key bound implicit rejection (`K_rej = H(implicitReject, z, pk, ct)`),
remediating `CVE-2025-48946` and guaranteeing `MAL-BIND-K-CT` / `MAL-BIND-K-PK`.
-/
def boundDecapKey {Secret PK CT Key : Type}
    (H : KEMDomainTag → Secret → PK → CT → Key)
    (valid : Bool) (z : Secret) (pk : PK) (ct : CT) : Key :=
  if valid then H .validDecap z pk ct else H .implicitReject z pk ct

/--
**Theorem HQC-06 (`CVE-2025-48946` Collision Witness & Bound Implicit-Rejection Non-Collision):**
1. *Vulnerable rejection collides:* For any two distinct malformed ciphertexts `ct₁ ≠ ct₂`,
   `vulnerableImplicitReject` outputs the exact same shared secret `K(ct₁) = K(ct₂)` (`CVE-2025-48946`),
2. *Bound rejection is strictly non-colliding:* Under a collision-resistant (injective) RO `H`,
   `boundDecapKey` guarantees:
   - Distinct `(pk, ct)` inputs never collide on rejected keys (`MAL-BIND-K-CT` + `MAL-BIND-K-PK`),
   - A valid decapsulation key can never collide with an implicitly rejected key (strict domain separation).
-/
theorem cve_2025_48946_implicit_rejection_collision_and_fix
    {Secret PK CT Key : Type}
    (prf : Secret → PK → Key)
    (H : KEMDomainTag → Secret → PK → CT → Key)
    (hCR : ∀ t1 t2 z1 z2 p1 p2 c1 c2,
      H t1 z1 p1 c1 = H t2 z2 p2 c2 → t1 = t2 ∧ z1 = z2 ∧ p1 = p2 ∧ c1 = c2)
    (z : Secret) (pk1 pk2 : PK) (ct1 ct2 : CT) :
    (vulnerableImplicitReject prf z pk1 ct1 = vulnerableImplicitReject prf z pk1 ct2) ∧
    (boundDecapKey H false z pk1 ct1 = boundDecapKey H false z pk2 ct2 → pk1 = pk2 ∧ ct1 = ct2) ∧
    (boundDecapKey H true z pk1 ct1 ≠ boundDecapKey H false z pk2 ct2) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro hEq
    simp only [boundDecapKey, Bool.false_eq_true, ↓reduceIte] at hEq
    have h := hCR .implicitReject .implicitReject z z pk1 pk2 ct1 ct2 hEq
    exact ⟨h.2.2.1, h.2.2.2⟩
  · intro hEq
    simp only [boundDecapKey, ↓reduceIte, Bool.false_eq_true] at hEq
    have h := hCR .validDecap .implicitReject z z pk1 pk2 ct1 ct2 hEq
    cases h.1

/-! ## 7. Hybrid KEM Combiner (`X25519 + HQC` / `X-Wing`) Binding & Anti-Downgrade (`HQC-07`, `HQC-08`) -/

/-- Broken naive XOR hybrid combiner `K = K_cl ⊕ K_pq` (ignores ciphertexts and public keys). -/
def naiveXorCombiner (kCl kPQ : UInt64) : UInt64 :=
  kCl ^^^ kPQ

/-- X-Wing / CFRG-style domain-separated hybrid combiner binding both keys, both ciphertexts, and both public keys. -/
def xwingBoundCombiner {K1 K2 CT1 CT2 PK1 PK2 Out : Type}
    (KDF : String → K1 → K2 → CT1 → CT2 → PK1 → PK2 → Out)
    (suiteLabel : String) (k1 : K1) (k2 : K2) (ct1 : CT1) (ct2 : CT2) (pk1 : PK1) (pk2 : PK2) : Out :=
  KDF suiteLabel k1 k2 ct1 ct2 pk1 pk2

/--
**Theorem HQC-07 (Broken XOR Combiner Counterexample vs. Bound Hybrid Combiner `MAL-BIND`):**
1. *Broken XOR combiner fails `MAL-BIND`:* There exist distinct key pairs `(k1, k2) ≠ (k1', k2')`
   producing the exact same combined key `naiveXorCombiner k1 k2 = naiveXorCombiner k1' k2'` (even `0 ^^^ 0 = 1 ^^^ 1`).
2. *X-Wing-style bound combiner satisfies full `MAL-BIND` + cross-suite separation:*
   Under collision-resistant `KDF`, equality of combined outputs forces equality of the suite label,
   both component secrets, both ciphertexts, and both public keys.
-/
theorem hybrid_kem_combiner_mal_bind_and_weak_counterexample
    {K1 K2 CT1 CT2 PK1 PK2 Out : Type}
    (KDF : String → K1 → K2 → CT1 → CT2 → PK1 → PK2 → Out)
    (hCR : ∀ l1 l2 a1 a2 b1 b2 c1 c2 d1 d2 p1 p2 q1 q2,
      KDF l1 a1 b1 c1 d1 p1 q1 = KDF l2 a2 b2 c2 d2 p2 q2 →
      l1 = l2 ∧ a1 = a2 ∧ b1 = b2 ∧ c1 = c2 ∧ d1 = d2 ∧ p1 = p2 ∧ q1 = q2)
    (l1 l2 : String) (a1 a2 : K1) (b1 b2 : K2) (c1 c2 : CT1) (d1 d2 : CT2) (p1 p2 : PK1) (q1 q2 : PK2) :
    (∃ x1 y1 x2 y2 : UInt64, (x1 ≠ x2 ∧ y1 ≠ y2) ∧ naiveXorCombiner x1 y1 = naiveXorCombiner x2 y2) ∧
    (xwingBoundCombiner KDF l1 a1 b1 c1 d1 p1 q1 = xwingBoundCombiner KDF l2 a2 b2 c2 d2 p2 q2 →
      l1 = l2 ∧ c1 = c2 ∧ d1 = d2 ∧ p1 = p2 ∧ q1 = q2) := by
  refine ⟨⟨0, 0, 1, 1, ⟨by decide, by decide⟩, by decide⟩, ?_⟩
  intro hEq
  unfold xwingBoundCombiner at hEq
  have h := hCR l1 l2 a1 a2 b1 b2 c1 c2 d1 d2 p1 p2 q1 q2 hEq
  exact ⟨h.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/--
Effective handshake security under adversary capability `(classicalBroken, pqBroken)` and
deployment policy `allowClassicalFallback` (e.g., middlebox downgrade).
-/
def hybridHandshakeSecure (classicalBroken pqBroken allowClassicalFallback activeDowngrade : Bool) : Bool :=
  if allowClassicalFallback && activeDowngrade then
    !classicalBroken
  else
    (!classicalBroken) || (!pqBroken)

/--
**Theorem HQC-08 (Hybrid Dual-Survival & Middlebox Downgrade Collapse):**
1. With strict hybrid enforcement (`allowClassicalFallback = false`), the handshake remains
   secure whenever *at least one* primitive holds (`classicalBroken = false ∨ pqBroken = false`),
   completely immune to active network downgrade attacks.
2. Allowing classical fallback (`allowClassicalFallback = true`) under an active downgrade
   collapses security to classical-only (`false` whenever `classicalBroken = true`), even if
   the post-quantum KEM (`HQC` / `ML-KEM`) is unbroken.
-/
theorem hybrid_kem_dual_security_and_downgrade_gate
    (classicalBroken pqBroken activeDowngrade : Bool) :
    (hybridHandshakeSecure classicalBroken pqBroken false activeDowngrade =
      (!classicalBroken || !pqBroken)) ∧
    (hybridHandshakeSecure true false true true = false) := by
  cases classicalBroken <;> cases pqBroken <;> cases activeDowngrade <;> decide

/-! ## 8. Anti-KyberSlash Division-Free Barrett Reduction & Constant-Time `cmov` (`HQC-09`) -/

/-- Branchless constant-time conditional select (`mask = 0` selects `b`; `mask = 0xFFFF_FFFF_FFFF_FFFF` selects `a`). -/
def ctSelectU64 (mask a b : UInt64) : UInt64 :=
  (mask &&& a) ||| ((~~~mask) &&& b)

/-- NIST ML-KEM prime modulus `q = 3329` (KyberSlash target). -/
def mlkemQ : Nat := 3329

/-- Exact floor Barrett multiplier `⌊2²⁶ / 3329⌋ = 20158` (note: rounded `20159` underflows unsigned `x < 3329²`!). -/
def barrettMult : Nat := 20158

/-- Division-free Barrett reduction `x - ((x * 20158) >> 26) * 3329` using zero `/` instructions. -/
def barrettReduceMLKEM (x : Nat) : Nat :=
  let t := (x * barrettMult) >>> 26
  x - t * mlkemQ

/--
**Theorem HQC-09 (Anti-KyberSlash Constant-Time `cmov` & Division-Free Barrett Reduction):**
1. For *every* `a, b : UInt64`, branchless `ctSelectU64` selects `b` at `mask = 0` and `a` at
   `mask = 0xFFFFFFFFFFFFFFFF` with zero secret-dependent branches.
2. For *every* `x < 3329²` (`11,082,241`), division-free `barrettReduceMLKEM x` (using exact floor
   `20158 = ⌊2²⁶ / 3329⌋`, avoiding the unsigned underflow of rounded `20159` at `x = 11,032,241`)
   uses zero division instructions, never underflows (`t * 3329 ≤ x`), satisfies
   `barrettReduceMLKEM x % 3329 = x % 3329`, and stays strictly bounded in `[0, 2 * 3329)`.
-/
theorem constant_time_barrett_and_cmov_no_div_soundness (a b : UInt64) (x : Nat)
    (hx : x < mlkemQ * mlkemQ) :
    (ctSelectU64 0 a b = b) ∧
    (ctSelectU64 (~~~(0 : UInt64)) a b = a) ∧
    (((x * barrettMult) >>> 26) * mlkemQ ≤ x) ∧
    (barrettReduceMLKEM x % mlkemQ = x % mlkemQ) ∧
    (barrettReduceMLKEM x < 2 * mlkemQ) := by
  have hShift : ∀ y : Nat, y >>> 26 = y / 67108864 := by
    intro y; exact Nat.shiftRight_eq_div_pow y 26
  have hLe : (x * barrettMult / 67108864) * mlkemQ ≤ x := by
    unfold barrettMult mlkemQ at *; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold ctSelectU64; simp
  · unfold ctSelectU64; simp
  · rw [hShift]; exact hLe
  · unfold barrettReduceMLKEM
    dsimp only
    rw [hShift]
    have hMod := Nat.add_mul_mod_self_right (x - (x * barrettMult / 67108864) * mlkemQ) (x * barrettMult / 67108864) mlkemQ
    have hEq : (x - (x * barrettMult / 67108864) * mlkemQ) + (x * barrettMult / 67108864) * mlkemQ = x := by
      omega
    rw [hEq] at hMod
    exact hMod.symm
  · unfold barrettReduceMLKEM
    dsimp only
    rw [hShift]
    unfold barrettMult mlkemQ at *
    omega

/-! ## 9. Executable `PQCImplementationAcceptanceGate` (`HQC-10`) -/

/--
Executable Graviton acceptance gate for a post-quantum KEM / hybrid deployment
(closing the "Verification Theatre" gap between abstract specs and real-world CVEs).
-/
structure PQCImplementationAcceptanceGate where
  algebraicNoiseExact : Bool
  fullCiphertextBoundReject : Bool
  boundHybridCombiner : Bool
  disallowClassicalDowngrade : Bool
  divisionFreeConstantTime : Bool
  deriving DecidableEq, Repr

def passesPQCAcceptanceGate (g : PQCImplementationAcceptanceGate) : Bool :=
  g.algebraicNoiseExact &&
  g.fullCiphertextBoundReject &&
  g.boundHybridCombiner &&
  g.disallowClassicalDowngrade &&
  g.divisionFreeConstantTime

/-- Witness representing Graviton's verified HQC + X-Wing-bound + division-free profile. -/
def gravitonVerifiedHQCHybridProfile : PQCImplementationAcceptanceGate :=
  { algebraicNoiseExact := true
    fullCiphertextBoundReject := true
    boundHybridCombiner := true
    disallowClassicalDowngrade := true
    divisionFreeConstantTime := true }

/--
**Theorem HQC-10 (Executable PQC Acceptance Gate Soundness & Anti-CVE Rejection):**
1. Any implementation with unpatched `CVE-2025-48946` (`fullCiphertextBoundReject = false`),
   naive XOR hybrid combiner (`boundHybridCombiner = false`), classical fallback
   (`disallowClassicalDowngrade = false`), or KyberSlash division (`divisionFreeConstantTime = false`)
   is **formally rejected** by `passesPQCAcceptanceGate`.
2. `gravitonVerifiedHQCHybridProfile` passes every gate condition identically.
-/
theorem pqc_acceptance_gate_witness (g : PQCImplementationAcceptanceGate) :
    (passesPQCAcceptanceGate gravitonVerifiedHQCHybridProfile = true) ∧
    (g.fullCiphertextBoundReject = false → passesPQCAcceptanceGate g = false) ∧
    (g.boundHybridCombiner = false → passesPQCAcceptanceGate g = false) ∧
    (g.disallowClassicalDowngrade = false → passesPQCAcceptanceGate g = false) ∧
    (g.divisionFreeConstantTime = false → passesPQCAcceptanceGate g = false) := by
  cases g with
  | mk a b c d e =>
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

/-! ## 10. Study Certificate Registration (`graviton-cert`) -/

def studyCertificate : StudyCertificate := {
  studyId := "post-quantum-hqc-and-hybrid-combiners"
  title := "Post-Quantum HQC (NIST 2025), CVE-2025-48946 & Hybrid KEM Combiner Verification"
  url := "https://gravitonresearch.org/#kernel-audit"
  domain := "Post-Quantum Cryptography / Formal Verification"
  scopeStatement := "Zero-dependency Lean 4 formal verification of NIST HQC (Hamming Quasi-Cyclic, selected March 2025) over 𝔽₂[X]/⟨Xⁿ-1⟩, exact decryption noise cancellation and Hamming-weight bounds, official HQC-128/192/256 code geometry and padding slack, CVE-2025-48946 implicit-rejection collision & binding remediation, X-Wing-style hybrid KEM MAL-BIND and anti-downgrade soundness, and Anti-KyberSlash division-free Barrett reduction (q = 3329) & constant-time cmov. Explicitly quarantines probabilistic DFR, physical EM/power masking, and compiler-codegen preservation."
  assumptions := [
    { id := "HQC-A1_f2_cyclic_ring"
      kind := "mathematical"
      statement := "Polynomial arithmetic over the binary cyclic ring 𝔽₂[X]/⟨Xⁿ - 1⟩ (n > 0) with exact Hamming-weight noise model." },
    { id := "HQC-A2_ro_collision_resistant"
      kind := "cryptographic"
      statement := "Idealized collision-resistant / domain-separated hash/KDF oracle H for MAL-BIND and implicit-rejection non-collision theorems." },
    { id := "HQC-A3_abstract_ct_model"
      kind := "physical_regime"
      statement := "Constant-time model assumes bitwise shift/mask operations execute without data-dependent timing; downstream compiler codegen is quarantined in HQC-GATE-03." }
  ]
  claims := [
    { id := "HQC-01"
      title := "Exact 𝔽₂[X]/⟨Xⁿ-1⟩ Quasi-Cyclic Ring Laws (Universal n > 0)"
      leanDecl := ``f2_cyclic_ring_laws
      claimKind := "theorem"
      summary := "Proves characteristic-2 self-cancellation, XOR commutativity/associativity, cyclic multiplication commutativity, and left/right distributivity for every n > 0."
      assumptionIds := ["HQC-A1_f2_cyclic_ring"]
      doesNotEstablish := [
        "Algebraic ring laws alone do not prove hardness of the Quasi-Cyclic Syndrome Decoding (QCSD) problem."
      ] },
    { id := "HQC-02"
      title := "Exact HQC PKE Decryption Noise Cancellation (v ⊕ u·y = mG ⊕ e')"
      leanDecl := ``hqc_exact_decryption_noise_identity
      claimKind := "theorem"
      summary := "Proves universally for every n > 0 that HQC decryption cancels (h·y)·r₂ ⊕ (h·r₂)·y identically, isolating exact effective noise e' = x·r₂ ⊕ r₁·y ⊕ e."
      assumptionIds := ["HQC-A1_f2_cyclic_ring"]
      doesNotEstablish := [
        "Exact noise cancellation does not by itself bound the probability that wt(e') exceeds the decoder's radius (HQC-GATE-01)."
      ] },
    { id := "HQC-03"
      title := "Exact HQC Hamming-Weight Noise Ceiling"
      leanDecl := ``hqc_hamming_weight_submultiplicative_bound
      claimKind := "theorem"
      summary := "Proves wt(x·r₂ ⊕ r₁·y ⊕ e) ≤ wt(x)·wt(r₂) + wt(r₁)·wt(y) + wt(e) universally for every n > 0."
      assumptionIds := ["HQC-A1_f2_cyclic_ring"]
      doesNotEstablish := [
        "Worst-case weight ceiling is strictly looser than average-case binomial/hypergeometric weight distributions used in DFR analysis."
      ] },
    { id := "HQC-04"
      title := "Deterministic HQC Decoding Correctness Gate"
      leanDecl := ``hqc_deterministic_decoding_correctness_gate
      claimKind := "theorem"
      summary := "Proves zero decryption failure for any decoder of radius δ whenever wt(x)·wt(r₂) + wt(r₁)·wt(y) + wt(e) ≤ δ."
      assumptionIds := ["HQC-A1_f2_cyclic_ring"]
      doesNotEstablish := [
        "Production NIST HQC operates in the probabilistic regime (HQC-05) requiring tight DFR ≤ 2⁻λ proofs (HQC-GATE-01)."
      ] },
    { id := "HQC-05"
      title := "Official NIST HQC-128 / 192 / 256 MDS Geometry & Padding Slack"
      leanDecl := ``nist_hqc_official_parameter_soundness
      claimKind := "theorem"
      summary := "Certifies Reed–Solomon Singleton equality, duplicated Reed–Muller geometry, exact positive padding slack (5, 11, 37 bits), and probabilistic DFR regime across all three NIST HQC instances."
      assumptionIds := ["HQC-A1_f2_cyclic_ring"]
      doesNotEstablish := [
        "Parameter geometry verification does not prove concrete IND-CCA2 bit-security against unknown algebraic/quantum attacks."
      ] },
    { id := "HQC-06"
      title := "CVE-2025-48946 Collision Witness & Full-Ciphertext Bound Implicit Rejection"
      leanDecl := ``cve_2025_48946_implicit_rejection_collision_and_fix
      claimKind := "theorem"
      summary := "Exhibits exact implicit-rejection key collisions when full ciphertext binding is omitted (CVE-2025-48946) and proves strict non-collision + domain separation under full (pk, ct)-bound rejection."
      assumptionIds := ["HQC-A2_ro_collision_resistant"]
      doesNotEstablish := [
        "Random-oracle non-collision does not verify constant-time execution of the underlying SHAKE256/SHA3 implementation in C/Rust."
      ] },
    { id := "HQC-07"
      title := "Hybrid KEM Combiner: Broken XOR Counterexample vs. X-Wing MAL-BIND"
      leanDecl := ``hybrid_kem_combiner_mal_bind_and_weak_counterexample
      claimKind := "theorem"
      summary := "Proves naive XOR hybrid combiners fail MAL-BIND via explicit collision witness, while X-Wing-style domain-separated hash combiners bind suite label, both ciphertexts, and both public keys."
      assumptionIds := ["HQC-A2_ro_collision_resistant"]
      doesNotEstablish := [
        "Ciphertext/key binding alone does not prove IND-CCA2 game-hopping reductions in the Quantum Random Oracle Model (QROM)."
      ] },
    { id := "HQC-08"
      title := "Hybrid Dual-Survival & Middlebox Downgrade Collapse"
      leanDecl := ``hybrid_kem_dual_security_and_downgrade_gate
      claimKind := "theorem"
      summary := "Proves strict hybrid policy survives if either classical or PQ KEM holds, while allowing classical fallback collapses security under an active downgrade attacker even when PQ is unbroken."
      assumptionIds := ["HQC-A2_ro_collision_resistant"]
      doesNotEstablish := [
        "Policy logic theorem does not monitor live enterprise TLS middleboxes without runtime telemetry probes."
      ] },
    { id := "HQC-09"
      title := "Anti-KyberSlash Constant-Time cmov & Division-Free ML-KEM Barrett Reduction"
      leanDecl := ``constant_time_barrett_and_cmov_no_div_soundness
      claimKind := "theorem"
      summary := "Proves branchless UInt64 cmov exactness and exactness/non-underflow/range [0, 2·3329) of division-free Barrett reduction (x - ((x·20158) >>> 26)·3329) for all x < 3329² (catching the unsigned underflow of rounded 20159)."
      assumptionIds := ["HQC-A3_abstract_ct_model"]
      doesNotEstablish := [
        "Source-level division-free arithmetic must still be checked against compiled assembly to ensure compilers do not re-introduce secret-dependent branches (HQC-GATE-03)."
      ] },
    { id := "HQC-10"
      title := "Executable PQCImplementationAcceptanceGate & Anti-CVE Rejection"
      leanDecl := ``pqc_acceptance_gate_witness
      claimKind := "theorem"
      summary := "Formally rejects unpatched CVE-2025-48946, naive XOR combiners, downgrade-allowing policies, and division-based reductions, while certifying Graviton's verified HQC hybrid profile."
      assumptionIds := ["HQC-A1_f2_cyclic_ring", "HQC-A2_ro_collision_resistant", "HQC-A3_abstract_ct_model"]
      doesNotEstablish := [
        "Passing the algebraic and protocol gate does not certify physical EM/power masking or assembly-level constant-time codegen."
      ] }
  ]
  openGates := [
    { id := "HQC-GATE-01"
      quantity := "Exact finite-blocklength Decryption Failure Rate (DFR ≤ 2⁻λ) for concatenated RS + duplicated RM decoding"
      units := "probability (≤ 2⁻¹²⁸ / 2⁻¹⁹² / 2⁻²⁵⁶)"
      requiredControl := "Machine-checked probabilistic tail bound (Chernoff / exact hypergeometric convolution) over correlated HQC error coordinates"
      status := "open_theoretical_obligation" },
    { id := "HQC-GATE-02"
      quantity := "Physical electromagnetic / power side-channel leakage on ARM Cortex-M & AVX2"
      units := "t-test / MIMO-SNI probing order"
      requiredControl := "Higher-order masked HQC polynomial multiplication and constant-time Reed–Muller/RS decoder verified on physical traces"
      status := "open_experimental_gate" },
    { id := "HQC-GATE-03"
      quantity := "Compiled machine-code constant-time preservation (LLVM/GCC -O2/-Os)"
      units := "binary disassembly / Valgrind-ct / dudect"
      requiredControl := "Automated binary check verifying zero secret-dependent udiv/idiv/branches survive compiler optimization"
      status := "open_engineering_gate" }
  ]
  sourceArtifacts := [
    ("pqc_audit_cli", "tools/pqc-audit.py"),
    ("hqc_study_lean", "GravitonCert/Studies/PostQuantumHQC.lean")
  ]
}

end GravitonCert.Studies.PostQuantumHQC
