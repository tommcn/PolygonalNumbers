/-
  Proof of Cauchy's Polygonal Number Theorem:

  Adapted from: https://www.ams.org/journals/proc/1987-099-01/S0002-9939-1987-0866422-3/S0002-9939-1987-0866422-3.pdf

  Also Proved in Isabelle: https://www.isa-afp.org/entries/Polygonal_Number_Theorem.html#

  Lean (version 4.15.0-rc1, arm64-apple-darwin23.6.0, commit ffac974dba79, Release)

  Tomas McNamer
-/

import Mathlib.Tactic
import Mathlib.Data.Set.Defs

/-
  ==================== Support for Polygonal Numbers ====================
-/

def IsTriangular (n : ℚ) := ∃ (k : ℤ), (k * (k + 1)) = 2 * n
def IsnPolygonal (m : ℤ) (n : ℚ) := ∃ (k : ℤ), (((m : ℚ) - 2) / 2) * (k * (k - 1)) + k = n
def IsnPolygonal' (m : ℤ) (a : ℚ) := ∃ (k : ℤ), (((m : ℚ) - 2) / 2) * (k^2 - k) + k = a


def Triangular := Subtype (fun (n : ℤ) ↦ IsTriangular n)
def Polygonal (n : ℤ) := Subtype (fun (m : ℚ) ↦ IsnPolygonal n m)

instance : BEq (Polygonal n) where
  beq a b := if (a.val == b.val)
             then true
             else false

instance : LawfulBEq (Polygonal n) where
  rfl := by
    intro a
    rw [BEq.beq]
    dsimp [instBEqPolygonal]
    simp

  eq_of_beq := by
    intro a b
    intro h₁
    rw [BEq.beq] at h₁
    dsimp [instBEqPolygonal] at h₁
    simp at h₁
    rw [a.eq_iff]
    exact h₁

instance : DecidableEq (Polygonal n) :=
  fun a b =>
    if h : a.val = b.val then
      isTrue (by rw [a.eq_iff]; exact h)
    else
      isFalse (by rw [a.eq_iff]; exact h)

#check Polygonal

def foldrfun (n : ℤ) := fun (x1 : Polygonal n) (x2 : ℚ) ↦ x1.val + x2

instance : LeftCommutative (foldrfun n : Polygonal n → ℚ → ℚ) where
  left_comm := by
    intro a b c
    simp [foldrfun]
    ring

/--
  Sum of a multiset of polygonal numbers of same order `n` (i.e., rational
  numbers) into a rational number
-/
def sumPolyToInt (n : ℤ) (S : Multiset (Polygonal n)) : ℚ := S.foldr (foldrfun n) 0


lemma revenk (r : ℤ) : ∃ k : ℤ, r * (r - 1) = 2 * k := by
  have h : Even (r * (r - 1)) := by
    apply Int.even_mul_pred_self
  dsimp [Even] at h
  let ⟨ k, hk ⟩ := h
  use k
  rw [hk]
  ring


/--
  Both conditions `IsnPolygonal` and `IsnPolygonal'` are equivalent.
-/
lemma PolyEquiv: IsnPolygonal = IsnPolygonal' := by
  have kfactq (k : ℚ) : k * (k - 1) = k^2 - k := by
    ring

  unfold IsnPolygonal IsnPolygonal'
  funext m a
  apply propext
  constructor
  . intro h
    let ⟨ k, hk ⟩ := h
    use k
    rw [kfactq k] at hk
    exact hk

  . intro h
    let ⟨ k, hk ⟩ := h
    use k
    rw [kfactq k]
    exact hk

/--
  `Polygonal` numbers, despite being a subtype of `ℚ`, are equal to their integer part.
-/
lemma PolygonalInteger (n : ℤ) (a : Polygonal n) : a.val = ⌊ a.val ⌋ := by
  dsimp [Polygonal, IsnPolygonal] at a
  let ⟨ k, hk ⟩ := a
  let ⟨ r, hr ⟩ := hk
  simp

  rw [← hr]
  simp

  let ⟨ e, he ⟩ := revenk r
  let e' := (e : ℚ)

  have tworatint : (2 : ℚ) = (2 : ℤ) := rfl
  have oneratint : (1 : ℚ) = (1 : ℤ) := rfl


  have he' : (r : ℚ) * ((r : ℚ) - 1) = 2 * e' := by
    rw [oneratint]
    rw [← Int.cast_sub r 1]
    rw [← Int.cast_mul r (r - 1)]
    rw [he]
    simp

  rw [he']
  have htwoassoc : (n - 2) / 2 * (2 * e') = (n - 2) * e' := by
    ring
  rw [htwoassoc]
  dsimp [e']

  rw [tworatint]
  rw [← Int.cast_sub n 2]
  rw [← Int.cast_mul (n - 2)]
  exact rfl

instance : HAdd Triangular Triangular ℤ where
  hAdd a b :=  a.val + b.val

instance : HAdd Triangular ℤ ℤ where
  hAdd a b := a.val + b

instance : HAdd ℤ Triangular ℤ where
  hAdd a b := a + b.val



/-
  ==================== Examples for Polygonal Numbers ====================
-/

example : IsTriangular 6 := by
  unfold IsTriangular
  use 3
  simp
  linarith

example : IsnPolygonal 3 6 := by
  unfold IsnPolygonal
  use 3
  linarith

/--
  A `Polygonal` number of order $3$ is triangular.
-/
lemma PolyThreeIsTriangular : IsnPolygonal 3 = IsTriangular := by
  unfold IsnPolygonal
  unfold IsTriangular
  simp
  funext a
  apply propext
  constructor
  . intro h
    let ⟨ k, hk ⟩ := h
    rw [← hk]
    ring_nf
    use k
  . intro h
    let ⟨ k, hk ⟩ := h
    ring_nf
    use k
    rw [← add_mul]
    simp
    have honetwo (a b : ℚ) : 2 * a = 2 * b → a = b := by
      intro hone
      apply mul_left_cancel₀ two_ne_zero hone

    apply honetwo
    rw [← hk]
    ring

/-
  ==================== Cauchy Lemma for Polygonal Numbers ====================
-/
-- https://proofwiki.org/wiki/Integer_as_Sum_of_Three_Odd_Squares
lemma IntegerSumThreeOddSquares (r : ℤ) (h : r ≥ 0) : r ≡ 3 [ZMOD 8] ↔ ∃ s t u : ℤ,
                                  r = s^2 + t^2 + u^2
                                ∧ Odd (s^2)
                                ∧ Odd (t^2)
                                ∧ Odd (u^2) := by
  sorry

-- https://proofwiki.org/wiki/Integer_is_Sum_of_Three_Triangular_Numbers
lemma GaussEureka (n : ℤ) (h : n ≥ 0) : ∃ s t v : Triangular, n = s + t + v := by
  sorry

lemma CauchyLemma (a : ℕ) (b : ℕ) (aOdd : Odd a) (bOdd : Odd b) (h₁ : b^2 < 4*a) (h₂ : 3*a < b^2 + 2*b + 4) : ∃ s t v u : ℕ, (a = s^2 + t^2 + v^2 + u^2) ∧ (b = s + t + v + u) := by
  sorry

/-
  ==================== Various Lemmas for Polygonal Numbers ====================
-/

lemma interval_length (n m : ℕ) (h : n ≥ 120 * m) : ((2 / 3) + √(8 * (n / m) - 8)) - (1 / 2 + √(6 * (n/m) - 3)) > 4 := by
  sorry

lemma bound_positive :  1 / 2 + √(6 * (↑n / ↑m) - 3) > 0 := by
  sorry

lemma odd_pair_four_interval (ep₁ ep₂ : ℝ) (h : ep₂ - ep₁ > 4 ) (hpo : ep₁ > 0) : ∃ (b₁ b₂ : ℕ),
      (Odd b₁)
    ∧ (Odd b₂)
    ∧ (b₁ > ep₁)
    ∧ (b₂ < ep₂)
    ∧ (b₂ = b₁ + 2) := by
    have heiorarb (a : ℤ) : (Odd a) ∨ (Odd (a + 1)) := by
      have hoddornot : (Odd a) ∨ ¬ Odd (a) := Decidable.em (Odd a)

      rcases (hoddornot) with hodd₁ | hnotodd₁
      . left; exact hodd₁
      . right; rw [Int.not_odd_iff_even] at hnotodd₁; apply Even.add_one at hnotodd₁; exact hnotodd₁

    have hep₁inornot : ep₁ < ⌈ ep₁ ⌉ ∨ ep₁ = ⌈ ep₁ ⌉  := by
      refine lt_or_eq_of_le ?_
      exact Int.le_ceil ep₁

    have hep₁ : ⌈ep₁⌉ = ⌈ep₁⌉.natAbs := by
      refine Eq.symm (Int.natAbs_of_nonneg ?_)
      refine Int.ceil_nonneg ?_
      exact le_of_lt hpo

    have hep₁' : (⌈ep₁⌉ : ℝ) = ⌈ep₁⌉.natAbs := by
      exact congrArg Int.cast hep₁

    rcases (heiorarb ⌈ ep₁ ⌉) with epodd | ep1odd
    <;> rcases hep₁inornot with ep₁lt | ep₁eq
    . use ⌈ ep₁ ⌉.natAbs, ⌈ ep₁ ⌉.natAbs + 2
      and_intros
      . simp
        simp at hep₁
        assumption
      . contrapose epodd
        simp
        simp at epodd
        have epodd_two : ⌈ ep₁ ⌉ + 2 + -2 = ⌈ ep₁ ⌉ := by simp
        rw [← epodd_two]
        simp
        rw [hep₁]
        refine (Int.even_coe_nat ⌈ep₁⌉.natAbs).mpr ?_
        -- refine Int.natAbs_even.mpr ?_

        have even_add_two (a : ℕ) : Even (a + 2) → Even (a) := by
          dsimp [Even]
          intro heven
          let ⟨ r, hr ⟩ := heven
          use r - 1
          sorry
          -- apply?



        apply even_add_two ⌈ ep₁ ⌉.natAbs epodd
        -- assumption

        -- apply Even.add epodd even_neg_two

      . simp
        exact lt_of_lt_of_eq ep₁lt (congrArg Int.cast hep₁)
      . calc
          _ ≤ (⌈ ep₁ ⌉ : ℝ) + 2 := by simp; exact Eq.ge (congrArg Int.cast hep₁)
          _ < ep₁ + 1 + 2 := by
            simp
            apply Int.ceil_lt_add_one (ep₁)
          _ ≤ ep₁ + 4 := by linarith
          _ ≤ ep₂ := by linarith
      . rfl
    . use ⌈ ep₁ ⌉.natAbs + 2, ⌈ ep₁ ⌉.natAbs + 4
      and_intros
      . refine Nat.odd_add.mpr ?_; simp; assumption
      . refine Nat.odd_add.mpr ?_
        have heven4 : Even (4 : ℕ) := by dsimp [Even]; use 2;
        constructor <;> intro _
        . exact heven4
        . exact Odd.natAbs epodd
      . simp
        sorry
      . rw [Nat.cast_add]; simp; rw [← hep₁', ← ep₁eq]; linarith
      . ring
    . use ⌈ ep₁ ⌉.natAbs + 1, ⌈ ep₁ ⌉.natAbs + 3
      and_intros
      . rw [hep₁] at ep1odd
        exact (Int.odd_coe_nat (⌈ep₁⌉.natAbs + 1)).mp ep1odd
      . contrapose ep1odd
        simp
        simp at ep1odd
        have ep1odd_two : ⌈ ep₁ ⌉ + 3 + -2 = ⌈ ep₁ ⌉ + 1 := by linarith
        rw [← ep1odd_two]

        apply Even.add ?_ ?_
        . rw [hep₁]
          exact Int.natAbs_even.mp ep1odd
        . simp
      . simp
        linarith
      . simp
        calc
          _ ≤ (⌈ ep₁ ⌉ : ℝ) + 3 := le_of_eq (congrFun (congrArg HAdd.hAdd (id (Eq.symm hep₁'))) 3)
          _ < ep₁ + 1 + 3 := by
            simp
            apply Int.ceil_lt_add_one (ep₁)
          _ ≤ ep₁ + 4 := by linarith
          _ ≤ ep₂ := by linarith
      . ring
    . use ⌈ ep₁ ⌉.natAbs + 1, ⌈ ep₁ ⌉.natAbs + 3
      and_intros
      . refine Even.add_one ?_; sorry
      . dsimp [Odd]
        dsimp [Odd] at ep1odd
        let ⟨ k, hk ⟩ := ep1odd

        use (k + 1).natAbs
        simp
        sorry
      . simp
        linarith
      . simp
        linarith
      . ring


-- Lemma 1.11 (p. 42)
lemma cauchy_setup (m N : ℕ)
                   (hm : m ≥ 3)
                   (hnineq : N ≥ 2 * m)
                   (a b r : ℕ)
                   (hr : r < m)
                   (hneq : N = ((m : ℚ) / 2)*(a - b) + b + r)
    : (1 / 2 + √((6 * N) / m - 3)) < b
        → b < (2 / 3 + √(8 *( N / m) - 8))
      → b^2 < 4*a ∧ 3*a < b^2 + 2*b + 4 := by
  sorry

/-
  ==================== Theorem I for Polygonal Numbers ====================
-/
/--
  # Theorem I
  Let m ≥ 3 and n ≥ 120*m. Then n is the sum of m + 1 polygonal numbers of
  order m + 2, at most four of which are different from 0 or `1`
-/
theorem CauchyPolygonalNumberTheorem (m : ℕ) (n : ℕ) (nmpos : n ≥ 1) (mb : m ≥ 3) (nb : n ≥ 120*m) : ∃ (S : Multiset (Polygonal (m+2))),
      (sumPolyToInt (m+2) S = n)                  -- Sum = n
    ∧ (Multiset.card S ≤ m+1)
      := by
  have hmqgeq3 : (m : ℚ) ≥ 3 := by
    exact Nat.ofNat_le_cast.mpr mb
  have hmgt0 : (m : ℚ) > 0 := by
    exact gt_of_ge_of_gt hmqgeq3 rfl
  have hmnot0 : (m : ℚ) ≠ 0 := by
    linarith

  let ⟨ b₁,
        b₂,
        hbo₁,
        hbo₂,
        hb₁,
        hb₂,
        hb₁b₂
      ⟩
      := odd_pair_four_interval
          (1/2 + √(6 * (n/m) - 3))
          ((2 / 3) + √(8 * (n / m) - 8))
          (interval_length n m nb)
          bound_positive


  have h₁ : ∃ r ∈ List.range (((m-3) + 1 : ℕ)), ∃ b ∈ [b₁, b₂], n ≡ (b + r) [MOD m] := by
    simp
    -- Proof by pigeonhole principle, the set of numbers `b+r` as defined above is larger than the set of residues mod m
    sorry

  let ⟨ r, hr ⟩ := h₁
  let ⟨ b, hb ⟩ := hr.right

  have hb₁ohb₂o : b = b₁ ∨ b = b₂ := by
    rw [← List.mem_pair]
    exact hb.left

  have hbo : Odd b := by
    rcases hb₁ohb₂o with hb₁ | hb₂
    . rw [hb₁]
      exact hbo₁
    . rw [hb₂]
      exact hbo₂

  have hbub : b < ((2 / 3) + √(8 * (n / m) - 8)) := by
    have hbleqb₂ : b ≤ (b₂ : ℝ) := by
      rcases hb₁ohb₂o with hb₁ | hb₂
      . rw [hb₁]
        rw [hb₁b₂]
        refine Int.cast_le.mpr ?_
        exact Int.le.intro 2 rfl
      . rw [hb₂]
    calc
      b ≤ (b₂ : ℝ) := hbleqb₂
      _ < ((2 / 3) + √(8 * (n / m) - 8)) := hb₂

  have hblb : ((1 / 2) + √(6 * (n / m) - 3)) < b := by
    have hbleqb₁ : b ≥ (b₁ : ℝ) := by
      rcases hb₁ohb₂o with hb₁ | hb₂
      . rw [hb₁]
      . rw [hb₂]
        rw [hb₁b₂]
        refine Int.cast_le.mpr ?_
        exact Int.le.intro 2 rfl
    calc
      ((1 / 2) + √(6 * (n / m) - 3)) < b₁ := by apply hb₁
      _ ≤ b := hbleqb₁

  let a : ℕ := 2 * ((n - b - r) / m) + b

  have hao : Odd a := by
    have hae₁ : Even (2 * ((n - b - ↑r) / ↑m)) := by
      exact even_two_mul ((n - b - ↑r) / ↑m)
    dsimp [a]
    exact Even.add_odd hae₁ hbo


  let cauchy_setset_up := cauchy_setup m n mb sorry a b r sorry sorry
  let ⟨ clemma_left, clemma_right ⟩ := cauchy_setset_up sorry hbub

  let ⟨ s, t, u, v, hstuv ⟩ := CauchyLemma a b hao hbo clemma_left clemma_right
  let sl : ℚ := (m / 2) * (s^2 - s) + s
  let tl : ℚ := (m / 2) * (t^2 - t) + t
  let ul : ℚ := (m / 2) * (u^2 - u) + u
  let vl : ℚ := (m / 2) * (v^2 - v) + v

  /- `s`, `t`, `u`, `v` are polygonal -/
  have ps : IsnPolygonal (m+2) sl := by
    rw [PolyEquiv]
    unfold IsnPolygonal'
    use s
    simp

  have pt : IsnPolygonal (m+2) tl := by
    rw [PolyEquiv]
    unfold IsnPolygonal'
    use t
    simp

  have pu : IsnPolygonal (m+2) ul := by
    rw [PolyEquiv]
    unfold IsnPolygonal'
    use u
    simp

  have pv : IsnPolygonal (m+2) vl := by
    rw [PolyEquiv]
    unfold IsnPolygonal'
    use v
    simp

  /-
    Change to `r ≤ m-3` or whatever
  -/
  let poly1 : Polygonal (m+2) := ⟨ 1, sorry ⟩
  have hr : r = 0 ∨ r = 1:= by
    sorry
  -- let rArr := Multiset.ofList (mkArray r poly1)
  have hrp : IsnPolygonal (m+2) r := by
    rcases hr with hr0 | hr1
    . unfold IsnPolygonal
      rw [hr0]
      use 0
      simp
    . unfold IsnPolygonal
      rw [hr1]
      use 1
      simp


  /-
    Equation (5)
  -/
  have h₂ : (n : ℚ) = ((m : ℚ) / 2) * ((a : ℚ) - b) + b + r := by
    dsimp [a]
    simp
    rw [← mul_assoc, mul_comm]
    simp
    -- apply?
    sorry
    -- rw [← hnbrzq] at hg
    -- simp at hg
    -- rw [← hg.left]
    -- -- rw [div_mul_cancel₀ ((n : ℚ) - (b) - r) hmnot0]
    -- -- ring
    -- sorry

  /- The sum of the numbers is `n` -/
  have corsum : sl + tl + ul + vl + r = n := by
    dsimp [sl, tl, ul, vl]
    rw [h₂, hstuv.left, hstuv.right]
    simp
    ring

  let S : Multiset (Polygonal (m+2)) := {⟨ sl, ps ⟩, ⟨ tl, pt ⟩, ⟨ ul, pu ⟩, ⟨ vl, pv ⟩, ⟨ r, hrp ⟩}

  use S
  constructor
  . -- Proof it adds to `n`
    simp [sumPolyToInt]
    simp [S]
    simp [foldrfun]
    rw [← add_assoc, ← add_assoc, ← add_assoc]
    exact corsum
  . -- Proof it has at most 5 elements
    simp [S]
    sorry
