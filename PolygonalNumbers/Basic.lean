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
def IsnPolygonal (m : ℤ) (a : ℚ) := ∃ (k : ℤ), (((m : ℚ) - 2) / 2) * (k * (k - 1)) + k = a
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

-- instance : HAdd (Polygonal n) (Polygonal n) ℚ where
--   hAdd a b := a.val + b.val

-- instance : HAdd (Polygonal n) ℤ ℚ where
--   hAdd a b := a.val + b

-- instance : HAdd (Polygonal n) ℚ ℚ where
--   hAdd a b := a.val + b

-- instance : HAdd ℚ (Polygonal n) ℚ where
--   hAdd a b := a + b.val

-- instance : HAdd (Polygonal n) ℚ ℚ where
--   hAdd a b := a.val + b

-- instance : HAdd (Polygonal n) (Polygonal n) ℚ where
--   hAdd a b := a.val + b.val

-- instance : HAdd ℤ (Polygonal n) ℚ where
--   hAdd a b := a + b.val

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

/-
Proof omitted as it is purely algebraic manipulation, and in the interest of time
-/
lemma CauchyLemma (a : ℚ) (b : ℤ) (aOdd : Odd a) (bOdd : Odd b) (h₁ : b^2 < 4*a) (h₂ : 3*a < b^2 + 2*b + 4) : ∃ s t v u : ℕ, (a = s^2 + t^2 + v^2 + u^2) ∧ (b = s + t + v + u) := by
  sorry


/-
  ==================== Theorem I for Polygonal Numbers ====================
-/
/--
  n : Number we want to write as the sum
  m : Polygonal order
-/
theorem ThmOne (m : ℕ) (n : ℕ) (nmpos : n ≥ 1) (mb : m ≥ 3) (nb : n ≥ 120*m) : ∃ (S : Multiset (Polygonal (m+2))),
      (sumPolyToInt (m+2) S = n)                  -- Sum = m
    ∧ (Multiset.card S ≤ 5)               -- With at most m+1 elements (as 0 is always a polygonal number, we can always "fill" the multiset with 0's to get the correct cardinality), and so we will only look at the set without the zeros (which, we assert has cardinality at most 4)
      := by

  have hIntervalLength : ((2 / 3) + √(8 * (n / m) - 8)) - (0.5 + √(6 * (n/m) - 3)) ≥ 4 := by
    sorry

  have hExistsOddPair (ep₁ ep₂ : ℝ) (hfour : ep₂ - ep₁ ≥ 4 ) : ∃ (b₁ b₂ : ℤ), (Odd b₁) ∧ (Odd b₂) ∧ (b₁ > ep₁) ∧ (b₂ < ep₂) ∧ (b₂ = b₁ + 2) := by
    have heiorarb (a : ℤ) : (Odd a) ∨ (Odd (a + 1)) := by
      have hoddornot : (Odd a) ∨ ¬ Odd (a) := Decidable.em (Odd a)

      rcases (hoddornot) with hodd₁ | hnotodd₁
      . left; exact hodd₁
      . right; rw [Int.not_odd_iff_even] at hnotodd₁; apply Even.add_one at hnotodd₁; exact hnotodd₁

    have ep₁inornot : ep₁ < ⌈ ep₁ ⌉ ∨ ep₁ = ⌈ ep₁ ⌉  := by
      refine lt_or_eq_of_le ?_
      exact Int.le_ceil ep₁

    rcases (heiorarb ⌈ ep₁ ⌉ ) with epodd | ep1odd
    . use ⌈ ep₁ ⌉, ⌈ ep₁ ⌉ + 2
      and_intros
      . assumption
      . contrapose epodd
        simp
        simp at epodd
        have epodd_two : ⌈ ep₁ ⌉ + 2 + -2 = ⌈ ep₁ ⌉ := by simp
        rw [← epodd_two]
        apply Even.add epodd even_neg_two
      . simp
        sorry
      . calc
          _ ≤ (⌈ ep₁ ⌉ : ℝ) + 2 := by simp
          _ < ep₁ + 1 + 2 := by
            simp
            apply Int.ceil_lt_add_one (ep₁)
          _ ≤ ep₁ + 4 := by linarith
          _ ≤ ep₂ := by linarith
      . rfl

    . use ⌈ ep₁ ⌉ + 1, ⌈ ep₁ ⌉ + 3
      and_intros
      . assumption
      . contrapose ep1odd
        simp
        simp at ep1odd
        have ep1odd_two : ⌈ ep₁ ⌉ + 3 + -2 = ⌈ ep₁ ⌉ + 1 := by linarith
        rw [← ep1odd_two]
        apply Even.add ep1odd even_neg_two
      . simp
        sorry
      . simp
        calc
          _ ≤ (⌈ ep₁ ⌉ : ℝ) + 3 := by simp
          _ < ep₁ + 1 + 3 := by
            simp
            apply Int.ceil_lt_add_one (ep₁)
          _ ≤ ep₁ + 4 := by linarith
          _ ≤ ep₂ := by linarith
      . ring

  let ⟨ b₁, b₂, hbo₁, hbo₂, hb₁, hb₂, hb₁b₂ ⟩ := hExistsOddPair (0.5 + √(6 * (n/m) - 3)) ((2 / 3) + √(8 * (n / m) - 8)) hIntervalLength


  have h₁ : ∃ r ∈ List.range (((m-3) + 1 : ℕ)), ∃ b ∈ [b₁, b₂], n ≡ (b + r : ℤ) [ZMOD m] := by
    simp
    -- SORRY
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

  let a : ℚ := 2 * ((n - b - r) / m) + b

  have hao : Odd a := by
    have hae₁ : Even (2 * (((n : ℚ) - b - ↑r) / ↑m)) := by
      exact even_two_mul (((n : ℚ) - b - ↑r) / ↑m)
    dsimp [a]
    refine Even.add_odd hae₁ (Odd.intCast hbo)

  /-
    Change to `r ≤ m-3` or whatever
  -/
  have hr : r = 0 ∨ r = 1:= by
    sorry

  /-
    Equation (5)
  -/
  have h₂ : n = (m / 2) * (a - b) + b + r := by
    dsimp [a]
    simp
    rw [← mul_assoc, mul_comm]
    simp
    -- SORRY: Again, this is a simple case of `x/n*n=x`, but for some reason, I can not manipulate this one to get the correct types.
    -- The result follows directly after this step
    -- rw [div_mul_cancel (n - b - r) m]
    -- rw [div_mul_cancel (n - b - r) m]
    sorry

  have h₇ : b^2 < 4 * a ∧ 3 * a < b^2 + 2 * b + 4 := by
    constructor
    . dsimp [a]
      sorry
    . dsimp [a]
      sorry

  let ⟨ s, t, u, v, hstuv ⟩ := CauchyLemma a b hao hbo h₇.left h₇.right
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

  /- `r` (being `0` or `1`) is polygonal -/
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

  /- The sum of the numbers is `n` -/
  have corsum : sl + tl + ul + vl + r = n := by
    dsimp [sl, tl, ul, vl]
    rw [h₂, hstuv.left, hstuv.right]
    simp
    ring

  let S : Multiset (Polygonal (m+2)) :={⟨ sl, ps ⟩, ⟨ tl, pt ⟩, ⟨ ul, pu ⟩, ⟨ vl, pv ⟩, ⟨ r, hrp ⟩}

  use S
  constructor
  . simp [sumPolyToInt] -- Proof it adds to `n`
    simp [S]
    simp [foldrfun]
    rw [← add_assoc, ← add_assoc, ← add_assoc]
    exact corsum
  . simp [S] -- Proof it has at most 5 elements
