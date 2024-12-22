/-
  Proof of Cauchy's Polygonal Number Theorem:

  Adapted from: https://www.ams.org/journals/proc/1987-099-01/S0002-9939-1987-0866422-3/S0002-9939-1987-0866422-3.pdf

  Also Proved in Isabelle: https://www.isa-afp.org/entries/Polygonal_Number_Theorem.html#

  Lean (version 4.15.0-rc1, arm64-apple-darwin23.6.0, commit ffac974dba79, Release)

  Tomas McNamer

  ---

  The result is stated as

  > Every non-negative integer is written as the sum of m+2 polygonal number of order m+2 for m ≥ 3

  In order to formalize the result, we introduce a subtype of ℕ which contains all numbers which are polygonal of order n, for n ∈ ℕ

  We then introduce Finsets of those subtypes, which we can sum (over ↑Polygonal = ℕ) and verify their (finite) cardinality.

  For now, using sums such of Polygonal numbers using n.val is fine enough, but I might want to define addition and such operations on Polygonal numbers (which might be hard as they are not closed under addition).

  Another difficulty will be the existence of the Finset, without necessarily constructing the Finset explicitly
-/

import Mathlib.Tactic
import Mathlib.Data.Set.Defs

/-
  ==================== Support for Polygonal Numbers ====================
-/


/-
Note that we define Polygonal/Triangular Numbers as subtypes of ℚ, instead of the more natural ℕ, as we need to perform division on them (which does not behave as expected on ℕ or ℤ).

However, it is easy to show that the numbers we are interested in are always integers, `m` and `k` are both integers (thus, while not formally proved, `a` will have a denominator of `1`, making it an integer).
-/
def IsTriangular (n : ℚ) := ∃ (k : ℤ), (k * (k + 1)) = 2 * n
def IsnPolygonal (m : ℤ) (a : ℚ) := ∃ (k : ℤ), (((m : ℚ) - 2) / 2) * (k * (k - 1)) + k = a
def IsnPolygonal' (m : ℤ) (a : ℚ) := ∃ (k : ℤ), (((m : ℚ) - 2) / 2) * (k^2 - k) + k = a


def Triangular := Subtype (fun (n : ℤ) ↦ IsTriangular n)
def Polygonal (n : ℤ) := Subtype (fun (m : ℚ) ↦ IsnPolygonal n m)


/-
The following instances define equality and addition for Polygonal numbers, which will be useful for the proof.

We do not use all of them, and some instances are remnants of previous attempts at the proof, and they are left here as a testament to the work done.

The same is true for `BEq`, `LawfulBEq`, and `DecidableEq` instances, which were used in the proof when I was trying to define a `Finset` of `Polygonal` numbers, which required equality to be defined on them, as `Finset`s do not allow for duplicates.
-/

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

instance : HAdd (Polygonal n) (Polygonal n) ℚ where
  hAdd a b := a.val + b.val

instance : HAdd (Polygonal n) ℤ ℚ where
  hAdd a b := a.val + b

instance : HAdd (Polygonal n) ℚ ℚ where
  hAdd a b := a.val + b

instance : HAdd ℚ (Polygonal n) ℚ where
  hAdd a b := a + b.val

instance : HAdd (Polygonal n) ℚ ℚ where
  hAdd a b := a.val + b

instance : HAdd (Polygonal n) (Polygonal n) ℚ where
  hAdd a b := a.val + b.val

instance : HAdd ℤ (Polygonal n) ℚ where
  hAdd a b := a + b.val


/-
Defining the function which sums all numbers in the `Multiset`, as a `foldr` function, which is (provably) left commutative.
-/
def foldrfun (n : ℤ) := fun (x1 : Polygonal n) (x2 : ℚ) ↦ (x1.val : ℚ) + (x2 : ℚ)

instance : LeftCommutative (foldrfun n : Polygonal n → ℚ → ℚ) where
  left_comm := by
    intro a b c
    simp [foldrfun]
    ring

def sumPolyToInt (n : ℤ) (S : Multiset (Polygonal n)) : ℚ := S.foldr (foldrfun n) 0

lemma kfactq (k : ℚ) : k * (k - 1) = k^2 - k := by
  ring

lemma PolyEquiv: IsnPolygonal = IsnPolygonal' := by
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
    ring_nf
    sorry

  /-
    Given two endpoints whose difference is at least 4, we can find two odd integers between them which differ by 2

    This is a long proof, which is seems odd to me
  -/
  have hExistsOddPair (ep₁ ep₂ : ℝ) (hfour : ep₂ - ep₁ ≥ 4 ) : ∃ (b₁ b₂ : ℤ), (Odd b₁) ∧ (Odd b₂) ∧ (b₁ ≥ ep₁) ∧ (b₂ ≤ ep₂) ∧ (b₂ = b₁ + 2) := by
    /-
      Given two consecutive integers, one of them is odd
    -/
    have heiorarb (a : ℤ) : (Odd a) ∨ (Odd (a + 1)) := by
      have hoddornot : (Odd a) ∨ ¬ Odd (a) := Decidable.em (Odd a)

      rcases (hoddornot) with hodd₁ | hnotodd₁
      . left; exact hodd₁
      . right; rw [Int.not_odd_iff_even] at hnotodd₁; apply Even.add_one at hnotodd₁; exact hnotodd₁

    /-
      And so we prove that the ceiling of the first endpoint (or its successor) is odd, and that the following odd number is at most the second endpoint
    -/
    rcases (heiorarb ⌈ ep₁ ⌉) with epodd | ep1odd
    . use ⌈ ep₁ ⌉, ⌈ ep₁ ⌉ + 2
      constructor
      . assumption
      . constructor
        . contrapose epodd
          simp
          simp at epodd
          have epodd_two : ⌈ ep₁ ⌉ + 2 + -2 = ⌈ ep₁ ⌉ := by simp
          rw [← epodd_two]
          apply Even.add epodd even_neg_two
        . constructor
          . apply Int.le_ceil
          . constructor
            . calc
                _ ≤ (⌈ ep₁ ⌉ : ℝ) + 2 := by simp
                _ ≤ ep₁ + 1 + 2 := by
                  simp
                  -- SORRY: ↑⌈ep₁⌉ ≤ ep₁ + 1
                  -- There is the following lemma in mathlib:
                  -- apply Int.ceil_lt_add_one (ep₁)
                  -- but it is a strict inequality, and I using it breaks the `calc` tactic
                  sorry
                _ ≤ ep₁ + 4 := by linarith
                _ ≤ ep₂ := by linarith
            . rfl

    . use ⌈ ep₁ ⌉ + 1, ⌈ ep₁ ⌉ + 3
      constructor
      . assumption
      . constructor
        . contrapose ep1odd
          simp
          simp at ep1odd
          have ep1odd_two : ⌈ ep₁ ⌉ + 3 + -2 = ⌈ ep₁ ⌉ + 1 := by linarith
          rw [← ep1odd_two]
          apply Even.add ep1odd even_neg_two
        . constructor
          . simp
            -- SORRY: ↑(⌈ep₁⌉ + 1) ≥ ep₁
            -- See above
            sorry
          . constructor
            . simp
              calc
                _ ≤ (⌈ ep₁ ⌉ : ℝ) + 3 := by simp
                _ ≤ ep₁ + 1 + 3 := by
                  simp
                  -- SORRY: ep₁ ≤ ↑⌈ep₁⌉ + 1
                  -- See above
                  sorry
                _ ≤ ep₁ + 4 := by linarith
                _ ≤ ep₂ := by linarith
            . ring

  /-
    Given that the interval is at least 4, we can find two (consecutive) odd numbers in the interval
  -/
  let ⟨ b₁, b₂, hbo₁, hbo₂, hb₁, hb₂, hb₁b₂ ⟩ := hExistsOddPair (0.5 + √(6 * (n/m) - 3)) ((2 / 3) + √(8 * (n / m) - 8)) hIntervalLength


  have h₁ : ∃ r ∈ List.range (((m-3) + 1 : ℕ)), ∃ b ∈ [b₁, b₂], n ≡ (b + r : ℤ) [ZMOD m] := by
    simp
    -- SORRY
    -- Proof by pigeonhole principle, the set of numbers `b+r` as defined above is larger than the set of residues mod m
    sorry

  let ⟨ r, hr ⟩ := h₁
  let ⟨ b, hb ⟩ := hr.right

  /-
    Little lemma, if `b` is chosen as above, it is either `b₁` or `b₂`
  -/
  have hb₁ohb₂o : b = b₁ ∨ b = b₂ := by
    rw [← List.mem_pair]
    exact hb.left
  /-
    And as such, it must be odd
  -/
  have hbo : Odd b := by
    rcases hb₁ohb₂o with hb₁ | hb₂
    . rw [hb₁]
      exact hbo₁
    . rw [hb₂]
      exact hbo₂

  /-
    Equation (4)
  -/
  let a : ℚ := 2 * ((n - b - r) / m) + b

  /-
    `a` is odd
  -/
  have hao : Odd a := by
    have hae₁ : Even (2 * (((n : ℚ) - b - ↑r) / ↑m)) := by
      exact even_two_mul (((n : ℚ) - b - ↑r) / ↑m)
    dsimp [a]
    refine Even.add_odd hae₁ (Odd.intCast hbo)

  /-
    `r` is either 0 or 1, I do not know why this is true, but every source online seems to assert this, so I'm leaving this here
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
    -- SORRY: Again, this is a simple case of `x/n*n=x`, but for some reason, I can not manipulate this one to get the correct types. The result follows directly after this step
    -- rw [div_mul_cancel (n - b - r) m]
    sorry

  /-
    Setting up Cauchy's Lemma
  -/
  have h₇ : b^2 < 4 * a ∧ 3 * a < b^2 + 2 * b + 4 := by
    constructor
    . dsimp [a]
      sorry
    . dsimp [a]
      sorry

  let ⟨ s, t, u, v, hstuv ⟩ := CauchyLemma a b hao hbo h₇.left h₇.right
  /- Define the numbers as in the paper -/
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

  /- Define the multiset of the numbers -/
  let S : Multiset (Polygonal (m+2)) :={⟨ sl, ps ⟩, ⟨ tl, pt ⟩, ⟨ ul, pu ⟩, ⟨ vl, pv ⟩, ⟨ r, hrp ⟩}

  use S
  constructor
  . simp [sumPolyToInt] -- Proof it adds to `n`
    simp [S]
    simp [foldrfun]
    rw [← add_assoc, ← add_assoc, ← add_assoc]
    exact corsum
  . simp [S] -- Proof it has at most 5 elements
