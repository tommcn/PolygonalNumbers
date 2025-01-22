/-
  Proof of Cauchy's Polygonal Number Theorem:

  Adapted from: https://www.ams.org/journals/proc/1987-099-01/S0002-9939-1987-0866422-3/S0002-9939-1987-0866422-3.pdf

  Also Proved in Isabelle: https://www.isa-afp.org/entries/Polygonal_Number_Theorem.html#

  Lean (version 4.15.0-rc1, aarch64-unknown-linux-gnu, commit ffac974dba79, Release)

  Tomas McNamer
-/

import Mathlib.Tactic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Fin.Parity
import Init.Data.List.Basic

import PolygonalNumbers.Polygonal
import PolygonalNumbers.Lemmas

def foldrfun (n : ℤ) := fun (x1 : Polygonal n) (x2 : ℤ) ↦ x1.val + x2

instance : LeftCommutative (foldrfun n : Polygonal n → ℤ → ℤ) where
  left_comm := by
    intro a b c
    simp [foldrfun]
    ring

/--
  Sum of a multiset of polygonal numbers of same order `n` (i.e., rational
  numbers) into a rational number
-/
def sumPolyToInt (n : ℤ) (S : Multiset (Polygonal n)) : ℤ := S.foldr (foldrfun n) 0






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
  have htwoa : 2 * (a : ℚ) = (((2 * a) : ℤ) : ℚ) := by simp
  constructor
  . intro h
    let ⟨ k, hk ⟩ := h
    use k
    have hiff : k * (k + 1) = 2 * a ↔ k * (k + 1) = 2 * (a : ℚ) := by
      constructor
      . intro h
        rw [htwoa]
        rw [← h]
        simp
      . intro h
        have hkr : (k : ℚ) * (k + 1) = ((k * (k + 1) : ℤ)) := by
          simp
        rw [hkr, htwoa] at h
        sorry
        -- exact Eq.symm ((fun {a b} ↦ Real.intCast_inj.mp) (id (Eq.symm h)))
    apply hiff.mpr
    rw [← hk]
    ring_nf
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

    rw [htwoa]
    rw [← hk]
    ring_nf
    simp

lemma polygonal_m_one (m : ℕ) : IsnPolygonal m 1 := by
  unfold IsnPolygonal
  use 1
  ring

/-
  ==================== Cauchy Lemma for Polygonal Numbers ====================
-/
lemma CauchyLemma (a : ℕ) (b : ℕ) (aOdd : Odd a) (bOdd : Odd b) (h₁ : b^2 < 4*a) (h₂ : 3*a < b^2 + 2*b + 4) : ∃ s t v u : ℕ, (a = s^2 + t^2 + v^2 + u^2) ∧ (b = s + t + v + u) := by
  sorry

/-
  ==================== Various Lemmas for Polygonal Numbers ====================
-/



-- Lemma 1.11 (p. 42)
lemma cauchy_setup_a
                   (m n : ℕ)
                   (hm : m ≥ 3)
                   (a b r : ℕ)
                   (hr : r < m)
                   (ha : (a) = (1 - (2/m)) * b + 2 * ((n - r) / m))
    : b < ((2 / 3) + √(8 * (n / m) - 8))
      → b^2 < 4*a := by
  sorry

lemma cauchy_setup_b (m N : ℕ)
                   (hm : m ≥ 3)
                  --  (hnineq : N ≥ 2 * m)
                   (a b r : ℕ)
                   (hr : r < m)
                  --  (hneq : N = ((m : ℚ) / 2)*(a - b) + b + r)
    : b < ((2 / 3) + √(8 * (n / m) - 8))
      → 3*a < b^2 + 2*b + 4 := by
  sorry

lemma cauchy_setup (m N : ℕ)
                   (hm : m ≥ 3)
                  --  (hnineq : N ≥ 2 * m)
                   (a b r : ℕ)
                  --  (hr : r < m)
                  --  (hneq : N = ((m : ℚ) / 2)*(a - b) + b + r)
    : (1 / 2 + √(6 * (N / m) - 3)) < b
        → b < (2 / 3 + √(8 * (N / m) - 8))
      → b^2 < 4*a ∧ 3*a < b^2 + 2*b + 4 := by
  intro h₁
  intro h₂
  sorry
  -- constructor
  -- . exact cauchy_setup_a m m hm a b 2 hm h₂
  -- . exact cauchy_setup_b m m hm a b 2 hm h₂


/-
  ==================== Theorem I for Polygonal Numbers ====================
-/
/--
  Theorem I
  Let m ≥ 3 and n ≥ 120*m. Then n is the sum of m + 1 polygonal numbers of
  order m + 2, at most four of which are different from 0 or `1`
-/
theorem CauchyPolygonalNumberTheorem
          (m n: ℕ)
          (nmpos : n ≥ 1)
          (mb : m ≥ 3)
          (nb : n ≥ 120*m)
    : ∃ (S : Multiset (Polygonal (m+2))),
      (sumPolyToInt (m+2) S = n)                  -- Sum = n
    ∧ (Multiset.card S ≤ m+1)
      := by
  have hmqgeq3 : (m : ℚ) ≥ 3 := by
    exact Nat.ofNat_le_cast.mpr mb
  have hmgtq0 : (m : ℚ) > 0 := by
    exact gt_of_ge_of_gt hmqgeq3 rfl
  have hmgtn0 : m  > 0 := by
    exact Nat.zero_lt_of_lt mb
  have hmnot0 : (m : ℚ) ≠ 0 := by
    linarith
  have ngeq2m : n ≥ 2 * m := by
    linarith
  have hnmr : (n : ℝ) / m ≥ 120 := by
    sorry

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
          (interval_length n m hmgtn0 nb)
          (bound_positive hnmr)


  have h₁ : ∃ r ∈ List.range (((m-3) + 1 : ℕ)), ∃ b ∈ [b₁, b₂], n ≡ (b + r) [MOD m] := by
    simp
    -- Proof by pigeonhole principle, the set of numbers `b+r` as defined above is larger than the set of residues mod m
    sorry



  let ⟨ r, hr ⟩ := h₁
  let ⟨ b, hb ⟩ := hr.right

  have hrb : r < (m - 3 + 1) := by
    let hrrange := hr.left
    apply List.mem_range.mp hrrange
  have hrb' : r ≤ m - 3 := by exact Nat.le_of_lt_succ hrb
  have hrltm : r < m := by
    calc r
      _ < m - 3 + 1 := by exact hrb
      _ < m := by refine Nat.add_lt_of_lt_sub ?_; refine Nat.sub_lt_sub_left ?_ ?_; exact
        Nat.lt_of_succ_lt mb; exact Nat.one_lt_succ_succ 1


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

  have hn : (n : ℚ) = ↑m / 2 * (↑a - ↑b) + ↑b + ↑r := by
    dsimp [a]
    simp
    sorry


  let cauchy_setset_up := cauchy_setup m n mb a b r
  let ⟨ clemma_left, clemma_right ⟩ := cauchy_setset_up hblb hbub

  let ⟨ s, t, u, v, hstuv ⟩ := CauchyLemma a b hao hbo clemma_left clemma_right
  let sl : ℚ := (m / 2) * (s^2 - s) + s
  let tl : ℚ := (m / 2) * (t^2 - t) + t
  let ul : ℚ := (m / 2) * (u^2 - u) + u
  let vl : ℚ := (m / 2) * (v^2 - v) + v

  -- have polyform (r : ℕ) : ((m : ℚ) / 2) * (r^2 - r) + r = ⌈ ((m : ℚ) / 2) * (r^2 - r) + r ⌉ := by
  --   simp
  --   rw [← (kfactq r)]
  --   let ⟨ e, he ⟩ := revenk' r
  --   simp at he
  --   rw [he]
  --   rw [← mul_assoc]
  --   simp
  --   have hms : (m : ℚ) = ((m : ℤ) : ℚ) := rfl
  --   rw [hms]
  --   rw [← Int.cast_mul m e]
  --   rw [@Int.ceil_intCast]

  have slint : sl = ⌈ sl ⌉ := by exact polyform m s
  have tlint : tl = ⌈ tl ⌉ := by exact polyform m t
  have ulint : ul = ⌈ ul ⌉ := by exact polyform m u
  have vlint : vl = ⌈ vl ⌉ := by exact polyform m v

  /- `s`, `t`, `u`, `v` are polygonal -/
  have ps : IsnPolygonal (m+2) ⌈ sl ⌉ := by
    rw [PolyEquiv]
    unfold IsnPolygonal'
    use s
    simp
    rw [← slint]

  have pt : IsnPolygonal (m+2) ⌈ tl ⌉ := by
    rw [PolyEquiv]
    unfold IsnPolygonal'
    use t
    rw [← tlint]
    simp

  have pu : IsnPolygonal (m+2) ⌈ ul ⌉ := by
    rw [PolyEquiv]
    unfold IsnPolygonal'
    rw [← ulint]
    use u
    simp

  have pv : IsnPolygonal (m+2) ⌈ vl ⌉ := by
    rw [PolyEquiv]
    unfold IsnPolygonal'
    use v
    rw [← vlint]
    simp


  let poly1 : Polygonal (m+2) := ⟨ 1, polygonal_m_one (m+2) ⟩

  let l₁ : List (Polygonal (m+2)) := []

  let ms₁ := Multiset.replicate r poly1

  have ms₃repl (r : ℕ) : Multiset.replicate (r + 1) poly1 = poly1 ::ₘ Multiset.replicate r poly1 := rfl

  have ms₁induc (r : ℕ) : sumPolyToInt (m+2) (Multiset.replicate r poly1) = r := by
    induction' r with r hr
    . simp [sumPolyToInt]
    . rw [ms₃repl]
      simp [sumPolyToInt]
      simp [foldrfun]

      simp [sumPolyToInt] at hr
      rw [hr]
      ring

  have ms₁sum' : Multiset.foldr (foldrfun (↑m + 2)) 0 ms₁ = r := by
    exact ms₁induc r

  have ms₁card : ms₁.card = r := by
    exact Multiset.card_replicate r poly1
  /-
    Equation (5)
  -/
  have h₂ : (n : ℚ) = ((m : ℚ) / 2) * ((a : ℚ) - b) + b + r := by
    dsimp [a]
    simp
    rw [← mul_assoc, mul_comm]
    simp
    sorry



  /- The sum of the numbers is `n` -/
  have corsum : sl + tl + ul + vl + r = n := by
    dsimp [sl, tl, ul, vl]
    rw [h₂, hstuv.left, hstuv.right]
    simp
    ring

  let S : Multiset (Polygonal (m+2)) := {⟨ ⌈sl⌉, ps ⟩, ⟨ ⌈tl⌉, pt ⟩, ⟨ ⌈ul⌉, pu ⟩, ⟨ ⌈vl⌉, pv ⟩} + ms₁

  use S
  constructor
  . -- Proof it adds to `n`
    simp [sumPolyToInt]
    simp [S]
    simp [foldrfun]
    rw [← add_assoc, ← add_assoc, ← add_assoc]
    rw [ms₁sum']
    sorry
    --exact corsum
  . -- Proof it has at most 5 elements
    simp [S]
    rw [ms₁card]

    sorry
