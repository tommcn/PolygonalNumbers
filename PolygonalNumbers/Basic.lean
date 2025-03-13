/-
  Proof of Cauchy's Polygonal Number Theorem:

  Adapted from: https://www.ams.org/journals/proc/1987-099-01/S0002-9939-1987-0866422-3/S0002-9939-1987-0866422-3.pdf

  Also Proved in Isabelle: https://www.isa-afp.org/entries/Polygonal_Number_Theorem.html#

  Lean (version 4.15.0-rc1, aarch64-unknown-linux-gnu, commit ffac974dba79, Release)

  Tomas McNamer
-/

import Mathlib.Tactic
import Mathlib.Tactic.Rify
import Mathlib.Data.Set.Defs
import Mathlib.Data.Fin.Parity
import Init.Data.List.Basic

import PolygonalNumbers.Polygonal
import PolygonalNumbers.Lemmas

def foldrfun (m : ℤ) (hm : m ≥ 3) := fun (x1 : Polygonal m hm) (x2 : ℤ) ↦ x1.val + x2

instance : LeftCommutative (foldrfun n hm : Polygonal n hm → ℤ → ℤ) where
  left_comm := by
    intro a b c
    simp [foldrfun]
    ring

/--
  Sum of a List of polygonal numbers of same order `n` (i.e., rational
  numbers) into a rational number
-/
def sumPolyToInt (m : ℤ) (hm : m ≥ 3) (S : List (Polygonal m hm)) : ℤ := S.foldr (foldrfun m hm) 0


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

example : IsnPolygonal 3 6 (by simp) := by
  unfold IsnPolygonal
  right
  use 3
  linarith


lemma polygonal_m_one (m : ℕ) (hm : (m : ℤ) ≥ 3) : IsnPolygonal m 1 hm := by
  unfold IsnPolygonal
  right
  use 1
  ring

/-
  ==================== Cauchy Lemma for Polygonal Numbers ====================
-/
lemma CauchyLemma
  (a : ℤ)
  (ha : a ≥ 0)
  (b : ℕ)
  (aOdd : Odd a) (bOdd : Odd b) (h₁ : b^2 < 4*a) (h₂ : 3*a < b^2 + 2*b + 4) : ∃ s t v u : ℕ, (a = s^2 + t^2 + v^2 + u^2) ∧ (b = s + t + v + u) := by
  sorry

/-
  ==================== Various Lemmas for Polygonal Numbers ====================
-/



-- Lemma 1.11 (p. 42)
-- i.e., Lemma 5
lemma cauchy_setup_a
                   (m n : ℕ)
                   (hnineq : n ≥ 2 * m)
                   (hm : m ≥ 3)
                   (a : ℤ)
                   (ha : a ≥ 0)
                   (b : ℕ)
                   (hb : 0 ≠ b)
                   (r : ℕ)
                   (hr : r < m)
                   (haeq : (a) = (1 - (2 : ℚ) / m) * b + 2 * ((n - r) / m))
    : b < ((2 / 3) + √(8 * (n / m) - 8))
      → b^2 < 4*a := by
  intro h

  have hsub : ((b : ℚ) - 2/3) ^ 2 < 8 * n/m - 8 := by

    have hleq : b - 2/3 < √(8 * n/m - 8) := by
      refine sub_right_lt_of_lt_add ?_
      rw [add_comm]
      rw [mul_div_assoc]
      exact h

    suffices h' : ((b : ℝ) - 2/3) ^ 2 < 8 * n/m - 8 by
      sorry

    have hbabs : (b : ℝ) - 2/3 = |(b : ℝ) - 2/3| := by
      have hgeq : (b : ℝ) - 2/3 ≥ 0 := by
        refine sub_nonneg_of_le ?_
        have hb : b ≥ 1 := by exact Nat.one_le_iff_ne_zero.mpr (id (Ne.symm hb))
        have hbr : (b : ℝ) ≥ 1 := by exact Nat.one_le_cast.mpr hb
        linarith
      exact Eq.symm (abs_of_nonneg hgeq)

    have hsqabs : √(8 * (n : ℝ) / m - 8) = |√(8 * n / m - 8)| := by
      have hgeq : √(8 * (n : ℝ) / m - 8) ≥ 0 := by exact Real.sqrt_nonneg (8 * (n : ℝ) / m - 8)
      exact Eq.symm (abs_of_nonneg hgeq)

    rw [hbabs, hsqabs] at hleq
    apply sq_lt_sq.mpr at hleq

    have hsqrtsq : √(8 * (n : ℝ) / m - 8) ^ 2 = (8 * (n : ℝ) / m - 8) := by
      refine Real.sq_sqrt ?_
      simp
      have h' : (n : ℝ) / m ≥ 1 := by
        refine one_le_div_iff.mpr ?_
        left
        constructor
        . have h' : (m : ℝ) ≥ 3 := by exact Nat.ofNat_le_cast.mpr hm
          linarith
        . apply GE.ge.le at hnineq
          have h' : (n : ℝ) ≥ ((2 * m : ℕ) : ℝ) := by
            exact Nat.cast_le.mpr hnineq
          calc (m : ℝ)
            _ ≤ 2 * m := by linarith
            _ ≤ ((2 * m : ℕ) : ℝ) := by simp
            _ ≤ (n : ℝ) := by exact h'
      calc (8 : ℝ)
        _ ≤ 8 * (n / m) := by simp; exact h'
        _ = 8 * n / m := by rw [@mul_div]

    rw [hsqrtsq] at hleq
    exact hleq

  suffices ht : (b : ℚ)^2 - 4 * a < 0 by
    refine lt_of_sub_neg ?_
    have hfoura : 4 * a = ((4 * a : ℤ) : ℚ) := by simp
    have hbsq : (b : ℚ)^2 = ((b^2 : ℤ) : ℚ) := by simp
    rw [hfoura, hbsq] at ht
    have hbfourasq : ((b^2 : ℤ) : ℚ) - ((4 * a : ℤ) : ℚ) = ((b^2 - 4 * a : ℤ) : ℚ) := by simp
    rw [hbfourasq] at ht
    exact (Mathlib.Tactic.Qify.intCast_lt ((b : ℤ) ^ 2 - 4 * a) 0).mpr ht

  calc (b : ℚ)^2 - 4 * a
    _ = (b - 2/3) ^ 2 + 4/3 * b - 4/9 - 4 * a := by ring
    _ < (8 * n/m - 8) + 4/3 * b - 4/9 - 4 * ((1 - (2/m)) * b + 2 * ((n - r) / m)) := by
      rw [haeq] --hsub
      simp
      exact hsub
    _ = -1 * (8 * b * (1/3 - 1/m) + 8 * (1 - r/m) + 4/9) := by ring
    _ < 0 := by
      refine mul_neg_of_neg_of_pos rfl ?_

      refine add_pos ?_ ?_
      . refine add_pos_of_nonneg_of_pos ?_ ?_
        . have hleq : 1/3 - 1/(m : ℚ) ≥ 0 := by
            simp
            refine inv_anti₀ ?_ ?_
            . linarith
            . exact Nat.ofNat_le_cast.mpr hm
          refine mul_nonneg ?_ ?_
          . linarith
          . exact hleq
        . simp
          suffices h : r < m by
            refine Bound.div_lt_one_of_pos_of_lt ?_ ?_
            . suffices h' : 0 < m by
                exact Nat.cast_pos'.mpr h'
              linarith
            . exact Nat.cast_lt.mpr hr
          exact hr
      . linarith


-- i.e., Lemma 6
lemma cauchy_setup_b (m N : ℕ)
                   (hm : m ≥ 3)
                   (hnineq : N ≥ 2 * m)
                   (a : ℤ)
                   (ha : a ≥ 0)
                   (b r : ℕ)
                   (hb : 0 ≠ b)
                   (hr : r < m)
                   (haeq : (a) = (1 - (2 : ℚ) / m) * b + 2 * ((N - r) / m))
                  --  (hneq : N = ((m : ℚ) / 2)*(a - b) + b + r)
    : b > ((1 / 2) + √(6 * (N / m) - 3))
      → 3*a < b^2 + 2*b + 4 := by
  intro h
  suffices h' : 3 * a < (b : ℚ)^2 + 2 * b + 4 by
    have hlhs : 3 * a = ((3 * a : ℤ) : ℚ) := by simp
    have hrhs : (b : ℚ)^2 + 2 * b + 4 = ((b^2 + 2 * b + 4 : ℤ) : ℚ) := by simp
    rw [hlhs, hrhs] at h'
    exact (Mathlib.Tactic.Qify.intCast_lt (3 * a) (↑b ^ 2 + 2 * ↑b + 4)).mpr h'

  suffices h' : 0 < (b : ℚ)^2 + 2 * b + 4 - 3 * a by
    linarith

  have hineq : ((b : ℚ) - 1/2)^2 > 6 * N / m - 3 := by
    have hbq : (b : ℝ) - 1/2 > √(6 * (N / m) - 3) := by
      linarith

    have hbabs : |(b : ℚ) - 1/2| = b - 1/2 := by
      simp
      have hb : b ≥ 1 := by exact Nat.one_le_iff_ne_zero.mpr (id (Ne.symm hb))
      calc 2⁻¹
        _ ≤  (1 : ℚ) := by norm_num
        _ ≤ (b : ℚ) := by exact Nat.one_le_cast.mpr hb

    rw [← hbabs]

    have hbabs' : |(b : ℝ) - 1/2| = b - 1/2 := by
      simp
      have hb : b ≥ 1 := by exact Nat.one_le_iff_ne_zero.mpr (id (Ne.symm hb))
      calc 2⁻¹
        _ ≤  (1 : ℝ) := by norm_num
        _ ≤ (b : ℝ) := by exact Nat.one_le_cast.mpr hb

    have hsqabs : (6 * (N : ℚ) / ↑m - 3) = |(6 * (N : ℚ) / ↑m - 3)| := by
      suffices h' : (6 * (N : ℚ) / m - 3) ≥ 0 by
        exact Eq.symm (abs_of_nonneg h')
      simp

      have hnrat : (N : ℝ) / m ≥ 2 := by
        have hnn : (N : ℝ) ≥ 2 * m := by
          have htwoz : ((2 * (m : ℕ) : ℕ) : ℝ) = 2 * (m : ℝ) := by simp
          rw [← htwoz]
          exact Nat.cast_le.mpr hnineq

        apply GE.ge.le at hnn
        simp
        refine (le_mul_inv_iff₀ ?_).mpr hnn
        calc 0
          _ < (3 : ℝ) := by norm_num
          _ ≤ (m : ℝ) := by exact Nat.ofNat_le_cast.mpr hm

      suffices h' : 3 ≤ 6 * ((N : ℚ) / m) by
        rw [@mul_div_assoc]
        exact h'

      calc 3
        _ ≤ (6 : ℚ) := by norm_num
        _ ≤ 6 * 2 := by
          simp
        _ ≤ 6 * ((N : ℚ) / m) := by
          refine mul_le_mul_of_nonneg_left ?_ ?_
          . have h' : (N : ℝ) / m = ((N : ℚ) / (m : ℚ) : ℚ) := by
              simp
            rw [h'] at hnrat
            apply GE.ge.le at hnrat
            let a : ℚ := N / m
            have ha : a = N / m := by simp
            rw [← ha] at hnrat
            rw [← ha]
            apply (Mathlib.Tactic.Rify.ratCast_le 2 a).mpr
            exact hnrat
          . linarith

    rw [← hbabs'] at hbq

    rw [hsqabs]
    suffices h' : |6 * (N : ℚ) / ↑m - 3| < |(b : ℚ) - 1 / 2| ^ 2 by
      exact h'

    -- apply GT.gt.lt at hbsqq

    sorry

  have hbsuba : (b : ℚ) - a = 2 / m * b - 2 * ((N - r) / m) := by
    rw [haeq]
    ring

  apply GT.gt.lt

  calc (b : ℚ) ^ 2 + 2 * b + 4 - 3 * a
    _ = (b - 1/2) ^ 2 + 3*b + 15/4 - 3 * a := by ring
    _ > 6 * N / m - 3 + 3 * b + 15/4 - 3 * a := by linarith
    _ = 6 * N / m - 3 + 15/4 + 3 * (b - a) := by ring
    _ = 6 * N / m + 3/4 + 3 * (b - a) := by ring
    _ = 6 * N / m + 3/4 + 3 * (2 / m * b - 2 * ((N - r) / m)) := by
      rw [haeq]
      ring_nf
    _ = 3/4 + 6 * (b + r) / m := by ring
    _ > 0 := by
      refine Right.add_pos_of_pos_of_nonneg ?_ ?_
      . norm_num
      . refine Rat.div_nonneg ?_ ?_
        . linarith
        . linarith

lemma cauchy_setup (m N : ℕ)
                   (hm : m ≥ 3)
                   (hnineq : N ≥ 2 * m)
                   (a : ℤ)
                   (ha : a ≥ 0)
                   (b : ℕ)
                   (hb : 0 ≠ b)
                   (r : ℕ)
                   (haeq : (a) = (1 - (2 : ℚ) / m) * b + 2 * ((N - r) / m))
                   (hr : r < m)
                  --  (hneq : N = ((m : ℚ) / 2)*(a - b) + b + r)
    : (1 / 2 + √(6 * (N / m) - 3)) < b
        → b < (2 / 3 + √(8 * (N / m) - 8))
      → b^2 < 4*a ∧ 3*a < b^2 + 2*b + 4 := by

  intro h₁
  intro h₂
  constructor
  . exact cauchy_setup_a m N hnineq hm a ha b hb r hr haeq h₂
  . exact cauchy_setup_b m N hm hnineq a ha b r hb hr haeq h₁

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
    : ∃ (S : List (Polygonal (m+2) (by linarith))),
      (sumPolyToInt (m+2) (by linarith) S  = n)                  -- Sum = n
    ∧ (S.length ≤ m+1)
      := by
  have hmqgeq3 : (m : ℚ) ≥ 3 := by
    exact Nat.ofNat_le_cast.mpr mb
  have hm2geq3 : ((m : ℤ) + 2) ≥ 3 := by linarith
  have hmgtq0 : (m : ℚ) > 0 := by
    exact gt_of_ge_of_gt hmqgeq3 rfl
  have hmgtn0 : m  > 0 := by
    exact Nat.zero_lt_of_lt mb
  have hmnot0 : (m : ℚ) ≠ 0 := by
    linarith
  have ngeq2m : n ≥ 2 * m := by
    linarith
  have hnmr : (n : ℝ) / m ≥ 120 := by
    have hypr : (n : ℝ) ≥ (((120 * m) : ℕ) : ℝ) := by
      exact Nat.cast_le.mpr nb
    simp at hypr
    apply ge_iff_le.mp at hypr
    apply ge_iff_le.mpr
    ring_nf
    refine (le_mul_inv_iff₀ ?_).mpr hypr
    exact Nat.cast_pos'.mpr hmgtn0

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

    suffices h : ∃ r : ℤ, 0 ≤ r ∧ r ≤ m-3 ∧ (∃ b ∈ [(b₁ : ℤ), (b₂ : ℤ)], n ≡ (b + r : ℤ) [ZMOD m]) by
      let ⟨ r, hr ⟩ := h
      use r.natAbs
      have hrpos : r ≥ 0 := by
        exact hr.left
      sorry

    have hbb : (b₂ : ℤ) = b₁ + 2 := by
      exact congrArg Nat.cast hb₁b₂

    apply mod_m_congr b₁ b₂ hbb n m (sorry)


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

  let a : ℤ := 2 * ((n - b - r) / m) + b


  have hazq : (a : ℚ) = 2 * (((n : ℚ) - b - r) / m) + b := by
    dsimp [a]
    simp
    have hex : ∃ (k : ℤ), (n - b - r) = m * k := by
      let hmod := hb.right
      have hnpm : (n : ℤ) - b - r = n - (b + r) := by linarith
      apply Nat.ModEq.symm at hmod
      rw [hnpm]
      apply Nat.ModEq.dvd at hmod
      let ⟨ k, hk ⟩ := hmod
      use k
      simp at hk
      rw [hk]
    let ⟨ k, hk ⟩ := hex
    have hzdiv : ((n - b - r) / m) = k := by
      rw [hk]
      refine Int.mul_ediv_cancel_left k ?_
      linarith
    have hqdiv : (((n : ℚ) - b - r) / m) = k := by
      have hnzq : (n : ℚ) - b - r = ((n - b - r) : ℤ) := by
        simp
      rw [hnzq]
      rw [hk]
      simp
      exact mul_div_cancel_left₀ (↑k) hmnot0
    rw [hzdiv]
    rw [hqdiv]

  have haalt : a = ((1 : ℚ) - 2 / m) * b + 2 * ((n - r) / m) := by
    rw [hazq]
    ring
  have haalt' : a = ((1 : ℚ) - 2 / m) * b + 2 * (n - r) / m := by
    rw [haalt]
    ring

  have hapos : a ≥ 0 := by
    suffices hapos' : (a : ℚ) ≥ 0 by
      exact (Mathlib.Tactic.Qify.intCast_le 0 a).mpr hapos'

    rw [haalt']
    refine Rat.add_nonneg ?_ ?_
    . refine Rat.mul_nonneg ?_ ?_
      . refine (Rat.le_iff_sub_nonneg (2 / ↑m) 1).mp ?_
        refine (div_le_one₀ hmgtq0).mpr (by linarith)
      . linarith
    . refine Rat.div_nonneg ?_ ?_
      . have hmnq : (n : ℚ) ≥ 120 * (m : ℕ) := by
          let m' : ℚ := n
          let n' : ℕ := 120 * m
          suffices hmn' : m' ≥ n' by
            dsimp [m', n'] at hmn'
            simp at hmn'
            exact hmn'
          apply Rat.cast_le_natCast.mpr
          simp
          dsimp [n']
          exact nb
        refine Rat.mul_nonneg rfl ?_
        refine (Rat.le_iff_sub_nonneg ↑r ↑n).mp ?_
        calc (r : ℚ)
          _ ≤ m := by refine Nat.cast_le.mpr (by linarith)
          _ ≤ 120 * m := by exact (le_mul_iff_one_le_left hmgtq0).mpr rfl
          _ ≤ n := by exact hmnq
      . linarith

  have hao : Odd a := by
    have hae₁ : Even ((2 : ℤ) * ((n - b - r) / m)) := by
      exact even_two_mul (((n : ℤ) - b - r) / m)
    dsimp [a]
    have hboz : Odd (b : ℤ) := by
      exact (Int.odd_coe_nat b).mpr hbo
    exact Even.add_odd hae₁ hboz


  have hbnez : 0 ≠ b := by
    intro h
    have hoddz : Odd 0 := by rw [← h] at hbo; exact hbo
    have hnoddz : ¬ Odd 0 := by exact Nat.not_odd_zero
    contradiction

  let cauchy_setset_up := cauchy_setup m n mb ngeq2m a hapos b  hbnez r haalt hrltm
  let ⟨ clemma_left, clemma_right ⟩ := cauchy_setset_up hblb hbub

  let ⟨ s, t, u, v, hstuv ⟩ := CauchyLemma a hapos b hao hbo clemma_left clemma_right
  /- Probably rewrite to one-two lines to not overpopulate state -/
  let sl : ℚ := (m / 2) * (s^2 - s) + s
  let tl : ℚ := (m / 2) * (t^2 - t) + t
  let ul : ℚ := (m / 2) * (u^2 - u) + u
  let vl : ℚ := (m / 2) * (v^2 - v) + v

  have slint : sl = |⌈ sl ⌉| := by dsimp [sl]; apply polyform m s hm2geq3
  have tlint : tl = |⌈ tl ⌉| := by dsimp [tl]; apply polyform m t hm2geq3
  have ulint : ul = |⌈ ul ⌉| := by dsimp [ul]; apply polyform m u hm2geq3
  have vlint : vl = |⌈ vl ⌉| := by dsimp [vl]; apply polyform m v hm2geq3


  let poly1 : Polygonal (m+2) (by linarith) := ⟨ 1, polygonal_m_one (m+2) (hm2geq3)⟩

  let l₁ : List (Polygonal (m+2) (by linarith)) := []

  let ms₁ := List.replicate r poly1

  have ms₃repl (r : ℕ) : List.replicate (r + 1) poly1 = poly1 :: List.replicate r poly1 := rfl

  have ms₁induc (r : ℕ) : sumPolyToInt (m+2) hm2geq3 (List.replicate r poly1)  = r := by
    induction' r with r hr
    . simp [sumPolyToInt]
    . rw [ms₃repl]
      simp [sumPolyToInt]
      simp [foldrfun]

      simp [sumPolyToInt] at hr
      rw [hr]
      ring

  have ms₁sum' : List.foldr (foldrfun (↑m + 2) hm2geq3) 0 ms₁ = r := by
    exact ms₁induc r

  have ms₁card : ms₁.length = r := by
    exact List.length_replicate r poly1
  /-
    Equation (5)
  -/
  have h₂ : (n : ℚ) = ((m : ℚ) / 2) * ((a : ℚ) - b) + b + r := by
    have hmeq : (m : ℚ) * (m : ℚ)⁻¹ = 1 := by
      exact Rat.mul_inv_cancel (↑m) hmnot0
    rw [hazq]
    simp
    rw [← mul_assoc, mul_comm]
    simp
    ring
    repeat
      rw [mul_assoc]
      rw [hmeq]
      simp


  /- The sum of the numbers is `n` -/
  have corsum : sl + tl + ul + vl + r = n := by
    dsimp [sl, tl, ul, vl]
    rw [h₂, hstuv.left, hstuv.right]
    simp
    ring

  have corsum₀ : (((|⌈ sl ⌉| + |⌈ tl ⌉| + |⌈ ul ⌉| + |⌈ vl ⌉| + r) : ℤ) : ℚ) = (n : ℤ) := by
    simp

    have hstep (x : ℚ) : |(⌈ x ⌉ : ℚ)| = |⌈ x ⌉| := by
      simp

    rw [hstep sl, hstep tl, hstep ul, hstep vl]
    rw [← slint, ← tlint, ← ulint, ← vlint]
    exact corsum

  have corsum' : |⌈ sl ⌉| + |⌈ tl ⌉| + |⌈ ul ⌉| + |⌈ vl ⌉| + r = n := by
    exact Eq.symm ((fun {a b} ↦ Rat.intCast_inj.mp) (id (Eq.symm corsum₀)))

  let S : List (Polygonal (m+2) hm2geq3) :=
    ⟨ ⌈sl⌉.natAbs, polyformval m s hm2geq3 ⟩ ::
    ⟨ ⌈tl⌉.natAbs, polyformval m t hm2geq3 ⟩ ::
    ⟨ ⌈ul⌉.natAbs, polyformval m u hm2geq3 ⟩ ::
    ⟨ ⌈vl⌉.natAbs, polyformval m v hm2geq3 ⟩ ::
    ms₁

  use S
  constructor
  . -- Proof it adds to `n`
    simp [sumPolyToInt]
    simp [S]
    simp [foldrfun]
    rw [← add_assoc, ← add_assoc, ← add_assoc]
    rw [ms₁sum']
    exact corsum'
  . -- Proof its size is correct
    simp [S]
    rw [ms₁card]
    have hr : r + 3 ≤ m := by
      exact Nat.add_le_of_le_sub mb hrb'
    exact hr
