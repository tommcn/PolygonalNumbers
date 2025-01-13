import Mathlib.Tactic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Fin.Parity
import Init.Data.List.Basic

lemma sqrt_geq_four (x : ℕ) (hx : x ≥ 120) : √(8*x-8) - √(6*x-3) > 4 := by
  have sqrt_in_gt_zero : (8 * (x : ℝ) - 8) > 0 := by
    calc 8 * (x : ℝ) - 8
      _ = 8* (x - 1):= by exact Eq.symm (mul_sub_one 8 (x : ℝ))
      _ ≥ 8 * (120 - 1) := by
        refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
        simp
        simp
        exact hx
        simp
        calc (x : ℝ) - 1
          _ ≥ 120 - 1 := by simp; exact hx
          _ ≥ 0 := by linarith
      _ = 8 * 119 := by simp; ring
      _ > 0 := by linarith
  have sqrt_ne_zero : √(8*x-8) ≠ 0 := by
    refine Real.sqrt_ne_zero'.mpr ?_;
    exact sqrt_in_gt_zero
  have sqrt_in_gt_zero' : 6 * (x : ℝ) - 3 > 0 := by
    calc 6 * (x : ℝ) - 3
      _ = 6 * (x - 1) + 3 := by ring
      _ ≥ 6 * (120 - 1) + 3 := by
        refine add_le_add ?_ ?_
        . refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
          simp
          simp
          exact hx
          simp
          calc (x : ℝ) - 1
            _ ≥ 120 - 1 := by simp; exact hx
            _ ≥ 0 := by linarith
        . linarith
      _ = 6 * 119 + 3 := by ring
      _ > 0 := by linarith
  have sqrt_in_geq_zero : (8 * (x : ℝ) - 8) ≥ 0 := by exact le_of_lt sqrt_in_gt_zero
  have sqrt_in_geq_zero' : (6 * (x : ℝ) - 3) ≥ 0 := by exact le_of_lt sqrt_in_gt_zero'
  have sqrt_ne_zero' : √(6*x-3) ≠ 0 := by
    refine Real.sqrt_ne_zero'.mpr ?_;
    exact sqrt_in_gt_zero'
  have sqrt_pos : √(8*x-8) > 0 := by
    apply lt_iff_le_and_ne.mpr
    constructor
    . exact Real.sqrt_nonneg (8*x-8)
    . apply Ne.symm; exact sqrt_ne_zero
  have sqrt_pos' : √(6*x-3) > 0 := by
    apply lt_iff_le_and_ne.mpr
    constructor
    . exact Real.sqrt_nonneg (6*x-3)
    . apply Ne.symm; exact sqrt_ne_zero'

  have x_sub_sub : ((8*(x : ℝ)-8) < (8*x-4)) := by linarith

  have sqrt_lt_sqrt_eight_four : (√(8*x-8) < √(8*x-4)) := by
    apply Real.sqrt_lt_sqrt;
    exact sqrt_in_geq_zero; exact x_sub_sub

  have sqrt_add_lt : (√(8*x-8) + √(6*x-3)) < (√(8*x-4) + √(6*x-3)) := by
    exact (add_lt_add_iff_right √(6 * (x : ℝ) - 3)).mpr sqrt_lt_sqrt_eight_four

  have sqrt_add_ne_zero : (√(8*x-8) + √(6*x-3)) ≠ 0 := by
    apply ne_of_gt
    apply add_pos sqrt_pos sqrt_pos'
  have sqrt_four_two : √4 = 2 := by
    refine Real.sqrt_eq_cases.mpr ?_
    constructor
    constructor
    . ring
    . linarith

  have sqrt_sq_two_one : (√(2 * x - 1))^2 = 2 * x - 1 := by
    refine Real.sq_sqrt ?_
    calc 2 * (x : ℝ) - 1
      _ ≥ 2 * 120  - 1 := by simp; exact hx
      _ ≥ 0 := by linarith

  have sqrt_sq_sqrt_div : (√(2*x-1))^2 / (√(2*x - 1)) = (√(2*x-1)) := by
    calc (√(2*x-1))^2 / (√(2*x - 1))
      _ = (√(2*x-1)) * (√(2*x - 1)) / (√(2*x - 1)) := by rw [@sq]
      _ = (√(2*x-1)) := by exact mul_self_div_self √(2 * (x : ℝ) - 1)

  have sqrt_sub_four_lt : (√(2*x - 1) - 4 / (√(2*x - 1))) ≥ (√(2 * 120 - 1) - 4/ (√(2*x - 1))) := by
    refine tsub_le_tsub_right ?_ (4 / √(2 * ↑x - 1))
    refine (Real.sqrt_le_sqrt_iff ?_).mpr ?_
    linarith
    simp
    exact hx

  have sqrt_three_pos : √3 > 0 := by
    refine Real.sqrt_pos_of_pos ?_
    linarith
  have zero_lt_two_sqrt : 0 < 2 + √3 := by
    apply add_pos ?_ sqrt_three_pos
    linarith

  have sqrt_two_x : √(2 * (x : ℝ) - 1) > 0 := by
    refine Real.sqrt_pos_of_pos ?_
    calc 2 * (x : ℝ) - 1
      _ ≥ 2 * 120 - 1 := by
        refine sub_le_sub_right ?_ 1
        simp
        exact hx
      _ > 0 := by linarith


  calc √(8*x-8) - √(6*x-3)
    _ = (√(8*x-8) - √(6*x-3)) * (√(8*x-8) + √(6*x-3)) / (√(8*x-8) + √(6*x-3)) := by
      apply Eq.symm;
      exact mul_div_cancel_right₀ (√(8 * ↑x - 8) - √(6 * ↑x - 3)) sqrt_add_ne_zero
    _ = (√(8*x-8) + √(6*x-3)) * (√(8*x-8) - √(6*x-3)) / (√(8*x-8) + √(6*x-3)) := by ring
    _ = ((√(8*x-8))^2 - (√(6*x-3))^2)  / (√(8*x-8) + √(6*x-3)) := by
      rw [← sq_sub_sq (√(8*x-8)) (√(6*x-3))]
    _ = (8*x-8 - (6*x-3)) / (√(8*x-8) + √(6*x-3)) := by
      rw [Real.sq_sqrt, Real.sq_sqrt]
      . exact le_of_lt sqrt_in_gt_zero'
      . exact le_of_lt sqrt_in_gt_zero
    _ = ((2*x - 1) - 4) / (√(8*x-8) + √(6*x-3)) := by ring
    _ > ((2*x - 1) - 4) / (√(8*x-4) + √(6*x-3)) := by
      refine div_lt_div_of_pos_left ?_ ?_ sqrt_add_lt
      . calc 2 * (x : ℝ) - 1 - 4
          _ = 2 * ↑x - 5 := by linarith
          _ ≥ 2 * 120 - 5 := by
            refine tsub_le_tsub ?_ ?_
            simp
            exact hx
            simp
          _ > 0 := by linarith
      . exact Right.add_pos' sqrt_pos sqrt_pos'
    _ = ((2*x - 1) - 4) / (√(4 * (2*x - 1)) + √(3*(2*x - 1))) := by ring_nf
    _ = ((2*x - 1) - 4) / ((√(4) * √(2*x - 1)) + √(3)*√(2*x - 1)) := by simp
    _ = ((2*x - 1) - 4) / ((2 * √(2*x - 1)) + √(3)*√(2*x - 1)) := by rw [sqrt_four_two]
    _ = ((2*x - 1) - 4) / ((2 + √3) * √(2*x - 1)) := by ring
    _ = (1 / (2 + √(3))) * (((2*x - 1) - 4) / (√(2*x - 1))) := by
      calc ((2*x - 1) - 4) / ((2 + √3) * √(2*x - 1))
        _ = (((2*x - 1) - 4) / (2 + √3)) / √(2*x - 1) := by
          exact div_mul_eq_div_div (2 * (x : ℝ) - 1 - 4) (2 + √3) √(2 * (x : ℝ) - 1)
        _ = (1 / (2 + √3)) * ((2*x - 1 - 4) / √(2*x - 1)) := by ring
    _ = (1 / (2 + √(3))) * ((2*x - 1) / (√(2*x - 1)) - 4 / (√(2*x - 1))) := by ring
    _ = (1 / (2 + √(3))) * ((√(2*x-1))^2 / (√(2*x - 1)) - 4 / (√(2*x - 1))) := by rw [sqrt_sq_two_one]
    _ = (1 / (2 + √(3))) * (√(2*x - 1) - 4 / (√(2*x - 1))) := by rw [sqrt_sq_sqrt_div]
    _ ≥ (1 / (2 + √(3))) * (√(2 * 120 - 1) - 4/ (√(2*x - 1))) := by
      refine mul_le_mul_of_nonneg ?_ sqrt_sub_four_lt ?_ ?_
      . rfl
      . refine one_div_nonneg.mpr ?_
        exact le_of_lt zero_lt_two_sqrt
      . simp
        refine (Real.le_sqrt' ?_).mpr ?_
        . apply div_pos
          . linarith
          . exact sqrt_two_x
        . sorry
    _ ≥ (1 / (2 + √(3))) * (√(2 * 120 - 1) - 4 / (√(2*120 - 1))) := by
      sorry
    _ > 4 := by sorry -- apply? --sorry --norm_num

lemma interval_length (n m : ℕ) (hm : m > 0) (hn : n ≥ 120 * m) : ((2 / 3) + √(8 * (n / m) - 8)) - (1 / 2 + √(6 * (n/m) - 3)) > 4 := by
  let x := (n :ℚ) / m

  have hnq : (n : ℚ) ≥ 120 * (m : ℚ) := by sorry

  have x_geq : x ≥ 120 := by
    calc (n : ℚ) / (m)
      _ ≥ 120 * m / m := by
        refine (div_le_div_iff_of_pos_right ?_).mpr hnq
        exact Nat.cast_pos'.mpr hm
      _ = 120 * (m / m) := by ring
      _ = 120 := by simp; sorry
  sorry

lemma bound_positive :  1 / 2 + √(6 * (↑n / ↑m) - 3) > 0 := by
  have hsqrtpos : √(6 * (↑n / ↑m) - 3) ≥ 0 := by exact Real.sqrt_nonneg (6 * (n / m) - 3)
  have hhalfpos : (1 : ℝ) / 2 > 0 := by exact one_half_pos
  exact Right.add_pos_of_pos_of_nonneg hhalfpos hsqrtpos

/--
  In an interval of length strictly greater than 4, there exists two odd numbers in the interval
-/
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
      . have epodd' : Odd (⌈ ep₁ ⌉.natAbs) := Odd.natAbs epodd
        refine Nat.odd_add_one.mpr ?_
        simp
        exact Odd.add_one epodd'
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
        linarith
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
      . have hepabs : ⌈ ep₁ ⌉.natAbs = ⌈ ep₁ ⌉ := by exact id (Eq.symm hep₁)
        have hoddimp : Odd (⌈ ep₁ ⌉ + 1) → Odd (⌈ ep₁ ⌉.natAbs + 1) := by
          intro h; rw [← hepabs] at h; exact (Int.odd_coe_nat (⌈ep₁⌉.natAbs + 1)).mp h
        exact hoddimp ep1odd
      . have hepabs : ⌈ ep₁ ⌉.natAbs = ⌈ ep₁ ⌉ := by exact id (Eq.symm hep₁)
        rw [← hepabs] at ep1odd
        have heven : Even ((⌈ep₁⌉.natAbs : ℤ) + 1 + 1) := by exact Odd.add_one ep1odd
        have hodd : Odd ((⌈ep₁⌉.natAbs : ℤ) + 1 + 1 + 1) := by exact Even.add_one heven
        exact (Int.odd_coe_nat (⌈ep₁⌉.natAbs + 3)).mp hodd
      . simp
        linarith
      . simp
        linarith
      . ring
