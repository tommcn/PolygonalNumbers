import Mathlib.Tactic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Fin.Parity
import Init.Data.List.Basic

lemma revenk (r : ℤ) : ∃ k : ℤ, r * (r - 1) = 2 * k := by
  have h : Even (r * (r - 1)) := by
    apply Int.even_mul_pred_self
  dsimp [Even] at h
  let ⟨ k, hk ⟩ := h
  use k
  rw [hk]
  ring

lemma revenk' (r : ℤ) : ∃ k : ℤ, (r : ℚ) * (r - 1) = 2 * k := by
  have h : Even (r * (r - 1)) := by
    apply Int.even_mul_pred_self

  dsimp [Even] at h
  let ⟨ k, hk ⟩ := h
  use k
  have oneratint : (1 : ℚ) = (1 : ℤ) := by simp
  rw [oneratint]
  rw [← Int.cast_sub r 1]
  rw [← Int.cast_mul r (r - 1)]
  rw [hk]
  simp
  exact Eq.symm (two_mul (k : ℚ))


lemma bound_positive (hn : n / m ≥ 120) :  1 / 2 + √(6 * (↑n / ↑m) - 3) > 0 := by
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



/- EXTRA -/
lemma ab {a b : ℝ} (ha : a > 0) (hb : b > 0) : √a - √b = (a - b) / (√a + √b) := by
  have : (√a - √b) * (√a + √b) = a - b := by
    ring_nf
    simp [Real.sq_sqrt, le_of_lt ha, le_of_lt hb]
  rw [← this, ← mul_div]
  have : √a + √b > 0 := Right.add_pos' (Real.sqrt_pos_of_pos ha) (Real.sqrt_pos_of_pos hb)
  simp [div_self (Ne.symm (ne_of_lt this))]

lemma nn : (1 : ℝ) / (2 + √3) > 0.267 := by
  have : √3 < 1.733 := by
    apply (Real.sqrt_lt' _).mpr
    . ring_nf; linarith
    . ring_nf; linarith
  have dd : 2 + √3 < 2 + 1.733 := by exact (Real.add_lt_add_iff_left 2).mpr this
  have h1 : (1 : ℝ) / (2 + √3) > (1 : ℝ) / (2 + 1.733) := by
    rw [gt_iff_lt]
    apply (one_div_lt_one_div ?ha ?hb).mpr dd
    . ring_nf; linarith
    . have : √3 > 0 := by refine Real.sqrt_pos_of_pos ?_; linarith
      ring_nf at this
      rw [← gt_iff_lt]
      exact Right.add_pos' zero_lt_two this
  have h2 : (1 : ℝ)  / (2 + 1.733) > 0.267 := by
    rw [gt_iff_lt]
    ring_nf; linarith
  exact gt_trans h1 h2

lemma nn' : (1 : ℝ) / (2 + √3) > 0 := by
  have : 0.267 > (0 : ℝ) := by ring_nf; linarith
  exact gt_trans nn this

lemma g239 : √239 > 15.459 := by
  apply Real.lt_sqrt_of_sq_lt; ring_nf; linarith

lemma gz239 : √239 > (0 : ℝ) := by
  apply Real.sqrt_pos_of_pos; linarith

lemma l239 : (4 : ℝ) / √239 < 0.259 := by
  refine (div_lt_iff₀' ?hc).mpr ?_
  exact gz239
  have h1 : 15.459 * 0.259 < √239 * 0.259 := by
    refine mul_lt_mul_of_pos_of_nonneg' ?h₁ ?h₂ ?c0 (le_of_lt gz239)
    exact g239
    linarith
    ring_nf;
    linarith
  have h2 : (4 : ℝ) < 15.459 * 0.259 := by
    ring_nf; linarith
  exact gt_trans h1 h2

lemma f239 : √239 - 4 / √239 > 15.2 := by
  have : √239 - 4/√239 > 15.459 - 0.259 := by
    refine sub_lt_sub ?hab ?hcd
    exact g239
    exact l239
  have g : (15.459 : ℝ) - 0.259 = 15.2 := by
    ring_nf
  exact lt_of_eq_of_lt (id (Eq.symm g)) this

lemma f239gt0 : √239 - 4 / √239 > (0 : ℝ) := by
  have : 15.2 > (0 : ℝ) := by ring_nf; linarith
  exact gt_trans f239 this

lemma lemma1 (a x : ℝ) (ha : a > 0) (hx : x ≥ a) : √x - 4 / √x ≥ √a - 4 /√a := by
  have g1 : √x - √a ≥ 0 := sub_nonneg_of_le (Real.sqrt_le_sqrt hx)
  have g2 : (1 : ℝ) + 4 / √(a * x) > 0 := by
    have : √(a * x) > 0 := Real.sqrt_pos_of_pos (mul_pos ha (gt_of_ge_of_gt hx ha))
    have h : 4 / √(a * x) > 0 := by
      rw [gt_iff_lt, div_eq_mul_inv]
      apply mul_pos (by linarith) (inv_pos_of_pos this)
    exact Right.add_pos' (by linarith) h
  have addfrac : 1 / √a - 1 / √x = (√x - √a ) / (√a * √x) := by
    rw [div_sub_div]
    . rw [one_mul, mul_one]
    . exact Real.sqrt_ne_zero'.mpr ha
    . exact Real.sqrt_ne_zero'.mpr (gt_of_ge_of_gt hx ha)
  have : √x - 4 / √x - ( √a - 4 /√a ) ≥ 0 := by
    calc
      _ = √x - √a + 4 / √a - 4 /√x := by ring
      _ = √x - √a + 4 * ( 1 / √a - 1 / √x ) := by ring
      _ = √x - √a + 4 * ( √x - √a ) / (√a * √x) := by rw [addfrac]; ring
      _ = √x - √a + 4 * ( √x - √a ) / √(a * x) := by rw [← (Real.sqrt_mul (le_of_lt ha) x)]
      _ = (√x - √a) * ( 1 + 4 / √(a * x) ) := by have : √x - √a = (√x - √a) * 1 := by ring_nf
                                                 nth_rw 1 [this]; rw [mul_comm 4]; ring_nf
      _ >= (√x - √a) * 0 := mul_le_mul_of_nonneg_left (le_of_lt g2) g1
      _ >= 0 := Left.mul_nonneg g1 (by rfl)
  exact sub_nonneg.mp this

lemma lemma2 (x : ℝ) (hx : x ≥ 120) :  √(8 * x - 8) - √(6 * x - 3) > 4 := by
  have t1 : 8 * x - 8 > 0 := by linarith
  have t2 : 6 * x - 3 > 0 := by linarith
  have g : 1 / (√(8 * x - 8) + √(6 * x - 3)) > 1 / (√(8 * x - 4)  + √(6 * x - 3)) := by
    apply one_div_lt_one_div_of_lt ?ha ?ga
    exact Right.add_pos' (Real.sqrt_pos_of_pos t1) (Real.sqrt_pos_of_pos t2)
    field_simp; linarith
  have g' :   (( 2 * x - 1) - 4) / (√(8 * x - 8) + √(6 * x - 3))
            > (( 2 * x - 1) - 4) / (√(8 * x - 4)  + √(6 * x - 3)) := by
    rw [gt_iff_lt, div_eq_mul_inv, div_eq_mul_inv]
    rw [mul_lt_mul_iff_of_pos_left]
    simp [← one_div, g]
    linarith
  have lb : (√( 2 * x - 1 ) - 4 / √(2 * x - 1)) ≥ (√239 - 4 / √239) := by
    apply lemma1 239 (2 * x - 1)
    . linarith
    . linarith
  have hsqrtf : √4 = 2 := by
    refine Real.sqrt_eq_cases.mpr ?_
    simp
    linarith
  have hsqrtsq : (√(2 * x - 1) * √(2 * x - 1)) = 2 * x - 1 := by
    refine Real.mul_self_sqrt ?_
    linarith

  have hstep : ((√(2 * x - 1))) / ((2 + √3) * √(2 * x - 1)) * √(2 * x - 1) =
    ((√(2 * x - 1))) / ((2 + √3)) := by
    calc ((√(2 * x - 1))) / ((2 + √3) * √(2 * x - 1)) * √(2 * x - 1)
      _ = √(2 * x - 1) * (1 / ((2 + √3) * √(2 * x - 1))) * √(2 * x - 1) := by ring
      _ = √(2 * x - 1) * ((1 / ((2 + √3))) * (1 / √(2 * x - 1))) * √(2 * x - 1) := by
        simp
        left
        ring
      _ = √(2 * x - 1) * ((1 / ((2 + √3))) * (√(2 * x - 1) / √(2 * x - 1))) := by ring
      _ = √(2 * x - 1) * ((1 / ((2 + √3))) * 1) := by
        simp
        rw [div_self]
        simp
        refine (Real.sqrt_ne_zero ?_).mpr ?_
        linarith
        have hgt : (2 * x - 1) > 0 := by
          linarith
        exact Ne.symm (ne_of_lt hgt)
    ring
  have hnez : √(2 * x - 1) ≠ 0 := by
            refine Real.sqrt_ne_zero'.mpr ?_
            linarith
  calc
    _ = ( (8 * x - 8) - (6 * x - 3)) / (√(8 * x - 8) + √(6 * x - 3)) := ab t1 t2
    _ = (( 2 * x - 1 ) - 4) / (√(8 * x - 8) + √(6 * x - 3)) := by field_simp; ring
    _ > (( 2 * x - 1 ) - 4) / (√(8 * x - 4) + √(6 * x - 3)) := by exact g'
    _ = (( 2 * x - 1 ) - 4) / (√(4 *(2* x - 1)) + √(3 * (2*x - 1))) := by ring_nf
    _ = (( 2 * x - 1 ) - 4) / (√(4) *√(2* x - 1) + √(3 * (2*x - 1))) := by rw [Real.sqrt_mul]; simp
    _ = (( 2 * x - 1 ) - 4) / (√(4) *√(2* x - 1) + √(3) * √((2*x - 1))) := by rw [Real.sqrt_mul]; simp
    _ = (( 2 * x - 1 ) - 4) / (2 *√(2* x - 1) + √(3) * √((2*x - 1))) := by rw [hsqrtf] -- sqrt 4 = 2
    _ = (( 2 * x - 1 ) - 4) / ((2 + √3) * √(2 * x - 1)) := by ring
    _ = (( 2 * x - 1 )) / ((2 + √3) * √(2 * x - 1)) - 4 / ((2 + √3) * √(2 * x - 1)) := by ring
    _ = ((√(2 * x - 1) * √(2 * x - 1))) / ((2 + √3) * √(2 * x - 1)) - 4 / ((2 + √3) * √(2 * x - 1)) := by rw [hsqrtsq]
    _ = ((√(2 * x - 1))) / ((2 + √3) * √(2 * x - 1)) * √(2 * x - 1) - 4 / ((2 + √3) * √(2 * x - 1)) := by ring
    _ = √(2 * x - 1) / ((2 + √3)) * (1 / √(2 * x - 1)) * √(2 * x - 1) - 4 / ((2 + √3) * √(2 * x - 1)) := by
      rw [hstep]
      simp
      apply Eq.symm
      calc √(2 * x - 1) / (2 + √3) * (√(2 * x - 1))⁻¹ * √(2 * x - 1)
        _ = √(2 * x - 1) / (2 + √3) * (√(2 * x - 1) * (√(2 * x - 1))⁻¹) := by ring
        _ = √(2 * x - 1) / (2 + √3) * 1 := by
          rw [mul_inv_cancel₀ hnez]
      simp
    _ = √(2 * x - 1) / ((2 + √3)) * (√(2 * x - 1) / √(2 * x - 1)) - 4 / ((2 + √3) * √(2 * x - 1)) := by ring
    _ = √(2 * x - 1) / ((2 + √3)) * 1 - 4 / ((2 + √3) * √(2 * x - 1)) := by
      simp
      exact div_mul_div_cancel₀' hnez (2 + √3) √(2 * x - 1)
    _ = √(2 * x - 1) * 1 / ((2 + √3)) - 4 / ((2 + √3) * √(2 * x - 1)) := by ring
    _ = 1 / ((2 + √3)) * √(2 * x - 1) - 4 * (1 / ((2 + √3) * √(2 * x - 1))) := by ring
    _ = 1 / ((2 + √3)) * √(2 * x - 1) - 4 * (1 / ((2 + √3)) *  1 / √(2 * x - 1)) := by simp; ring
    _ = 1 / ((2 + √3)) * √(2 * x - 1) - 4 * (1 / ((2 + √3))) *  1 / √(2 * x - 1) := by ring
    _ = (1 : ℝ) / (2 + √3) * (√( 2 * x - 1 ) - 4 / √(2 * x - 1)) := by ring
    _ ≥ (1 : ℝ) / (2 + √3) * (√239 - 4 / √239) := by
          refine (mul_le_mul_iff_of_pos_left ?a0).mpr lb
          exact nn'
    _ ≥ 0.267 * (√239 - 4 / √239) := by
         apply mul_le_mul_of_nonneg_right
         exact le_of_lt nn
         exact le_of_lt f239gt0
    _ ≥ 0.267 * 15.2 := by
         apply mul_le_mul_of_nonneg_left
         exact le_of_lt f239
         ring_nf; linarith
    _ > 4 := by ring_nf; linarith

def sqrt_geq_four := lemma2


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
