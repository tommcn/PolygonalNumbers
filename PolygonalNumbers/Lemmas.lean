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


/- EXTRA -/
lemma ab {a b : ℝ} (ha : a > 0) (hb : b > 0) : √a - √b = (a - b) / (√a + √b) := by
  have : (√a - √b) * (√a + √b) = a - b := by
    ring_nf; simp [Real.sq_sqrt, le_of_lt ha, le_of_lt hb]
  rw [← this, ← mul_div]
  have : √a + √b > 0 := add_pos (Real.sqrt_pos_of_pos ha) (Real.sqrt_pos_of_pos hb)
  rw [div_self (Ne.symm (ne_of_lt this)), mul_one]

lemma sqrt_mul_eq_mul_sqrt {p x y : ℝ} (hp : p > 0) (h : p * x + y ≥ 0) : √(p * x + y) = √p * √( x + 1 / p * y) := by
  suffices p * x + y = p * (x + 1 / p * y) by
    rw [← Real.sqrt_inj, Real.sqrt_mul] at this
    exact this
    repeat linarith
  ring_nf
  field_simp

lemma sqrt_sub_sqrt {a b p q x y : ℝ} (hab : a > b) (hb : b > 0) (hx : x ≥ y)
  (hy : y ≥ (b ^ 2 * p - a ^ 2 * q) / (a * b * (a - b)))
  (hayppos : a * y + p > 0) (hbyqpos : b * y + q > 0)
  : √(a * x + p) - √(b * x + q) ≥ √(a * y + p) - √(b * y + q) := by

  have ha : a > 0 := by linarith

  have haxppos : a * x + p > 0 := by
    calc
      a * x + p ≥ a * y + p := by apply add_le_add_right; exact (mul_le_mul_iff_of_pos_left ha).mpr hx
      _ > 0 := by exact hayppos

  have hbxqpos : b * x + q > 0 := by
    calc
      b * x + q ≥ b * y + q := by apply add_le_add_right; exact (mul_le_mul_iff_of_pos_left hb).mpr hx
      _ > 0 := by exact hbyqpos

  have y' : ∃ γ : ℝ, γ ≥ 0 ∧ y = γ + (b ^ 2 * p - a ^ 2 * q) / (a * b * (a - b)) := by
    use y - (b ^ 2 * p - a ^ 2 * q) / (a * b * (a - b))
    simp [hy]

  rcases y' with ⟨ γ, ⟨ hn_γ, hγ ⟩ ⟩

  have x' : ∃ δ : ℝ, δ ≥ γ ∧ x = δ + (b ^ 2 * p - a ^ 2 * q) / (a * b * (a - b))  := by
    use x - (b ^ 2 * p - a ^ 2 * q) / (a * b * (a - b))
    constructor
    . linarith
    . linarith

  rcases x' with ⟨ δ, ⟨ hn_δ, hδ ⟩  ⟩

  let θ := (b * p - a * q) / (a - b)

  let a_sub_b : a - b > 0 := sub_pos.mpr hab

  have div_mul {p q : ℝ} (hp : p > 0) (hq : q > 0) : p / (p * q) = q⁻¹ := by
    apply div_mul_cancel_left₀ _ q; exact Ne.symm (ne_of_lt hp)

  have albp : (b ^ 2 * p - a ^ 2 * q) * (a / (a * (b * (a - b)))) + p = a / b * θ := by
    have : a / (a * (b * (a - b))) = (b * (a - b))⁻¹ := by
      apply div_mul ha
      apply mul_pos hb
      exact a_sub_b
    rw [this]
    calc
      _ = (b ^ 2 * p - a ^ 2 * q) / (b * (a - b)) + p := by exact rfl
      _ = (b ^ 2 * p - a ^ 2 * q) / (b * (a - b)) + (a * b * p - b ^ 2 * p) / (b * (a - b)) := by
            suffices p = (a * b * p - b ^ 2 * p) / (b * (a - b)) by exact congrArg (HAdd.hAdd ((b ^ 2 * p - a ^ 2 * q) / (b * (a - b)))) this
            calc
              _ = p * 1 := by exact Eq.symm (MulOneClass.mul_one p)
              _ = p * ((b * (a - b)) / (b * (a - b))) := by suffices (b * (a - b)) * (b * (a - b))⁻¹ = 1 by exact congrArg (HMul.hMul p) (Eq.symm this)
                                                            have : b * (a - b) ≠ 0 := by suffices b * (a - b) > 0 by exact Ne.symm (ne_of_lt this)
                                                                                         exact mul_pos hb a_sub_b

                                                            apply mul_inv_cancel₀ this
              _ = (p * b * (a - b)) / (b * (a - b)) := by ring
              _ = _ := by ring
      _ = ((b ^ 2 * p - a ^ 2 * q) + (a * b * p - b ^ 2 * p)) / (b * (a - b)) := by apply div_add_div_same
      _ = (a * (b * p - a * q)) / (b * (a - b)) := by ring
      _ = _ := by field_simp [θ]

  have blbq : (b ^ 2 * p - a ^ 2 * q) * (b / (a * (b * (a - b)))) + q = b / a * θ := by
    have : b / (a * (b * (a - b))) = (a * (a - b))⁻¹ := by
      calc
        _ = b / (b * (a * (a - b))) := by ring
        _ = _ := by apply div_mul hb
                    apply mul_pos ha
                    exact a_sub_b
    rw [this]
    calc
      _ = (b ^ 2 * p - a ^ 2 * q) / (a * (a - b)) + q := by exact rfl
      _ = (b ^ 2 * p - a ^ 2 * q) / (a * (a - b)) + (a ^ 2 * q - a * b * q) / (a * (a - b)) := by
            suffices q = (a ^ 2 * q - a * b * q) / (a * (a - b)) by exact congrArg (HAdd.hAdd ((b ^ 2 * p - a ^ 2 * q) / (a * (a - b)))) this
            calc
              _ = q * 1 := by exact Eq.symm (MulOneClass.mul_one q)
              _ = q * ((a * (a - b)) / (a * (a - b))) := by suffices (a * (a - b)) * (a * (a - b))⁻¹ = 1 by exact congrArg (HMul.hMul q) (Eq.symm this)
                                                            have : a * (a - b) ≠ 0 := by suffices a * (a - b) > 0 by exact Ne.symm (ne_of_lt this)
                                                                                         exact mul_pos ha a_sub_b

                                                            apply mul_inv_cancel₀ this
              _ = (q * a * (a - b)) / (a * (a - b)) := by ring
              _ = _ := by ring
      _ = ((b ^ 2 * p - a ^ 2 * q) + (a ^ 2 * q - a * b * q)) / (a * (a - b)) := by apply div_add_div_same
      _ = (b * (b * p - a * q)) / (a * (a - b)) := by ring
      _ = _ := by field_simp [θ]

  have haxp : a * x + p = a / b * θ + a * δ := by
    rw [hδ]
    calc
      _ = a * δ + ((b ^ 2 * p - a ^ 2 * q) * (a / (a * (b * (a - b)))) + p) := by ring
      _ = a * δ + a / b * θ := by simp [albp]
      _ = _ := by rw [add_comm]

  have hbxq : b * x + q = b / a * θ + b * δ := by
    rw [hδ]
    calc
      _ = b * δ + ((b ^ 2 * p - a ^ 2 * q) * (b / (a * (b * (a - b)))) + q) := by ring
      _ = b * δ + b / a * θ := by simp [blbq]
      _ = _ := by rw [add_comm]

  have hayp : a * y + p = a / b * θ + a * γ := by
    rw [hγ]
    calc
      _ = a * γ + ((b ^ 2 * p - a ^ 2 * q) * (a / (a * (b * (a - b)))) + p) := by ring
      _ = a * γ + a / b * θ := by simp [albp]
      _ = _ := by rw [add_comm]

  have hbyq : b * y + q = b / a * θ + b * γ := by
    rw [hγ]
    calc
      _ = b * γ + ((b ^ 2 * p - a ^ 2 * q) * (b / (a * (b * (a - b)))) + q) := by ring
      _ = b * γ + b / a * θ := by simp [blbq]
      _ = _ := by rw [add_comm]

  suffices √(a * x + p) - √(a * y + p) ≥ √(b * x + q) - √(b * y + q) by linarith

  suffices √(a / b * θ + a * δ) - √(a / b * θ + a * γ) ≥ √(b / a * θ + b * δ) - √(b / a * θ + b * γ)
  by simp [haxp, hbxq, hayp, hbyq, this]

  have div_mul_mul {p q r : ℝ} (hq : q > 0) : (p / q) * (q * r) = p * r := by field_simp; ring

  let habyb := div_pos ha hb
  let hbbya := div_pos hb ha

  calc
    _ = ((a / b * θ + a * δ) - (a / b * θ + a * γ)) / (√(a / b * θ + a * δ) + √(a / b * θ + a * γ)) := by
          rw [ab]
          . rw [← haxp]; exact haxppos
          . rw [← hayp]; exact hayppos
    _ = (δ - γ) * a / (√(a / b * θ + a * δ) + √(a / b * θ + a * γ)) := by ring
    _ = (δ - γ) * a / (√(a / b) * (√(θ + b * δ) + √(θ + b * γ))) := by
          suffices √(a / b * θ + a * δ) + √(a / b * θ + a * γ) = √(a / b) * (√(θ + b * δ) + √(θ + b * γ)) by exact congrArg (HDiv.hDiv ((δ - γ) * a)) this
          calc
            _ = √(a / b) * (√(θ + (1 / (a / b)) * (a * δ))) + √(a / b) * (√(θ + (1 / (a / b) * (a * γ)))) := by
                  repeat rw [@sqrt_mul_eq_mul_sqrt (a / b) θ _]
                  . exact habyb
                  . rw [← hayp]; exact le_of_lt hayppos
                  . exact habyb
                  . rw [← haxp]; exact le_of_lt haxppos
            _ = √(a / b) * (√(θ + (1 / (a / b)) * (a * δ)) + √(θ + (1 / (a / b) * (a * γ)))) := by ring
            _ = √(a / b) * (√(θ + (b / a) * (a * δ)) + √(θ + (b / a) * (a * γ))) := by rw [one_div_div a b]
            _ = _ := by have t1 : (b / a) * (a * δ) = b * δ := div_mul_mul ha
                        have t2 : (b / a) * (a * γ) = b * γ := div_mul_mul ha
                        rw [t1, t2]
    _ = (δ - γ) * (a / √(a / b)) / (√(θ + b * δ) + √(θ + b * γ)) := by field_simp; ring
    _ = (δ - γ) * (b / √(b / a)) / (√(θ + b * δ) + √(θ + b * γ)) := by
          suffices  b / √(b / a) = a / √(a / b) by exact congrFun (congrArg HDiv.hDiv (congrArg (HMul.hMul (δ - γ)) (id (Eq.symm this)))) (√(θ + b * δ) + √(θ + b * γ))
          have {p q : ℝ} (hp : p > 0) (hq : q > 0) : q / √(q / p) = √p * √q := by
            calc
              _ = √p * q / √q := by field_simp; ring
              _ = √p * √q := by have : q = √q * √q := by rw [Real.mul_self_sqrt (le_of_lt hq)];
                                nth_rewrite 1 [this]; field_simp; nth_rewrite 1 [this]; rw [mul_assoc]
          let lhs := this ha hb
          let rhs := this hb ha
          rw [lhs, rhs, mul_comm]
    _ = (δ - γ) * b / (√(b / a) * (√(θ + b * δ) + √(θ + b * γ))) := by field_simp; ring
    _ ≥ (δ - γ) * b / (√(b / a) * (√(θ + a * δ) + √(θ + a * γ))) := by
          have sqrtbya : √( b / a) > 0 := by exact Real.sqrt_pos_of_pos hbbya
          suffices √(b / a) * (√(θ + a * δ) + √(θ + a * γ)) ≥ √(b / a) * (√(θ + b * δ) + √(θ + b * γ)) by
            refine div_le_div_of_nonneg_left ?_ ?_ this
            . exact (mul_nonneg_iff_of_pos_right hb).mpr (sub_nonneg_of_le hn_δ)
            . rw [← gt_iff_lt]
              have t1 : √(θ + b * γ) > 0 := by
                apply Real.sqrt_pos_of_pos
                calc
                  θ + b * γ = b / a * a / b * θ + (b / a * a) * γ := by field_simp
                  _ = b / a * (a / b * θ + (a * γ)):= by ring
                  _ = (b / a) * (a * y + p) := by rw [hayp]
                  _ > 0 := by exact mul_pos hbbya hayppos
              have t2 : √(θ + b * δ) > 0 := by
                suffices √(θ + b * δ) ≥ √(θ + b * γ) by exact gt_of_ge_of_gt this t1
                exact Real.sqrt_le_sqrt (add_le_add_left ((mul_le_mul_iff_of_pos_left hb).mpr hn_δ) θ)
              exact mul_pos sqrtbya (add_pos t2 t1)
          have t1 : √(θ + a * δ) ≥ √(θ + b * δ) := by apply Real.sqrt_le_sqrt
                                                      apply add_le_add_left
                                                      exact mul_le_mul_of_nonneg_right (le_of_lt hab) (Preorder.le_trans 0 γ δ hn_γ hn_δ)
          have t2 : √(θ + a * γ) ≥ √(θ + b * γ) := by apply Real.sqrt_le_sqrt
                                                      apply add_le_add_left
                                                      exact mul_le_mul_of_nonneg_right (le_of_lt hab) hn_γ
          exact (mul_le_mul_iff_of_pos_left sqrtbya).mpr (add_le_add t1 t2)
    _ = (δ - γ) * b / (√(b / a * θ + b * δ) + √(b / a * θ + b * γ)) := by
          suffices √(b / a * θ + b * δ) + √(b / a * θ + b * γ) = √(b / a) * (√(θ + a * δ) + √(θ + a * γ)) by exact congrArg (HDiv.hDiv ((δ - γ) * b)) (id (Eq.symm this))
          calc
            _ = √(b / a) * (√(θ + (1 / (b / a)) * (b * δ))) + √(b / a) * (√(θ + (1 / (b / a) * (b * γ)))) := by
                  repeat rw [@sqrt_mul_eq_mul_sqrt (b / a) θ _]
                  . exact hbbya
                  . rw [← hbyq]; exact le_of_lt hbyqpos
                  . exact hbbya
                  . rw [← hbxq]; exact le_of_lt hbxqpos
            _ = √(b / a) * (√(θ + (1 / (b / a)) * (b * δ)) + √(θ + (1 / (b / a) * (b * γ)))) := by ring
            _ = √(b / a) * (√(θ + (a / b) * (b * δ)) + √(θ + (a / b) * (b * γ))) := by rw [one_div_div b a]
            _ = _ := by have t1 : (a / b) * (b * δ) = a * δ := div_mul_mul hb
                        have t2 : (a / b) * (b * γ) = a * γ := div_mul_mul hb
                        rw [t1, t2]
    _ = (δ - γ) * b / (√(b / a * θ + b * δ) + √(b / a * θ + b * γ)) := by ring
    _ = ((b / a * θ + b * δ) - (b / a * θ + b * γ)) / (√(b / a * θ + b * δ) + √(b / a * θ + b * γ)) := by ring
    _ = _ := by rw [← ab]
                . rw [← hbxq]; exact hbxqpos
                . rw [← hbyq]; exact hbyqpos


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

lemma cor2 (x : ℝ) (hx : x ≥ 53) : (5 : ℝ) / 4 + √(8 * x - 4) - √(6 * x - ((15 : ℝ) / 4)) > 4.002 := by
  apply (Real.add_lt_add_iff_left (-5 / 4)).mp
  rw [← gt_iff_lt]
  have : √(8 * x + -4) - √(6 * x + - (15 / 4)) ≥ √(8 * 53 + -4) - √(6 * 53 + -(15 / 4)) := by
    apply @sqrt_sub_sqrt 8 6 (-4) (- ((15 : ℝ)/4)) x 53 (by norm_num) (by norm_num) hx
    repeat norm_num
  calc
   _ = √(8 * x - 4) - √(6 * x -(15 / 4)) := by ring
   _ = √(8 * x + -4) - √(6 * x + -(15 / 4)) := by rw [sub_eq_add_neg (8 * x) _, sub_eq_add_neg (6 * x)];
   _ ≥ √(8 * 53 + -4) - √(6 * 53 + -(15 / 4)) := by exact this
   _ = √420 - √(1257 / 4) := by norm_num
   _ > - (5 : ℝ) / 4 + 4.002 := by have t1 : √420 > 20.49 := Real.lt_sqrt_of_sq_lt (by norm_num)
                                   have t2 : √(1257 / 4) < 17.73 := by rw [Real.sqrt_lt]; repeat norm_num
                                   have t3 : √420 - √(1257 / 4) > 20.49 - 17.73 := sub_lt_sub t1 t2
                                   have t4 : 20.49 - 17.73 > - (5 : ℝ) / 4 + 4.002 := by norm_num
                                   exact gt_trans t3 t4

lemma cor3 (x : ℝ) (hx : x ≥ 159) : (7 : ℝ) / 6 + √(8 * x + ((4 : ℝ) / 9)) - √(6 * x - ((15 : ℝ) / 4)) > 6.002 := by
  apply (Real.add_lt_add_iff_left (-7 / 6)).mp
  rw [← gt_iff_lt]
  have : √(8 * x + (4 : ℝ) / 9) - √(6 * x + - (15 / 4)) ≥ √(8 * 159 + (4 : ℝ)/ 9) - √(6 * 159 + -(15 / 4)) := by
    apply @sqrt_sub_sqrt 8 6 ((4 : ℝ) / 9) (- ((15 : ℝ)/4)) x 159 (by norm_num) (by norm_num) hx
    repeat norm_num
  calc
   _ = √(8 * x + 4 / 9) - √(6 * x -(15 / 4)) := by ring
   _ = √(8 * x + 4 / 9) - √(6 * x + -(15 / 4)) := by rw [sub_eq_add_neg (6 * x)];
   _ ≥ √(8 * 159 + 4 / 9) - √(6 * 159 + -(15 / 4)) := by exact this
   _ = √(11452 / 9) - √(3801 / 4) := by norm_num
   _ > - (7 : ℝ) / 6 + 6.002 := by have t1 : √(11452 / 9) > 35.67 := Real.lt_sqrt_of_sq_lt (by norm_num)
                                   have t2 : √(3801 / 4) < 30.83 := by rw [Real.sqrt_lt]; repeat norm_num
                                   have t3 : √(11452 / 9) - √(3801 / 4) > 35.67 - 30.83 := sub_lt_sub t1 t2
                                   have t4 : 35.67 - 30.83 > - (7 : ℝ) / 6 + 6.002 := by norm_num
                                   exact gt_trans t3 t4

noncomputable
def I_ub (n m : ℤ) : ℝ :=
  (2 : ℝ) * (↑1 - 2 / m) + √(↑4 * (↑1 - 2 / m) ^ 2 + ↑8 * (n - (m - 3)) / m)

noncomputable
def I_lb (n m : ℤ) : ℝ :=
  ((1 : ℝ) / 2 - ↑3 / m) + √(((1 : ℝ) / 2 - ↑3 / m) ^ 2 + (↑6 * n / m - 4))


-- 3.3
lemma lemma4 {n m : ℤ} (hm : m ≥ 3)
  :   ((m ≥ 4 ∧ n ≥ 53 * m) → I_ub n m - I_lb n m > (4.002 : ℝ))
    ∧ ((m = 3 ∧ n ≥ 159 * m) → I_ub n m - I_lb n m > (6.002 : ℝ)) := by

  dsimp [I_ub, I_lb]
  let x := (n : ℝ) / (m : ℝ)
  have hx : x = (n : ℝ) / (m : ℝ) := by exact rfl

  constructor
  . rintro ⟨ hm', hnm ⟩
    have t1 :  √(8 * ↑n / ↑m + 4 * (1 - 2 / ↑m) ^ 2 - 8 * (↑m - 3) / ↑m) ≥ √(8 * x - 4) := by
      apply Real.sqrt_le_sqrt
      rw [← ge_iff_le]
      calc
        _ = (8 : ℝ) * x + 4 - 16 / ↑m + 16 / ↑m ^ 2 - 8 * (↑m - 3)/ ↑m := by ring
        _ = (8 : ℝ) * x + 4 - 16 / ↑m + 16 / ↑m ^ 2 - 8 * (↑m - 3)/ ↑m := by simp
        _ = (8 : ℝ) * x + 4 + 8 / ↑m + 16 / ↑m ^ 2 - 8 * (↑m / ↑m) := by ring
        _ = (8 : ℝ) * x + 4 + 8 / ↑m + 16 / ↑m ^ 2 - (8 * 1) := by have : (m : ℝ) / ↑m = 1 := by apply mul_inv_cancel₀; simp; linarith
                                                                   rw [this]
        _ = (8 : ℝ) * x - 4 + (8 / ↑m + 16 / ↑m ^ 2) := by ring
        _ ≥ _ := by suffices (8 : ℝ) / ↑m + 16 / ↑m ^ 2 ≥ 0 by exact (le_add_iff_nonneg_right _).mpr this
                    have g1 : (8 : ℝ) / ↑m  ≥ 0 := by apply div_nonneg; norm_num; norm_cast; linarith
                    have g2 : (16 : ℝ) / ↑m ^ 2 ≥ 0 := by apply div_nonneg; norm_num; norm_cast; exact sq_nonneg m
                    exact add_nonneg g1 g2

    have t2 :  √(6 * ↑n / ↑m + (1 / 2 - 3 / ↑m) ^ 2 - 4) ≤ √(6 * x - 15 / 4) := by
      apply Real.sqrt_le_sqrt
      calc
        _ = (6 * x + (1 / 2 - 3 / ↑m) ^ 2 - 4) := by ring
        _ = 6 * x - 15 / 4 - (3 / ↑m * (1 - 3 / ↑m)) := by ring
        _ ≤ 6 * x - 15 / 4 - 0 := by suffices (0 : ℝ) ≤ 3 / ↑m * (1 - 3 / ↑m) by exact tsub_le_tsub_left this _
                                     field_simp
                                     apply div_nonneg
                                     norm_cast; linarith;
                                     exact mul_self_nonneg (m : ℝ)
        _ = _ := by rw [sub_zero]

    calc
      _ = - ((1 : ℝ) / ↑m) + (3 : ℝ) / 2 + (√(8 * ↑n / ↑m + 4 * (1 - 2 / ↑m) ^ 2 - 8 * (↑m - 3) / ↑m)
          - √(6 * ↑n / ↑m + (1 / 2 - 3 / ↑m) ^ 2 - 4)) := by ring_nf
      _ ≥ - ((1 : ℝ) / ↑m) + (3 : ℝ) / 2 + (√(8 * x - 4) - √(6 * x - 15 / 4)) := by
                suffices   √(8 * ↑n / ↑m + 4 * (1 - 2 / ↑m) ^ 2 - 8 * (↑m - 3) / ↑m) - √(6 * ↑n / ↑m + (1 / 2 - 3 / ↑m) ^ 2 - 4)
                         ≥ √(8 * x - 4) - √(6 * x - 15 / 4) by apply (add_le_add_iff_left _).mpr this
                exact tsub_le_tsub t1 t2
      _ = (3 : ℝ) / 2 + (√(8 * x - 4) - √(6 * x - 15 / 4)) - ((1 : ℝ) / ↑m) := by ring
      _ ≥ (3 : ℝ) / 2 + (√(8 * x - 4) - √(6 * x - 15 / 4)) - ((1 : ℝ) / 4) := by
                suffices (1 : ℝ) / ↑m  ≤ ((1 : ℝ) / 4) by exact tsub_le_tsub_left this _
                rw [one_div_le_one_div]
                . norm_cast
                . norm_cast; linarith
                . norm_num
      _ = (5 : ℝ) / 4 + √(8 * x - 4) - √(6 * x - 15 / 4) := by ring
      _ > _ := by refine cor2 x ?hx; rw [hx]
                  have : (n : ℝ) ≥ 53 * (m : ℝ) := by norm_cast
                  rw [ge_iff_le]
                  calc
                    _ = 53 * 1 := by norm_num
                    _ = 53 * ((m : ℝ) * (m : ℝ)⁻¹) := by rw [mul_inv_cancel₀ _]; simp; linarith
                    _ = 53 * (m : ℝ) * (m : ℝ)⁻¹ := by rw [mul_assoc]
                    _ ≤ n * (m : ℝ)⁻¹ := by apply mul_le_mul_of_nonneg_right this
                                            simp; linarith
  . rintro ⟨ hm', hnm ⟩
    have t1 :   4 * (1 - 2 / ↑m) ^ 2 + 8 * ↑n / ↑m
              = (8 : ℝ) * ((n : ℝ)/ m) + 4 * (1 - 2 / ↑m) ^ 2 := by ring
    have t2 :   (1 / 2 - 3 / ↑m) ^ 2 + ((6 : ℝ) * ↑n / ↑m - (4 : ℝ))
              = (6 : ℝ) * (↑n / ↑m) + (1 / 2 - 3 / ↑m) ^ 2 - 4 := by ring
    have : (m : ℝ) - 3 = 0 := by norm_cast; linarith
    rw [this]
    have : (n : ℝ) - 0 = n := by norm_cast; linarith
    rw [this, t1, t2]
    rw [← hx]
    rw [hm']
    norm_num
    rw [← gt_iff_lt]
    calc
      _ = 2 / 3 + √(8 * x + 4 / 9) + 1 / 2 - √(6 * x + 1 / 4 - 4) := by ring
      _ = (7 : ℝ) / 6 + √(8 * x + 4 / 9) - √(6 * x - 15 / 4) := by ring_nf
      _ > 6.002 := by refine cor3 x ?_; rw [hx]
                      have : (n : ℝ) ≥ 159 * (m : ℝ) := by norm_cast
                      rw [ge_iff_le]
                      calc
                        _ = 159 * 1 := by norm_num
                        _ = 159 * ((m : ℝ) * (m : ℝ)⁻¹) := by rw [mul_inv_cancel₀ _]; simp [hm']
                        _ = 159 * (m : ℝ) * (m : ℝ)⁻¹ := by rw [mul_assoc]
                        _ ≤ n * (m : ℝ)⁻¹ := by apply mul_le_mul_of_nonneg_right this
                                                rw [hm']; norm_num
      _ = _ := by norm_num


lemma sqrt_sq_add_pos_gt_abs_self (a b : ℝ) (hb : b > 0): √(a ^ 2 + b) > |a| := by
  simp [Real.lt_sqrt, sq_abs, abs_nonneg, hb]

lemma qub (x p c : ℝ) (hc : c > 0) (hxlb : 0 ≤ x) (hxub : x < p / 2 + √((p / 2) ^ 2 + c))
  : x ^ 2 - p * x - c < 0 := by
  by_cases xzero : x ≤ (0 : ℝ)
  . have : x = 0 := by linarith
    simp [xzero, hxlb, this, hc]
  . calc
      _ = -c + x * (x - p) := by ring
      _ < -c + ((p / 2) + √((p / 2) ^ 2 + c)) * ((p / 2 + √((p / 2) ^ 2 + c)) - p) := by
          have : x * (x - p) < (p / 2 + √((p / 2) ^ 2 + c)) * ((p / 2 + √((p / 2) ^ 2 + c)) - p) := by
            let g := sqrt_sq_add_pos_gt_abs_self (p / 2) c hc
            let g' := gt_of_gt_of_ge g (le_abs_self (p / 2))
            apply mul_lt_mul_of_pos hxub (sub_lt_sub_right hxub p) (lt_of_not_ge xzero)
            linarith
          apply (add_lt_add_iff_left (-c)).mpr this
      _ = -c + (- (p / 2) ^ 2  + (√((p / 2) ^ 2 + c)) ^ 2 ) := by ring_nf
      _ = -c + (- (p / 2) ^ 2  + ((p / 2) ^ 2 + c) ) := by rw [Real.sq_sqrt (add_nonneg (sq_nonneg (p / 2)) (le_of_lt hc))]
      _ = 0 := by ring

lemma qlb (x p c : ℝ) (hc : c > 0) (hxlb : x > p / 2 + √((p / 2) ^ 2 + c))
  : x ^ 2 - p * x - c > 0 := by
  calc
    _ = -c + x * (x - p) := by ring
    _ > -c + (p / 2 + √((p / 2) ^ 2 + c)) * ((p / 2 + √((p / 2) ^ 2 + c)) - p) := by
        have : x * (x - p) > (p / 2 + √((p / 2) ^ 2 + c)) * ((p / 2) + √((p / 2) ^ 2 + c) - p) := by
          let g := sqrt_sq_add_pos_gt_abs_self (p / 2) c hc
          let g' := gt_of_gt_of_ge g (le_abs_self (p / 2))
          let g'' := gt_of_gt_of_ge g (neg_le_abs (p / 2))
          apply mul_lt_mul_of_pos hxlb (sub_lt_sub_right hxlb p)
          . exact neg_lt_iff_pos_add'.mp g''
          . have : x > p := by
              calc
              _ > p / 2 + √((p / 2) ^ 2 + c) := by exact hxlb
              _ > p / 2 + p / 2 := by apply add_lt_add_left g'
              _ ≥ p := by linarith
            rw [sub_pos]
            exact this
        exact (add_lt_add_iff_left (-c)).mpr this
    _ = -c + (- (p / 2) ^ 2  + (√((p / 2) ^ 2 + c)) ^ 2 ) := by ring_nf
    _ = -c + (- (p / 2) ^ 2  + ((p / 2) ^ 2 + c) ) := by rw [Real.sq_sqrt (add_nonneg (sq_nonneg (p / 2)) (le_of_lt hc))]
    _ = 0 := by ring

lemma I_lb_pos (n m b r : ℤ) (hr : 0 ≤ r ∧ r ≤ m - 3) (hblb : b > I_lb n m) (hm : 3 ≤ m) (hmn : 2 * m ≤ n) : (b : ℝ) > 0 := by

  have hblb' : √((1 / 2 - 3 / ↑m) ^ 2 + (6 * (↑n - ↑r) / ↑m - 4)) ≤ √((1 / 2 - 3 / ↑m) ^ 2 + (6 * ↑n / ↑m - 4)) := by
      apply Real.sqrt_le_sqrt
      suffices (6 : ℝ) * (↑n - ↑r) / ↑m - 4 ≤ 6 * ↑n / ↑m - 4 by exact (add_le_add_iff_left _).mpr this
      suffices (6 : ℝ) * (↑n - ↑r) / ↑m ≤ 6 * ↑n / ↑m  by exact tsub_le_tsub_right this 4
      suffices (6 : ℝ) * (↑n - ↑r) ≤ 6 * ↑n by refine div_le_div_of_nonneg_right this ?_; norm_cast; linarith
      norm_cast; linarith
  calc
    _ > ((1 : ℝ) / 2 - ↑3 / m) + √(((1 : ℝ) / 2 - ↑3 / m) ^ 2 + (↑6 * (n - r) / m - 4)) := by dsimp [I_lb] at hblb; exact add_lt_of_add_lt_left hblb hblb'
    _ > ((1 : ℝ) / 2 - ↑3 / m) + |(1 : ℝ) / 2 - ↑3 / m| := by
            have : √(((1 : ℝ) / 2 - ↑3 / m) ^ 2 + (↑6 * (n - r) / m - 4)) > |(1 : ℝ) / 2 - ↑3 / m| := by
             apply sqrt_sq_add_pos_gt_abs_self; field_simp; norm_cast; linarith
            exact (Real.add_lt_add_iff_left ((1 : ℝ) / 2 - 3 / ↑m)).mpr this
    _ ≥ 0 := by let g := add_abs_nonneg ((1 : ℝ) / 2 - 3 / ↑m)
                exact g

lemma main {n m b r : ℤ} (hr : 0 ≤ r ∧ r ≤ m - 3) (hm : 3 ≤ m) (hmn : 2 * m ≤ n)
    (hblb : b > I_lb n m) (hbub : b < I_ub n m)
    (hnbr : m ∣ n - b - r) (hob : Odd b)
  : ∃ a : ℤ, Odd a ∧ b ^ 2 - 4 * a < 0 ∧ b ^ 2 + 2 * b + 4 - 3 * a > 0 ∧ (a : ℚ) = 2 * ((n : ℚ) - b - r) / m + b := by

  have hblb' : √((1 / 2 - 3 / ↑m) ^ 2 + (6 * (↑n - ↑r) / ↑m - 4)) ≤ √((1 / 2 - 3 / ↑m) ^ 2 + (6 * ↑n / ↑m - 4)) := by
    apply Real.sqrt_le_sqrt
    suffices (6 : ℝ) * (↑n - ↑r) / ↑m - 4 ≤ 6 * ↑n / ↑m - 4 by exact (add_le_add_iff_left _).mpr this
    suffices (6 : ℝ) * (↑n - ↑r) / ↑m ≤ 6 * ↑n / ↑m  by exact tsub_le_tsub_right this 4
    suffices (6 : ℝ) * (↑n - ↑r) ≤ 6 * ↑n by refine div_le_div_of_nonneg_right this ?_; norm_cast; linarith
    norm_cast; linarith

  have bpos : ↑b > (0 : ℝ) := by exact I_lb_pos n m b r hr hblb hm hmn

  rcases hnbr with ⟨ k, hk ⟩
  let a := 2 * k + b
  have hao : Odd a := by
    refine Int.odd_add'.mpr ?_
    constructor
    . intro _; exact even_two_mul k
    . intro _; exact hob
  have hk' : (a : ℝ) = 2 * ( (n : ℝ) - b - r ) / m + b:= by
    simp [a]
    have : (2 : ℝ) * k = 2 * (n - b - r) / m := by
      calc
        _ = (2 : ℝ) * k * 1 := by rw [mul_one]
        _ = (2 : ℝ) * k * (m / m) := by rw [div_self]; norm_cast; linarith
        _ = (2 : ℝ) * ( m * k ) / m := by ring
        _ = (2 : ℝ) * ( (m * k ): ℤ) / m := by norm_cast
        _ = (2 : ℝ) * ( (n - b - r) : ℤ ) / m := by rw [← hk]
        _ = _ := by norm_cast
    rw [this]
  use a
  and_intros
  . exact hao
  . have g : ( b ^ 2 - (4 : ℝ) * a ) < 0 := by
      rw [hk']
      calc
        _ = b ^ 2 - ( (4 : ℝ) * (↑1 - 2 / m)) * b - (↑8 * ((n : ℝ) - r) / m) := by ring
        _ < 0 := by
          let g := qub b ((4 : ℝ)* (↑1 - 2/m)) ((8 : ℝ) * (( n : ℝ) - r) / m)
          apply g
          . field_simp; linarith
          . exact le_of_lt bpos
          . have g' : (4 : ℝ) * ( 1 - 2 / m) / 2 = (2 : ℝ) * (1 - 2 / m) := by ring
            have g'': (4 : ℝ) * ( 1 - 2 / m) ^ 2 = ((2 : ℝ) * (1 - 2 / m)) ^ 2 := by ring
            rw [g', ← g'']
            dsimp [I_ub] at hbub
            suffices √(4 * (1 - 2 / ↑m) ^ 2 + 8 * (↑n - (↑m - 3)) / ↑m) ≤ √(4 * (1 - 2 / ↑m) ^ 2 + 8 * (↑n - ↑r) / ↑m) by exact lt_add_of_lt_add_left hbub this
            apply Real.sqrt_le_sqrt
            suffices (8 : ℝ) * (↑n - (↑m - 3)) / ↑m ≤ 8 * (↑n - ↑r) / ↑m by exact (add_le_add_iff_left _).mpr this
            suffices (8 : ℝ) * (↑n - (↑m - 3)) ≤ 8 * (↑n - ↑r) by refine div_le_div_of_nonneg_right this ?_; norm_cast; linarith
            norm_cast; linarith
    have   : ( b ^ 2 - (4 : ℤ)  * a ) < 0 := by norm_cast at g
    exact this
  . have g : ( b ^ 2 + 2 * b + 4 - (3 : ℝ) * a ) > 0 := by
      rw [hk']
      calc
        _ = b ^ 2 - ((1 : ℝ) - ↑6 / m) * b - (( ↑6 * (↑n - r) / m) - ↑4) := by ring
        _ > 0 := by
          let g := qlb b ((1 : ℝ) - ↑6 / m) ((6 : ℝ) * (↑n - r) / m - ↑4)
          apply g
          . field_simp; norm_cast; linarith
          . have : ((1 : ℝ) - 6 / ↑m) / 2 = ((1 : ℝ) / 2 - 3 / ↑m) := by field_simp; norm_cast; ring
            rw [this]
            dsimp [I_lb] at hblb
            suffices √((1 / 2 - 3 / ↑m) ^ 2 + (6 * (↑n - ↑r) / ↑m - 4)) ≤ √((1 / 2 - 3 / ↑m) ^ 2 + (6 * ↑n / ↑m - 4)) by exact add_lt_of_add_lt_left hblb hblb'
            apply Real.sqrt_le_sqrt
            suffices (6 : ℝ) * (↑n - ↑r) / ↑m - 4 ≤ 6 * ↑n / ↑m - 4 by exact (add_le_add_iff_left _).mpr this
            suffices (6 : ℝ) * (↑n - ↑r) / ↑m ≤ 6 * ↑n / ↑m  by exact tsub_le_tsub_right this 4
            suffices (6 : ℝ) * (↑n - ↑r) ≤ 6 * ↑n by refine div_le_div_of_nonneg_right this ?_; norm_cast; linarith
            norm_cast; linarith
    have   : ( b ^ 2 + 2 * b + 4 - 3 * a ) > 0 := by norm_cast at g
    exact this
  . norm_cast at hk'
    norm_cast


lemma mod_m_congr (b₁ b₂ : ℤ) (hcon : b₂ = b₁ + 2) (n : ℤ) (m : ℕ) (hm : m ≥ 4)
  : ∃ r : ℤ, 0 ≤ r ∧ r ≤ m-3 ∧ (∃ b ∈ [b₁, b₂], n ≡ (b + r : ℤ) [ZMOD m]) := by
  let r' := (n - b₁) % m
  have rnonneg : r' ≥ 0 := by
    refine Int.emod_nonneg (n - ↑b₁) ?_
    simp
    exact Nat.not_eq_zero_of_lt hm
  have : r' + 3 ≤ m ∨ r' + 3 > m := by exact le_or_lt (r' + 3) m
  rcases this with  hl | hr
  . use r'
    constructor
    . exact rnonneg
    . constructor
      . exact Int.le_sub_right_of_add_le hl
      . use b₁
        simp
        have : n - b₁ ≡ r' [ZMOD m] := by exact Int.ModEq.symm (Int.mod_modEq (n - b₁) ↑m)
        have : b₁ + (n - b₁) ≡ b₁ + r' [ZMOD m] := by exact Int.ModEq.add rfl this
        simp at this
        exact this
  . use r' - 2
    have foo : r' ≥ ↑m - 2 := by linarith
    constructor
    . linarith
    . constructor
      . norm_num
        ring_nf
        rw [add_comm, ← sub_eq_add_neg]
        change (n - b₁) % m ≤ m -1
        refine Int.le_sub_one_of_lt ?h.right.left.H
        refine Int.emod_lt_of_pos (n-b₁) ?H
        linarith
      . use b₂
        simp
        have : n - b₁ ≡ (n - b₁) % m [ZMOD m] := by exact Int.ModEq.symm (Int.mod_modEq (n - b₁) ↑m)
        have bar : b₁ + (n - b₁) ≡ b₁ + (n - b₁) % m [ZMOD m] := by exact Int.ModEq.add rfl this
        simp at bar
        change n ≡ b₂ + (r'- 2) [ZMOD ↑m]
        rw [hcon]
        ring_nf
        exact bar


theorem Real.exists_ceil (x : ℝ) : ∃ (lb : ℤ), ↑lb ≥ x ∧ ∀ (z : ℤ), ↑z ≥ x → z ≥ lb := by
  rcases Real.exists_floor (-x) with ⟨ negub, ⟨ hl, hr ⟩  ⟩
  use -negub
  constructor
  . simp; linarith
  . intro z
    let hrnegz := hr (-z)
    simp at hrnegz
    intro h
    exact Int.neg_le_of_neg_le (hrnegz h)

theorem Real.exists_ceil' (x : ℝ) : ∃ (lb : ℤ), ↑lb ≥ x ∧ x > lb - 1 := by
  rcases Real.exists_ceil x with ⟨ lb , hlb ⟩
  use lb
  constructor
  . exact hlb.left
  . by_contra h
    simp at h
    let con := hlb.right (lb - 1)
    simp [h] at con


lemma blist (p q : ℝ) (k : ℕ+) (h : q - p ≥ 2 * k)
  : ∃ b : List ℤ,
      b.length = k
    ∧ (∃ m : ℤ, ∀ i : Fin b.length, b.get i = 2 * (m + i) + 1 ∧ b.get i ≥ p ∧ b.get i ≤ q) := by
  rcases Real.exists_ceil' p with ⟨ lb, ⟨ hb1, hb2 ⟩  ⟩

  have kpos : ∃ r : ℕ, k = r + 1 := by refine Nat.exists_eq_add_one.mpr ?_; exact k.property
  rcases kpos with ⟨ r, hr ⟩
  rw [hr] at h

  let lk := List.range k
  have lklen : lk.length = k := by simp [lk]
  rcases Int.even_or_odd lb with g | g
  . let f := fun m : ℕ ↦ lb + 1 + 2 * m
    let mf := List.length_map lk f
    use List.map f lk
    constructor
    . rw [mf]; exact lklen
    . rcases g with ⟨ m, hm ⟩
      use m
      intro i
      simp [f, lk, hm]; ring_nf; simp
      constructor
      . calc
          _ ≤ (lb : ℝ) := by exact hb1
          _ = m + m := by rw [hm]; norm_cast
          _ ≤ 2 * m + (i : ℝ) * 2 := by ring_nf; apply le_add_of_nonneg_right; linarith
          _ ≤ _ := by ring_nf; linarith
      . calc
          _ = ((m + m) + 1 + (↑↑i * 2) : ℝ) := by ring_nf
          _ = (lb + 1 + ↑↑i * 2) := by rw [hm]; norm_cast
          _ ≤ (lb + 1 + ↑↑r * 2) := by simp [Fin.is_lt i]; omega
          _ ≤ (p + 1 + 1 + ↑↑r * 2) := by simp [le_of_lt (lt_add_of_tsub_lt_right hb2)]
          _ = (p + (↑↑r + 1) * 2) := by ring_nf
          _ ≤ q := by simp at h; linarith
  . let f := fun m : ℕ ↦ lb + 2 * m
    let mf := List.length_map lk f
    use List.map f lk
    constructor
    . rw [mf]; exact lklen
    . rcases g with ⟨ m, hm ⟩
      use m
      intro i
      simp [f, lk, hm]; ring_nf; simp
      constructor
      . calc
          _ ≤ (lb : ℝ) := by exact hb1
          _ = 2 * m + 1 := by rw [hm]; norm_cast
          _ ≤ 2 * m + 1 + (i : ℝ) * 2 := by apply le_add_of_nonneg_right; linarith
          _ = _ := by ring_nf
      . calc
          _ = (2 * m + 1 + (↑↑i * 2) : ℝ) := by ring_nf
          _ = (lb + ↑↑i * 2) := by rw [hm]; norm_cast
          _ ≤ (lb + ↑↑r * 2) := by simp [Fin.is_lt i]; omega
          _ ≤ (p + 1 + ↑↑r * 2) := by simp [le_of_lt (lt_add_of_tsub_lt_right hb2)]
          _ ≤ q := by simp at h; linarith


lemma res_b (b₁ b₂ b₃: ℤ) (h12 : b₂ = b₁ + 2) (h23 : b₃ = b₂ + 2) (n : ℤ)
  : 3 ∣ n - b₁ ∨ 3 ∣ n - b₂ ∨ 3 ∣ n - b₃ := by
  mod_cases h : n % 3
  . mod_cases hb : b₁ % 3
    . left; exact Int.ModEq.dvd (Int.ModEq.trans hb (id (Int.ModEq.symm h)))
    . right; left; rw [h12]; refine Int.ModEq.dvd ?_
      calc
        _ ≡ 1 + 2 [ZMOD 3] := by exact Int.ModEq.add hb rfl
        _ ≡ n [ZMOD 3] := by exact id (Int.ModEq.symm h)
    . right; right; rw [h23, h12]; refine Int.ModEq.dvd ?_
      calc
        _ = b₁ + (2 + 2) := by ring
        _ ≡ 2 + (2 + 2) [ZMOD 3] := by exact Int.ModEq.add hb rfl
        _ ≡ n [ZMOD 3] := by exact id (Int.ModEq.symm h)
  . mod_cases hb : b₁ % 3
    . right; right; rw [h23, h12]; refine Int.ModEq.dvd ?_
      calc
        _ = b₁ + (2 + 2) := by ring
        _ ≡ 0 + (2 + 2) [ZMOD 3] := by exact Int.ModEq.add hb rfl
        _ ≡ n [ZMOD 3] := by exact id (Int.ModEq.symm h)
    . left; exact Int.ModEq.dvd (Int.ModEq.trans hb (id (Int.ModEq.symm h)))
    . right; left; rw [h12]; refine Int.ModEq.dvd ?_
      calc
        _ ≡ 2 + 2 [ZMOD 3] := by exact Int.ModEq.add hb rfl
        _ ≡ n [ZMOD 3] := by exact id (Int.ModEq.symm h)
  . mod_cases hb : b₁ % 3
    . right; left; refine Int.ModEq.dvd ?_; rw [h12]
      calc
        _ ≡ 0 + 2 [ZMOD 3] := by exact Int.ModEq.add hb rfl
        _ ≡ n [ZMOD 3] := by exact id (Int.ModEq.symm h)
    . right; right; rw [h23, h12]; refine Int.ModEq.dvd ?_
      calc
        _ = b₁ + (2 + 2) := by ring
        _ ≡ 1 + (2 + 2) [ZMOD 3] := by exact Int.ModEq.add hb rfl
        _ ≡ n [ZMOD 3] := by exact id (Int.ModEq.symm h)
    . left; exact Int.ModEq.dvd (Int.ModEq.trans hb (id (Int.ModEq.symm h)))

lemma res_b_r (b₁ b₂ : ℤ) (hcon : b₂ = b₁ + 2) (n m : ℤ) (hm : m ≥ 4)
  : ∃ r : ℤ, 0 ≤ r ∧ r ≤ m-3 ∧ (m ∣ n - b₁ - r ∨ m ∣ n - b₂ - r) := by
  let r' := (n - b₁) % m
  have rnonneg : r' ≥ 0 := Int.emod_nonneg (n - b₁) (by linarith)
  have : r' + 3 ≤ m ∨ r' + 3 > m := by exact le_or_lt (r' + 3) m
  rcases this with  hl | hr
  . use r'
    constructor
    . exact rnonneg
    . constructor
      . exact Int.le_sub_right_of_add_le hl
      . left; exact Int.dvd_sub_of_emod_eq rfl
  . use r' - 2
    constructor
    . linarith
    . constructor
      . norm_num
        ring_nf
        rw [add_comm, ← sub_eq_add_neg]
        change (n - b₁) % m ≤ m -1
        refine Int.le_sub_one_of_lt ?h.right.left.H
        refine Int.emod_lt_of_pos (n - b₁) ?H
        linarith
      . right
        rw [hcon]
        dsimp [r']
        ring_nf
        have bar : b₁ + (n - b₁) ≡ b₁ + (n - b₁) % m [ZMOD m] := Int.ModEq.add rfl (Int.ModEq.symm (Int.mod_modEq (n - b₁) ↑m))
        simp at bar
        suffices n + (-b₁ - (n - b₁) % m) ≡ 0 [ZMOD m] by exact Int.dvd_of_emod_eq_zero this
        calc
        _ ≡ (b₁ + (n - b₁) % m) + (-b₁ - (n - b₁) % m) [ZMOD m] := by exact Int.ModEq.add bar rfl
        _ ≡ 0 [ZMOD m] := by ring_nf; exact rfl

-- Lemma 2.2
lemma b_r (n m : ℤ) (h : (m ≥ 4 ∧ n ≥ 53 * m) ∨ (m = 3 ∧ n ≥ 159 * m)) :
  ∃ b r : ℤ,
       Odd b
    ∧ (b > I_lb n m) ∧ (b < I_ub n m)
    ∧ 0 ≤ r ∧ r ≤ m - 3
    ∧ m ∣ n - b - r := by

  rcases h with ⟨hm, hnm⟩ | ⟨hm, hnm⟩
  . have : 0 ≤ m - 3 ∧ m - 3 ≤ m - 3 := ⟨ Int.sub_nonneg_of_le (Int.le_of_lt hm),  Int.le_refl (m - 3) ⟩

    let instlemma4 := (@lemma4 n m (Int.le_of_lt hm)).left
    have : (I_ub n m - 0.001) - (I_lb n m + 0.001) ≥ 2 * 2 := by
      apply le_of_lt
      calc
            (I_ub n m - 0.001) - (I_lb n m + 0.001)
          = (I_ub n m - I_lb n m) - 0.002 := by ring_nf
        _ > 4.002 - 0.002 := by suffices I_ub n m - I_lb n m > 4.002 by exact sub_lt_sub_right this 2e-3
                                apply instlemma4
                                exact ⟨ hm, hnm ⟩
        _ = 2 * 2 := by norm_num

    rcases blist (I_lb n m + 0.001) (I_ub n m - 0.001) 2 this with ⟨ b', ⟨ hbl, ⟨k, hk⟩⟩ ⟩
    let idx₁ : Fin b'.length := ⟨0, by linarith⟩
    let idx₂ : Fin b'.length := ⟨1, by linarith⟩
    obtain ⟨odd₁, lb₁, ub₁⟩  := hk idx₁
    obtain ⟨odd₂, lb₂, ub₂⟩  := hk idx₂
    let b₁ := b'.get idx₁
    let b₂ := b'.get idx₂

    have h12 : b₂ = b₁ + 2 := by unfold b₁; unfold b₂; rw [odd₁, odd₂]; ring

    obtain ⟨ r, ⟨ hrlb, hrub, hdisj ⟩ ⟩ := res_b_r b₁ b₂ h12 n m hm
    rcases hdisj with g | g
    . use b₁
      use r
      constructor
      . use (k + idx₁)
      . constructor
        . unfold b₁
          calc
            _ ≥ I_lb n m + 0.001 := by exact lb₁
            _ > _ := by norm_num
        . constructor
          . unfold b₁
            calc
              _ ≤ I_ub n m - 0.001 := by exact ub₁
              _ < _ := by norm_num
          . constructor
            . exact hrlb
            . constructor
              . exact hrub
              . exact g
    . use b₂
      use r
      constructor
      . use (k + idx₂)
      . constructor
        . unfold_let b₁
          calc
            _ ≥ I_lb n m + 0.001 := by exact lb₂
            _ > _ := by norm_num
        . constructor
          . unfold_let b₁
            calc
              _ ≤ I_ub n m - 0.001 := by exact ub₂
              _ < _ := by norm_num
          . constructor
            . exact hrlb
            . constructor
              . linarith
              . exact g
  . rw [hm]

    let instlemma4 := (@lemma4 n 3 (by norm_num)).right

    have : (I_ub n 3 - 0.001) - (I_lb n 3 + 0.001) ≥ 2 * 3 := by
      apply le_of_lt
      calc
            (I_ub n 3 - 0.001) - (I_lb n 3 + 0.001)
          = (I_ub n 3 - I_lb n 3) - 0.002 := by ring_nf
        _ > 6.002 - 0.002 := by suffices I_ub n 3 - I_lb n 3 > 6.002 by exact sub_lt_sub_right this 2e-3
                                apply instlemma4
                                constructor
                                . rfl
                                . rw [← hm]; exact hnm
        _ = 2 * 3 := by norm_num
    rcases blist (I_lb n 3 + 0.001) (I_ub n 3 - 0.001) 3 this with ⟨ b', ⟨ hbl, ⟨k, hk⟩⟩ ⟩
    let idx₁ : Fin b'.length := ⟨0, by linarith⟩
    let idx₂ : Fin b'.length := ⟨1, by linarith⟩
    let idx₃ : Fin b'.length := ⟨2, by linarith⟩
    obtain ⟨odd₁, lb₁, ub₁⟩  := hk idx₁
    obtain ⟨odd₂, lb₂, ub₂⟩  := hk idx₂
    obtain ⟨odd₃, lb₃, ub₃⟩  := hk idx₃
    let b₁ := b'.get idx₁
    let b₂ := b'.get idx₂
    let b₃ := b'.get idx₃

    have h12 : b₂ = b₁ + 2 := by unfold b₁; unfold b₂; rw [odd₁, odd₂]; ring

    have h23 : b₃ = b₂ + 2 := by unfold b₂; unfold b₃; rw [odd₂, odd₃]; ring

    rcases res_b b₁ b₂ b₃ h12 h23 n with g | g | g
    . use b₁
      use 0
      constructor
      . use (k + idx₁)
      . constructor
        . unfold b₁
          calc
            _ ≥ I_lb n 3 + 0.001 := by exact lb₁
            _ > _ := by norm_num
        . constructor
          . unfold b₁
            calc
              _ ≤ I_ub n 3 - 0.001 := by exact ub₁
              _ < _ := by norm_num
          . constructor
            . rfl
            . constructor
              . simp
              . simp; exact g
    . use b₂
      use 0
      constructor
      . use (k + idx₂)
      . constructor
        . unfold_let b₁
          calc
            _ ≥ I_lb n 3 + 0.001 := by exact lb₂
            _ > _ := by norm_num
        . constructor
          . unfold_let b₁
            calc
              _ ≤ I_ub n 3 - 0.001 := by exact ub₂
              _ < _ := by norm_num
          . constructor
            . rfl
            . constructor
              . simp
              . simp; exact g
    . use b₃
      use 0
      constructor
      . use (k + idx₃)
      . constructor
        . unfold_let b₁
          calc
            _ ≥ I_lb n 3 + 0.001 := by exact lb₃
            _ > _ := by norm_num
        . constructor
          . unfold_let b₁
            calc
              _ ≤ I_ub n 3 - 0.001 := by exact ub₃
              _ < _ := by norm_num
          . constructor
            . rfl
            . constructor
              . simp
              . simp; exact g




example (n : ℤ) (m : ℕ) (hm : m > 0): r = n % m → r < m := by
  intro h
  rw [h]
  refine Int.emod_lt_of_pos n ?H
  exact Int.ofNat_pos.mpr hm
