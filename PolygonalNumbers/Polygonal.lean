/-
  ==================== Support for Polygonal Numbers ====================
-/
import Mathlib.Tactic
import Mathlib.Data.Set.Defs
import Init.Data.List.Basic
import Mathlib.Data.Rat.Sqrt
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Group.TypeTags.Basic

import PolygonalNumbers.Lemmas

-- Wikipedia definitions
-- `m` -> order
def IsTriangular (n : ℤ) := ∃ (k : ℤ), (k * (k + 1)) = 2 * n
def IsnPolygonal (m : ℤ) (n : ℕ) (_ : m ≥ 3) := n = 0 ∨ ∃ (k : ℕ), (((m : ℚ) - 2) / 2) * (k * (k - 1)) + k = n --∧ k > 0
def IsnPolygonal' (m : ℤ) (n : ℕ) (_ : m ≥ 3) := n = 0 ∨ ∃ (k : ℕ), (((m : ℚ) - 2) / 2) * (k^2 - k) + k = n --∧ k > 0
def IsnPolygonal'' (m : ℤ) (n : ℕ) (_ : m ≥ 3) := n = 0 ∨ ∃ (k : ℕ), (((m : ℚ)- 2)*k^2 - (m - 4)*k) / 2 = n --∧ k > 0
-- def IsnPolygonal₀ (m : ℤ) (n : ℤ) := (√(8*(m-2)*n + (m-4)^2) + (m - 4)) / (2 * (m - 2))
def IsnPolygonal₀ (m : ℤ) (n : ℕ) (_ : m ≥ 3) := n = 0 ∨ (IsSquare (8*(m-2)*n + (m-4)^2)
                        ∧ (Int.sqrt (8*(m-2)*n + (m-4)^2) + (m - 4)) % (2 * (m - 2)) = 0)
                        --∧ n ≠ 0
                     --   ∧ (∃ (k : ℕ), (k ^ 2 = (8*(m-2)*n + (m-4)^2) ∧ (k + (m - 4)) % (2 * (m - 2)) = 0))
                     -- Rat.sqrt


def Triangular := Subtype (fun (n : ℕ) ↦ IsTriangular n)
def Polygonal (m : ℤ) (hm : m ≥ 3) := Subtype (fun (n : ℕ) ↦ IsnPolygonal m n hm)

/--
  Both conditions `IsnPolygonal` and `IsnPolygonal'` are equivalent.
-/
lemma kfactq (k : ℚ) : k * (k - 1) = k^2 - k := by
  ring

lemma PolyEquiv: IsnPolygonal = IsnPolygonal' := by
  unfold IsnPolygonal IsnPolygonal'
  funext m a hm
  apply propext
  constructor
  . intro h
    rcases h with h₀ | h
    . left; exact h₀
    . right
      let ⟨ k, hk ⟩ := h
      use k
      rw [kfactq k] at hk
      exact hk

  . intro h
    rcases h with h₀ | h
    . left; exact h₀
    . let ⟨ k, hk ⟩ := h
      right
      use k
      rw [kfactq k]
      exact hk

lemma PolyEquiv' : IsnPolygonal = IsnPolygonal'' := by
  unfold IsnPolygonal IsnPolygonal''
  funext m a hm
  apply propext
  constructor
  . intro h
    -- let ⟨ k, ⟨ hk, hnez⟩ ⟩ := h
    rcases h with h₀ | h
    . left; exact h₀
    . right;
      let ⟨ k, hk ⟩ := h
      use k
      rw [← hk]
      ring
    -- simp
    -- assumption
  . intro h
    rcases h with h₀ | h
    . left; exact h₀
    . right;
    -- let ⟨ k, ⟨ hk, hnez ⟩ ⟩ := h
      let ⟨ k, hk ⟩ := h
      use k
      rw [← hk]
      ring
    -- simp
    -- assumption

lemma PolyEquiv₀ : IsnPolygonal = IsnPolygonal₀ := by
  unfold IsnPolygonal₀
  funext m x hm
  apply propext

  have hcasesthr : m = 3 ∨ m > 3 := by
    exact Or.symm (LE.le.gt_or_eq hm)

  constructor
  . intro h
    dsimp [IsSquare]
    -- let ⟨ k, ⟨ hk, hnez ⟩ ⟩ := h
    -- let ⟨ k, hk ⟩ := h
    let hcpy := h
    dsimp [IsnPolygonal] at hcpy
    have hexzero : x = 0 ∨ x > 0 := by
      exact Nat.eq_zero_or_pos x
    rcases hexzero with hzero | hpos
    . left; exact hzero

    -- rcases hcpy with hzero | h₁
    -- . left; exact hzero
    right
    have hexne : x ≠ 0 := by exact Nat.not_eq_zero_of_lt hpos
    have hexz : x = 0 ↔ False := by exact iff_false_intro hexne
    rw [hexz] at hcpy
    simp at hcpy

    let ⟨ k, hk ⟩ := hcpy
    have hsqrtsq : 8 * (m - 2) * x + (m - 4) ^ 2 = (2 * k * (m - 2) - (m - 4)) * (2 * k * (m - 2) - (m - 4)) := by
      have hev : Even ((m - 2) * k ^ 2 - (m - 4) * k) := by
        refine Int.even_sub.mpr ?_
        constructor
        . intro heven
          refine Int.even_mul.mpr ?_
          apply Int.even_mul.mp at heven
          rcases heven with h₁ | h₁
          . left
            refine (Int.even_sub).mpr ?_
            . have hmnet : m ≠ 3 := by
                contrapose h₁
                simp at h₁
                simp
                rw [h₁]
                simp
              have hmgtf : m > 3 := by
                exact lt_of_le_of_ne hm (id (Ne.symm hmnet))
              constructor
              . intro _
                dsimp [Even]
                use 2
                simp
              . intro _
                let ⟨ r, hr ⟩ := h₁
                use r + 1
                linarith
          . right
            rw [@sq] at h₁
            apply Int.even_mul.mp at h₁
            simp at h₁
            exact (Int.even_coe_nat k).mpr h₁
            -- exact h₁
        . intro heven
          refine Int.even_mul.mpr ?_
          apply Int.even_mul.mp at heven
          rcases heven with h₁ | h₁
          . left
            refine (Int.even_sub).mpr ?_
            constructor
            . intro _
              dsimp [Even]
              use 1
              linarith
            . intro _
              dsimp [Even] at h₁
              let ⟨ r, hr ⟩ := h₁
              use r + 2
              linarith
          . right
            rw [@sq]
            exact Even.mul_right h₁ k
      have hint : ((m - 2) * k ^ 2 - (↑m - 4) * k) / 2 = x := by
        refine Eq.symm (Int.eq_ediv_of_mul_eq_right ?_ ?_)
        linarith
        have hq : (((m : ℚ) - 2) * k ^ 2 - (m - 4) * k) = 2 * x := by
          rw [← hk]
          ring
        apply Eq.symm
        have htx : (2 * (x : ℚ)) = (((2 * x) : ℤ) : ℚ) := by
          simp

        have htmk : ((m : ℚ) - 2) * k ^ 2 - (m - 4) * k = ((((m - 2) * k ^ 2 - (m - 4) * k) : ℤ) : ℚ) := by
          simp
        rw [htx, htmk] at hq
        exact Eq.symm ((fun {a b} ↦ Rat.intCast_inj.mp) (id (Eq.symm hq)))
      rw [← hint]
      have hexr : ∃ (r : ℤ), ((m - 2) * k ^ 2 - (m - 4) * k) = 2 * r := by
        exact Even.exists_two_nsmul ((m - 2) * k ^ 2 - (m - 4) * k) hev
      let ⟨ r, hr ⟩ := hexr
      calc 8 * (m - 2) * (((m - 2) * k ^ 2 - (m - 4) * k) / 2) + (m - 4) ^ 2
        _ = 4 * (m - 2) * (((m - 2) * k ^ 2 - (m - 4) * k)) + (m - 4) ^ 2 := by
          rw [hr]
          simp
          ring
        _ = ((2 * (m - 2) * k) - (m - 4))^2 := by ring
      ring

    have hexzero : x = 0 ∨ x > 0 := by
      exact Nat.eq_zero_or_pos x

    constructor
    . rw [PolyEquiv'] at h
      use (2 * k * (m - 2) - (m - 4))
    . rw [hsqrtsq]
      have hintsqrt : Int.sqrt ((2 * k * (m - 2) - (m - 4)) * (2 * k * (m - 2) - (m - 4))) = (2 * k * (m - 2) - (m - 4)).natAbs := by
        rw [Int.sqrt_eq]
      rw [hintsqrt]
      simp
      -- constructor
      use k
      have hkor : k = 0 ∨ k > 0 := by
        exact Nat.eq_zero_or_pos k
      rcases hkor with hzero | hpos
      . rw [hzero]
        simp
        have habs : 4 - m ≥ 0 ∨ 4 - m < 0 := by
          exact Int.le_or_lt 0 (4 - m)
        rcases habs with hnonneg | hneg
        . have habs' : abs (4 - m) = 4 - m := by
            exact abs_of_nonneg hnonneg
          rw [habs']
          simp
        . have habs' : abs (4 - m) = -(4 - m) := by
            exact abs_of_neg hneg
          rw [habs']
          simp
          rw [hzero] at hk
          simp at hk
          exfalso
          have hnez : 0 ≠ (x : ℚ) := by
            apply Ne.symm
            apply Nat.cast_ne_zero.mpr
            exact hexne
          contradiction
      . have htsqrtpos : 2 * k * (m - 2) - (m - 4) ≥ 0 := by
          rcases hcasesthr with hthree | hneqthree
          . rw [hthree]
            linarith
          . simp
            have hmt : m - 2 > 0 := by
              linarith
            refine Int.le_add_of_sub_right_le ?_
            calc m - 4
              _ ≤ 2 * (m - 2) := by linarith
            refine Int.mul_le_mul_of_nonneg_right ?_ ?_
            . linarith
            . linarith

        have habs : |2 * k * (m - 2) - (m - 4)| = 2 * k * (m - 2) - (m - 4) := by
          exact abs_of_nonneg htsqrtpos

        rw [habs]
        ring

  . have hexzerocases : x = 0 ∨ x > 0 := by exact Nat.eq_zero_or_pos x
    rcases hexzerocases with hzero | hpos
    . intro _; dsimp [IsnPolygonal]; left; exact hzero
    intro h₁
    have hand : IsSquare (8 * (m - 2) * ↑x + (m - 4) ^ 2) ∧ (Int.sqrt (8 * (m - 2) * ↑x + (m - 4) ^ 2) + (m - 4)) % (2 * (m - 2)) = 0 := by
      have hexne : x ≠ 0 := by exact Nat.not_eq_zero_of_lt hpos
      have hexz : x = 0 ↔ False := by exact iff_false_intro hexne
      rw [hexz] at h₁
      simp at h₁
      simp
      exact h₁
    -- let ⟨ hsq, hdiv ⟩ := hand
    let ⟨ ⟨ r', hr' ⟩, h₂ ⟩ := hand
    have hrest : ∃ (r : ℤ), 8 * (m - 2) * ↑x + (m - 4) ^ 2 = r * r ∧ r ≥ 0 := by
      let r := r'.natAbs
      use r
      constructor
      . dsimp [r]
        apply Eq.symm
        calc (r'.natAbs : ℤ) * r'.natAbs
          _ = r' * r' := by simp
        rw [hr']
      . exact Int.ofNat_zero_le r

    let ⟨ r, ⟨ hr, hrgeq ⟩ ⟩ := hrest

    rw [hr] at h₂
    rw [Int.sqrt_eq] at h₂
    dsimp [IsnPolygonal]

    let rm₄ := r.natAbs + (m - 4)
    have hf : 2 * ((m : ℝ) - 2) > 0 := by
        refine mul_pos ?_ ?_
        simp
        ring_nf
        suffices h : 2 < m by
          have ht : (2 : ℝ) < m := by
            exact Int.cast_lt.mpr h
          exact lt_neg_add_iff_lt.mpr ht
        linarith
    have hf₂ : 2 * ((m : ℝ) - 2) ≠ 0 := by exact Ne.symm (ne_of_lt hf)
    have hfq : 2 * ((m : ℚ) - 2) > 0 := by
        refine mul_pos ?_ ?_
        simp
        have hmr : (m : ℚ) ≥ 3 := by
          exact Int.ceil_le.mp hm
        linarith
    have hf₂q : 2 * ((m : ℚ) - 2) ≠ 0 := by exact Ne.symm (ne_of_lt hfq)
    have htwo : (2 * ((m : ℚ) - 2)) /  (2 * ((m : ℚ) - 2)) = 1 := by
        rw [div_self]
        exact hf₂q
    have heq : ((((rm₄) / (2 * (m - 2))) : ℤ) : ℚ) = (rm₄ : ℚ) / (2 * (m - 2)) := by
      have hl : ((((rm₄ / (2 * (m - 2))) : ℚ) * (2 * (m - 2)))) = rm₄ := by
        refine
          Eq.symm
            ((fun a b ↦ (Mathlib.Tactic.Rify.ratCast_eq a b).mpr) (↑rm₄)
              (↑rm₄ / (2 * (↑m - 2)) * (2 * (↑m - 2))) ?_)
        simp
        refine Eq.symm (div_mul_cancel_of_imp ?_)
        intro h
        exfalso
        have hf₃ : 2 * ((m : ℝ) - 2) = 0 ∧ 2 * ((m : ℝ) - 2) ≠ 0:= by
          constructor
          exact h
          exact hf₂

        simp at hf₃
      refine eq_div_of_mul_eq ?_ ?_
      . exact hf₂q
      . --let ⟨ hdiv, hneq ⟩ := h₂
        let hdiv := h₂
        have hex : ∃ (k : ℤ), rm₄ = (2 * (m - 2)) * k := by
          dsimp [rm₄]
          refine exists_eq_mul_right_of_dvd ?_
          exact Int.dvd_of_emod_eq_zero hdiv

        have hmodrm : rm₄ % (2 * (m - 2)) = 0 := by
          dsimp [rm₄]
          exact Int.emod_eq_zero_of_dvd hex

        have hexrm : ∃ (k : ℤ), rm₄ = 2 * (m - 2) * k := by
          refine dvd_iff_exists_eq_mul_right.mp ?_
          exact Int.dvd_of_emod_eq_zero hdiv

        let ⟨ k, hk ⟩ := hex
        rw [hk]
        simp
        calc 2 * ((m : ℚ) - 2) * k / (2 * (m - 2)) * (2 * (m - 2))
          _ = k * ((2 * ((m : ℚ) - 2)) / (2 * (m - 2))) * (2 * (m - 2)) := by ring
          _ = k * 1 * (2 * (m - 2)) := by rw [htwo]
        ring

    have heq' : ((((rm₄) / (2 * (m - 2))).natAbs) : ℚ) = abs ((rm₄) / (2 * (m - 2))) := by
      exact Nat.cast_natAbs (rm₄ / (2 * (m - 2)))

    have heq'' : (abs ((rm₄) / (2 * (m - 2))) : ℤ) = abs (((rm₄ : ℚ)) / (2 * (m - 2))) := by
      rw [← heq]
      exact Int.cast_abs

    rcases hcasesthr with heqthree | hneqthree
    . rw [heqthree]
      simp
      right
      use ((rm₄) / (2 * (m - 2))).natAbs
      rw [heq',heq'']
      have hrm₄thr : rm₄ = r.natAbs - 1 := by
        dsimp [rm₄]
        rw [heqthree]
        ring

      have reqzeroiff : r = 0 ↔ 8 * (m - 2) * x + (m - 4) ^ 2 = 0:= by
        constructor
        . intro ha
          rw [hr, ha]
          simp
        . intro ha
          rw [hr] at ha
          exact zero_eq_mul_self.mp (id (Eq.symm ha))

      have hreqzerocases : r = 0 ∨ r > 0 := by
        exact Or.symm (LE.le.gt_or_eq hrgeq)

      rcases hreqzerocases with hzero | hpos
      . have hrm4zero : rm₄ = -1 := by
          dsimp [rm₄]
          rw [hzero, heqthree]
          simp
        rw [hrm4zero]
        -- rw [habs]
        rw [heqthree]
        have hfal : 8 * (x : ℤ) + 1 = 0 := by
          rw [heqthree, hzero] at hr
          simp at hr
          exact hr
        have hfal' : 8 * (x : ℤ) = -1 := by
          exact (Int.add_left_inj 1).mp hfal
        have hxgeq : (x : ℤ) ≥ 0 := by
          linarith
        have hxgeq' : 8 * (x : ℤ) ≥ 0 := by
          exact Int.le.intro_sub (8 * x + 0) rfl
        exfalso
        contradiction
      . have hreqone : r = 1 ∨ r > 1 := by
          exact Or.symm (LE.le.gt_or_eq hpos)

        rcases hreqone with hone | hgtone
        . have rm₄zero : rm₄ = 0 := by
            dsimp [rm₄]
            rw [hone, heqthree]
            simp
          rw [rm₄zero]
          simp
          -- have hex : 8 * (x : ℤ) = 1 := by
          rw [heqthree, hone] at hr
          simp at hr
          apply Eq.symm
          exact Rat.natCast_eq_zero.mpr hr
          -- let ⟨ _, hf ⟩ := h₂
          -- exact hf hr

        . have hgeqzero : (rm₄ / (2 * (m - 2))) ≥ 0 := by
            refine Int.ediv_nonneg ?_ ?_
            . dsimp [rm₄]
              rw [heqthree]
              have hrgeq : r.natAbs = r := by
                exact Int.natAbs_of_nonneg hrgeq
              rw [hrgeq]
              linarith
            . linarith
          have hrabs : r.natAbs = r := by
            exact Int.natAbs_of_nonneg hrgeq
          have hrm₄geqzero : rm₄ ≥ 0 := by
            dsimp [rm₄]
            rw [heqthree]


            rw [hrabs]
            linarith

          have hrm₄abs : (rm₄ / (2 * (m - 2))).natAbs = (rm₄ / (2 * (m - 2))) := by
            refine Int.natAbs_of_nonneg ?_
            refine (Int.div_nonneg_iff_of_pos ?_).mpr hrm₄geqzero
            linarith

          -- have hrm₄qeq : (((rm₄ / (2 * (m - 2))).natAbs) : ℚ) = (((rm₄ / (2 * (m - 2))) : ℤ) : ℚ) := by
          --   exact Rat.ext hrm₄abs rfl

          -- rw [hrm₄qeq]
          dsimp [rm₄]
          rw [hrabs]
          rw [heqthree]
          simp
          ring
          have habshalf : |(1/2) * (-1 + (r : ℚ))| = (1/2) * |(r : ℚ) - 1| := by
            rw [abs_mul]
            have hposhalf : abs ((1 : ℚ)/2) = 1/2 := by simp
            rw [hposhalf]
            ring

          have hrabs : abs ((r: ℚ) - 1)  = r - 1 := by
            refine abs_of_pos ?_
            refine sub_pos.mpr ?_
            exact Int.floor_lt.mp hgtone
          have hstep1 : 8 * (x : ℚ) + 1 = r * r := by
            apply Eq.symm
            calc (r : ℚ) * r
              _ = ((r * r) : ℤ) := by exact Eq.symm (Rat.intCast_mul r r)
            rw [← hr]
            simp
            rw [heqthree] at hr
            simp at hr
            rw [heqthree]
            simp
            ring

          have hxeq : (x : ℚ) = 8⁻¹ * ((r : ℚ) * r - 1) := by
            suffices hassumpt : 8 * (x : ℚ) = (r : ℚ) * r - 1 by
              apply Eq.symm
              refine (IsUnit.inv_mul_eq_iff_eq_mul ?_).mpr (id (Eq.symm hassumpt))
              simp
            apply Eq.symm
            apply sub_eq_iff_eq_add.mpr ?_
            exact Eq.symm hstep1
          -- constructor
          calc |-1 / 2 + (r : ℚ) * (1 / 2)| * (1 / 2) + |-1 / 2 + ↑r * (1 / 2)| ^ 2 * (1 / 2)
            _ =  |(1/2) * (-1 + (r : ℚ))| * (1 / 2) + (|(1/2) * (-1 + (r : ℚ))|) ^ 2 * (1 / 2) := by ring
            _ = (1 / 2) * |(r: ℚ) - 1| * (1 / 2) + ((1/2) * |(r : ℚ) - 1|) ^ 2 * (1 / 2) := by rw [habshalf]
            _ = (1 / 4) * |(r : ℚ) - 1| + (1 / 8) * |(r : ℚ) - 1| ^ 2 := by ring
            _ = (1 / 4) * ((r : ℚ) - 1) + (1 / 8) * ((r : ℚ) - 1) ^2 := by rw [hrabs]
          rw [heqthree] at hr
          simp at hr
          rw [hxeq]
          ring
    have hrm₄geqzero : rm₄ ≥ 0 := by
      dsimp [rm₄]
      linarith
    right
    use (rm₄ / (2 * (m - 2))).natAbs

    have hrn : r.natAbs * r.natAbs = r * r := by simp
    have hrnq : (r.natAbs : ℚ) * r.natAbs = r * r := by
      apply Eq.symm
      calc (r : ℚ) * r
        _ = ((r * r) : ℤ) := by exact Eq.symm (Rat.intCast_mul r r)
      rw [← hrn]
      apply Eq.symm
      exact Eq.symm (Rat.intCast_mul ↑r.natAbs ↑r.natAbs)

    have hrq : 8 * (m - 2) * x + (m - 4) ^ 2 = (r : ℚ) * r := by
      apply Eq.symm
      calc (r : ℚ) * r
        _ = ((r * r) : ℤ) := by exact Eq.symm (Rat.intCast_mul r r)
      rw [← hr]
      simp

    have habs : abs r = r.natAbs := by
      simp
    have habsq : abs (r : ℚ) = r.natAbs := by
      rw [@Int.cast_natAbs]
      exact Eq.symm Int.cast_abs
    have hrnq : (r.natAbs : ℚ) * r.natAbs = r * r := by
      ring
      refine sq_eq_sq_iff_eq_or_eq_neg.mpr ?_
      rcases abs_choice (r : ℚ) with hp | hn
      . left
        rw [← hp]
        rw [← habsq]
      . right
        rw [← hn]
        rw [← habsq]

    have h : x = ((r.natAbs : ℚ) * r.natAbs - (m-4)^2) / (8 *(m-2)) := by
      rw [hrnq]
      rw [← hrq]
      simp
      apply Eq.symm
      have h : (m - 2) / (m - 2) = 1 := by
        refine Int.ediv_self ?_
        linarith

      have hemtq : (8*((m : ℚ)-2)) / ((8*(m-2))) = 1 := by
        refine div_self ?_
        simp
        have hmt : (m : ℚ) - 2 > 0 := by
          linarith
        exact right_ne_zero_of_mul hf₂q


      calc
        _ = (((8*(m-2))) * (x : ℚ) ) / (8*(m-2)) := by ring
        _ = (x * ((8*(m-2)))) / (8*(m-2)) := by rw [mul_comm]
        _ = x * ((8*(m-2)) / (8*(m-2))) := by ring
        _ = x * 1 := by rw [hemtq]
      simp
    rw [h]

    have hrm₄abs : (rm₄ / (2 * (m - 2))).natAbs = (rm₄ / (2 * (m - 2))) := by
      refine Int.natAbs_of_nonneg ?_
      refine (Int.div_nonneg_iff_of_pos ?_).mpr hrm₄geqzero
      linarith

    have hrm₄qeq : (((rm₄ / (2 * (m - 2))).natAbs) : ℚ) = (((rm₄ / (2 * (m - 2))) : ℤ) : ℚ) := by
      exact Rat.ext hrm₄abs rfl

    rw [hrm₄qeq]
    rw [heq]

    have heq' : ((r.natAbs + (m - 4)) : ℤ) = ((r.natAbs + (m - 4)) : ℚ) := by
      simp
      rw [@Int.cast_natAbs]
      exact Eq.symm Int.cast_abs
      -- have heq'' : (r).natAbs

    have hmtwo : (((m : ℚ) - 2) / (2 * (m - 2))) = 1 / 2 := by
      calc (((m : ℚ) - 2) / (2 * (m - 2)))
        _ = 2 / 2 * ((m - 2) / (2 * (m - 2))):= by ring
        _ = 1 / 2 * 2 * ((m - 2) / (2 * (m - 2))):= by ring
        _ = 1 / 2 * (2 * (m - 2) / (2 * (m - 2))):= by ring
        _ = 1 / 2 * (1):= by rw [htwo]
        _ = 1 / 2 := by simp
    -- constructor
    calc ((m : ℚ) - 2) / 2 * (rm₄ / (2 * (m - 2)) * (rm₄ / (2 * (m - 2)) - 1)) + rm₄ / (2 * (m - 2))
      _ = ((m - 2) / 2) * ((rm₄ / (2 * (m - 2))) * (rm₄ / (2 * (m - 2)) - 1)) + (rm₄ / (2 * (m - 2))) := by simp
      _ = ((m - 2) / 2) * ((rm₄ / (2 * (m - 2))) * (rm₄ / (2 * (m - 2)) - ((2 * (m - 2)) / (2 * (m - 2))))) + (rm₄ / (2 * (m - 2))) := by rw [htwo]
      _ = ((m - 2) / 2) * ((rm₄ / (2 * (m - 2))) * ((rm₄ - (2 * (m - 2))) / (2 * (m - 2)))) + (rm₄ / (2 * (m - 2))) := by ring
      _ = ((m - 2) / 2) * ((rm₄ / (2 * (m - 2))) * ((((r.natAbs + (m - 4)) : ℤ) - (2 * (m - 2))) / (2 * (m - 2)))) + (rm₄ / (2 * (m - 2))) := by dsimp [rm₄]
      _ = ((m - 2) / 2) * ((rm₄ / (2 * (m - 2))) * ((((r.natAbs + (m - 4))) - (2 * (m - 2))) / (2 * (m - 2)))) + (rm₄ / (2 * (m - 2))) := by rw [heq']
      _ = (1 / (2 * (m - 2))) * (((m - 2) / 2) * (rm₄ * (r.natAbs - m) / (2 * (m - 2))) + rm₄) := by ring
      _ = (1 / (2 * (m - 2))) * ((1 / 2) * ((m - 2)) * (rm₄ * (r.natAbs - m) / (2 * (m - 2))) + ((2 * (m - 2)) / (2 * (m - 2)) * rm₄)) := by rw [htwo]; ring
      _ = (1 / (2 * (m - 2))) * (((1 / 2) * ((rm₄ * r.natAbs - m * rm₄ + 4 * rm₄)) * ((m - 2) / (2 * (m - 2))))) := by ring
      _ = (1 / (2 * (m - 2))) * (((1 / 2) * ((rm₄ * r.natAbs - m * rm₄ + 4 * rm₄)) * (1 / 2))) := by rw [hmtwo]
      _ = ((1 / 4) * (1 / (2 * (m - 2)))) * (rm₄ * (r.natAbs - m + 4)) := by ring
      _ = ((1 / 4) * (1 / (2 * (m - 2)))) * (((r.natAbs + (m - 4)) : ℤ) * (r.natAbs - m + 4)) := by dsimp [rm₄]
      _ = ((1 / 4) * (1 / (2 * (m - 2)))) * ((r.natAbs + (m - 4)) * (r.natAbs - m + 4)) := by rw [heq']
      _ = ((1 / 4) * (1 / (2 * (m - 2)))) * (r.natAbs ^ 2 - m * r.natAbs + 4 * r.natAbs + (m - 4) * r.natAbs - (m - 4) * m + (m - 4) * 4) := by ring
      _ = ((1 / 4) * (1 / (2 * (m - 2)))) * (r.natAbs ^ 2 - m ^ 2 + 8 * m - 16) := by ring
      _ = ((1 / 4) * (1 / (2 * (m - 2)))) * (r.natAbs * r.natAbs - (m - 4) ^ 2) := by ring
      _ = ((1 / 4) * (1 / (2 * (m - 2)))) * (r * r - (m - 4) ^ 2) := by rw [hrnq]
    simp
    calc 4⁻¹ * (((m : ℚ) - 2)⁻¹ * 2⁻¹) * (r * r - (↑m - 4) ^ 2)
      _ = (r * r - (↑m - 4) ^ 2) * ((8)⁻¹ * ((m : ℚ) - 2)⁻¹)  := by ring
      _ = (r * r - (↑m - 4) ^ 2) * (8 * ((m : ℚ) - 2))⁻¹  := by
        simp
        left
        linarith
      _ = (r * r - (m - 4)^2) / (8 * (m - 2)) := by ring

    rw [hrnq]

instance : BEq (Polygonal m hm) where
  beq a b := if (a.val == b.val)
             then true
             else false

instance : LawfulBEq (Polygonal m hm) where
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

instance : DecidableEq (Polygonal n hm) :=
  fun a b =>
    if h : a.val = b.val then
      isTrue (by rw [a.eq_iff]; exact h)
    else
      isFalse (by rw [a.eq_iff]; exact h)

instance : LE (Polygonal m hm) where
  le a b := a.val ≤ b.val


lemma Polyrw (m : ℤ) (n : ℕ) (hm : m ≥ 3) : IsnPolygonal m n hm ↔ IsnPolygonal' m n hm := by
  rw [PolyEquiv]

theorem one_is_poly (m : ℤ) (hm : m ≥ 3) : IsnPolygonal m 1 hm := by
  dsimp [IsnPolygonal]
  right
  use 1
  simp

theorem zero_is_poly (m : ℤ) (hm : m ≥ 3) : IsnPolygonal m 0 hm := by
  dsimp [IsnPolygonal]
  simp

def PolyOne (m : ℤ) (hm : m ≥ 3) : Polygonal m hm := ⟨ 1, one_is_poly m hm ⟩
def PolyZero (m : ℤ) (hm : m ≥ 3) : Polygonal m hm := ⟨ 0, zero_is_poly m hm ⟩

#eval PolyZero (3) (by linarith) ≤ PolyOne (3) (by linarith)

instance : Decidable (IsnPolygonal m n h) := by
  rw [PolyEquiv₀]
  dsimp [IsnPolygonal₀]
  exact instDecidableOr

#eval decide <| IsnPolygonal 5 5 (by simp) -- true
#eval decide <| IsnPolygonal 14 53 (by simp) -- false
#eval decide <| IsnPolygonal 14 0 (by simp) -- true


/- n is the sum of k polygonal numbers of order m-/
def IsNKPolygonal (m : ℤ) (n : ℕ) (k : ℕ) (hm : m ≥ 3) := ∃ (l : List (Polygonal m hm)), l.length = k ∧ n = l.foldl (fun a b => a + b.val) 0

def IsNKPolygonal' (m : ℤ) (n : ℕ) (k : ℕ) (hm : m ≥ 3) := (k = 1 ∧ IsnPolygonal m n hm) ∨ (k > 1 ∧ ∃ (l : List (Polygonal m hm)), l.length = (k - 1) ∧ IsnPolygonal m (n - l.foldl (fun a b => a + b.val) 0) hm)

-- instance : Decidable (IsNKPolygonal m n k hm) := by
--   rw [IsNKPolygonal]

--   refine instDecidableAnd ?_ ?_


lemma polyform (m : ℤ) (r : ℕ) (hm2geq3 : (m + 2) ≥ 3) : ((m : ℚ) / 2) * (r^2 - r) + r = |⌈ ((m : ℚ) / 2) * (r^2 - r) + r ⌉| := by
  simp
  rw [← (kfactq r)]
  let ⟨ e, he ⟩ := revenk' r
  simp at he
  rw [he]
  rw [← mul_assoc]
  simp
  have hms : (m : ℚ) = ((m : ℤ) : ℚ) := rfl
  rw [hms]
  rw [← Int.cast_mul m e]
  rw [@Int.ceil_intCast]

  have hepos : e ≥ 0 := by
    contrapose he
    simp at he
    have hr : r * (r - 1) ≥ 0 := by
      exact Nat.zero_le (r * (r - 1))
    have he₂ : 2 * e < 0 := by
      refine Int.mul_neg_of_pos_of_neg ?_ he
      simp

    have hrpos : (r : ℚ) * (r - 1) ≥ 0 := by
      have hrzorpos : r = 0 ∨ r > 0 := by
        exact Or.symm (LE.le.gt_or_eq (Nat.zero_le r))
      rcases hrzorpos with hrzero | hrpos
      . rw [hrzero]
        simp
      . have hgeq : r ≥ 1 := by
          exact Nat.succ_le_iff.mpr hrpos
        have hgeq' : (r : ℚ) ≥ 1 := by
          exact Nat.one_le_cast.mpr hrpos
        refine Rat.mul_nonneg ?_ ?_
        linarith
        linarith

    have hneq : 2 * (e : ℚ) < (r : ℚ) * (r - 1) := by
      calc 2 * (e : ℚ)
        _ < 0 := by
          refine mul_neg_of_pos_of_neg rfl ?_
          exact Rat.num_neg.mp he
        _ ≤ r * (r - 1) := by exact hrpos
    exact ne_of_gt hneq

  have hempos : (((m * e) : ℤ) : ℚ) + r ≥ 0 := by
    simp
    have hem : (m * e) ≥ 0 := by
      refine mul_nonneg ?_ ?_
      linarith
      exact hepos
    refine Rat.add_nonneg ?_ ?_
    . refine Rat.mul_nonneg ?_ ?_
      . refine Int.cast_nonneg.mpr ?_
        linarith
      . exact Rat.num_nonneg.mp hepos
    . exact Nat.cast_nonneg' r

  exact Eq.symm (abs_of_nonneg hempos)

lemma polyformval (m : ℤ) (r : ℕ) (hm2geq3 : (m + 2) ≥ 3) : IsnPolygonal (m+2) ⌈ (((m / 2) * (r^2 - r) + r) : ℚ) ⌉.natAbs (hm2geq3) := by
  let rl : ℚ := (m / 2) * (r^2 - r) + r
  have rleq : rl = (m / 2) * (r^2 - r) + r := by exact rfl

  have hposconv (k : ℕ) : (k : ℚ) ^ 2 - k = (k^2 - k : ℕ) := by
    have hsgt : k^2 ≥ k := by
      refine Nat.le_self_pow ?_ k
      simp
    have hsq : (k : ℚ) ^ 2 = (k^2 : ℕ) := by
      simp
    rw [hsq]
    rw [← Nat.cast_sub hsgt]

  have hmpos : m ≥ 0 := by
    linarith
  have hmpos' : (m : ℚ) ≥ 0 := by
    exact Rat.num_nonneg.mp hmpos

  have hgt : rl ≥ 0 := by
    dsimp [rl]
    refine Rat.add_nonneg ?_ ?_
    . refine Rat.mul_nonneg ?_ ?_
      . refine Rat.div_nonneg ?_ rfl
        exact hmpos'
      . suffices h : r^2 - r ≥ 0 by
          have hconv : (r : ℚ) ^ 2 - r = (r^2 - r: ℕ) := hposconv r
          rw [hconv]
          exact Nat.cast_nonneg' (r ^ 2 - r)
        linarith
    . linarith
  rw [← rleq]

  have hgtabs : ⌈ rl ⌉ ≥ 0 := by
    exact Int.ceil_nonneg hgt
  have hgtabs' : ⌈ rl ⌉.natAbs = ⌈ rl ⌉ := by exact Int.natAbs_of_nonneg hgtabs
  have hgtabs₀ : (⌈ rl ⌉.natAbs : ℚ) = ⌈ rl ⌉ := by exact Rat.ext hgtabs' rfl

  rw [PolyEquiv]
  unfold IsnPolygonal'
  have hzeroornot : ⌈ rl ⌉.natAbs = 0 ∨ ⌈ rl ⌉.natAbs ≠ 0 := by
    exact Or.symm (ne_or_eq ⌈rl⌉.natAbs 0)
  rcases hzeroornot with hzero | hnonzero
  . left; dsimp [rl] at hzero; exact hzero
  right
  use r
  simp
  dsimp [rl]
  suffices hl : (m : ℚ) / 2 * (↑r ^ 2 - ↑r) + ↑r = |⌈ (m : ℚ) / 2 * (↑r ^ 2 - ↑r) + ↑r ⌉| by
    nth_rewrite 1 [hl]
    exact Eq.symm (Nat.cast_natAbs ⌈(m : ℚ) / 2 * (↑r ^ 2 - ↑r) + ↑r⌉)
  exact polyform m r hm2geq3

def getnthpoly (m : ℤ) (n : ℕ) (hm : m ≥ 3) : Polygonal m hm :=
  let num : ℚ := (((m : ℚ) - 2) / 2) * (n ^2 - n) + n
  have hnum : num  = |⌈ num ⌉| := by
    dsimp [num]
    have h : (m : ℚ) - 2 = (((m - 2) : ℤ) : ℚ) := by simp
    rw [h]
    apply polyform (((m - 2) : ℤ)) n
    linarith

  have h : IsnPolygonal m ⌈ num ⌉.natAbs hm := by
    have hm' : (m - 2 + 2) ≥ 3 := by linarith
    dsimp [num]
    suffices h' :  IsnPolygonal (m - 2 + 2) ⌈(((m - 2) : ℤ) : ℚ)/ 2 * (↑n ^ 2 - ↑n) + ↑n⌉.natAbs hm' by
      simp at h'
      simp
      exact h'
    refine polyformval (m - 2) n hm'

  ⟨ ⌈ num ⌉.natAbs, h ⟩


lemma getnthpoly_monotone (m : ℤ) (n : ℕ) (hm : m ≥ 3) : (getnthpoly m n hm).val ≤ (getnthpoly m (n + 1) hm).val := by
  dsimp [getnthpoly]
  have hm' : m - 2 + 2 ≥ 3 := by linarith
  suffices h : |(⌈((m : ℚ) - 2) / 2 * (↑n ^ 2 - ↑n) + ↑n⌉)| ≤ |⌈((m : ℚ) - 2) / 2 * ((↑n + 1) ^ 2 - (↑n + 1)) + (↑n + 1)⌉| by
    norm_cast at h
    simp
    simp at h
    norm_cast

    have h₀ (m : ℤ) : m.natAbs = |m| := by
      simp

    let a := ⌈Rat.divInt (m - 2) 2 * ↑(Int.subNatNat (n ^ 2) n)⌉ + n
    have a_eq : a = ⌈Rat.divInt (m - 2) 2 * ↑(Int.subNatNat (n ^ 2) n)⌉ + n := by
      dsimp [a]

    let a' := |⌈Rat.divInt (m - 2) 2 * (↑n ^ 2 - ↑n)⌉ + ↑n|
    have a'_eq : a' = |⌈Rat.divInt (m - 2) 2 * (↑n ^ 2 - ↑n)⌉ + ↑n| := by
      dsimp [a']

    have haa' : a = a' := by
      dsimp [a]
      dsimp [a']
      simp

      have h₅ : ⌈Rat.divInt (m - 2) 2 * (↑n ^ 2 - ↑n)⌉ + n ≥ 0 := by
        refine Int.add_nonneg ?_ ?_
        . refine Int.ceil_nonneg ?_
          refine Rat.mul_nonneg ?_ ?_
          . refine Rat.divInt_nonneg ?_ ?_
            repeat linarith
          . refine (Rat.le_iff_sub_nonneg (n) (n ^ 2)).mp ?_
            norm_cast
            refine Nat.le_self_pow ?_ n
            linarith
        . linarith

      exact Eq.symm (abs_of_nonneg h₅)

    rw [← a_eq]
    rw [← a'_eq] at h

    let b := ⌈Rat.divInt (m - 2) 2 * ↑(Int.subNatNat ((n + 1) ^ 2) (n + 1)) + ↑(n + 1)⌉

    have b_eq : b = ⌈Rat.divInt (m - 2) 2 * ↑(Int.subNatNat ((n + 1) ^ 2) (n + 1)) + ↑(n + 1)⌉ := by
      dsimp [b]

    let b' := |⌈Rat.divInt (m - 2) 2 * ((↑n + 1) ^ 2 - (↑n + 1)) + (↑n + 1)⌉|

    have b'_eq : b' = |⌈Rat.divInt (m - 2) 2 * ((↑n + 1) ^ 2 - (↑n + 1)) + (↑n + 1)⌉| := by
      dsimp [b']

    rw [← b_eq]
    rw [← b'_eq] at h

    have hbb' : b = b' := by
      dsimp [b]
      dsimp [b']
      simp
      have h₅ : ⌈Rat.divInt (m - 2) 2 * ((↑n + 1) ^ 2 - (↑n + 1)) + (↑n + 1)⌉ ≥ 0 := by
        refine Int.ceil_nonneg ?_
        refine Rat.add_nonneg ?_ ?_
        . refine Rat.mul_nonneg ?_ ?_
          . refine Rat.divInt_nonneg ?_ ?_
            . linarith
            . linarith
          . ring_nf
            norm_cast
            exact Nat.le_add_left 0 (n.add (n ^ 2))
        . linarith
      exact Eq.symm (abs_of_nonneg h₅)


    have h₄ : a ≥ 0 := by
      rw [haa']
      dsimp [a']
      exact abs_nonneg (⌈Rat.divInt (m - 2) 2 * (↑n ^ 2 - ↑n)⌉ + ↑n)

    have h₄' : b ≥ 0 := by
      rw [hbb']
      dsimp [b']
      exact abs_nonneg ⌈Rat.divInt (m - 2) 2 * ((↑n + 1) ^ 2 - (↑n + 1)) + (↑n + 1)⌉

    suffices h' : a ≤ b by
      have haabs : a = a.natAbs := by exact Int.eq_natAbs_of_zero_le h₄
      have hbabs : b = b.natAbs := by exact Int.eq_natAbs_of_zero_le h₄'
      rw [haabs, hbabs] at h'
      norm_cast at h'

    rw [← haa', ← hbb'] at h
    exact h

  have hsub : (m - 2 : ℚ) = (((m - 2) : ℤ) : ℚ) := by
    simp
  rw [hsub]
  let h₀ := polyform (m - 2) n hm'
  let h₀' := polyform (m - 2) (n + 1) hm'

  suffices h₁ : ((|⌈((m : ℚ) - 2) / 2 * (↑n ^ 2 - ↑n) + ↑n⌉|) : ℚ) ≤ |⌈((m : ℚ) - 2) / 2 * ((↑n + 1) ^ 2 - (↑n + 1)) + (↑n + 1)⌉| by
    norm_cast
    norm_cast at h₁

  simp
  simp at h₀
  simp at h₀'

  rw [← h₀, ← h₀']

  refine add_le_add ?_ ?_
  . refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
    . simp
    . linarith
    . refine div_nonneg ?_ rfl
      norm_cast
      linarith
    . simp
      refine le_self_pow₀ ?_ ?_
      . linarith
      . linarith
  . linarith

lemma getnthpoly_polyone (m : ℤ) (hm : m ≥ 3) : (getnthpoly m 1 hm) = PolyOne m hm := by
  dsimp [getnthpoly]
  dsimp [PolyOne]
  simp

lemma getnthpoly_intone (m : ℤ) (hm : m ≥ 3) : (getnthpoly m 1 hm).val = 1 := by
  dsimp [getnthpoly]
  simp

lemma getnthpoly_geq (m : ℤ) (n : ℕ) (hm : m ≥ 3) : (getnthpoly m n hm).val ≥ n := by
  dsimp [getnthpoly]
  have h₀ : (((m - 2) : ℤ) : ℚ) / 2 * (↑n ^ 2 - ↑n) + ↑n = |⌈(((m - 2) : ℤ) : ℚ)/ 2 * (↑n ^ 2 - ↑n) + ↑n⌉| := by
    -- apply polyform m n hm
    apply polyform (m - 2) n
    linarith

  have hm2 : (((m - 2) : ℤ) : ℚ) = m - 2 := by simp

  rw [hm2] at h₀
  let a :=  ((m : ℚ) - 2) / 2 * (↑n ^ 2 - ↑n) + ↑n
  have haeq : a = ((m : ℚ) - 2) / 2 * (↑n ^ 2 - ↑n) + ↑n := by rfl
  suffices h₁ : ((m : ℚ) - 2) / 2 * (↑n ^ 2 - ↑n) + ↑n ≥ n by
    rw [← haeq]
    rw [← haeq] at h₁

    have haeq' : a = |⌈a⌉| := by
      dsimp [a]
      rw [← hm2]
      apply polyform (m - 2) n
      linarith
    have hnab : ⌈a⌉.natAbs = a := by
      nth_rw 2 [haeq']
      exact Nat.cast_natAbs ⌈a⌉

    suffices h₂ : a ≥ n by
      rw [← hnab] at h₁
      norm_cast at h₁
    exact h₁
  simp

  refine Rat.mul_nonneg ?_ ?_
  . refine Rat.div_nonneg ?_ rfl
    norm_cast
    linarith
  . simp
    norm_cast
    refine Nat.le_self_pow ?_ n
    linarith

lemma poly_set (m : ℤ) (hm : m ≥ 3) : {x : ℕ | IsnPolygonal m x hm} = { (getnthpoly m n hm).val | n : ℕ} := by
  refine Set.ext ?_
  intro x
  constructor
  . intro h
    simp at h
    rw [PolyEquiv] at h
    dsimp [IsnPolygonal'] at h
    rcases h with g | g
    . simp
      use 0
      dsimp [getnthpoly]
      simp
      exact Eq.symm g
    . let ⟨ k, hk ⟩ := g
      simp
      use k
      dsimp [getnthpoly]
      have h' : (((m - 2) : ℤ) : ℚ) / 2 * (k ^ 2 - k) + k  = |⌈(((m - 2) : ℤ) : ℚ) / 2 * (↑k ^ 2 - ↑k) + k⌉| := by
        apply polyform (m - 2) k
        linarith

      suffices h₀ : (((m - 2) : ℤ) : ℚ) / 2 * (k ^ 2 - k) + k = x by
        have h₁ : |⌈(((m - 2) : ℤ) : ℚ) / 2 * (↑k ^ 2 - ↑k) + ↑k⌉| = ⌈(((m - 2) : ℤ) : ℚ) / 2 * (↑k ^ 2 - ↑k) + ↑k⌉.natAbs := by
          exact Int.abs_eq_natAbs ⌈(((m - 2) : ℤ) : ℚ) / 2 * (↑k ^ 2 - ↑k) + ↑k⌉
        suffices h₃ : |⌈(((m - 2) : ℤ) : ℚ) / 2 * (↑k ^ 2 - ↑k) + ↑k⌉| = x by
          rw [hk]
          simp
        rw [h₀]
        simp
      simp
      exact hk

  . simp
    intro a
    let k := getnthpoly m a hm
    intro h
    have hkeq : k.val = (getnthpoly m a hm).val := by rfl

    have hxk : x = k.val := by
      nth_rw 2 [h] at hkeq
      exact Eq.symm hkeq
    rw [hxk]
    let ⟨ k', p⟩ := k
    exact p

---- =================================================== --------

-- def LEPolygonal (m : ℤ) (hm : m ≥ 3) (b : ℕ) := Subtype (fun (n : Polygonal m hm) ↦ n.val ≤ b)
-- def LEPolygonal (m : ℤ) (hm : m ≥ 3) (b : ℕ) := {n : Polygonal m hm // n.val ≤ b}
-- instance : Fintype (LEPolygonal m hm b) where
--   elems :=
--     let S := Fin b
--     let S' := { (getnthpoly m (x : ℕ) hm) | (x : ℕ) ∈ Fin b}
--     -- let S' : Multiset ℕ := Multiset.set
--     -- let S : Finset ℕ  := ⟨ ({a | a ≤ b} : Multiset (Polygonal m hm)), sorry ⟩
--     sorry
--   complete := sorry

def getnthpolyfun (m : ℤ) (hm : m ≥ 3) (x : ℕ) : Polygonal m hm := getnthpoly m x hm

example (m : ℤ) (hm : m ≥ 3) (b : ℕ) : Set.Finite ((getnthpolyfun m hm) '' {x | x ≤ b}) := by
  exact Set.toFinite (getnthpolyfun m hm '' {x | x ≤ b})

def getlepoly₀ (m : ℤ) (hm : m ≥ 3) (b : ℕ) : Set (Polygonal m hm) :=
  let S := (getnthpolyfun m hm) '' {x | x ≤ b}
  have hf : Set.Finite S := by
    exact Set.toFinite S

  let MS : Multiset (Polygonal m hm) := ⟨ S, hf ⟩


  sorry

-- def getuptonthpoly (m : ℤ) (b : ℕ) (hm : m ≥ 3) : Finset (LEPolygonal m hm b) :=
--   let S : Finset (LEPolygonal m hm b) := { ⟨ getnthpoly m x hm, sorry ⟩  | h : x ≤ b }

--   S


def getlepoly (m : ℤ) (n : ℕ) (hm : m ≥ 3) : Finset (Polygonal m hm) :=
  let rec loop (i : ℕ) (s : Finset (Polygonal m hm)) : Finset (Polygonal m hm) :=
    match i with
    | 0 => s
    | i + 1 =>
      let poly := getnthpoly m (i + 1) hm
      if poly.val ≤ n then
        loop (i) (insert poly s)
      else
        loop (i) s
  termination_by i

  let S' := loop n Finset.empty
  S'

def getlepoly_helper (m : ℤ) (n : ℕ) (hm : m ≥ 3) (i : ℕ) (s : Finset (Polygonal m hm)) : Finset (Polygonal m hm) :=
  have h₀ : IsnPolygonal m 0 hm := by
    dsimp [IsnPolygonal]
    left
    simp
  match i with
  | 0 => (insert (PolyZero m hm) s)
  | i + 1 =>
    let poly := getnthpoly m (i + 1) hm
    if poly.val ≤ n then
      getlepoly_helper m n hm i (insert poly s)
    else
      getlepoly_helper m n hm i s

def getlepoly' (m : ℤ) (n : ℕ) (hm : m ≥ 3) : Finset (Polygonal m hm) :=
  getlepoly_helper m n hm n Finset.empty

lemma getlepoly_helper_subset (m : ℤ) (n : ℕ) (hm : m ≥ 3) (i : ℕ) : ∀ s : Finset (Polygonal m hm), s ⊆ getlepoly_helper m n hm i s := by
  induction i with
  | zero =>
    intro s
    rw [getlepoly_helper]
    exact Finset.subset_insert (PolyZero m hm) s
  | succ i hi =>
    intro s
    rw [getlepoly_helper]
    split
    . case isTrue ha =>
      intro p
      intro h
      have hss₁ : s ⊆ (insert (getnthpoly m (i + 1) hm) s) := Finset.subset_insert (getnthpoly m (i + 1) hm) s
      let q := (insert (getnthpoly m (i + 1) hm) s)
      have hqeq : q = insert (getnthpoly m (i + 1) hm) s := by
        exact rfl
      have hq : p ∈ q := by
        exact hss₁ h
      rw [← hqeq]
      exact hi q (hss₁ h)
    . case isFalse ha =>
      exact hi s

-- #eval (({ x : Polygonal 3 (by linarith) | x.val ≤ 10 }) : Finset (Polygonal 3 (by linarith))).size

example (m : ℤ) (n : ℕ) (hm : m ≥ 3) : getlepoly' m n hm = { x : Polygonal m hm | x.val ≤ n } := by
  refine Set.ext ?_
  intro p
  constructor
  . intro h
    induction n with
    | zero =>
      simp
      dsimp [getlepoly', getlepoly_helper] at h
      simp at h
      rcases h with g | g
      . sorry
      . contrapose g
        exact Finset.disjoint_singleton_left.mp fun ⦃x⦄ a a ↦ a
    | succ n hn =>
      dsimp [getlepoly', getlepoly_helper] at h
      simp at *
      suffices h' : p ∈ getlepoly' m n hm by
        apply hn at h'
        linarith

      split at h
      . sorry
      . rw [getlepoly_helper.eq_def] at h
        simp at h
        match n with
        | 0 =>
          simp at h
          sorry
        | i + 1 =>
          simp at h
          rw [getlepoly']
          split at h
          .
            sorry
          . sorry
  . sorry


theorem getlepolyCorrect (m : ℤ) (n : ℕ) (hm : m ≥ 3) : getlepoly' m n hm = { x : Polygonal m hm | x.val ≤ n } := by
  dsimp [getlepoly']
  refine Set.ext ?_
  intro p
  constructor
  . intro h
    simp at h
    refine Set.mem_setOf.mpr ?_
    rw [getlepoly_helper.eq_def] at h

    match n with
    | 0 =>
      simp
      simp at h
      rcases h with g | g
      . sorry
      . sorry
    | i + 1 =>
      simp
      simp at h
      split at h
      . sorry
      . sorry

    -- split at h
    -- . simp
    --   simp at h
    --   rcases h with g | g
    --   . sorry
    --   . sorry
    -- . simp
    --   simp at h
    --   split at h
    --   . rw [getlepoly_helper.eq_def] at h
    --     sorry
    --   . sorry
  . intro h
    simp
    simp at h
    rw [getlepoly_helper.eq_def]
    match n with
    | 0 =>
      simp
      simp at h
      left
      sorry
    | i + 1 => sorry

def S := { x : Polygonal 4 (by simp) | x.val ≤ 879 }

-- #eval S

#eval getlepoly 5 879 (by simp)
#eval getlepoly' 5 879 (by simp)


-- def IsNKPoly (m : ℤ) (n : ℕ) (k : ℕ) (hm : m ≥ 3) :=



/-
  ==================== Helper Functions ====================
  The following are helper functions **not formally verified** in Lean4
-/


/-
def getnthpoly (m : ℤ) (n : ℕ) (hm : m ≥ 3) : Polygonal m hm :=
  let num : ℚ := (((m : ℚ) - 2) / 2) * (n ^2 - n) + n
  have hnum : num  = ⌈ num ⌉ := by
    dsimp [num]
    have h : (m : ℚ) - 2 = (((m - 2) : ℤ) : ℚ) := by simp
    rw [h]
    apply polyform (((m - 2) : ℤ)) n

  have h : IsnPolygonal m ⌈ num ⌉ hm := by
    rw [PolyEquiv]
    unfold IsnPolygonal'
    use n
    simp
    rw [← hnum]

  ⟨ ⌈ num ⌉, h ⟩


#eval getnthpoly 4 1 (by simp)

/--
 Test whether the a'th polygonal number is equal to n.
-/
def ismnapoly_helper (m n : ℤ) (a : ℕ) (hm : m ≥ 3) : Bool :=
  match a with
  | 0 => false
  | k + 1 => if ((getnthpoly m (k + 1) hm).val== n) then true else (ismnapoly_helper m n k hm)

/--
  Test whether n is a polygonal number of order m, by checking if it's the
  k'th polygonal number, decrementing k until it reaches 0
  (here k is n, but there are probably better upper bounds for a)
-/
def ismnpoly (m n : ℤ) (hm : m ≥ 3) : Bool := ismnapoly_helper m n n.natAbs hm

#eval ismnpoly 3 15 (by simp)


--
-- Given `s` and `x`, if `x` is an s-gonal number, returns
-- `some n` so that x is the nth s-gonal number. Otherwise
-- returns `none`.
def nthPolygonal (s x : Nat) : Option Nat :=
  let sq := if (s < 4) then 8 * (s - 2) * x + (4 - s) ^ 2 else 8 * (s - 2) * x + (s - 4) ^ 2
  if IsSquare sq then
    let r := dbgTraceVal <| Nat.sqrt sq
    let d := 2 * (s - 2)
    if (r + s - 4) % d == 0 then
      some <| (r + s - 4) / d
    else
      none
  else
    none


#eval nthPolygonal 3 55 -- some 10
#eval nthPolygonal 4 17 -- none
#eval nthPolygonal 6 66 -- some 6
-/


/-
  A `Polygonal` number of order $3$ is triangular.
-/
-- lemma PolyThreeIsTriangular (a : ℕ) : IsnPolygonal 3 a hm = (IsTriangular a) := by
--   unfold IsnPolygonal
--   unfold IsTriangular
--   simp
--   have htwoa : 2 * (a : ℚ) = (((2 * a) : ℤ) : ℚ) := by simp
--   constructor
--   . intro h
--     let ⟨ k, hk ⟩ := h
--     use k
--     have hiff : k * (k + 1) = 2 * a ↔ k * (k + 1) = 2 * (a : ℚ) := by
--       constructor
--       . intro h
--         rw [htwoa]
--         rw [← h]
--         simp
--       . intro h
--         have hkr : (k : ℚ) * (k + 1) = ((k * (k + 1) : ℤ)) := by
--           simp
--         rw [hkr, htwoa] at h
--         sorry
--         -- exact Eq.symm ((fun {a b} ↦ Real.intCast_inj.mp) (id (Eq.symm h)))
--     apply hiff.mpr
--     rw [← hk]
--     ring_nf
--   . intro h
--     let ⟨ k, hk ⟩ := h
--     ring_nf
--     use k
--     rw [← add_mul]
--     simp
--     have honetwo (a b : ℚ) : 2 * a = 2 * b → a = b := by
--       intro hone
--       apply mul_left_cancel₀ two_ne_zero hone

--     apply honetwo

--     rw [htwoa]
--     rw [← hk]
--     ring_nf
--     simp
