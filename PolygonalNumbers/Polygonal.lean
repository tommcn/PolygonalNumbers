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
def IsnPolygonal (s : ℤ) (_ : s ≥ 3) (n : ℕ)  := n = 0 ∨ ∃ (k : ℕ), (((s : ℚ) - 2) / 2) * (k * (k - 1)) + k = n
def IsnPolygonal' (s : ℤ) (_ : s ≥ 3) (n : ℕ)  := n = 0 ∨ ∃ (k : ℕ), (((s : ℚ) - 2) / 2) * (k^2 - k) + k = n
def IsnPolygonal'' (s : ℤ) (_ : s ≥ 3) (n : ℕ) := n = 0 ∨ ∃ (k : ℕ), (((s : ℚ)- 2)*k^2 - (s - 4)*k) / 2 = n
def IsnPolygonal₀ (s : ℤ) (_ : s ≥ 3) (n : ℕ) := n = 0 ∨ (IsSquare (8*(s-2)*n + (s-4)^2)
                        ∧ (Int.sqrt (8*(s-2)*n + (s-4)^2) + (s - 4)) % (2 * (s - 2)) = 0)


def Triangular := Subtype (fun (n : ℕ) ↦ IsTriangular n)
def Polygonal (s : ℤ) (hs : s ≥ 3) := Subtype (fun (n : ℕ) ↦ IsnPolygonal s hs n)


def foldrfun (s : ℤ) (hs : s ≥ 3) := fun (x1 : Polygonal s hs) (x2 : ℤ) ↦ x1.val + x2

instance : LeftCommutative (foldrfun n hs : Polygonal n hs → ℤ → ℤ) where
  left_comm := by
    intro a b c
    simp [foldrfun]
    ring

def sumPolyToInt (s : ℤ) (hs : s ≥ 3) (S : List (Polygonal s hs)) : ℤ := S.foldr (foldrfun s hs) 0


/--
  Both conditions `IsnPolygonal` and `IsnPolygonal'` are equivalent.
-/
lemma kfactq (k : ℚ) : k * (k - 1) = k^2 - k := by
  ring

lemma PolyEquiv: IsnPolygonal = IsnPolygonal' := by
  unfold IsnPolygonal IsnPolygonal'
  funext s hs a
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
  funext s hs a
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
  funext s hs a
  apply propext

  have hcasesthr : s = 3 ∨ s > 3 := by
    exact Or.symm (LE.le.gt_or_eq hs)

  constructor
  . intro h
    dsimp [IsSquare]
    -- let ⟨ k, ⟨ hk, hnez ⟩ ⟩ := h
    -- let ⟨ k, hk ⟩ := h
    let hcpy := h
    dsimp [IsnPolygonal] at hcpy
    have hexzero : a = 0 ∨ a > 0 := by
      exact Nat.eq_zero_or_pos a
    rcases hexzero with hzero | hpos
    . left; exact hzero

    -- rcases hcpy with hzero | h₁
    -- . left; exact hzero
    right
    have hexne : a ≠ 0 := by exact Nat.not_eq_zero_of_lt hpos
    have hexz : a = 0 ↔ False := by exact iff_false_intro hexne
    rw [hexz] at hcpy
    simp at hcpy

    let ⟨ k, hk ⟩ := hcpy
    have hsqrtsq : 8 * (s - 2) * a + (s - 4) ^ 2 = (2 * k * (s - 2) - (s - 4)) * (2 * k * (s - 2) - (s - 4)) := by
      have hev : Even ((s - 2) * k ^ 2 - (s - 4) * k) := by
        refine Int.even_sub.mpr ?_
        constructor
        . intro heven
          refine Int.even_mul.mpr ?_
          apply Int.even_mul.mp at heven
          rcases heven with h₁ | h₁
          . left
            refine (Int.even_sub).mpr ?_
            . have hmnet : s ≠ 3 := by
                contrapose h₁
                simp at h₁
                simp
                rw [h₁]
                simp
              have hmgtf : s > 3 := by
                exact lt_of_le_of_ne hs (id (Ne.symm hmnet))
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
      have hint : ((s - 2) * k ^ 2 - (s - 4) * k) / 2 = a := by
        refine Eq.symm (Int.eq_ediv_of_mul_eq_right ?_ ?_)
        linarith
        have hq : (((s : ℚ) - 2) * k ^ 2 - (s - 4) * k) = 2 * a := by
          rw [← hk]
          ring
        apply Eq.symm
        have htx : (2 * (a : ℚ)) = (((2 * a) : ℤ) : ℚ) := by
          simp

        have htmk : ((s : ℚ) - 2) * k ^ 2 - (s - 4) * k = ((((s - 2) * k ^ 2 - (s - 4) * k) : ℤ) : ℚ) := by
          simp
        rw [htx, htmk] at hq
        exact Eq.symm ((fun {a b} ↦ Rat.intCast_inj.mp) (id (Eq.symm hq)))
      rw [← hint]
      have hexr : ∃ (r : ℤ), ((s - 2) * k ^ 2 - (s - 4) * k) = 2 * r := by
        exact Even.exists_two_nsmul ((s - 2) * k ^ 2 - (s - 4) * k) hev
      let ⟨ r, hr ⟩ := hexr
      calc 8 * (s - 2) * (((s - 2) * k ^ 2 - (s - 4) * k) / 2) + (s - 4) ^ 2
        _ = 4 * (s - 2) * (((s - 2) * k ^ 2 - (s - 4) * k)) + (s - 4) ^ 2 := by
          rw [hr]
          simp
          ring
        _ = ((2 * (s - 2) * k) - (s - 4))^2 := by ring
      ring

    have hexzero : a = 0 ∨ a > 0 := by
      exact Nat.eq_zero_or_pos a

    constructor
    . rw [PolyEquiv'] at h
      use (2 * k * (s - 2) - (s - 4))
    . rw [hsqrtsq]
      have hintsqrt : Int.sqrt ((2 * k * (s - 2) - (s - 4)) * (2 * k * (s - 2) - (s - 4))) = (2 * k * (s - 2) - (s - 4)).natAbs := by
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
        have habs : 4 - s ≥ 0 ∨ 4 - s < 0 := by
          exact Int.le_or_lt 0 (4 - s)
        rcases habs with hnonneg | hneg
        . have habs' : abs (4 - s) = 4 - s := by
            exact abs_of_nonneg hnonneg
          rw [habs']
          simp
        . have habs' : abs (4 - s) = -(4 - s) := by
            exact abs_of_neg hneg
          rw [habs']
          simp
          rw [hzero] at hk
          simp at hk
          exfalso
          have hnez : 0 ≠ (a : ℚ) := by
            apply Ne.symm
            apply Nat.cast_ne_zero.mpr
            exact hexne
          contradiction
      . have htsqrtpos : 2 * k * (s - 2) - (s - 4) ≥ 0 := by
          rcases hcasesthr with hthree | hneqthree
          . rw [hthree]
            linarith
          . simp
            have hmt : s - 2 > 0 := by
              linarith
            refine Int.le_add_of_sub_right_le ?_
            calc s - 4
              _ ≤ 2 * (s - 2) := by linarith
            refine Int.mul_le_mul_of_nonneg_right ?_ ?_
            . linarith
            . linarith

        have habs : |2 * k * (s - 2) - (s - 4)| = 2 * k * (s - 2) - (s - 4) := by
          exact abs_of_nonneg htsqrtpos

        rw [habs]
        ring

  . have hexzerocases : a = 0 ∨ a > 0 := by exact Nat.eq_zero_or_pos a
    rcases hexzerocases with hzero | hpos
    . intro _; dsimp [IsnPolygonal]; left; exact hzero
    intro h₁
    have hand : IsSquare (8 * (s - 2) * ↑a + (s - 4) ^ 2) ∧ (Int.sqrt (8 * (s - 2) * ↑a + (s - 4) ^ 2) + (s - 4)) % (2 * (s - 2)) = 0 := by
      have hexne : a ≠ 0 := by exact Nat.not_eq_zero_of_lt hpos
      have hexz : a = 0 ↔ False := by exact iff_false_intro hexne
      rw [hexz] at h₁
      simp at h₁
      simp
      exact h₁
    -- let ⟨ hsq, hdiv ⟩ := hand
    let ⟨ ⟨ r', hr' ⟩, h₂ ⟩ := hand
    have hrest : ∃ (r : ℤ), 8 * (s - 2) * ↑a + (s - 4) ^ 2 = r * r ∧ r ≥ 0 := by
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

    let rm₄ := r.natAbs + (s - 4)
    have hf : 2 * ((s : ℝ) - 2) > 0 := by
        refine mul_pos ?_ ?_
        simp
        ring_nf
        suffices h : 2 < s by
          have ht : (2 : ℝ) < s := by
            exact Int.cast_lt.mpr h
          exact lt_neg_add_iff_lt.mpr ht
        linarith
    have hf₂ : 2 * ((s : ℝ) - 2) ≠ 0 := by exact Ne.symm (ne_of_lt hf)
    have hfq : 2 * ((s : ℚ) - 2) > 0 := by
        refine mul_pos ?_ ?_
        simp
        have hsr : (s : ℚ) ≥ 3 := by
          exact Int.ceil_le.mp hs
        linarith
    have hf₂q : 2 * ((s : ℚ) - 2) ≠ 0 := by exact Ne.symm (ne_of_lt hfq)
    have htwo : (2 * ((s : ℚ) - 2)) /  (2 * ((s : ℚ) - 2)) = 1 := by
        rw [div_self]
        exact hf₂q
    have heq : ((((rm₄) / (2 * (s - 2))) : ℤ) : ℚ) = (rm₄ : ℚ) / (2 * (s - 2)) := by
      have hl : ((((rm₄ / (2 * (s - 2))) : ℚ) * (2 * (s - 2)))) = rm₄ := by
        refine
          Eq.symm
            ((fun a b ↦ (Mathlib.Tactic.Rify.ratCast_eq a b).mpr) (↑rm₄)
              (↑rm₄ / (2 * (↑s - 2)) * (2 * (↑s - 2))) ?_)
        simp
        refine Eq.symm (div_mul_cancel_of_imp ?_)
        intro h
        exfalso
        have hf₃ : 2 * ((s : ℝ) - 2) = 0 ∧ 2 * ((s : ℝ) - 2) ≠ 0:= by
          constructor
          exact h
          exact hf₂

        simp at hf₃
      refine eq_div_of_mul_eq ?_ ?_
      . exact hf₂q
      . --let ⟨ hdiv, hneq ⟩ := h₂
        let hdiv := h₂
        have hex : ∃ (k : ℤ), rm₄ = (2 * (s - 2)) * k := by
          dsimp [rm₄]
          refine exists_eq_mul_right_of_dvd ?_
          exact Int.dvd_of_emod_eq_zero hdiv

        have hmodrm : rm₄ % (2 * (s - 2)) = 0 := by
          dsimp [rm₄]
          exact Int.emod_eq_zero_of_dvd hex

        have hexrm : ∃ (k : ℤ), rm₄ = 2 * (s - 2) * k := by
          refine dvd_iff_exists_eq_mul_right.mp ?_
          exact Int.dvd_of_emod_eq_zero hdiv

        let ⟨ k, hk ⟩ := hex
        rw [hk]
        simp
        calc 2 * ((s : ℚ) - 2) * k / (2 * (s - 2)) * (2 * (s - 2))
          _ = k * ((2 * ((s : ℚ) - 2)) / (2 * (s - 2))) * (2 * (s - 2)) := by ring
          _ = k * 1 * (2 * (s - 2)) := by rw [htwo]
        ring

    have heq' : ((((rm₄) / (2 * (s - 2))).natAbs) : ℚ) = abs ((rm₄) / (2 * (s - 2))) := by
      exact Nat.cast_natAbs (rm₄ / (2 * (s - 2)))

    have heq'' : (abs ((rm₄) / (2 * (s - 2))) : ℤ) = abs (((rm₄ : ℚ)) / (2 * (s - 2))) := by
      rw [← heq]
      exact Int.cast_abs

    rcases hcasesthr with heqthree | hneqthree
    . rw [heqthree]
      simp
      right
      use ((rm₄) / (2 * (s - 2))).natAbs
      rw [heq',heq'']
      have hrm₄thr : rm₄ = r.natAbs - 1 := by
        dsimp [rm₄]
        rw [heqthree]
        ring

      have reqzeroiff : r = 0 ↔ 8 * (s - 2) * a + (s - 4) ^ 2 = 0:= by
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
        have hfal : 8 * (a : ℤ) + 1 = 0 := by
          rw [heqthree, hzero] at hr
          simp at hr
          exact hr
        have hfal' : 8 * (a : ℤ) = -1 := by
          exact (Int.add_left_inj 1).mp hfal
        have hxgeq : (a : ℤ) ≥ 0 := by
          linarith
        have hxgeq' : 8 * (a : ℤ) ≥ 0 := by
          exact Int.le.intro_sub (8 * a + 0) rfl
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

        . have hgeqzero : (rm₄ / (2 * (s - 2))) ≥ 0 := by
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

          have hrm₄abs : (rm₄ / (2 * (s - 2))).natAbs = (rm₄ / (2 * (s - 2))) := by
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
          have hstep1 : 8 * (a : ℚ) + 1 = r * r := by
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

          have hxeq : (a : ℚ) = 8⁻¹ * ((r : ℚ) * r - 1) := by
            suffices hassumpt : 8 * (a : ℚ) = (r : ℚ) * r - 1 by
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
    use (rm₄ / (2 * (s - 2))).natAbs

    have hrn : r.natAbs * r.natAbs = r * r := by simp
    have hrnq : (r.natAbs : ℚ) * r.natAbs = r * r := by
      apply Eq.symm
      calc (r : ℚ) * r
        _ = ((r * r) : ℤ) := by exact Eq.symm (Rat.intCast_mul r r)
      rw [← hrn]
      apply Eq.symm
      exact Eq.symm (Rat.intCast_mul ↑r.natAbs ↑r.natAbs)

    have hrq : 8 * (s - 2) * a + (s - 4) ^ 2 = (r : ℚ) * r := by
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

    have h : a = ((r.natAbs : ℚ) * r.natAbs - (s-4)^2) / (8 *(s-2)) := by
      rw [hrnq]
      rw [← hrq]
      simp
      apply Eq.symm
      have h : (s - 2) / (s - 2) = 1 := by
        refine Int.ediv_self ?_
        linarith

      have hemtq : (8*((s : ℚ)-2)) / ((8*(s-2))) = 1 := by
        refine div_self ?_
        simp
        have hmt : (s : ℚ) - 2 > 0 := by
          linarith
        exact right_ne_zero_of_mul hf₂q


      calc
        _ = (((8*(s-2))) * (a : ℚ) ) / (8*(s-2)) := by ring
        _ = (a * ((8*(s-2)))) / (8*(s-2)) := by rw [mul_comm]
        _ = a * ((8*(s-2)) / (8*(s-2))) := by ring
        _ = a * 1 := by rw [hemtq]
      simp
    rw [h]

    have hrm₄abs : (rm₄ / (2 * (s - 2))).natAbs = (rm₄ / (2 * (s - 2))) := by
      refine Int.natAbs_of_nonneg ?_
      refine (Int.div_nonneg_iff_of_pos ?_).mpr hrm₄geqzero
      linarith

    have hrm₄qeq : (((rm₄ / (2 * (s - 2))).natAbs) : ℚ) = (((rm₄ / (2 * (s - 2))) : ℤ) : ℚ) := by
      exact Rat.ext hrm₄abs rfl

    rw [hrm₄qeq]
    rw [heq]

    have heq' : ((r.natAbs + (s - 4)) : ℤ) = ((r.natAbs + (s - 4)) : ℚ) := by
      simp
      rw [@Int.cast_natAbs]
      exact Eq.symm Int.cast_abs
      -- have heq'' : (r).natAbs

    have hmtwo : (((s : ℚ) - 2) / (2 * (s - 2))) = 1 / 2 := by
      calc (((s : ℚ) - 2) / (2 * (s - 2)))
        _ = 2 / 2 * ((s - 2) / (2 * (s - 2))):= by ring
        _ = 1 / 2 * 2 * ((s - 2) / (2 * (s - 2))):= by ring
        _ = 1 / 2 * (2 * (s - 2) / (2 * (s - 2))):= by ring
        _ = 1 / 2 * (1):= by rw [htwo]
        _ = 1 / 2 := by simp
    -- constructor
    calc ((s : ℚ) - 2) / 2 * (rm₄ / (2 * (s - 2)) * (rm₄ / (2 * (s - 2)) - 1)) + rm₄ / (2 * (s - 2))
      _ = ((s - 2) / 2) * ((rm₄ / (2 * (s - 2))) * (rm₄ / (2 * (s - 2)) - 1)) + (rm₄ / (2 * (s - 2))) := by simp
      _ = ((s - 2) / 2) * ((rm₄ / (2 * (s - 2))) * (rm₄ / (2 * (s - 2)) - ((2 * (s - 2)) / (2 * (s - 2))))) + (rm₄ / (2 * (s - 2))) := by rw [htwo]
      _ = ((s - 2) / 2) * ((rm₄ / (2 * (s - 2))) * ((rm₄ - (2 * (s - 2))) / (2 * (s - 2)))) + (rm₄ / (2 * (s - 2))) := by ring
      _ = ((s - 2) / 2) * ((rm₄ / (2 * (s - 2))) * ((((r.natAbs + (s - 4)) : ℤ) - (2 * (s - 2))) / (2 * (s - 2)))) + (rm₄ / (2 * (s - 2))) := by dsimp [rm₄]
      _ = ((s - 2) / 2) * ((rm₄ / (2 * (s - 2))) * ((((r.natAbs + (s - 4))) - (2 * (s - 2))) / (2 * (s - 2)))) + (rm₄ / (2 * (s - 2))) := by rw [heq']
      _ = (1 / (2 * (s - 2))) * (((s - 2) / 2) * (rm₄ * (r.natAbs - s) / (2 * (s - 2))) + rm₄) := by ring
      _ = (1 / (2 * (s - 2))) * ((1 / 2) * ((s - 2)) * (rm₄ * (r.natAbs - s) / (2 * (s - 2))) + ((2 * (s - 2)) / (2 * (s - 2)) * rm₄)) := by rw [htwo]; ring
      _ = (1 / (2 * (s - 2))) * (((1 / 2) * ((rm₄ * r.natAbs - s * rm₄ + 4 * rm₄)) * ((s - 2) / (2 * (s - 2))))) := by ring
      _ = (1 / (2 * (s - 2))) * (((1 / 2) * ((rm₄ * r.natAbs - s * rm₄ + 4 * rm₄)) * (1 / 2))) := by rw [hmtwo]
      _ = ((1 / 4) * (1 / (2 * (s - 2)))) * (rm₄ * (r.natAbs - s + 4)) := by ring
      _ = ((1 / 4) * (1 / (2 * (s - 2)))) * (((r.natAbs + (s - 4)) : ℤ) * (r.natAbs - s + 4)) := by dsimp [rm₄]
      _ = ((1 / 4) * (1 / (2 * (s - 2)))) * ((r.natAbs + (s - 4)) * (r.natAbs - s + 4)) := by rw [heq']
      _ = ((1 / 4) * (1 / (2 * (s - 2)))) * (r.natAbs ^ 2 - s * r.natAbs + 4 * r.natAbs + (s - 4) * r.natAbs - (s - 4) * s + (s - 4) * 4) := by ring
      _ = ((1 / 4) * (1 / (2 * (s - 2)))) * (r.natAbs ^ 2 - s ^ 2 + 8 * s - 16) := by ring
      _ = ((1 / 4) * (1 / (2 * (s - 2)))) * (r.natAbs * r.natAbs - (s - 4) ^ 2) := by ring
      _ = ((1 / 4) * (1 / (2 * (s - 2)))) * (r * r - (s - 4) ^ 2) := by rw [hrnq]
    simp
    calc 4⁻¹ * (((s : ℚ) - 2)⁻¹ * 2⁻¹) * (r * r - (s - 4) ^ 2)
      _ = (r * r - (s - 4) ^ 2) * ((8)⁻¹ * ((s : ℚ) - 2)⁻¹)  := by ring
      _ = (r * r - (s - 4) ^ 2) * (8 * ((s : ℚ) - 2))⁻¹  := by
        simp
        left
        linarith
      _ = (r * r - (s - 4)^2) / (8 * (s - 2)) := by ring

    rw [hrnq]

instance : BEq (Polygonal s hs) where
  beq a b := if (a.val == b.val)
             then true
             else false


instance : LawfulBEq (Polygonal s hs) where
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

instance : DecidableEq (Polygonal s hs) :=
  fun a b =>
    if h : a.val = b.val then
      isTrue (by rw [a.eq_iff]; exact h)
    else
      isFalse (by rw [a.eq_iff]; exact h)


instance : LE (Polygonal s hs) where
  le a b := a.val ≤ b.val

lemma Polyrw (s : ℤ) (hs : s ≥ 3) (n : ℕ) : IsnPolygonal s hs n ↔ IsnPolygonal' s hs n := by
  rw [PolyEquiv]

theorem one_is_poly (s : ℤ) (hs : s ≥ 3) : IsnPolygonal s hs 1 := by
  dsimp [IsnPolygonal]
  right
  use 1
  simp

theorem zero_is_poly (s : ℤ) (hs : s ≥ 3) : IsnPolygonal s hs 0 := by
  dsimp [IsnPolygonal]
  simp

def PolyOne (s : ℤ) (hs : s ≥ 3) : Polygonal s hs := ⟨ 1, one_is_poly s hs ⟩
def PolyZero (s : ℤ) (hs : s ≥ 3) : Polygonal s hs := ⟨ 0, zero_is_poly s hs ⟩

#eval PolyZero (3) (by linarith) ≤ PolyOne (3) (by linarith)

#eval decide <| PolyOne (3) (by linarith) = PolyZero (3) (by linarith)

instance : Decidable (IsnPolygonal₀ m n h) := by
  dsimp [IsnPolygonal₀]
  exact instDecidableOr

instance : Decidable (IsnPolygonal m n h) := by
  apply decidable_of_iff (IsnPolygonal₀ m n h)
  refine Eq.to_iff ?_
  rw [PolyEquiv₀]


#eval decide <| IsnPolygonal 5 (by simp) 5 -- true
#eval decide <| IsnPolygonal 14 (by simp) 53 -- false
#eval decide <| IsnPolygonal 14 (by simp) 0  -- true


example : IsnPolygonal 5 (by decide) 5  := by
  decide +kernel -- works!


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

lemma polyformval (m : ℤ) (r : ℕ) (hm2geq3 : (m + 2) ≥ 3) : IsnPolygonal (m+2) hm2geq3 ⌈ (((m / 2) * (r^2 - r) + r) : ℚ) ⌉.natAbs := by
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

def getnthpoly (s : ℤ) (hs : s ≥ 3) (n : ℕ) : Polygonal s hs :=
  let num : ℚ := (((s : ℚ) - 2) / 2) * (n ^2 - n) + n
  have hnum : num  = |⌈ num ⌉| := by
    dsimp [num]
    have h : (s : ℚ) - 2 = (((s - 2) : ℤ) : ℚ) := by simp
    rw [h]
    apply polyform (((s - 2) : ℤ)) n
    linarith

  have h : IsnPolygonal s hs ⌈ num ⌉.natAbs  := by
    have hm' : (s - 2 + 2) ≥ 3 := by linarith
    dsimp [num]
    suffices h' :  IsnPolygonal (s - 2 + 2) hm' ⌈(((s - 2) : ℤ) : ℚ)/ 2 * (↑n ^ 2 - ↑n) + ↑n⌉.natAbs  by
      simp at h'
      simp
      exact h'
    refine polyformval (s - 2) n hm'

  ⟨ ⌈ num ⌉.natAbs, h ⟩

lemma getnthpoly_monotone (s : ℤ) (hs : s ≥ 3) (n : ℕ)  : (getnthpoly s hs n).val ≤ (getnthpoly s hs (n + 1)).val := by
  dsimp [getnthpoly]
  have hm' : s - 2 + 2 ≥ 3 := by linarith
  suffices h : |(⌈((s : ℚ) - 2) / 2 * (↑n ^ 2 - ↑n) + ↑n⌉)| ≤ |⌈((s : ℚ) - 2) / 2 * ((↑n + 1) ^ 2 - (↑n + 1)) + (↑n + 1)⌉| by
    norm_cast at h
    simp
    simp at h
    norm_cast

    have h₀ (m : ℤ) : m.natAbs = |m| := by
      simp

    let a := ⌈Rat.divInt (s - 2) 2 * ↑(Int.subNatNat (n ^ 2) n)⌉ + n
    have a_eq : a = ⌈Rat.divInt (s - 2) 2 * ↑(Int.subNatNat (n ^ 2) n)⌉ + n := by
      dsimp [a]

    let a' := |⌈Rat.divInt (s - 2) 2 * (↑n ^ 2 - ↑n)⌉ + ↑n|
    have a'_eq : a' = |⌈Rat.divInt (s - 2) 2 * (↑n ^ 2 - ↑n)⌉ + ↑n| := by
      dsimp [a']

    have haa' : a = a' := by
      dsimp [a]
      dsimp [a']
      simp

      have h₅ : ⌈Rat.divInt (s - 2) 2 * (↑n ^ 2 - ↑n)⌉ + n ≥ 0 := by
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

    let b := ⌈Rat.divInt (s - 2) 2 * ↑(Int.subNatNat ((n + 1) ^ 2) (n + 1)) + ↑(n + 1)⌉

    have b_eq : b = ⌈Rat.divInt (s - 2) 2 * ↑(Int.subNatNat ((n + 1) ^ 2) (n + 1)) + ↑(n + 1)⌉ := by
      dsimp [b]

    let b' := |⌈Rat.divInt (s - 2) 2 * ((↑n + 1) ^ 2 - (↑n + 1)) + (↑n + 1)⌉|

    have b'_eq : b' = |⌈Rat.divInt (s - 2) 2 * ((↑n + 1) ^ 2 - (↑n + 1)) + (↑n + 1)⌉| := by
      dsimp [b']

    rw [← b_eq]
    rw [← b'_eq] at h

    have hbb' : b = b' := by
      dsimp [b]
      dsimp [b']
      simp
      have h₅ : ⌈Rat.divInt (s - 2) 2 * ((↑n + 1) ^ 2 - (↑n + 1)) + (↑n + 1)⌉ ≥ 0 := by
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
      exact abs_nonneg (⌈Rat.divInt (s - 2) 2 * (↑n ^ 2 - ↑n)⌉ + ↑n)

    have h₄' : b ≥ 0 := by
      rw [hbb']
      dsimp [b']
      exact abs_nonneg ⌈Rat.divInt (s - 2) 2 * ((↑n + 1) ^ 2 - (↑n + 1)) + (↑n + 1)⌉

    suffices h' : a ≤ b by
      have haabs : a = a.natAbs := by exact Int.eq_natAbs_of_zero_le h₄
      have hbabs : b = b.natAbs := by exact Int.eq_natAbs_of_zero_le h₄'
      rw [haabs, hbabs] at h'
      norm_cast at h'

    rw [← haa', ← hbb'] at h
    exact h

  have hsub : (s - 2 : ℚ) = (((s - 2) : ℤ) : ℚ) := by
    simp
  rw [hsub]
  let h₀ := polyform (s - 2) n hm'
  let h₀' := polyform (s - 2) (n + 1) hm'

  suffices h₁ : ((|⌈((s : ℚ) - 2) / 2 * (↑n ^ 2 - ↑n) + ↑n⌉|) : ℚ) ≤ |⌈((s : ℚ) - 2) / 2 * ((↑n + 1) ^ 2 - (↑n + 1)) + (↑n + 1)⌉| by
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

lemma getnthpoly_polyone (s : ℤ) (hs : s ≥ 3) : (getnthpoly s hs 1) = PolyOne s hs := by
  dsimp [getnthpoly]
  dsimp [PolyOne]
  simp

lemma getnthpoly_intone (s : ℤ) (hs : s ≥ 3) : (getnthpoly s hs 1).val = 1 := by
  dsimp [getnthpoly]
  simp

lemma getnthpoly_geq (s : ℤ) (hs : s ≥ 3) (n : ℕ) : (getnthpoly s hs n).val ≥ n := by
  dsimp [getnthpoly]
  have h₀ : (((s - 2) : ℤ) : ℚ) / 2 * (↑n ^ 2 - ↑n) + ↑n = |⌈(((s - 2) : ℤ) : ℚ)/ 2 * (↑n ^ 2 - ↑n) + ↑n⌉| := by
    -- apply polyform m n hm
    apply polyform (s - 2) n
    linarith

  have hm2 : (((s - 2) : ℤ) : ℚ) = s - 2 := by simp

  rw [hm2] at h₀
  let a :=  ((s : ℚ) - 2) / 2 * (↑n ^ 2 - ↑n) + ↑n
  have haeq : a = ((s : ℚ) - 2) / 2 * (↑n ^ 2 - ↑n) + ↑n := by rfl
  suffices h₁ : ((s : ℚ) - 2) / 2 * (↑n ^ 2 - ↑n) + ↑n ≥ n by
    rw [← haeq]
    rw [← haeq] at h₁

    have haeq' : a = |⌈a⌉| := by
      dsimp [a]
      rw [← hm2]
      apply polyform (s - 2) n
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

lemma poly_set (s : ℤ) (hs : s ≥ 3) : {x : ℕ | IsnPolygonal s hs x} = { (getnthpoly s hs n).val | n : ℕ} := by
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
      have h' : (((s - 2) : ℤ) : ℚ) / 2 * (k ^ 2 - k) + k  = |⌈(((s - 2) : ℤ) : ℚ) / 2 * (↑k ^ 2 - ↑k) + k⌉| := by
        apply polyform (s - 2) k
        linarith

      suffices h₀ : (((s - 2) : ℤ) : ℚ) / 2 * (k ^ 2 - k) + k = x by
        have h₁ : |⌈(((s - 2) : ℤ) : ℚ) / 2 * (↑k ^ 2 - ↑k) + ↑k⌉| = ⌈(((s - 2) : ℤ) : ℚ) / 2 * (↑k ^ 2 - ↑k) + ↑k⌉.natAbs := by
          exact Int.abs_eq_natAbs ⌈(((s - 2) : ℤ) : ℚ) / 2 * (↑k ^ 2 - ↑k) + ↑k⌉
        suffices h₃ : |⌈(((s - 2) : ℤ) : ℚ) / 2 * (↑k ^ 2 - ↑k) + ↑k⌉| = x by
          rw [hk]
          simp
        rw [h₀]
        simp
      simp
      exact hk

  . simp
    intro a
    let k := getnthpoly s hs a
    intro h
    have hkeq : k.val = (getnthpoly s hs a).val := by rfl

    have hxk : x = k.val := by
      nth_rw 2 [h] at hkeq
      exact Eq.symm hkeq
    rw [hxk]
    let ⟨ k', p⟩ := k
    exact p


def getnthpolyfun (s : ℤ) (hs : s ≥ 3) (a : ℕ) : Polygonal s hs := getnthpoly s hs a

def getlepoly₀ (s : ℤ) (hs : s ≥ 3) (b : ℕ) : Finset (Polygonal s hs) :=
  let r : Finset ℕ := Finset.range (b + 1)
  let S := (getnthpolyfun s hs) '' r
  let FS : Finset (Polygonal s hs) := S.toFinset
  FS.filter (fun x ↦ x.val ≤ b)


#eval (getlepoly₀ 7 (by linarith) 146)
#eval decide <| IsnPolygonal 3 (by linarith) 1456

#check Decidable (∃ n < 2, IsnPolygonal 3 (by linarith) n)

def finCaseDec (p : ℕ → Prop) (n : ℕ) [DecidablePred p] : Decidable (∃ a < n + 1, (p a)) := by
  suffices h : Decidable (∃ a ∈ Finset.range (n + 1), p a) by
    simp at h
    exact h
  exact List.decidableBEx p (List.range (n + 1))


theorem getlepoly₀Correct (s : ℤ) (hs : s ≥ 3) (n : ℕ) : getlepoly₀ s hs n = { a : Polygonal s hs | a.val ≤ n } := by
  dsimp [getlepoly₀]
  refine Set.ext ?_
  intro p
  constructor
  . intro h
    simp
    simp at h
    let ⟨ a, ⟨ ha₁, ha₂ ⟩ ⟩ := h.left
    let h₁ := h.right
    exact h₁
  . intro h
    simp
    simp at h
    constructor
    . let ⟨a, ha⟩ := p
      dsimp [IsnPolygonal] at h
      dsimp [IsnPolygonal] at ha
      rcases ha with g | g
      . use 0
        dsimp [getnthpolyfun]
        dsimp [getnthpoly]
        simp
        apply Subtype.ext_iff_val.mpr
        simp
        exact Eq.symm g
      . let ⟨ k, hk ⟩ := g
        use k
        constructor
        . have h₂ : ((s : ℚ) - 2) / 2 * (k * (k - 1)) + k ≥ k := by
            simp
            refine Rat.mul_nonneg ?_ ?_
            . refine Rat.div_nonneg ?_ rfl
              norm_cast
              linarith
            . have hkp : (k : ℚ) ≥ 0 := by
                refine Nat.cast_nonneg' k
              have hk' : k = 0 ∨ k > 0 := by
                exact Or.symm (Nat.zero_le k).gt_or_eq
              rcases hk' with hkzero | hkpos
              . rw [hkzero]
                simp
              . have hkposq : (k : ℚ) ≥ 1 := by
                  exact Nat.one_le_cast.mpr hkpos
                refine Rat.mul_nonneg ?_ ?_
                linarith
                linarith
          rw [hk] at h₂
          simp at h₂
          linarith
        . dsimp [getnthpolyfun]
          dsimp [getnthpoly]

          have h₀ : (((s - 2) : ℤ) : ℚ) / 2 * (↑k ^ 2 - ↑k) + ↑k = |⌈(((s - 2) : ℤ) : ℚ)/ 2 * (↑k ^ 2 - ↑k) + ↑k⌉| := by
            apply polyform (s - 2) k
            linarith

          suffices h' :  (getnthpoly s hs k).val = a by
            dsimp [getnthpoly] at h'
            simp

            apply Subtype.ext_iff_val.mpr
            simp

            have h₂ : ⌈((s : ℚ) - 2) / 2 * (↑k ^ 2 - ↑k)⌉ + ↑k = ⌈((s : ℚ) - 2) / 2 * (↑k ^ 2 - ↑k) + k⌉ := by
              exact Eq.symm (Int.ceil_add_nat (((s : ℚ) - 2) / 2 * (↑k ^ 2 - ↑k)) k)

            rw [← h₂] at h'
            exact h'

          dsimp [getnthpoly]
          have hm2 : (((s - 2) : ℤ) : ℚ) = s - 2 := by simp
          rw [← hm2]
          rw [hm2] at h₀
          rw [← kfactq k] at h₀
          rw [h₀] at hk

          suffices h₁ : |⌈((s : ℚ) - 2) / 2 * (↑k * (↑k - 1)) + ↑k⌉| = ⌈((s : ℚ) - 2) / 2 * (↑k ^ 2 - ↑k) + ↑k⌉.natAbs by
            suffices h₂ : (a : ℚ) = (⌈((s : ℚ) - 2) / 2 * (↑k ^ 2 - ↑k) + ↑k⌉.natAbs : ℚ) by
              apply Eq.symm
              norm_cast
              norm_cast at h₂
            rw [← hk]
            rw [h₁]
            simp
            rw [← hm2]
            simp
            norm_cast
            norm_cast at h₁
            exact Eq.symm (Nat.cast_natAbs (⌈Rat.divInt (s - 2) 2 * ↑(Int.subNatNat (k ^ 2) k)⌉ + ↑k))
          simp
          rw [← kfactq k]
    . exact h

def IsNKPolygonal (s : ℤ) (hs : s ≥ 3) (k : ℕ) (n : ℕ) :=
  ∃ S : List ℕ, S.all (IsnPolygonal s hs) ∧ S.length = k ∧ S.sum = n

instance (m : ℤ) (hm : m ≥ 3): DecidablePred (IsNKPolygonal m hm 0) := by
  intro n
  unfold IsNKPolygonal
  match n with
  | 0  => have : ∃ S : List ℕ, S.all (IsnPolygonal m hm) ∧ S.length = 0 ∧ S.sum = 0 := by
            use []
            constructor
            . rw [List.all_nil]
            . exact Nat.eq_zero_of_add_eq_zero rfl
          exact (isTrue this)
  | k + 1 => have : ¬∃ S : List ℕ, S.all (IsnPolygonal m hm) ∧ S.length = 0 ∧ S.sum = k + 1 := by
               by_contra g
               obtain ⟨ polygonals, _, hpolygonalslen, hpolygonalssum ⟩ := g
               have : polygonals.sum = 0 := by
                 have : polygonals = [] := by exact List.length_eq_zero.mp hpolygonalslen
                 rw [this]
                 exact rfl
               rw [this] at hpolygonalssum
               set g := Nat.succ_ne_zero k
               apply g
               norm_cast at hpolygonalssum
             exact (isFalse this)

example : IsNKPolygonal 3 (by norm_num) 0 0 := by decide +kernel
example : ¬IsNKPolygonal 3 (by norm_num) 0 1 := by decide +kernel

instance (s : ℤ) (hs : s ≥ 3) (k : ℕ): DecidablePred (IsNKPolygonal s hs k) := by
  induction k with
  | zero => intro n; exact inferInstance
  | succ k ih =>
      intro n
      -- We show that whether n is the sum of k + 1 polygonals is decidable.

      -- Get the list of polygonals less than or equal to n
      let numsToTest := (List.range (n + 1)).filter (IsnPolygonal s hs)

      -- Filter the list down to those p such that n - p is the sum of
      -- k primes.
      let numList := numsToTest.filter (fun p ↦ IsNKPolygonal s hs k (n - p))

      if h : numList ≠ [] then
        -- If the list is nonempty, let p be the head.
        let p := numList.head h
        have claim1 : IsnPolygonal s hs p := by
          have : ∀ n ∈ numList, IsnPolygonal s hs n := by simp [numList, numsToTest]
          simp [p, this]

        -- Also, n - p is the sum of k primes.
        have claim2 : IsNKPolygonal s hs k (n - p) := by
          have : ∀ p ∈ numList, IsNKPolygonal s hs k (n - p) := by
            simp [numsToTest, numList]
            intro _ _ h _
            exact h
          apply this p
          exact List.head_mem h

        -- Then n is the sum of k + 1 polygonals.
        have pf : IsNKPolygonal s hs (k + 1) n := by
          -- Get the list of k primes whose sum is n - p
          obtain ⟨ polygonals', ⟨ hpolygonals, hpolygonalslen, hpolygonalssum ⟩ ⟩ := claim2
          -- Add p to the head of the list and this list has
          -- length k + 1 and sum to n.
          set polygonals := p :: polygonals'
          use polygonals
          constructor
          . simp [claim1, polygonals, hpolygonals]
          . simp [polygonals, hpolygonalssum]
            rw [add_comm, Nat.sub_add_cancel]
            constructor
            . exact hpolygonalslen
            . rfl
            suffices p ∈ numsToTest by simp [numsToTest] at this; linarith
            apply List.head_filter_mem

        exact (isTrue pf)
      else -- The list of p such that n - p is the sum of k polygonals is empty
        have pf : ¬IsNKPolygonal s hs (k + 1) n := by
          -- We proceed by contradiction.
          by_contra g
          simp [IsNKPolygonal] at g
          -- Get the list of k + 1primes whose sum is n
          obtain ⟨ polygonals, ⟨ hpolygonals, hpolygonalslen, hpolygonalssum ⟩ ⟩ := g

          -- It suffices to show that the list of p such that
          -- n - p is the sum of k primes is not empty
          apply h

          -- Let p be the head of the list.
          set p := polygonals.head (by exact List.ne_nil_of_length_eq_add_one hpolygonalslen)

          by_cases g : p > n
          . -- p > n can be easily excluded since it is part of the list of
            -- primes that sum to n.
            have : p ∈ polygonals := by exact List.head_mem (List.ne_nil_of_length_eq_add_one hpolygonalslen)
            obtain pge := List.le_sum_of_mem this
            obtain pgtn := Nat.lt_of_lt_of_le g pge
            simp [hpolygonalssum] at pgtn
          . -- We show that p is in the list of p' such that n - p' is the sum of k primes
            have : p ∈ numList := by
              dsimp [numList]
              rw [List.mem_filter]
              constructor
              . -- p ∈ numsToTest
                simp [numsToTest]
                constructor
                . simp at g
                  exact Order.lt_add_one_iff.mpr g
                . apply hpolygonals
                  exact List.head_mem (List.ne_nil_of_length_eq_add_one hpolygonalslen)
              . -- IsNKPolygonal m hm k (n - p)
                simp [IsNKPolygonal]
                use polygonals.tail
                simp [ hpolygonalslen, hpolygonalssum, p]
                constructor
                . intro p hp
                  apply hpolygonals
                  exact List.mem_of_mem_tail hp
                . refine Nat.eq_sub_of_add_eq ?_
                  rw [add_comm, ← List.sum_cons]
                  simp [hpolygonalssum]

            exact List.ne_nil_of_mem this

        exact isFalse pf


example : IsNKPolygonal 3 (by norm_num) 1 0 := by decide +kernel
example : IsNKPolygonal 3 (by norm_num) 1 1 := by decide +kernel
example : IsNKPolygonal 5 (by norm_num) 1 5 := by decide +kernel
example : IsnPolygonal 5 (by norm_num) 5 := by decide +kernel
example : ¬IsNKPolygonal 3 (by norm_num) 1 11 := by decide +kernel
example : IsNKPolygonal 5 (by norm_num) 4 10 := by decide +kernel
example : IsNKPolygonal 5 (by norm_num) 5 9 := by decide +kernel
example : ¬IsNKPolygonal 5 (by norm_num) 4 9 := by decide +kernel
example : IsNKPolygonal 5 (by norm_num) 5 21 := by decide +kernel -- quite slow
example : ¬IsNKPolygonal 5 (by norm_num) 4 21 := by decide +kernel -- quite slow
