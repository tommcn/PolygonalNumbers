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
          (hb : (m ≥ 4 ∧ n ≥ 53 * m) ∨ (m = 3 ∧ n ≥ 159 * m))
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

  have hprepa : ((m : ℤ) ≥ 4 ∧ n ≥ 53 * (m : ℤ)) ∨ ((m : ℤ) = 3 ∧ n ≥ 159 * (m : ℤ)) := by
    norm_cast
  let ⟨ b, r, hob, hblb, hbub, hrgeq0, hrm, hmdiv ⟩ := b_r n m hprepa


  -- let a : ℤ := 2 * ((n - b - r) / m) + b

  let bn : ℕ := b.natAbs

  have hr : (0 ≤ r ∧ r ≤ m - 3)  := by
    constructor
    . exact hrgeq0
    . exact hrm

  have hbpos : (b : ℝ) > 0 := by
    have mb' : 3 ≤ (m : ℤ) := by
      exact Nat.ofNat_le_cast.mpr mb
    have ngeq2m' : 2 * (m : ℤ) ≤ n := by
      exact Nat.cast_le.mpr ngeq2m
    exact I_lb_pos n m b r hr hblb mb' ngeq2m'
  have hbposq : (b : ℚ) > 0 := by
    exact Rat.cast_pos.mp hbpos


  have hbnbz : b = bn := by
    refine Int.eq_natAbs_of_zero_le ?_
    refine Int.le_of_lt ?_
    apply GT.gt.lt
    norm_cast at hbpos

  have hobnn : Odd bn := by
    exact Odd.natAbs hob

  have hbnez : 0 ≠ bn := by
    intro h
    have hoddz : Odd 0 := by
      rw [h]
      exact hobnn
    have hnoddz : ¬ Odd 0 := by exact Nat.not_odd_zero
    contradiction

  have hrna : r = r.natAbs := by
    exact Int.eq_natAbs_of_zero_le hrgeq0
  have hrnaq : (r : ℚ) = r.natAbs := by
    exact congrArg Int.cast hrna
  have hbnbq : (bn : ℚ) = (b : ℚ) := by
    exact Rat.ext (id (Eq.symm hbnbz)) rfl


  have hrmn : r.natAbs < m := by
    -- norm_cast at hrm
    norm_cast
    suffices hz : (r.natAbs : ℤ) < (m : ℤ) by
      exact Int.ofNat_lt.mp hz
    linarith

  have h3m : (3 : ℤ) ≤ m := by
    exact Nat.ofNat_le_cast.mpr mb

  have hmn' : (2 : ℤ) * m ≤ n := by
    exact Int.toNat_le.mp ngeq2m

  let hgd := main hr h3m hmn' hblb hbub hmdiv hob

  let ⟨ a, hao, hleft, hright, hazq ⟩ := hgd

  have hapos : a ≥ 0 := by
    have hbbreorg : b ^ 2 < 4 * a := by
      exact Int.lt_of_sub_neg hleft
    have h2bpos : b^2 ≥ 0 := by
      exact sq_nonneg b

    have h4a : 0 < 4 * a := by
      calc _
        0 ≤ b^2 := by exact h2bpos
        _ < 4 * a := by exact hbbreorg

    contrapose h4a
    simp
    simp at h4a
    exact Int.le_of_lt h4a

  have hleft' : b.natAbs ^ 2 < 4 * a := by
    dsimp [bn] at hbnbz
    rw [← hbnbz]
    exact Int.lt_of_sub_neg hleft

  have hright' : 3 * a < b.natAbs ^ 2 + 2 * b.natAbs + 4 := by
    dsimp [bn] at hbnbz
    rw [← hbnbz]
    exact Int.lt_of_sub_pos hright

  let ⟨ s, t, u, v, hstuv ⟩ := CauchyLemma a hapos b.natAbs hao hobnn hleft' hright'

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

  let ms₁ := List.replicate r.natAbs poly1

  have ms₃repl (r : ℕ) : List.replicate (r + 1) poly1 = poly1 :: List.replicate r poly1 := rfl

  have ms₁induc (r : ℕ) : sumPolyToInt (m+2) hm2geq3 (List.replicate r poly1) = r := by
    induction' r with r hr
    . simp [sumPolyToInt]
    . rw [ms₃repl]
      simp [sumPolyToInt]
      simp [foldrfun]
      simp [sumPolyToInt] at hr
      rw [hr]
      ring

  have ms₁sum' : List.foldr (foldrfun (↑m + 2) hm2geq3) 0 ms₁ = r.natAbs := by
    exact ms₁induc r.natAbs

  have ms₁card : ms₁.length = r.natAbs := by
    exact List.length_replicate r.natAbs poly1
  /-
    Equation (5)
  -/
  have h₂ : (n : ℚ) = ((m : ℚ) / 2) * ((a : ℚ) - b) + b + r.natAbs := by
    have hmeq : (m : ℚ) * (m : ℚ)⁻¹ = 1 := by
      exact Rat.mul_inv_cancel (↑m) hmnot0
    rw [hazq]
    simp
    ring
    rw [mul_comm] at hmeq
    rw [← mul_comm, ← mul_assoc, mul_comm]
    rw [hmeq]
    simp
    ring
    rw [mul_comm] at hmeq
    rw [hmeq]
    simp
    ring
    rw [mul_assoc, mul_comm, mul_assoc]
    rw [mul_comm] at hmeq
    rw [hmeq]
    ring
    rw [← hrnaq]
    simp


  /- The sum of the numbers is `n` -/
  have corsum : sl + tl + ul + vl + r.natAbs = n := by
    dsimp [sl, tl, ul, vl]
    rw [h₂, hstuv.left]
    rw [hbnbz]
    dsimp [bn]
    rw [hstuv.right]
    simp
    ring

  have corsum₀ : (((|⌈ sl ⌉| + |⌈ tl ⌉| + |⌈ ul ⌉| + |⌈ vl ⌉| + r.natAbs) : ℤ) : ℚ) = (n : ℤ) := by
    simp

    have hstep (x : ℚ) : |(⌈ x ⌉ : ℚ)| = |⌈ x ⌉| := by
      simp

    rw [hstep sl, hstep tl, hstep ul, hstep vl]
    rw [← slint, ← tlint, ← ulint, ← vlint]
    rw [← corsum]
    simp
    norm_cast
    exact Eq.symm (Nat.cast_natAbs r)

  have corsum' : |⌈ sl ⌉| + |⌈ tl ⌉| + |⌈ ul ⌉| + |⌈ vl ⌉| + r = n := by
    rw [hrna]
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
    exact Eq.symm ((fun {a b} ↦ Rat.intCast_inj.mp) (id (Eq.symm corsum₀)))
  . -- Proof its size is correct
    simp [S]
    rw [ms₁card]
    have hr : r + 3 ≤ m := by
      exact Int.add_le_of_le_sub_right hrm

    rw [hrna] at hr
    norm_cast at hr
