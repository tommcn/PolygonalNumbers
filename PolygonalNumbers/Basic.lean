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
          (mb : m ≥ 3)
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
  have hgeq159 : n ≥ 53 * m := by
    rcases hb with ⟨ _, g ⟩  | ⟨ _, g ⟩ <;> linarith

  have ngeq2m : n ≥ 2 * m := by
    linarith

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


  let poly1 : Polygonal (m+2) (by linarith) := ⟨ 1, one_is_poly (m+2) (hm2geq3)⟩

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



def p0 : IsnPolygonal 5 (by norm_num) 0 := by simp [IsnPolygonal];
def p1 : IsnPolygonal 5 (by norm_num) 1 := by simp [IsnPolygonal]; use 1; ring
def p5 : IsnPolygonal 5 (by norm_num) 5 := by simp [IsnPolygonal]; use 2; ring
def p12 : IsnPolygonal 5 (by norm_num) 12 := by simp [IsnPolygonal]; use 3; ring
def p22 : IsnPolygonal 5 (by norm_num) 22 := by simp [IsnPolygonal]; use 4; ring
def p35 : IsnPolygonal 5 (by norm_num) 35 := by simp [IsnPolygonal]; use 5; ring
def p51 : IsnPolygonal 5 (by norm_num) 51 := by simp [IsnPolygonal]; use 6; ring
def p70 : IsnPolygonal 5 (by norm_num) 70 := by simp [IsnPolygonal]; use 7; ring
def p92 : IsnPolygonal 5 (by norm_num) 92 := by simp [IsnPolygonal]; use 8; ring
def p117 : IsnPolygonal 5 (by norm_num) 117 := by simp [IsnPolygonal]; use 9; ring
def p145 : IsnPolygonal 5 (by norm_num) 145 := by simp [IsnPolygonal]; use 10; ring
def p176 : IsnPolygonal 5 (by norm_num) 176 := by simp [IsnPolygonal]; use 11; ring
def p210 : IsnPolygonal 5 (by norm_num) 210 := by simp [IsnPolygonal]; use 12; ring
def p247 : IsnPolygonal 5 (by norm_num) 247 := by simp [IsnPolygonal]; use 13; ring
def p287 : IsnPolygonal 5 (by norm_num) 287 := by simp [IsnPolygonal]; use 14; ring
def p330 : IsnPolygonal 5 (by norm_num) 330 := by simp [IsnPolygonal]; use 15; ring
def p376 : IsnPolygonal 5 (by norm_num) 376 := by simp [IsnPolygonal]; use 16; ring
def p425 : IsnPolygonal 5 (by norm_num) 425 := by simp [IsnPolygonal]; use 17; ring

def pentaExceptions : Finset ℕ := {9, 21, 31, 43, 55, 89}

theorem SumOfFourPentagonalNumber : ∀ n : ℕ, ¬ (n ∈ pentaExceptions) → IsNKPolygonal 5 (by norm_num) 4 n := by
  intro n

  have h : n ≥ 477 ∨ n < 477 := by
    exact le_or_lt 477 n


  rcases h with g | g
  . intro _

    have hb : 3 ≥ 4 ∧ n ≥ 53 * 3 ∨ 3 = 3 ∧ n ≥ 159 * 3 := by
      right
      simp
      linarith

    suffices hs : ∃ (S : List (Polygonal (5) (by linarith))),
        (sumPolyToInt (5) (by linarith) S  = n)
      ∧ (S.length ≤ 4) by
      dsimp [IsNKPolygonal]
      simp
      let ⟨ S, hn ⟩ := hs
      let S' : List ℕ := List.map (fun x ↦ x.val) S
      let S₀ : List ℕ := List.replicate (4 - S'.length) 0
      use (S₀.append S')
      simp
      and_intros
      . intro n
        intro h
        rcases h with g | g
        . unfold S₀ at g
          simp at g
          rw [g.right]
          exact zero_is_poly 5 (by linarith)
        . unfold S' at g
          simp at g
          let ⟨ a, ha ⟩ := g
          rw [← ha.right]
          let ⟨ a, hpa ⟩ := a
          exact hpa
      . have hlen : S₀.length = 4 - S'.length := by
          unfold S₀
          simp
        have hslen : S'.length ≤ 4 := by
          have hleneq : S'.length = S.length := by
            exact List.length_map S fun x ↦ x.val
          rw [hleneq]
          exact hn.right
        rw [hlen]
        exact Nat.sub_add_cancel hslen
      . have hs' : S'.sum = sumPolyToInt 5 (by linarith) S := by
          dsimp [S', sumPolyToInt]
          unfold foldrfun
          simp
          unfold List.sum
          rw [List.foldr_map (Nat.cast ∘ fun x ↦ x.val) (fun x1 x2 ↦ x1 + x2) S 0]
          simp
        have hs₀ : S₀.sum = 0 := by
          unfold S₀
          simp
        rw [hs₀]
        simp
        rw [hn.left] at hs'
        norm_cast at hs'

    apply CauchyPolygonalNumberTheorem 3 n (by linarith) hb
  . suffices h : ∀ n : ℕ, n < 477 ∧ ¬ (n ∈ pentaExceptions) → IsNKPolygonal 5 (by norm_num) 4 n by
      intro h'
      simp at h
      let g' := h n g h'
      exact g'

    simp [pentaExceptions]

    intro n hn

    interval_cases n
    . decide
    . simp; use [1, 0, 0, 0]; simp [p1, p0, p0, p0]
    . simp; use [1, 1, 0, 0]; simp [p1, p1, p0, p0]
    . simp; use [1, 1, 1, 0]; simp [p1, p1, p1, p0]
    . simp; use [1, 1, 1, 1]; simp [p1, p1, p1, p1]
    . simp; use [5, 0, 0, 0]; simp [p5, p0, p0, p0]
    . simp; use [1, 5, 0, 0]; simp [p1, p5, p0, p0]
    . simp; use [1, 1, 5, 0]; simp [p1, p1, p5, p0]
    . simp; use [1, 1, 1, 5]; simp [p1, p1, p1, p5]
    . simp;
    . simp; use [5, 5, 0, 0]; simp [p5, p5, p0, p0]
    . simp; use [1, 5, 5, 0]; simp [p1, p5, p5, p0]
    . simp; use [12, 0, 0, 0]; simp [p12, p0, p0, p0]
    . simp; use [1, 12, 0, 0]; simp [p1, p12, p0, p0]
    . simp; use [1, 1, 12, 0]; simp [p1, p1, p12, p0]
    . simp; use [5, 5, 5, 0]; simp [p5, p5, p5, p0]
    . simp; use [1, 5, 5, 5]; simp [p1, p5, p5, p5]
    . simp; use [5, 12, 0, 0]; simp [p5, p12, p0, p0]
    . simp; use [1, 5, 12, 0]; simp [p1, p5, p12, p0]
    . simp; use [1, 1, 5, 12]; simp [p1, p1, p5, p12]
    . simp; use [5, 5, 5, 5]; simp [p5, p5, p5, p5]
    . simp;
    . simp; use [22, 0, 0, 0]; simp [p22, p0, p0, p0]
    . simp; use [1, 22, 0, 0]; simp [p1, p22, p0, p0]
    . simp; use [12, 12, 0, 0]; simp [p12, p12, p0, p0]
    . simp; use [1, 12, 12, 0]; simp [p1, p12, p12, p0]
    . simp; use [1, 1, 12, 12]; simp [p1, p1, p12, p12]
    . simp; use [5, 22, 0, 0]; simp [p5, p22, p0, p0]
    . simp; use [1, 5, 22, 0]; simp [p1, p5, p22, p0]
    . simp; use [5, 12, 12, 0]; simp [p5, p12, p12, p0]
    . simp; use [1, 5, 12, 12]; simp [p1, p5, p12, p12]
    . simp;
    . simp; use [5, 5, 22, 0]; simp [p5, p5, p22, p0]
    . simp; use [1, 5, 5, 22]; simp [p1, p5, p5, p22]
    . simp; use [12, 22, 0, 0]; simp [p12, p22, p0, p0]
    . simp; use [35, 0, 0, 0]; simp [p35, p0, p0, p0]
    . simp; use [1, 35, 0, 0]; simp [p1, p35, p0, p0]
    . simp; use [1, 1, 35, 0]; simp [p1, p1, p35, p0]
    . simp; use [1, 1, 1, 35]; simp [p1, p1, p1, p35]
    . simp; use [5, 12, 22, 0]; simp [p5, p12, p22, p0]
    . simp; use [5, 35, 0, 0]; simp [p5, p35, p0, p0]
    . simp; use [1, 5, 35, 0]; simp [p1, p5, p35, p0]
    . simp; use [1, 1, 5, 35]; simp [p1, p1, p5, p35]
    . simp;
    . simp; use [22, 22, 0, 0]; simp [p22, p22, p0, p0]
    . simp; use [1, 22, 22, 0]; simp [p1, p22, p22, p0]
    . simp; use [12, 12, 22, 0]; simp [p12, p12, p22, p0]
    . simp; use [12, 35, 0, 0]; simp [p12, p35, p0, p0]
    . simp; use [1, 12, 35, 0]; simp [p1, p12, p35, p0]
    . simp; use [5, 22, 22, 0]; simp [p5, p22, p22, p0]
    . simp; use [5, 5, 5, 35]; simp [p5, p5, p5, p35]
    . simp; use [51, 0, 0, 0]; simp [p51, p0, p0, p0]
    . simp; use [1, 51, 0, 0]; simp [p1, p51, p0, p0]
    . simp; use [1, 1, 51, 0]; simp [p1, p1, p51, p0]
    . simp; use [1, 1, 1, 51]; simp [p1, p1, p1, p51]
    . simp;
    . simp; use [5, 51, 0, 0]; simp [p5, p51, p0, p0]
    . simp; use [22, 35, 0, 0]; simp [p22, p35, p0, p0]
    . simp; use [1, 22, 35, 0]; simp [p1, p22, p35, p0]
    . simp; use [12, 12, 35, 0]; simp [p12, p12, p35, p0]
    . simp; use [1, 12, 12, 35]; simp [p1, p12, p12, p35]
    . simp; use [5, 5, 51, 0]; simp [p5, p5, p51, p0]
    . simp; use [5, 22, 35, 0]; simp [p5, p22, p35, p0]
    . simp; use [12, 51, 0, 0]; simp [p12, p51, p0, p0]
    . simp; use [1, 12, 51, 0]; simp [p1, p12, p51, p0]
    . simp; use [1, 1, 12, 51]; simp [p1, p1, p12, p51]
    . simp; use [22, 22, 22, 0]; simp [p22, p22, p22, p0]
    . simp; use [5, 5, 22, 35]; simp [p5, p5, p22, p35]
    . simp; use [5, 12, 51, 0]; simp [p5, p12, p51, p0]
    . simp; use [12, 22, 35, 0]; simp [p12, p22, p35, p0]
    . simp; use [70, 0, 0, 0]; simp [p70, p0, p0, p0]
    . simp; use [1, 70, 0, 0]; simp [p1, p70, p0, p0]
    . simp; use [1, 1, 70, 0]; simp [p1, p1, p70, p0]
    . simp; use [22, 51, 0, 0]; simp [p22, p51, p0, p0]
    . simp; use [1, 22, 51, 0]; simp [p1, p22, p51, p0]
    . simp; use [5, 70, 0, 0]; simp [p5, p70, p0, p0]
    . simp; use [1, 5, 70, 0]; simp [p1, p5, p70, p0]
    . simp; use [1, 1, 5, 70]; simp [p1, p1, p5, p70]
    . simp; use [5, 22, 51, 0]; simp [p5, p22, p51, p0]
    . simp; use [22, 22, 35, 0]; simp [p22, p22, p35, p0]
    . simp; use [5, 5, 70, 0]; simp [p5, p5, p70, p0]
    . simp; use [1, 5, 5, 70]; simp [p1, p5, p5, p70]
    . simp; use [12, 70, 0, 0]; simp [p12, p70, p0, p0]
    . simp; use [1, 12, 70, 0]; simp [p1, p12, p70, p0]
    . simp; use [1, 1, 12, 70]; simp [p1, p1, p12, p70]
    . simp; use [12, 22, 51, 0]; simp [p12, p22, p51, p0]
    . simp; use [35, 51, 0, 0]; simp [p35, p51, p0, p0]
    . simp; use [5, 12, 70, 0]; simp [p5, p12, p70, p0]
    . simp; use [1, 5, 12, 70]; simp [p1, p5, p12, p70]
    . simp;
    . simp; use [5, 12, 22, 51]; simp [p5, p12, p22, p51]
    . simp; use [5, 35, 51, 0]; simp [p5, p35, p51, p0]
    . simp; use [92, 0, 0, 0]; simp [p92, p0, p0, p0]
    . simp; use [1, 92, 0, 0]; simp [p1, p92, p0, p0]
    . simp; use [1, 1, 92, 0]; simp [p1, p1, p92, p0]
    . simp; use [22, 22, 51, 0]; simp [p22, p22, p51, p0]
    . simp; use [5, 5, 35, 51]; simp [p5, p5, p35, p51]
    . simp; use [5, 92, 0, 0]; simp [p5, p92, p0, p0]
    . simp; use [1, 5, 92, 0]; simp [p1, p5, p92, p0]
    . simp; use [1, 1, 5, 92]; simp [p1, p1, p5, p92]
    . simp; use [5, 22, 22, 51]; simp [p5, p22, p22, p51]
    . simp; use [22, 22, 22, 35]; simp [p22, p22, p22, p35]
    . simp; use [51, 51, 0, 0]; simp [p51, p51, p0, p0]
    . simp; use [1, 51, 51, 0]; simp [p1, p51, p51, p0]
    . simp; use [12, 92, 0, 0]; simp [p12, p92, p0, p0]
    . simp; use [35, 70, 0, 0]; simp [p35, p70, p0, p0]
    . simp; use [1, 35, 70, 0]; simp [p1, p35, p70, p0]
    . simp; use [5, 51, 51, 0]; simp [p5, p51, p51, p0]
    . simp; use [22, 35, 51, 0]; simp [p22, p35, p51, p0]
    . simp; use [5, 12, 92, 0]; simp [p5, p12, p92, p0]
    . simp; use [5, 35, 70, 0]; simp [p5, p35, p70, p0]
    . simp; use [1, 5, 35, 70]; simp [p1, p5, p35, p70]
    . simp; use [5, 5, 51, 51]; simp [p5, p5, p51, p51]
    . simp; use [5, 22, 35, 51]; simp [p5, p22, p35, p51]
    . simp; use [22, 92, 0, 0]; simp [p22, p92, p0, p0]
    . simp; use [1, 22, 92, 0]; simp [p1, p22, p92, p0]
    . simp; use [12, 12, 92, 0]; simp [p12, p12, p92, p0]
    . simp; use [117, 0, 0, 0]; simp [p117, p0, p0, p0]
    . simp; use [1, 117, 0, 0]; simp [p1, p117, p0, p0]
    . simp; use [1, 1, 117, 0]; simp [p1, p1, p117, p0]
    . simp; use [1, 1, 1, 117]; simp [p1, p1, p1, p117]
    . simp; use [51, 70, 0, 0]; simp [p51, p70, p0, p0]
    . simp; use [5, 117, 0, 0]; simp [p5, p117, p0, p0]
    . simp; use [1, 5, 117, 0]; simp [p1, p5, p117, p0]
    . simp; use [22, 51, 51, 0]; simp [p22, p51, p51, p0]
    . simp; use [1, 22, 51, 51]; simp [p1, p22, p51, p51]
    . simp; use [12, 22, 92, 0]; simp [p12, p22, p92, p0]
    . simp; use [35, 92, 0, 0]; simp [p35, p92, p0, p0]
    . simp; use [1, 35, 92, 0]; simp [p1, p35, p92, p0]
    . simp; use [12, 117, 0, 0]; simp [p12, p117, p0, p0]
    . simp; use [1, 12, 117, 0]; simp [p1, p12, p117, p0]
    . simp; use [1, 1, 12, 117]; simp [p1, p1, p12, p117]
    . simp; use [5, 35, 92, 0]; simp [p5, p35, p92, p0]
    . simp; use [12, 51, 70, 0]; simp [p12, p51, p70, p0]
    . simp; use [5, 12, 117, 0]; simp [p5, p12, p117, p0]
    . simp; use [1, 5, 12, 117]; simp [p1, p5, p12, p117]
    . simp; use [22, 22, 92, 0]; simp [p22, p22, p92, p0]
    . simp; use [35, 51, 51, 0]; simp [p35, p51, p51, p0]
    . simp; use [1, 35, 51, 51]; simp [p1, p35, p51, p51]
    . simp; use [22, 117, 0, 0]; simp [p22, p117, p0, p0]
    . simp; use [70, 70, 0, 0]; simp [p70, p70, p0, p0]
    . simp; use [12, 12, 117, 0]; simp [p12, p12, p117, p0]
    . simp; use [1, 1, 70, 70]; simp [p1, p1, p70, p70]
    . simp; use [51, 92, 0, 0]; simp [p51, p92, p0, p0]
    . simp; use [5, 22, 117, 0]; simp [p5, p22, p117, p0]
    . simp; use [145, 0, 0, 0]; simp [p145, p0, p0, p0]
    . simp; use [1, 145, 0, 0]; simp [p1, p145, p0, p0]
    . simp; use [1, 1, 145, 0]; simp [p1, p1, p145, p0]
    . simp; use [5, 51, 92, 0]; simp [p5, p51, p92, p0]
    . simp; use [22, 35, 92, 0]; simp [p22, p35, p92, p0]
    . simp; use [5, 145, 0, 0]; simp [p5, p145, p0, p0]
    . simp; use [1, 5, 145, 0]; simp [p1, p5, p145, p0]
    . simp; use [35, 117, 0, 0]; simp [p35, p117, p0, p0]
    . simp; use [51, 51, 51, 0]; simp [p51, p51, p51, p0]
    . simp; use [5, 22, 35, 92]; simp [p5, p22, p35, p92]
    . simp; use [12, 51, 92, 0]; simp [p12, p51, p92, p0]
    . simp; use [35, 51, 70, 0]; simp [p35, p51, p70, p0]
    . simp; use [12, 145, 0, 0]; simp [p12, p145, p0, p0]
    . simp; use [1, 12, 145, 0]; simp [p1, p12, p145, p0]
    . simp; use [1, 1, 12, 145]; simp [p1, p1, p12, p145]
    . simp; use [5, 12, 51, 92]; simp [p5, p12, p51, p92]
    . simp; use [22, 22, 117, 0]; simp [p22, p22, p117, p0]
    . simp; use [70, 92, 0, 0]; simp [p70, p92, p0, p0]
    . simp; use [1, 70, 92, 0]; simp [p1, p70, p92, p0]
    . simp; use [12, 35, 117, 0]; simp [p12, p35, p117, p0]
    . simp; use [22, 51, 92, 0]; simp [p22, p51, p92, p0]
    . simp; use [5, 22, 22, 117]; simp [p5, p22, p22, p117]
    . simp; use [22, 145, 0, 0]; simp [p22, p145, p0, p0]
    . simp; use [51, 117, 0, 0]; simp [p51, p117, p0, p0]
    . simp; use [12, 12, 145, 0]; simp [p12, p12, p145, p0]
    . simp; use [1, 1, 51, 117]; simp [p1, p1, p51, p117]
    . simp; use [22, 22, 35, 92]; simp [p22, p22, p35, p92]
    . simp; use [51, 51, 70, 0]; simp [p51, p51, p70, p0]
    . simp; use [5, 51, 117, 0]; simp [p5, p51, p117, p0]
    . simp; use [22, 35, 117, 0]; simp [p22, p35, p117, p0]
    . simp; use [35, 70, 70, 0]; simp [p35, p70, p70, p0]
    . simp; use [176, 0, 0, 0]; simp [p176, p0, p0, p0]
    . simp; use [1, 176, 0, 0]; simp [p1, p176, p0, p0]
    . simp; use [1, 1, 176, 0]; simp [p1, p1, p176, p0]
    . simp; use [12, 22, 145, 0]; simp [p12, p22, p145, p0]
    . simp; use [35, 145, 0, 0]; simp [p35, p145, p0, p0]
    . simp; use [5, 176, 0, 0]; simp [p5, p176, p0, p0]
    . simp; use [1, 5, 176, 0]; simp [p1, p5, p176, p0]
    . simp; use [1, 1, 5, 176]; simp [p1, p1, p5, p176]
    . simp; use [92, 92, 0, 0]; simp [p92, p92, p0, p0]
    . simp; use [1, 92, 92, 0]; simp [p1, p92, p92, p0]
    . simp; use [5, 5, 176, 0]; simp [p5, p5, p176, p0]
    . simp; use [70, 117, 0, 0]; simp [p70, p117, p0, p0]
    . simp; use [12, 176, 0, 0]; simp [p12, p176, p0, p0]
    . simp; use [1, 12, 176, 0]; simp [p1, p12, p176, p0]
    . simp; use [22, 51, 117, 0]; simp [p22, p51, p117, p0]
    . simp; use [51, 70, 70, 0]; simp [p51, p70, p70, p0]
    . simp; use [5, 70, 117, 0]; simp [p5, p70, p117, p0]
    . simp; use [5, 12, 176, 0]; simp [p5, p12, p176, p0]
    . simp; use [51, 51, 92, 0]; simp [p51, p51, p92, p0]
    . simp; use [5, 22, 51, 117]; simp [p5, p22, p51, p117]
    . simp; use [51, 145, 0, 0]; simp [p51, p145, p0, p0]
    . simp; use [35, 70, 92, 0]; simp [p35, p70, p92, p0]
    . simp; use [22, 176, 0, 0]; simp [p22, p176, p0, p0]
    . simp; use [12, 70, 117, 0]; simp [p12, p70, p117, p0]
    . simp; use [12, 12, 176, 0]; simp [p12, p12, p176, p0]
    . simp; use [5, 51, 145, 0]; simp [p5, p51, p145, p0]
    . simp; use [22, 35, 145, 0]; simp [p22, p35, p145, p0]
    . simp; use [5, 22, 176, 0]; simp [p5, p22, p176, p0]
    . simp; use [51, 51, 51, 51]; simp [p51, p51, p51, p51]
    . simp; use [5, 12, 12, 176]; simp [p5, p12, p12, p176]
    . simp; use [22, 92, 92, 0]; simp [p22, p92, p92, p0]
    . simp; use [5, 22, 35, 145]; simp [p5, p22, p35, p145]
    . simp; use [12, 51, 145, 0]; simp [p12, p51, p145, p0]
    . simp; use [92, 117, 0, 0]; simp [p92, p117, p0, p0]
    . simp; use [210, 0, 0, 0]; simp [p210, p0, p0, p0]
    . simp; use [1, 210, 0, 0]; simp [p1, p210, p0, p0]
    . simp; use [1, 1, 210, 0]; simp [p1, p1, p210, p0]
    . simp; use [51, 70, 92, 0]; simp [p51, p70, p92, p0]
    . simp; use [5, 92, 117, 0]; simp [p5, p92, p117, p0]
    . simp; use [5, 210, 0, 0]; simp [p5, p210, p0, p0]
    . simp; use [1, 5, 210, 0]; simp [p1, p5, p210, p0]
    . simp; use [1, 1, 5, 210]; simp [p1, p1, p5, p210]
    . simp; use [22, 51, 145, 0]; simp [p22, p51, p145, p0]
    . simp; use [51, 51, 117, 0]; simp [p51, p51, p117, p0]
    . simp; use [5, 5, 210, 0]; simp [p5, p5, p210, p0]
    . simp; use [12, 92, 117, 0]; simp [p12, p92, p117, p0]
    . simp; use [12, 210, 0, 0]; simp [p12, p210, p0, p0]
    . simp; use [1, 12, 210, 0]; simp [p1, p12, p210, p0]
    . simp; use [1, 12, 35, 176]; simp [p1, p12, p35, p176]
    . simp; use [5, 22, 22, 176]; simp [p5, p22, p22, p176]
    . simp; use [35, 51, 70, 70]; simp [p35, p51, p70, p70]
    . simp; use [51, 176, 0, 0]; simp [p51, p176, p0, p0]
    . simp; use [1, 51, 176, 0]; simp [p1, p51, p176, p0]
    . simp; use [1, 1, 51, 176]; simp [p1, p1, p51, p176]
    . simp; use [12, 22, 51, 145]; simp [p12, p22, p51, p145]
    . simp; use [35, 51, 145, 0]; simp [p35, p51, p145, p0]
    . simp; use [22, 210, 0, 0]; simp [p22, p210, p0, p0]
    . simp; use [22, 35, 176, 0]; simp [p22, p35, p176, p0]
    . simp; use [117, 117, 0, 0]; simp [p117, p117, p0, p0]
    . simp; use [51, 92, 92, 0]; simp [p51, p92, p92, p0]
    . simp; use [1, 51, 92, 92]; simp [p1, p51, p92, p92]
    . simp; use [92, 145, 0, 0]; simp [p92, p145, p0, p0]
    . simp; use [51, 70, 117, 0]; simp [p51, p70, p117, p0]
    . simp; use [12, 51, 176, 0]; simp [p12, p51, p176, p0]
    . simp; use [1, 5, 117, 117]; simp [p1, p5, p117, p117]
    . simp; use [22, 35, 92, 92]; simp [p22, p35, p92, p92]
    . simp; use [5, 92, 145, 0]; simp [p5, p92, p145, p0]
    . simp; use [1, 5, 92, 145]; simp [p1, p5, p92, p145]
    . simp; use [12, 22, 210, 0]; simp [p12, p22, p210, p0]
    . simp; use [35, 210, 0, 0]; simp [p35, p210, p0, p0]
    . simp; use [70, 176, 0, 0]; simp [p70, p176, p0, p0]
    . simp; use [247, 0, 0, 0]; simp [p247, p0, p0, p0]
    . simp; use [1, 247, 0, 0]; simp [p1, p247, p0, p0]
    . simp; use [1, 1, 247, 0]; simp [p1, p1, p247, p0]
    . simp; use [5, 35, 210, 0]; simp [p5, p35, p210, p0]
    . simp; use [5, 70, 176, 0]; simp [p5, p70, p176, p0]
    . simp; use [5, 247, 0, 0]; simp [p5, p247, p0, p0]
    . simp; use [1, 5, 247, 0]; simp [p1, p5, p247, p0]
    . simp; use [70, 92, 92, 0]; simp [p70, p92, p92, p0]
    . simp; use [22, 22, 35, 176]; simp [p22, p22, p35, p176]
    . simp; use [22, 117, 117, 0]; simp [p22, p117, p117, p0]
    . simp; use [5, 5, 247, 0]; simp [p5, p5, p247, p0]
    . simp; use [12, 70, 176, 0]; simp [p12, p70, p176, p0]
    . simp; use [12, 247, 0, 0]; simp [p12, p247, p0, p0]
    . simp; use [1, 12, 247, 0]; simp [p1, p12, p247, p0]
    . simp; use [51, 210, 0, 0]; simp [p51, p210, p0, p0]
    . simp; use [117, 145, 0, 0]; simp [p117, p145, p0, p0]
    . simp; use [1, 117, 145, 0]; simp [p1, p117, p145, p0]
    . simp; use [5, 12, 247, 0]; simp [p5, p12, p247, p0]
    . simp; use [1, 5, 12, 247]; simp [p1, p5, p12, p247]
    . simp; use [51, 70, 145, 0]; simp [p51, p70, p145, p0]
    . simp; use [22, 35, 210, 0]; simp [p22, p35, p210, p0]
    . simp; use [92, 176, 0, 0]; simp [p92, p176, p0, p0]
    . simp; use [22, 247, 0, 0]; simp [p22, p247, p0, p0]
    . simp; use [1, 22, 247, 0]; simp [p1, p22, p247, p0]
    . simp; use [12, 12, 247, 0]; simp [p12, p12, p247, p0]
    . simp; use [35, 92, 145, 0]; simp [p35, p92, p145, p0]
    . simp; use [12, 51, 210, 0]; simp [p12, p51, p210, p0]
    . simp; use [5, 22, 247, 0]; simp [p5, p22, p247, p0]
    . simp; use [1, 12, 117, 145]; simp [p1, p12, p117, p145]
    . simp; use [92, 92, 92, 0]; simp [p92, p92, p92, p0]
    . simp; use [1, 92, 92, 92]; simp [p1, p92, p92, p92]
    . simp; use [51, 51, 176, 0]; simp [p51, p51, p176, p0]
    . simp; use [70, 92, 117, 0]; simp [p70, p92, p117, p0]
    . simp; use [70, 210, 0, 0]; simp [p70, p210, p0, p0]
    . simp; use [35, 70, 176, 0]; simp [p35, p70, p176, p0]
    . simp; use [35, 247, 0, 0]; simp [p35, p247, p0, p0]
    . simp; use [1, 35, 247, 0]; simp [p1, p35, p247, p0]
    . simp; use [22, 117, 145, 0]; simp [p22, p117, p145, p0]
    . simp; use [5, 70, 210, 0]; simp [p5, p70, p210, p0]
    . simp; use [1, 5, 70, 210]; simp [p1, p5, p70, p210]
    . simp; use [287, 0, 0, 0]; simp [p287, p0, p0, p0]
    . simp; use [1, 287, 0, 0]; simp [p1, p287, p0, p0]
    . simp; use [1, 1, 287, 0]; simp [p1, p1, p287, p0]
    . simp; use [145, 145, 0, 0]; simp [p145, p145, p0, p0]
    . simp; use [22, 22, 247, 0]; simp [p22, p22, p247, p0]
    . simp; use [5, 287, 0, 0]; simp [p5, p287, p0, p0]
    . simp; use [117, 176, 0, 0]; simp [p117, p176, p0, p0]
    . simp; use [1, 117, 176, 0]; simp [p1, p117, p176, p0]
    . simp; use [5, 145, 145, 0]; simp [p5, p145, p145, p0]
    . simp; use [35, 51, 210, 0]; simp [p35, p51, p210, p0]
    . simp; use [5, 5, 287, 0]; simp [p5, p5, p287, p0]
    . simp; use [51, 247, 0, 0]; simp [p51, p247, p0, p0]
    . simp; use [12, 287, 0, 0]; simp [p12, p287, p0, p0]
    . simp; use [1, 12, 287, 0]; simp [p1, p12, p287, p0]
    . simp; use [92, 92, 117, 0]; simp [p92, p92, p117, p0]
    . simp; use [92, 210, 0, 0]; simp [p92, p210, p0, p0]
    . simp; use [5, 51, 247, 0]; simp [p5, p51, p247, p0]
    . simp; use [70, 117, 117, 0]; simp [p70, p117, p117, p0]
    . simp; use [12, 117, 176, 0]; simp [p12, p117, p176, p0]
    . simp; use [22, 22, 117, 145]; simp [p22, p22, p117, p145]
    . simp; use [70, 92, 145, 0]; simp [p70, p92, p145, p0]
    . simp; use [1, 5, 92, 210]; simp [p1, p5, p92, p210]
    . simp; use [22, 287, 0, 0]; simp [p22, p287, p0, p0]
    . simp; use [12, 51, 247, 0]; simp [p12, p51, p247, p0]
    . simp; use [12, 12, 287, 0]; simp [p12, p12, p287, p0]
    . simp; use [51, 51, 210, 0]; simp [p51, p51, p210, p0]
    . simp; use [51, 117, 145, 0]; simp [p51, p117, p145, p0]
    . simp; use [5, 22, 287, 0]; simp [p5, p22, p287, p0]
    . simp; use [22, 117, 176, 0]; simp [p22, p117, p176, p0]
    . simp; use [70, 70, 176, 0]; simp [p70, p70, p176, p0]
    . simp; use [70, 247, 0, 0]; simp [p70, p247, p0, p0]
    . simp; use [1, 70, 247, 0]; simp [p1, p70, p247, p0]
    . simp; use [51, 92, 176, 0]; simp [p51, p92, p176, p0]
    . simp; use [22, 51, 247, 0]; simp [p22, p51, p247, p0]
    . simp; use [145, 176, 0, 0]; simp [p145, p176, p0, p0]
    . simp; use [35, 287, 0, 0]; simp [p35, p287, p0, p0]
    . simp; use [1, 35, 287, 0]; simp [p1, p35, p287, p0]
    . simp; use [22, 92, 210, 0]; simp [p22, p92, p210, p0]
    . simp; use [35, 145, 145, 0]; simp [p35, p145, p145, p0]
    . simp; use [92, 117, 117, 0]; simp [p92, p117, p117, p0]
    . simp; use [117, 210, 0, 0]; simp [p117, p210, p0, p0]
    . simp; use [1, 117, 210, 0]; simp [p1, p117, p210, p0]
    . simp; use [12, 70, 247, 0]; simp [p12, p70, p247, p0]
    . simp; use [330, 0, 0, 0]; simp [p330, p0, p0, p0]
    . simp; use [1, 330, 0, 0]; simp [p1, p330, p0, p0]
    . simp; use [1, 1, 330, 0]; simp [p1, p1, p330, p0]
    . simp; use [12, 145, 176, 0]; simp [p12, p145, p176, p0]
    . simp; use [12, 35, 287, 0]; simp [p12, p35, p287, p0]
    . simp; use [5, 330, 0, 0]; simp [p5, p330, p0, p0]
    . simp; use [1, 5, 330, 0]; simp [p1, p5, p330, p0]
    . simp; use [35, 92, 210, 0]; simp [p35, p92, p210, p0]
    . simp; use [51, 287, 0, 0]; simp [p51, p287, p0, p0]
    . simp; use [92, 247, 0, 0]; simp [p92, p247, p0, p0]
    . simp; use [1, 92, 247, 0]; simp [p1, p92, p247, p0]
    . simp; use [51, 145, 145, 0]; simp [p51, p145, p145, p0]
    . simp; use [12, 330, 0, 0]; simp [p12, p330, p0, p0]
    . simp; use [1, 12, 330, 0]; simp [p1, p12, p330, p0]
    . simp; use [5, 92, 247, 0]; simp [p5, p92, p247, p0]
    . simp; use [12, 12, 145, 176]; simp [p12, p12, p145, p176]
    . simp; use [70, 92, 92, 92]; simp [p70, p92, p92, p92]
    . simp; use [5, 12, 330, 0]; simp [p5, p12, p330, p0]
    . simp; use [1, 5, 12, 330]; simp [p1, p5, p12, p330]
    . simp; use [51, 51, 247, 0]; simp [p51, p51, p247, p0]
    . simp; use [70, 70, 210, 0]; simp [p70, p70, p210, p0]
    . simp; use [12, 92, 247, 0]; simp [p12, p92, p247, p0]
    . simp; use [22, 330, 0, 0]; simp [p22, p330, p0, p0]
    . simp; use [1, 22, 330, 0]; simp [p1, p22, p330, p0]
    . simp; use [92, 117, 145, 0]; simp [p92, p117, p145, p0]
    . simp; use [145, 210, 0, 0]; simp [p145, p210, p0, p0]
    . simp; use [1, 145, 210, 0]; simp [p1, p145, p210, p0]
    . simp; use [70, 287, 0, 0]; simp [p70, p287, p0, p0]
    . simp; use [1, 70, 287, 0]; simp [p1, p70, p287, p0]
    . simp; use [1, 1, 70, 287]; simp [p1, p1, p70, p287]
    . simp; use [70, 145, 145, 0]; simp [p70, p145, p145, p0]
    . simp; use [22, 92, 247, 0]; simp [p22, p92, p247, p0]
    . simp; use [35, 117, 210, 0]; simp [p35, p117, p210, p0]
    . simp; use [70, 117, 176, 0]; simp [p70, p117, p176, p0]
    . simp; use [117, 247, 0, 0]; simp [p117, p247, p0, p0]
    . simp; use [35, 330, 0, 0]; simp [p35, p330, p0, p0]
    . simp; use [1, 35, 330, 0]; simp [p1, p35, p330, p0]
    . simp; use [12, 145, 210, 0]; simp [p12, p145, p210, p0]
    . simp; use [51, 70, 247, 0]; simp [p51, p70, p247, p0]
    . simp; use [12, 70, 287, 0]; simp [p12, p70, p287, p0]
    . simp; use [5, 35, 330, 0]; simp [p5, p35, p330, p0]
    . simp; use [70, 92, 92, 117]; simp [p70, p92, p92, p117]
    . simp; use [70, 92, 210, 0]; simp [p70, p92, p210, p0]
    . simp; use [35, 51, 287, 0]; simp [p35, p51, p287, p0]
    . simp; use [35, 92, 247, 0]; simp [p35, p92, p247, p0]
    . simp; use [5, 5, 35, 330]; simp [p5, p5, p35, p330]
    . simp; use [376, 0, 0, 0]; simp [p376, p0, p0, p0]
    . simp; use [1, 376, 0, 0]; simp [p1, p376, p0, p0]
    . simp; use [1, 1, 376, 0]; simp [p1, p1, p376, p0]
    . simp; use [92, 287, 0, 0]; simp [p92, p287, p0, p0]
    . simp; use [1, 92, 287, 0]; simp [p1, p92, p287, p0]
    . simp; use [5, 376, 0, 0]; simp [p5, p376, p0, p0]
    . simp; use [1, 5, 376, 0]; simp [p1, p5, p376, p0]
    . simp; use [1, 1, 5, 376]; simp [p1, p1, p5, p376]
    . simp; use [5, 92, 287, 0]; simp [p5, p92, p287, p0]
    . simp; use [92, 117, 176, 0]; simp [p92, p117, p176, p0]
    . simp; use [176, 210, 0, 0]; simp [p176, p210, p0, p0]
    . simp; use [35, 176, 176, 0]; simp [p35, p176, p176, p0]
    . simp; use [12, 376, 0, 0]; simp [p12, p376, p0, p0]
    . simp; use [1, 12, 376, 0]; simp [p1, p12, p376, p0]
    . simp; use [35, 145, 210, 0]; simp [p35, p145, p210, p0]
    . simp; use [5, 176, 210, 0]; simp [p5, p176, p210, p0]
    . simp; use [145, 247, 0, 0]; simp [p145, p247, p0, p0]
    . simp; use [12, 51, 330, 0]; simp [p12, p51, p330, p0]
    . simp; use [92, 92, 210, 0]; simp [p92, p92, p210, p0]
    . simp; use [5, 51, 92, 247]; simp [p5, p51, p92, p247]
    . simp; use [22, 22, 22, 330]; simp [p22, p22, p22, p330]
    . simp; use [70, 117, 210, 0]; simp [p70, p117, p210, p0]
    . simp; use [22, 376, 0, 0]; simp [p22, p376, p0, p0]
    . simp; use [1, 22, 376, 0]; simp [p1, p22, p376, p0]
    . simp; use [70, 330, 0, 0]; simp [p70, p330, p0, p0]
    . simp; use [22, 92, 287, 0]; simp [p22, p92, p287, p0]
    . simp; use [70, 70, 117, 145]; simp [p70, p70, p117, p145]
    . simp; use [51, 176, 176, 0]; simp [p51, p176, p176, p0]
    . simp; use [117, 287, 0, 0]; simp [p117, p287, p0, p0]
    . simp; use [1, 117, 287, 0]; simp [p1, p117, p287, p0]
    . simp; use [51, 145, 210, 0]; simp [p51, p145, p210, p0]
    . simp; use [117, 145, 145, 0]; simp [p117, p145, p145, p0]
    . simp; use [51, 70, 287, 0]; simp [p51, p70, p287, p0]
    . simp; use [5, 117, 287, 0]; simp [p5, p117, p287, p0]
    . simp; use [12, 22, 376, 0]; simp [p12, p22, p376, p0]
    . simp; use [35, 376, 0, 0]; simp [p35, p376, p0, p0]
    . simp; use [1, 35, 376, 0]; simp [p1, p35, p376, p0]
    . simp; use [92, 145, 176, 0]; simp [p92, p145, p176, p0]
    . simp; use [35, 92, 287, 0]; simp [p35, p92, p287, p0]
    . simp; use [51, 117, 247, 0]; simp [p51, p117, p247, p0]
    . simp; use [35, 51, 330, 0]; simp [p35, p51, p330, p0]
    . simp; use [1, 12, 117, 287]; simp [p1, p12, p117, p287]
    . simp; use [92, 92, 117, 117]; simp [p92, p92, p117, p117]
    . simp; use [92, 117, 210, 0]; simp [p92, p117, p210, p0]
    . simp; use [210, 210, 0, 0]; simp [p210, p210, p0, p0]
    . simp; use [1, 210, 210, 0]; simp [p1, p210, p210, p0]
    . simp; use [92, 330, 0, 0]; simp [p92, p330, p0, p0]
    . simp; use [176, 247, 0, 0]; simp [p176, p247, p0, p0]
    . simp; use [1, 176, 247, 0]; simp [p1, p176, p247, p0]
    . simp; use [425, 0, 0, 0]; simp [p425, p0, p0, p0]
    . simp; use [1, 425, 0, 0]; simp [p1, p425, p0, p0]
    . simp; use [51, 376, 0, 0]; simp [p51, p376, p0, p0]
    . simp; use [5, 176, 247, 0]; simp [p5, p176, p247, p0]
    . simp; use [1, 1, 51, 376]; simp [p1, p1, p51, p376]
    . simp; use [5, 425, 0, 0]; simp [p5, p425, p0, p0]
    . simp; use [1, 5, 425, 0]; simp [p1, p5, p425, p0]
    . simp; use [145, 287, 0, 0]; simp [p145, p287, p0, p0]
    . simp; use [22, 35, 376, 0]; simp [p22, p35, p376, p0]
    . simp; use [12, 92, 330, 0]; simp [p12, p92, p330, p0]
    . simp; use [145, 145, 145, 0]; simp [p145, p145, p145, p0]
    . simp; use [1, 5, 5, 425]; simp [p1, p5, p5, p425]
    . simp; use [12, 425, 0, 0]; simp [p12, p425, p0, p0]
    . simp; use [1, 12, 425, 0]; simp [p1, p12, p425, p0]
    . simp; use [35, 117, 287, 0]; simp [p35, p117, p287, p0]
    . simp; use [1, 35, 117, 287]; simp [p1, p35, p117, p287]
    . simp; use [22, 92, 117, 210]; simp [p22, p92, p117, p210]
    . simp; use [5, 12, 425, 0]; simp [p5, p12, p425, p0]
    . simp; use [51, 145, 247, 0]; simp [p51, p145, p247, p0]
    . simp; use [22, 92, 330, 0]; simp [p22, p92, p330, p0]
    . simp; use [22, 176, 247, 0]; simp [p22, p176, p247, p0]
    . simp; use [70, 376, 0, 0]; simp [p70, p376, p0, p0]
    . simp; use [22, 425, 0, 0]; simp [p22, p425, p0, p0]
    . simp; use [1, 117, 330, 0]; simp [p1, p117, p330, p0]
    . simp; use [70, 92, 287, 0]; simp [p70, p92, p287, p0]
    . simp; use [35, 51, 117, 247]; simp [p35, p51, p117, p247]
    . simp; use [5, 70, 376, 0]; simp [p5, p70, p376, p0]
    . simp; use [5, 22, 425, 0]; simp [p5, p22, p425, p0]
    . simp; use [1, 5, 117, 330]; simp [p1, p5, p117, p330]
    . simp; use [22, 145, 287, 0]; simp [p22, p145, p287, p0]
    . simp; use [35, 210, 210, 0]; simp [p35, p210, p210, p0]
    . simp; use [92, 117, 247, 0]; simp [p92, p117, p247, p0]
    . simp; use [210, 247, 0, 0]; simp [p210, p247, p0, p0]
    . simp; use [1, 210, 247, 0]; simp [p1, p210, p247, p0]
    . simp; use [12, 117, 330, 0]; simp [p12, p117, p330, p0]
    . simp; use [35, 425, 0, 0]; simp [p35, p425, p0, p0]
    . simp; use [1, 35, 425, 0]; simp [p1, p35, p425, p0]
    . simp; use [35, 51, 376, 0]; simp [p35, p51, p376, p0]
    . simp; use [176, 287, 0, 0]; simp [p176, p287, p0, p0]
    . simp; use [1, 176, 287, 0]; simp [p1, p176, p287, p0]
    . simp; use [5, 35, 425, 0]; simp [p5, p35, p425, p0]
    . simp; use [145, 145, 176, 0]; simp [p145, p145, p176, p0]
    . simp; use [35, 145, 287, 0]; simp [p35, p145, p287, p0]
    . simp; use [92, 376, 0, 0]; simp [p92, p376, p0, p0]
    . simp; use [1, 92, 376, 0]; simp [p1, p92, p376, p0]
    . simp; use [70, 70, 330, 0]; simp [p70, p70, p330, p0]
    . simp; use [51, 210, 210, 0]; simp [p51, p210, p210, p0]
    . simp; use [117, 145, 210, 0]; simp [p117, p145, p210, p0]
    . simp; use [51, 92, 330, 0]; simp [p51, p92, p330, p0]
    . simp; use [51, 176, 247, 0]; simp [p51, p176, p247, p0]
    . simp; use [145, 330, 0, 0]; simp [p145, p330, p0, p0]
    . simp; use [51, 425, 0, 0]; simp [p51, p425, p0, p0]


-- 0, 1, 6, 15, 28, 45, 66, 91, 120, 153, 190
def h0 : IsnPolygonal 6 (by norm_num) 0 := by simp [IsnPolygonal]
def h1 : IsnPolygonal 6 (by norm_num) 1 := by simp [IsnPolygonal]; use 1; ring
def h6 : IsnPolygonal 6 (by norm_num) 6 := by simp [IsnPolygonal]; use 2; ring
def h15 : IsnPolygonal 6 (by norm_num) 15 := by simp [IsnPolygonal]; use 3; ring
def h28 : IsnPolygonal 6 (by norm_num) 28 := by simp [IsnPolygonal]; use 4; ring
def h45 : IsnPolygonal 6 (by norm_num) 45 := by simp [IsnPolygonal]; use 5; ring
def h66 : IsnPolygonal 6 (by norm_num) 66 := by simp [IsnPolygonal]; use 6; ring
def h91 : IsnPolygonal 6 (by norm_num) 91 := by simp [IsnPolygonal]; use 7; ring
def h120 : IsnPolygonal 6 (by norm_num) 120 := by simp [IsnPolygonal]; use 8; ring
def h153 : IsnPolygonal 6 (by norm_num) 153 := by simp [IsnPolygonal]; use 9; ring
def h190 : IsnPolygonal 6 (by norm_num) 190 := by simp [IsnPolygonal]; use 10; ring

def hexaExceptions : Finset ℕ := {11, 26}

theorem SumOfFiveHexagonalNumber : ∀ n : ℕ, ¬ (n ∈ hexaExceptions) → IsNKPolygonal 6 (by norm_num) 5 n := by
  intro n

  have h : n ≥ 212 ∨ n < 212 := by
    exact le_or_lt 212 n


  rcases h with g | g
  . intro _

    have hb :  4 ≥ 4 ∧ n ≥ 53 * 4 ∨ 4 = 3 ∧ n ≥ 159 * 4 := by
      left
      simp
      linarith

    suffices hs : ∃ (S : List (Polygonal (6) (by linarith))),
        (sumPolyToInt (6) (by linarith) S  = n)
      ∧ (S.length ≤ 5) by
      dsimp [IsNKPolygonal]
      simp
      let ⟨ S, hn ⟩ := hs
      let S' : List ℕ := List.map (fun x ↦ x.val) S
      let S₀ : List ℕ := List.replicate (5 - S'.length) 0
      use (S₀.append S')
      simp
      and_intros
      . intro n
        intro h
        rcases h with g | g
        . unfold S₀ at g
          simp at g
          rw [g.right]
          exact zero_is_poly 6 (by linarith)
        . unfold S' at g
          simp at g
          let ⟨ a, ha ⟩ := g
          rw [← ha.right]
          let ⟨ a, hpa ⟩ := a
          exact hpa
      . have hlen : S₀.length = 5 - S'.length := by
          unfold S₀
          simp
        have hslen : S'.length ≤ 5 := by
          have hleneq : S'.length = S.length := by
            exact List.length_map S fun x ↦ x.val
          rw [hleneq]
          exact hn.right
        rw [hlen]
        exact Nat.sub_add_cancel hslen
      . have hs' : S'.sum = sumPolyToInt 6 (by linarith) S := by
          dsimp [S', sumPolyToInt]
          unfold foldrfun
          simp
          unfold List.sum
          rw [List.foldr_map (Nat.cast ∘ fun x ↦ x.val) (fun x1 x2 ↦ x1 + x2) S 0]
          simp
        have hs₀ : S₀.sum = 0 := by
          unfold S₀
          simp
        rw [hs₀]
        simp
        rw [hn.left] at hs'
        norm_cast at hs'

    apply CauchyPolygonalNumberTheorem 4 n (by linarith) hb
  . suffices h : ∀ n : ℕ, n < 212 ∧ ¬ (n ∈ hexaExceptions) → IsNKPolygonal 6 (by norm_num) 5 n by
      intro h'
      simp at h
      let g' := h n g h'
      exact g'

    simp [hexaExceptions]

    intro n hn

    interval_cases n
    . decide
    . simp; use [1, 0, 0, 0, 0]; simp [h1, h0, h0, h0, h0]
    . simp; use [1, 1, 0, 0, 0]; simp [h1, h1, h0, h0, h0]
    . simp; use [1, 1, 1, 0, 0]; simp [h1, h1, h1, h0, h0]
    . simp; use [1, 1, 1, 1, 0]; simp [h1, h1, h1, h1, h0]
    . simp; use [1, 1, 1, 1, 1]; simp [h1, h1, h1, h1, h1]
    . simp; use [6, 0, 0, 0, 0]; simp [h6, h0, h0, h0, h0]
    . simp; use [1, 6, 0, 0, 0]; simp [h1, h6, h0, h0, h0]
    . simp; use [1, 1, 6, 0, 0]; simp [h1, h1, h6, h0, h0]
    . simp; use [1, 1, 1, 6, 0]; simp [h1, h1, h1, h6, h0]
    . simp; use [1, 1, 1, 1, 6]; simp [h1, h1, h1, h1, h6]
    . simp;
    . simp; use [6, 6, 0, 0, 0]; simp [h6, h6, h0, h0, h0]
    . simp; use [1, 6, 6, 0, 0]; simp [h1, h6, h6, h0, h0]
    . simp; use [1, 1, 6, 6, 0]; simp [h1, h1, h6, h6, h0]
    . simp; use [15, 0, 0, 0, 0]; simp [h15, h0, h0, h0, h0]
    . simp; use [1, 15, 0, 0, 0]; simp [h1, h15, h0, h0, h0]
    . simp; use [1, 1, 15, 0, 0]; simp [h1, h1, h15, h0, h0]
    . simp; use [6, 6, 6, 0, 0]; simp [h6, h6, h6, h0, h0]
    . simp; use [1, 6, 6, 6, 0]; simp [h1, h6, h6, h6, h0]
    . simp; use [1, 1, 6, 6, 6]; simp [h1, h1, h6, h6, h6]
    . simp; use [6, 15, 0, 0, 0]; simp [h6, h15, h0, h0, h0]
    . simp; use [1, 6, 15, 0, 0]; simp [h1, h6, h15, h0, h0]
    . simp; use [1, 1, 6, 15, 0]; simp [h1, h1, h6, h15, h0]
    . simp; use [6, 6, 6, 6, 0]; simp [h6, h6, h6, h6, h0]
    . simp; use [1, 6, 6, 6, 6]; simp [h1, h6, h6, h6, h6]
    . simp;
    . simp; use [6, 6, 15, 0, 0]; simp [h6, h6, h15, h0, h0]
    . simp; use [28, 0, 0, 0, 0]; simp [h28, h0, h0, h0, h0]
    . simp; use [1, 28, 0, 0, 0]; simp [h1, h28, h0, h0, h0]
    . simp; use [15, 15, 0, 0, 0]; simp [h15, h15, h0, h0, h0]
    . simp; use [1, 15, 15, 0, 0]; simp [h1, h15, h15, h0, h0]
    . simp; use [1, 1, 15, 15, 0]; simp [h1, h1, h15, h15, h0]
    . simp; use [6, 6, 6, 15, 0]; simp [h6, h6, h6, h15, h0]
    . simp; use [6, 28, 0, 0, 0]; simp [h6, h28, h0, h0, h0]
    . simp; use [1, 6, 28, 0, 0]; simp [h1, h6, h28, h0, h0]
    . simp; use [6, 15, 15, 0, 0]; simp [h6, h15, h15, h0, h0]
    . simp; use [1, 6, 15, 15, 0]; simp [h1, h6, h15, h15, h0]
    . simp; use [1, 1, 6, 15, 15]; simp [h1, h1, h6, h15, h15]
    . simp; use [6, 6, 6, 6, 15]; simp [h6, h6, h6, h6, h15]
    . simp; use [6, 6, 28, 0, 0]; simp [h6, h6, h28, h0, h0]
    . simp; use [1, 6, 6, 28, 0]; simp [h1, h6, h6, h28, h0]
    . simp; use [6, 6, 15, 15, 0]; simp [h6, h6, h15, h15, h0]
    . simp; use [15, 28, 0, 0, 0]; simp [h15, h28, h0, h0, h0]
    . simp; use [1, 15, 28, 0, 0]; simp [h1, h15, h28, h0, h0]
    . simp; use [45, 0, 0, 0, 0]; simp [h45, h0, h0, h0, h0]
    . simp; use [1, 45, 0, 0, 0]; simp [h1, h45, h0, h0, h0]
    . simp; use [1, 1, 45, 0, 0]; simp [h1, h1, h45, h0, h0]
    . simp; use [1, 1, 1, 45, 0]; simp [h1, h1, h1, h45, h0]
    . simp; use [6, 15, 28, 0, 0]; simp [h6, h15, h28, h0, h0]
    . simp; use [1, 6, 15, 28, 0]; simp [h1, h6, h15, h28, h0]
    . simp; use [6, 45, 0, 0, 0]; simp [h6, h45, h0, h0, h0]
    . simp; use [1, 6, 45, 0, 0]; simp [h1, h6, h45, h0, h0]
    . simp; use [1, 1, 6, 45, 0]; simp [h1, h1, h6, h45, h0]
    . simp; use [1, 1, 1, 6, 45]; simp [h1, h1, h1, h6, h45]
    . simp; use [6, 6, 15, 28, 0]; simp [h6, h6, h15, h28, h0]
    . simp; use [28, 28, 0, 0, 0]; simp [h28, h28, h0, h0, h0]
    . simp; use [1, 28, 28, 0, 0]; simp [h1, h28, h28, h0, h0]
    . simp; use [15, 15, 28, 0, 0]; simp [h15, h15, h28, h0, h0]
    . simp; use [1, 15, 15, 28, 0]; simp [h1, h15, h15, h28, h0]
    . simp; use [15, 45, 0, 0, 0]; simp [h15, h45, h0, h0, h0]
    . simp; use [1, 15, 45, 0, 0]; simp [h1, h15, h45, h0, h0]
    . simp; use [6, 28, 28, 0, 0]; simp [h6, h28, h28, h0, h0]
    . simp; use [6, 6, 6, 45, 0]; simp [h6, h6, h6, h45, h0]
    . simp; use [6, 15, 15, 28, 0]; simp [h6, h15, h15, h28, h0]
    . simp; use [1, 6, 15, 15, 28]; simp [h1, h6, h15, h15, h28]
    . simp; use [66, 0, 0, 0, 0]; simp [h66, h0, h0, h0, h0]
    . simp; use [1, 66, 0, 0, 0]; simp [h1, h66, h0, h0, h0]
    . simp; use [1, 1, 66, 0, 0]; simp [h1, h1, h66, h0, h0]
    . simp; use [1, 1, 1, 66, 0]; simp [h1, h1, h1, h66, h0]
    . simp; use [1, 1, 1, 1, 66]; simp [h1, h1, h1, h1, h66]
    . simp; use [15, 28, 28, 0, 0]; simp [h15, h28, h28, h0, h0]
    . simp; use [6, 66, 0, 0, 0]; simp [h6, h66, h0, h0, h0]
    . simp; use [28, 45, 0, 0, 0]; simp [h28, h45, h0, h0, h0]
    . simp; use [1, 28, 45, 0, 0]; simp [h1, h28, h45, h0, h0]
    . simp; use [15, 15, 45, 0, 0]; simp [h15, h15, h45, h0, h0]
    . simp; use [1, 15, 15, 45, 0]; simp [h1, h15, h15, h45, h0]
    . simp; use [6, 15, 28, 28, 0]; simp [h6, h15, h28, h28, h0]
    . simp; use [6, 6, 66, 0, 0]; simp [h6, h6, h66, h0, h0]
    . simp; use [6, 28, 45, 0, 0]; simp [h6, h28, h45, h0, h0]
    . simp; use [1, 6, 28, 45, 0]; simp [h1, h6, h28, h45, h0]
    . simp; use [15, 66, 0, 0, 0]; simp [h15, h66, h0, h0, h0]
    . simp; use [1, 15, 66, 0, 0]; simp [h1, h15, h66, h0, h0]
    . simp; use [1, 1, 15, 66, 0]; simp [h1, h1, h15, h66, h0]
    . simp; use [28, 28, 28, 0, 0]; simp [h28, h28, h28, h0, h0]
    . simp; use [6, 6, 28, 45, 0]; simp [h6, h6, h28, h45, h0]
    . simp; use [15, 15, 28, 28, 0]; simp [h15, h15, h28, h28, h0]
    . simp; use [6, 15, 66, 0, 0]; simp [h6, h15, h66, h0, h0]
    . simp; use [15, 28, 45, 0, 0]; simp [h15, h28, h45, h0, h0]
    . simp; use [1, 15, 28, 45, 0]; simp [h1, h15, h28, h45, h0]
    . simp; use [45, 45, 0, 0, 0]; simp [h45, h45, h0, h0, h0]
    . simp; use [91, 0, 0, 0, 0]; simp [h91, h0, h0, h0, h0]
    . simp; use [1, 91, 0, 0, 0]; simp [h1, h91, h0, h0, h0]
    . simp; use [1, 1, 91, 0, 0]; simp [h1, h1, h91, h0, h0]
    . simp; use [28, 66, 0, 0, 0]; simp [h28, h66, h0, h0, h0]
    . simp; use [1, 28, 66, 0, 0]; simp [h1, h28, h66, h0, h0]
    . simp; use [6, 45, 45, 0, 0]; simp [h6, h45, h45, h0, h0]
    . simp; use [6, 91, 0, 0, 0]; simp [h6, h91, h0, h0, h0]
    . simp; use [1, 6, 91, 0, 0]; simp [h1, h6, h91, h0, h0]
    . simp; use [1, 1, 6, 91, 0]; simp [h1, h1, h6, h91, h0]
    . simp; use [6, 28, 66, 0, 0]; simp [h6, h28, h66, h0, h0]
    . simp; use [28, 28, 45, 0, 0]; simp [h28, h28, h45, h0, h0]
    . simp; use [6, 15, 15, 66, 0]; simp [h6, h15, h15, h66, h0]
    . simp; use [6, 6, 91, 0, 0]; simp [h6, h6, h91, h0, h0]
    . simp; use [1, 6, 6, 91, 0]; simp [h1, h6, h6, h91, h0]
    . simp; use [15, 45, 45, 0, 0]; simp [h15, h45, h45, h0, h0]
    . simp; use [15, 91, 0, 0, 0]; simp [h15, h91, h0, h0, h0]
    . simp; use [1, 15, 91, 0, 0]; simp [h1, h15, h91, h0, h0]
    . simp; use [1, 1, 15, 91, 0]; simp [h1, h1, h15, h91, h0]
    . simp; use [15, 28, 66, 0, 0]; simp [h15, h28, h66, h0, h0]
    . simp; use [1, 15, 28, 66, 0]; simp [h1, h15, h28, h66, h0]
    . simp; use [45, 66, 0, 0, 0]; simp [h45, h66, h0, h0, h0]
    . simp; use [1, 45, 66, 0, 0]; simp [h1, h45, h66, h0, h0]
    . simp; use [1, 6, 15, 91, 0]; simp [h1, h6, h15, h91, h0]
    . simp; use [1, 1, 1, 45, 66]; simp [h1, h1, h1, h45, h66]
    . simp; use [6, 15, 28, 66, 0]; simp [h6, h15, h28, h66, h0]
    . simp; use [15, 28, 28, 45, 0]; simp [h15, h28, h28, h45, h0]
    . simp; use [6, 45, 66, 0, 0]; simp [h6, h45, h66, h0, h0]
    . simp; use [28, 45, 45, 0, 0]; simp [h28, h45, h45, h0, h0]
    . simp; use [28, 91, 0, 0, 0]; simp [h28, h91, h0, h0, h0]
    . simp; use [120, 0, 0, 0, 0]; simp [h120, h0, h0, h0, h0]
    . simp; use [1, 120, 0, 0, 0]; simp [h1, h120, h0, h0, h0]
    . simp; use [1, 1, 120, 0, 0]; simp [h1, h1, h120, h0, h0]
    . simp; use [1, 1, 1, 120, 0]; simp [h1, h1, h1, h120, h0]
    . simp; use [6, 28, 45, 45, 0]; simp [h6, h28, h45, h45, h0]
    . simp; use [6, 28, 91, 0, 0]; simp [h6, h28, h91, h0, h0]
    . simp; use [6, 120, 0, 0, 0]; simp [h6, h120, h0, h0, h0]
    . simp; use [1, 6, 120, 0, 0]; simp [h1, h6, h120, h0, h0]
    . simp; use [1, 1, 6, 120, 0]; simp [h1, h1, h6, h120, h0]
    . simp; use [28, 28, 28, 45, 0]; simp [h28, h28, h28, h45, h0]
    . simp; use [6, 6, 28, 45, 45]; simp [h6, h6, h28, h45, h45]
    . simp; use [6, 6, 28, 91, 0]; simp [h6, h6, h28, h91, h0]
    . simp; use [66, 66, 0, 0, 0]; simp [h66, h66, h0, h0, h0]
    . simp; use [1, 66, 66, 0, 0]; simp [h1, h66, h66, h0, h0]
    . simp; use [15, 28, 91, 0, 0]; simp [h15, h28, h91, h0, h0]
    . simp; use [15, 120, 0, 0, 0]; simp [h15, h120, h0, h0, h0]
    . simp; use [45, 91, 0, 0, 0]; simp [h45, h91, h0, h0, h0]
    . simp; use [1, 45, 91, 0, 0]; simp [h1, h45, h91, h0, h0]
    . simp; use [6, 66, 66, 0, 0]; simp [h6, h66, h66, h0, h0]
    . simp; use [28, 45, 66, 0, 0]; simp [h28, h45, h66, h0, h0]
    . simp; use [6, 15, 28, 91, 0]; simp [h6, h15, h28, h91, h0]
    . simp; use [6, 15, 120, 0, 0]; simp [h6, h15, h120, h0, h0]
    . simp; use [6, 45, 91, 0, 0]; simp [h6, h45, h91, h0, h0]
    . simp; use [1, 6, 45, 91, 0]; simp [h1, h6, h45, h91, h0]
    . simp; use [6, 6, 66, 66, 0]; simp [h6, h6, h66, h66, h0]
    . simp; use [6, 28, 45, 66, 0]; simp [h6, h28, h45, h66, h0]
    . simp; use [28, 28, 45, 45, 0]; simp [h28, h28, h45, h45, h0]
    . simp; use [15, 66, 66, 0, 0]; simp [h15, h66, h66, h0, h0]
    . simp; use [28, 120, 0, 0, 0]; simp [h28, h120, h0, h0, h0]
    . simp; use [1, 28, 120, 0, 0]; simp [h1, h28, h120, h0, h0]
    . simp; use [15, 15, 120, 0, 0]; simp [h15, h15, h120, h0, h0]
    . simp; use [15, 45, 91, 0, 0]; simp [h15, h45, h91, h0, h0]
    . simp; use [1, 15, 45, 91, 0]; simp [h1, h15, h45, h91, h0]
    . simp; use [153, 0, 0, 0, 0]; simp [h153, h0, h0, h0, h0]
    . simp; use [1, 153, 0, 0, 0]; simp [h1, h153, h0, h0, h0]
    . simp; use [1, 1, 153, 0, 0]; simp [h1, h1, h153, h0, h0]
    . simp; use [45, 45, 66, 0, 0]; simp [h45, h45, h66, h0, h0]
    . simp; use [66, 91, 0, 0, 0]; simp [h66, h91, h0, h0, h0]
    . simp; use [1, 66, 91, 0, 0]; simp [h1, h66, h91, h0, h0]
    . simp; use [6, 153, 0, 0, 0]; simp [h6, h153, h0, h0, h0]
    . simp; use [1, 6, 153, 0, 0]; simp [h1, h6, h153, h0, h0]
    . simp; use [1, 1, 6, 153, 0]; simp [h1, h1, h6, h153, h0]
    . simp; use [6, 45, 45, 66, 0]; simp [h6, h45, h45, h66, h0]
    . simp; use [6, 66, 91, 0, 0]; simp [h6, h66, h91, h0, h0]
    . simp; use [28, 45, 91, 0, 0]; simp [h28, h45, h91, h0, h0]
    . simp; use [45, 120, 0, 0, 0]; simp [h45, h120, h0, h0, h0]
    . simp; use [1, 45, 120, 0, 0]; simp [h1, h45, h120, h0, h0]
    . simp; use [28, 28, 45, 66, 0]; simp [h28, h28, h45, h66, h0]
    . simp; use [15, 153, 0, 0, 0]; simp [h15, h153, h0, h0, h0]
    . simp; use [1, 15, 153, 0, 0]; simp [h1, h15, h153, h0, h0]
    . simp; use [1, 1, 15, 153, 0]; simp [h1, h1, h15, h153, h0]
    . simp; use [6, 45, 120, 0, 0]; simp [h6, h45, h120, h0, h0]
    . simp; use [15, 66, 91, 0, 0]; simp [h15, h66, h91, h0, h0]
    . simp; use [1, 15, 66, 91, 0]; simp [h1, h15, h66, h91, h0]
    . simp; use [6, 15, 153, 0, 0]; simp [h6, h15, h153, h0, h0]
    . simp; use [28, 28, 28, 91, 0]; simp [h28, h28, h28, h91, h0]
    . simp; use [28, 28, 120, 0, 0]; simp [h28, h28, h120, h0, h0]
    . simp; use [45, 66, 66, 0, 0]; simp [h45, h66, h66, h0, h0]
    . simp; use [15, 15, 28, 120, 0]; simp [h15, h15, h28, h120, h0]
    . simp; use [15, 28, 45, 91, 0]; simp [h15, h28, h45, h91, h0]
    . simp; use [15, 45, 120, 0, 0]; simp [h15, h45, h120, h0, h0]
    . simp; use [28, 153, 0, 0, 0]; simp [h28, h153, h0, h0, h0]
    . simp; use [91, 91, 0, 0, 0]; simp [h91, h91, h0, h0, h0]
    . simp; use [15, 15, 153, 0, 0]; simp [h15, h15, h153, h0, h0]
    . simp; use [1, 15, 15, 153, 0]; simp [h1, h15, h15, h153, h0]
    . simp; use [28, 66, 91, 0, 0]; simp [h28, h66, h91, h0, h0]
    . simp; use [66, 120, 0, 0, 0]; simp [h66, h120, h0, h0, h0]
    . simp; use [6, 28, 153, 0, 0]; simp [h6, h28, h153, h0, h0]
    . simp; use [6, 91, 91, 0, 0]; simp [h6, h91, h91, h0, h0]
    . simp; use [6, 15, 15, 153, 0]; simp [h6, h15, h15, h153, h0]
    . simp; use [190, 0, 0, 0, 0]; simp [h190, h0, h0, h0, h0]
    . simp; use [1, 190, 0, 0, 0]; simp [h1, h190, h0, h0, h0]
    . simp; use [1, 1, 190, 0, 0]; simp [h1, h1, h190, h0, h0]
    . simp; use [28, 45, 120, 0, 0]; simp [h28, h45, h120, h0, h0]
    . simp; use [6, 6, 91, 91, 0]; simp [h6, h6, h91, h91, h0]
    . simp; use [15, 15, 45, 120, 0]; simp [h15, h15, h45, h120, h0]
    . simp; use [6, 190, 0, 0, 0]; simp [h6, h190, h0, h0, h0]
    . simp; use [1, 6, 190, 0, 0]; simp [h1, h6, h190, h0, h0]
    . simp; use [45, 153, 0, 0, 0]; simp [h45, h153, h0, h0, h0]
    . simp; use [1, 45, 153, 0, 0]; simp [h1, h45, h153, h0, h0]
    . simp; use [1, 1, 45, 153, 0]; simp [h1, h1, h45, h153, h0]
    . simp; use [15, 66, 120, 0, 0]; simp [h15, h66, h120, h0, h0]
    . simp; use [6, 6, 190, 0, 0]; simp [h6, h6, h190, h0, h0]
    . simp; use [1, 45, 66, 91, 0]; simp [h1, h45, h66, h91, h0]
    . simp; use [6, 45, 153, 0, 0]; simp [h6, h45, h153, h0, h0]
    . simp; use [15, 190, 0, 0, 0]; simp [h15, h190, h0, h0, h0]
    . simp; use [1, 15, 190, 0, 0]; simp [h1, h15, h190, h0, h0]
    . simp; use [1, 1, 15, 190, 0]; simp [h1, h1, h15, h190, h0]
    . simp; use [6, 6, 6, 190, 0]; simp [h6, h6, h6, h190, h0]
    . simp; use [28, 28, 153, 0, 0]; simp [h28, h28, h153, h0, h0]
    . simp; use [28, 91, 91, 0, 0]; simp [h28, h91, h91, h0, h0]
    . simp; use [91, 120, 0, 0, 0]; simp [h91, h120, h0, h0, h0]
