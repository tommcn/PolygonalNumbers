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
  have oneratint : (1 : ℚ) = (1 : ℤ) := rfl
  rw [oneratint]
  rw [← Int.cast_sub r 1]
  rw [← Int.cast_mul r (r - 1)]
  rw [hk]
  simp
  exact Eq.symm (two_mul (k : ℚ))

lemma kfactq (k : ℚ) : k * (k - 1) = k^2 - k := by
  ring


/--
  Both conditions `IsnPolygonal` and `IsnPolygonal'` are equivalent.
-/
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

/--
  `Polygonal` numbers, despite being a subtype of `ℚ`, are equal to their integer part.
-/
-- lemma PolygonalInteger (n : ℤ) (a : Polygonal n) : a.val = ⌊ a.val ⌋ := by
--   dsimp [Polygonal, IsnPolygonal] at a
--   let ⟨ k, hk ⟩ := a
--   let ⟨ r, hr ⟩ := hk
--   simp

--   rw [← hr]
--   simp

--   let ⟨ e, he ⟩ := revenk r
--   let e' := (e : ℚ)

--   have tworatint : (2 : ℚ) = (2 : ℤ) := rfl
--   have oneratint : (1 : ℚ) = (1 : ℤ) := rfl


--   have he' : (r : ℚ) * ((r : ℚ) - 1) = 2 * e' := by
--     rw [oneratint]
--     rw [← Int.cast_sub r 1]
--     rw [← Int.cast_mul r (r - 1)]
--     rw [he]
--     simp

--   rw [he']
--   have htwoassoc : (n - 2) / 2 * (2 * e') = (n - 2) * e' := by
--     ring
--   rw [htwoassoc]
--   dsimp [e']

--   rw [tworatint]
--   rw [← Int.cast_sub n 2]
--   rw [← Int.cast_mul (n - 2)]
--   exact rfl

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
  linarith

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

lemma interval_length (n m : ℕ) (h : n ≥ 120 * m) : ((2 / 3) + √(8 * (n / m) - 8)) - (1 / 2 + √(6 * (n/m) - 3)) > 4 := by
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
  have hmgt0 : (m : ℚ) > 0 := by
    exact gt_of_ge_of_gt hmqgeq3 rfl
  have hmnot0 : (m : ℚ) ≠ 0 := by
    linarith
  have ngeq2m : n ≥ 2 * m := by
    linarith

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
          (interval_length n m nb)
          bound_positive


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

  have polyform (r : ℕ) : ((m : ℚ) / 2) * (r^2 - r) + r = ⌈ ((m : ℚ) / 2) * (r^2 - r) + r ⌉ := by
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

  have slint : sl = ⌈ sl ⌉ := by exact polyform s
  have tlint : tl = ⌈ tl ⌉ := by exact polyform t
  have ulint : ul = ⌈ ul ⌉ := by exact polyform u
  have vlint : vl = ⌈ vl ⌉ := by exact polyform v

  /- `s`, `t`, `u`, `v` are polygonal -/
  have ps : IsnPolygonal (m+2) ⌈ sl ⌉ := by
    rw [← slint]
    rw [PolyEquiv]
    unfold IsnPolygonal'
    use s
    dsimp [sl]
    simp

  have pt : IsnPolygonal (m+2) ⌈ tl ⌉ := by
    rw [← tlint]
    rw [PolyEquiv]
    unfold IsnPolygonal'
    use t
    simp

  have pu : IsnPolygonal (m+2) ⌈ ul ⌉ := by
    rw [← ulint]
    rw [PolyEquiv]
    unfold IsnPolygonal'
    use u
    simp

  have pv : IsnPolygonal (m+2) ⌈ vl ⌉ := by
    rw [← vlint]
    rw [PolyEquiv]
    unfold IsnPolygonal'
    use v
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
