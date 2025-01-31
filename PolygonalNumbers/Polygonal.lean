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
def IsnPolygonal (m : ℤ) (n : ℤ) (_ : m ≥ 3) := ∃ (k : ℤ), (((m : ℚ) - 2) / 2) * (k * (k - 1)) + k = n
def IsnPolygonal' (m : ℤ) (n : ℤ) (_ : m ≥ 3) := ∃ (k : ℤ), (((m : ℚ) - 2) / 2) * (k^2 - k) + k = n
def IsnPolygonal'' (m : ℤ) (n : ℤ) (_ : m ≥ 3) := ∃ (k : ℤ), (((m : ℚ)- 2)*k^2 - (m - 4)*k) / 2 = n
-- def IsnPolygonal₀ (m : ℤ) (n : ℤ) := (√(8*(m-2)*n + (m-4)^2) + (m - 4)) / (2 * (m - 2))
def IsnPolygonal₀ (m : ℤ) (n : ℤ) (_ : m ≥ 3) := IsSquare (8*(m-2)*n + (m-4)^2)
                        ∧ (Int.sqrt (8*(m-2)*n + (m-4)^2) + (m - 4)) % (2 * (m - 2)) = 0
                     --   ∧ (∃ (k : ℕ), (k ^ 2 = (8*(m-2)*n + (m-4)^2) ∧ (k + (m - 4)) % (2 * (m - 2)) = 0))
                     -- Rat.sqrt


def Triangular := Subtype (fun (n : ℤ) ↦ IsTriangular n)
def Polygonal (m : ℤ) (hm : m ≥ 3) := Subtype (fun (n : ℤ) ↦ IsnPolygonal m n hm)

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
    let ⟨ k, hk ⟩ := h
    use k
    rw [kfactq k] at hk
    exact hk

  . intro h
    let ⟨ k, hk ⟩ := h
    use k
    rw [kfactq k]
    exact hk

lemma PolyEquiv' : IsnPolygonal = IsnPolygonal'' := by
  unfold IsnPolygonal IsnPolygonal''
  funext m a hm
  apply propext
  constructor
  . intro h
    let ⟨ k, hk ⟩ := h
    use k
    rw [← hk]
    ring
  . intro h
    let ⟨ k, hk ⟩ := h
    use k
    rw [← hk]
    ring

lemma PolyEquiv₀ : IsnPolygonal = IsnPolygonal₀ := by
  unfold IsnPolygonal₀
  funext m x hm
  apply propext
  constructor
  . intro h
    let ⟨ k, hk ⟩ := h
    dsimp [IsSquare]
    constructor
    . sorry
    . sorry
  . intro ⟨ ⟨ r, hr ⟩, h₂ ⟩
    rw [hr] at h₂
    rw [Int.sqrt_eq] at h₂
    dsimp [IsnPolygonal]

    let rm₄ := r.natAbs + (m - 4)
    have hf : 2 * ((m : ℝ) - 2) > 0 := by
        refine mul_pos ?_ ?_
        simp
        have hmr : (m : ℝ) ≥ 3 := by
          sorry
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
      have ht : (2 * (m - 2)) = (2 * (m - 2)) := rfl

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
      . have hex : ∃ (k : ℤ), rm₄ = (2 * (m - 2)) * k := by
          dsimp [rm₄]
          refine exists_eq_mul_right_of_dvd ?_
          exact Int.dvd_of_emod_eq_zero h₂

        have hmodrm : rm₄ % (2 * (m - 2)) = 0 := by
          dsimp [rm₄]
          assumption

        have hexrm : ∃ (k : ℤ), rm₄ = 2 * (m - 2) * k := by
          refine dvd_iff_exists_eq_mul_right.mp ?_
          exact Int.dvd_of_emod_eq_zero h₂

        let ⟨ k, hk ⟩ := hex
        rw [hk]
        simp
        calc 2 * ((m : ℚ) - 2) * k / (2 * (m - 2)) * (2 * (m - 2))
          _ = k * ((2 * ((m : ℚ) - 2)) / (2 * (m - 2))) * (2 * (m - 2)) := by ring
          _ = k * 1 * (2 * (m - 2)) := by rw [htwo]
        ring

    use (rm₄ / (2 * (m - 2)))

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

lemma Polyrw (m n : ℤ) (hm : m ≥ 3) : IsnPolygonal m n hm ↔ IsnPolygonal' m n hm := by
  rw [PolyEquiv]


instance : Decidable (IsnPolygonal m n h) := by
  rw [PolyEquiv₀]
  dsimp [IsnPolygonal₀]
  exact instDecidableAnd

-- #eval decide <| IsnPolygonal 3 6 (by simp)

lemma polyform (m : ℤ) (r : ℕ) : ((m : ℚ) / 2) * (r^2 - r) + r = ⌈ ((m : ℚ) / 2) * (r^2 - r) + r ⌉ := by
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


-- theorem ismnpoly_correctness (m n : ℤ) : ismnpoly m n ↔ IsnPolygonal m n := by
--   -- rw [PolyEquiv]

--   constructor
--   . dsimp [ismnpoly]
--     intro h

--     -- rw [ismnapoly_helper.eq_def]


--     sorry
--   . sorry

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
