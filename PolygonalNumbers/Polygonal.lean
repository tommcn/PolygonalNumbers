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
def IsnPolygonal (m : ℤ) (n : ℤ) := ∃ (k : ℤ), (((m : ℚ) - 2) / 2) * (k * (k - 1)) + k = n
def IsnPolygonal' (m : ℤ) (n : ℤ) := ∃ (k : ℤ), (((m : ℚ) - 2) / 2) * (k^2 - k) + k = n
def IsnPolygonal'' (m : ℤ) (n : ℤ) := ∃ (k : ℤ), (((m : ℚ)- 2)*k^2 - (m - 4)*k) / 2 = n
-- def IsnPolygonal₀ (m : ℤ) (n : ℤ) := (√(8*(m-2)*n + (m-4)^2) + (m - 4)) / (2 * (m - 2))
def IsnPolygonal₀ (m : ℤ) (n : ℤ) := IsSquare (8*(m-2)*n + (m-4)^2)
                        ∧ (Int.sqrt (8*(m-2)*n + (m-4)^2) + (m - 4)) % (2 * (m - 2)) = 0
                     --   ∧ (∃ (k : ℕ), (k ^ 2 = (8*(m-2)*n + (m-4)^2) ∧ (k + (m - 4)) % (2 * (m - 2)) = 0))
                     -- Rat.sqrt


def Triangular := Subtype (fun (n : ℤ) ↦ IsTriangular n)
def Polygonal (m : ℤ) := Subtype (fun (n : ℤ) ↦ IsnPolygonal m n)

/--
  Both conditions `IsnPolygonal` and `IsnPolygonal'` are equivalent.
-/
lemma kfactq (k : ℚ) : k * (k - 1) = k^2 - k := by
  ring

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

lemma PolyEquiv' : IsnPolygonal = IsnPolygonal'' := by
  unfold IsnPolygonal IsnPolygonal''
  funext m a
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
  rw [PolyEquiv']
  unfold IsnPolygonal'' IsnPolygonal₀
  funext m x
  apply propext
  constructor
  . intro h
    let ⟨ k, hk ⟩ := h
    dsimp [IsSquare]
    constructor
    . sorry
    . sorry
  . intro ⟨ ⟨ r, hr ⟩, h₂ ⟩

    -- dsimp [IsSquare] at h₁
    -- let ⟨ r, hr ⟩ := h₁
    rw [hr] at h₂

    sorry


instance : BEq (Polygonal n) where
  beq a b := if (a.val == b.val)
             then true
             else false

instance : LawfulBEq (Polygonal n) where
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

instance : DecidableEq (Polygonal n) :=
  fun a b =>
    if h : a.val = b.val then
      isTrue (by rw [a.eq_iff]; exact h)
    else
      isFalse (by rw [a.eq_iff]; exact h)

lemma Polyrw (n m : ℤ) : IsnPolygonal n m ↔ IsnPolygonal' n m := by
  rw [PolyEquiv]

lemma IsnPolygonalIffInt (m n : ℤ) : IsnPolygonal m n ↔ IsSquare (8*(m-2)*n + (m-4)^2) ∧ (Rat.sqrt (8*(m-2)*n + (m-4)^2) + (m - 4)) % (2 * (m - 2)) = 0 := by
  constructor
  . rw [PolyEquiv₀]
    sorry
    -- apply?
    -- exact fun a ↦ a
  . intro h
    let ⟨ hsqu, hmod ⟩ := h
    rw [PolyEquiv₀]
    sorry
    -- exact ⟨ hsqu, hmod ⟩

-- instance (m : ℤ) : DecidablePred (IsnPolygonal m) :=
--   fun n ↦
--     decidable_of_iff (IsSquare (8*(m-2)*n + (m-4)^2) ∧ (√(8*(m-2)*n + (m-4)^2) + (m - 4)) % (2 * (m - 2)) = 0)  (Iff.symm (IsnPolygonalIffInt m n))


-- #eval decide <| IsnPolygonal 3 6

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


def getnthpoly (m : ℤ) (n : ℕ) : Polygonal m :=
  let num : ℚ := (((m : ℚ) - 2) / 2) * (n ^2 - n) + n
  have hnum : num  = ⌈ num ⌉ := by
    dsimp [num]
    have h : (m : ℚ) - 2 = (((m - 2) : ℤ) : ℚ) := by simp
    rw [h]
    apply polyform (((m - 2) : ℤ)) n

  have h : IsnPolygonal m ⌈ num ⌉ := by
    rw [PolyEquiv]
    unfold IsnPolygonal'
    use n
    simp
    rw [← hnum]

  ⟨ ⌈ num ⌉, h ⟩


#eval getnthpoly 4 1

/--
 Test whether the a'th polygonal number is equal to n.
-/
def ismnapoly_helper (m n : ℤ) (a : ℕ) : Bool :=
  match a with
  | 0 => false
  | k + 1 => if ((getnthpoly m (k + 1)).val == n) then true else (ismnapoly_helper m n k)

/--
  Test whether n is a polygonal number of order m, by checking if it's the
  k'th polygonal number, decrementing k until it reaches 0
  (here k is n, but there are probably better upper bounds for a)
-/
def ismnpoly (m n : ℤ) : Bool := ismnapoly_helper m n n.natAbs


theorem ismnpoly_correctness (m n : ℤ) : ismnpoly m n ↔ IsnPolygonal m n := by
  -- rw [PolyEquiv]

  constructor
  . dsimp [ismnpoly]
    intro h

    -- rw [ismnapoly_helper.eq_def]


    sorry
  . sorry

#eval ismnpoly 3 15


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
