/-
  ==================== Support for Polygonal Numbers ====================
-/
import Mathlib.Tactic
import Mathlib.Data.Set.Defs
import Init.Data.List.Basic
import Mathlib.Data.Rat.Sqrt
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Group.TypeTags.Basic

-- Wikipedia definitions
-- `m` -> order
def IsTriangular (n : ℤ) := ∃ (k : ℤ), (k * (k + 1)) = 2 * n
def IsnPolygonal (m : ℤ) (n : ℤ) := ∃ (k : ℤ), (((m : ℚ) - 2) / 2) * (k * (k - 1)) + k = n
def IsnPolygonal' (m : ℤ) (n : ℤ) := ∃ (k : ℤ), (((m : ℚ) - 2) / 2) * (k^2 - k) + k = n
def IsnPolygonal'' (m : ℤ) (n : ℤ) := ∃ (k : ℤ), (((m : ℚ)- 2)*k^2 - (m - 4)*k) / 2 = n
-- def IsnPolygonal₀ (m : ℤ) (n : ℤ) := (√(8*(m-2)*n + (m-4)^2) + (m - 4)) / (2 * (m - 2))
def IsnPolygonal₀ (m : ℤ) (n : ℤ) := IsSquare (8*(m-2)*n + (m-4)^2)
                        ∧ (√(8*(m-2)*n + (m-4)^2) + (m - 4)) % (2 * (m - 2)) = 0


def Triangular := Subtype (fun (n : ℤ) ↦ IsTriangular n)
def Polygonal (n : ℤ) := Subtype (fun (m : ℤ) ↦ IsnPolygonal n m)

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
  unfold IsnPolygonal IsnPolygonal₀
  funext m x
  apply propext
  constructor
  . intro h
    let ⟨ h₁, h₂ ⟩ := h


    constructor
    . sorry
    . sorry
  . intro h
    let ⟨ h₁, h₂ ⟩ := h
    dsimp [IsSquare] at h₁
    let ⟨ k, hk ⟩ := h₁

    have hintre : 8 * ((m : ℝ) - 2) * ↑x + (↑m - 4) ^ 2 = ((8 * (m - 2) * x + (m - 4) ^ 2 : ℤ) : ℝ) := by
      simp

    rw [hintre] at h₂
    rw [hk] at h₂

    have hsqrtintre : √((k*k) : ℤ) = k := by
      refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_
      . sorry
      . exact Eq.symm (Int.cast_mul k k)


    rw [hsqrtintre] at h₂

    let a := (k + (m - 4)) / (2 * (m - 2))

    use a

    dsimp [a]



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

lemma IsnPolygonalIffInt (m n : ℤ) : IsnPolygonal m n ↔ IsSquare (8*(m-2)*n + (m-4)^2) ∧ (√(8*(m-2)*n + (m-4)^2) + (m - 4)) % (2 * (m - 2)) = 0 := by
  constructor
  . rw [PolyEquiv₀]
    exact fun a ↦ a
  . intro h
    let ⟨ hsqu, hmod ⟩ := h
    rw [PolyEquiv₀]
    exact ⟨ hsqu, hmod ⟩

-- instance (m : ℤ) : DecidablePred (IsnPolygonal m) :=
--   fun n ↦
--     decidable_of_iff (IsSquare (8*(m-2)*n + (m-4)^2) ∧ (√(8*(m-2)*n + (m-4)^2) + (m - 4)) % (2 * (m - 2)) = 0)  (Iff.symm (IsnPolygonalIffInt m n))


-- #eval decide <| IsnPolygonal 3 6
