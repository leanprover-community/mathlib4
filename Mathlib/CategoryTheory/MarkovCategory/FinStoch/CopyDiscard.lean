/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.MarkovCategory.FinStoch.Braided
import Mathlib.CategoryTheory.CopyDiscardCategory.Basic

/-!
# Copy-Discard Structure on FinStoch

FinStoch has copy and discard operations making it a copy-discard category.

## Main definitions

* `copy` - Diagonal embedding
* `discard` - Map to singleton
* `ComonObj` instances
* `CopyDiscardCategory FinStoch`

## Implementation notes

Copy duplicates states (diagonal), discard maps all states to the unit.

## Tags

copy-discard, comonoid, Markov category
-/

namespace CategoryTheory.MarkovCategory

open FinStoch MonoidalCategory ComonObj

universe u

/-- Copy: diagonal embedding. Maps a state to both copies of itself. -/
def copy (X : FinStoch) : X ⟶ X ⊗ X where
  toMatrix := fun i (j₁, j₂) => if i = j₁ ∧ i = j₂ then 1 else 0
  row_sum := fun i => by
    rw [Fintype.sum_eq_single ⟨i, i⟩]
    · simp
    · aesop

/-- Discard: map to singleton. All states map to the unique unit state. -/
def discard (X : FinStoch) : X ⟶ tensorUnit where
  toMatrix := fun i _ => 1
  row_sum := fun i => by
    rw [Fintype.sum_eq_single ⟨⟩]
    simp_all
    intro x
    rfl

open scoped ComonObj

/-- FinStoch has comonoid structure on every object. -/
instance (X : FinStoch) : ComonObj X where
  comul := copy X
  counit := discard X
  counit_comul := by
    apply StochasticMatrix.ext
    ext i ⟨⟨⟩ , x⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp, copy, whiskerRight, discard,
               MonoidalCategoryStruct.leftUnitor, leftUnitor, StochasticMatrix.tensor,
               CategoryStruct.id, StochasticMatrix.id, leftUnitorInvDet, DetMorphism.ofFunc]
    -- Goal: Σ_{(j₁,j₂)} copy(i)(j₁,j₂) · (discard ⊗ id)(j₁,j₂)(unit_,x) = λ⁻¹(i)(unit_,x)
    -- LHS = Σ_{(j₁,j₂)} [i=j₁∧i=j₂] · 1 · [j₂=x] = [i=x]
    -- RHS = λ⁻¹(i)(unit_,x) = [i=x]
    rw [Fintype.sum_eq_single ⟨i, x⟩]
    · simp
      split_ifs with h h'
      · rfl
      · simp_all
      · grind only
      · rfl
    · intro ⟨j₁, j₂⟩ hne
      simp_all
      aesop
  comul_counit := by
    apply StochasticMatrix.ext
    ext i ⟨x, ⟨⟩⟩
    simp_all [CategoryStruct.comp, StochasticMatrix.comp, copy, whiskerLeft,
              StochasticMatrix.tensor, CategoryStruct.id, StochasticMatrix.id, discard,
              MonoidalCategoryStruct.rightUnitor, rightUnitor]
    -- The composition: copy ≫ (id ⊗ discard) ≫ rightUnitor
    -- First: copy(i) gives (i,i)
    -- Second: (id ⊗ discard)(i,i) gives (i,*)
    -- Third: rightUnitor(i,*) gives i
    -- Overall: identity morphism
    rw [Finset.sum_eq_single ⟨i, x⟩]
    · simp_all [rightUnitorInvDet, DetMorphism.ofFunc]
      grind only [cases Or]
    · simp_all
      grind only [cases Or]
    · simp_all
  comul_assoc := by
    apply StochasticMatrix.ext
    ext i ⟨j₁, ⟨j₂, j₃⟩⟩
    simp_all [CategoryStruct.comp, StochasticMatrix.comp, copy, whiskerLeft,
              StochasticMatrix.tensor, CategoryStruct.id, StochasticMatrix.id, whiskerRight,
              MonoidalCategoryStruct.associator, associator, associatorDet, DetMorphism.ofFunc]
    -- Both sides give 1 if i = j₁ = j₂ = j₃, else 0
    -- Show both paths equal this value
    by_cases h : i = j₁ ∧ i = j₂ ∧ i = j₃
    · -- Case when all are equal to i
      obtain ⟨h1, h2, h3⟩ := h
      subst h1 h2 h3
      -- Left path: copy ≫ (copy ⊗ id) ≫ α
      trans 1
      · simp only [and_self]
        rw [Fintype.sum_eq_single ⟨i, i⟩]
        · simp
        · aesop
      -- Right path
      · rw [Fintype.sum_eq_single ⟨i, i⟩]
        · simp_all
          rw [Fintype.sum_eq_single ⟨⟨i, i⟩, i⟩]
          · simp
          · aesop
        · aesop
    · -- Case when not all equal: both sides are 0
      -- Show both sums equal 0
      push_neg at h
      -- Left side
      trans 0
      · rw [Fintype.sum_eq_zero]
        intro ⟨k₁, k₂⟩
        simp only
        aesop
      -- Right side
      · symm
        rw [Fintype.sum_eq_zero]
        intro ⟨k₁, k₂⟩
        simp only
        by_cases hk : i = k₁ ∧ i = k₂
        · -- First copy gives 1, show second sum is 0
          simp only [hk]
          obtain ⟨h1, h2⟩ := hk
          subst h1 h2
          simp
          rw [Fintype.sum_eq_zero]
          intro ⟨⟨m₁, m₂⟩, m₃⟩
          simp only
          split_ifs with h_eq h_m3 h_m12
          · -- All hold: (m₁,m₂,m₃)=(j₁,j₂,j₃), i=m₃, i=m₁=m₂
            grind only
          · simp
          · simp
          · simp
        · -- First copy gives 0
          simp [hk]

/-- The comonoid structure in FinStoch is commutative. -/
instance (X : FinStoch) : CommComonObj X where
  isComm := by
    apply StochasticMatrix.ext
    ext i ⟨j₁, j₂⟩
    simp_all [CategoryStruct.comp, StochasticMatrix.comp]
    -- Copy is commutative: Δ ≫ β = Δ
    -- LHS: copy(i) gives (i,i), then swap gives (i,i)
    -- RHS: copy(i) gives (j₁,j₂) which is 1 iff i = j₁ = j₂
    rw [Fintype.sum_eq_single ⟨i, i⟩]
    · -- At (i,i): copy gives 1, swap keeps (i,i) → (i,i) with prob 1
      simp [comul, copy]
      -- swap (i,i) → (j₁,j₂) is 1 iff i = j₂ ∧ i = j₁
      have h_swap : (β_ X X).hom.toMatrix (i, i) (j₁, j₂) =
                    if i = j₂ ∧ i = j₁ then 1 else 0 := by
        simp only [BraidedCategory.braiding]
        rfl
      rw [h_swap]
      -- Both sides equal 1 iff i = j₁ = j₂
      split_ifs with h_cond h_copy
      · -- h_cond: i = j₂ ∧ i = j₁, so j₁ = j₂ = i
        tauto
      · -- h_copy: i = j₁ ∧ i = j₂
        tauto
      · tauto
      · rfl
    · -- Other pairs (x,y) with (x,y) ≠ (i,i) give copy value 0
      intro ⟨x, y⟩ hne
      simp only [comul, copy]
      split_ifs with h
      · -- If copy gives 1, then x = i ∧ y = i, contradicting hne
        obtain ⟨hx, hy⟩ := h
        subst hx hy
        exfalso
        exact hne rfl
      · simp

/-- Copy on unit equals left unitor inverse. -/
lemma copy_unit_eq : Δ[𝟙_ FinStoch] = (λ_ (𝟙_ FinStoch)).inv := by
  apply StochasticMatrix.ext
  ext ⟨⟩ ⟨⟨⟩, ⟨⟩⟩
  simp [comul, copy, MonoidalCategoryStruct.leftUnitor]
  rfl

/-- Discard on unit is identity. -/
lemma discard_unit_eq : ε[𝟙_ FinStoch] = 𝟙 (𝟙_ FinStoch) := by
  apply StochasticMatrix.ext
  ext ⟨⟩ ⟨⟩
  simp [ComonObj.counit, discard, CategoryStruct.id, StochasticMatrix.id]

/-- FinStoch has copy-discard structure. -/
instance : CopyDiscardCategory FinStoch where
  -- commComonObj uses inferInstance by default, which finds our instances above
  copy_tensor := by simp [Comon.tensorObj_comul]
  discard_tensor := by simp [Comon.tensorObj_counit]
  copy_unit := copy_unit_eq
  discard_unit := discard_unit_eq

end CategoryTheory.MarkovCategory
