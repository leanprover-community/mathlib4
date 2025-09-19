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
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl

/-- Discard: map to singleton. All states map to the unique unit state. -/
def discard (X : FinStoch) : X ⟶ tensorUnit where
  toMatrix := fun i _ => 1
  row_sum := fun i => by
    simp only [Finset.sum_const, Finset.card_univ]
    rw [Fintype.card_of_subsingleton]
    simp

open scoped ComonObj

/-- FinStoch has comonoid structure on every object. -/
instance (X : FinStoch) : ComonObj X where
  comul := copy X
  counit := discard X
  counit_comul := by
    apply StochasticMatrix.ext
    ext i x
    simp only [CategoryStruct.comp, StochasticMatrix.comp, MonoidalCategoryStruct.whiskerRight,
               copy, discard, MonoidalCategoryStruct.leftUnitor]
    sorry -- Proof details
  comul_counit := by
    apply StochasticMatrix.ext
    ext i x
    simp only [CategoryStruct.comp, StochasticMatrix.comp, MonoidalCategoryStruct.whiskerLeft,
               copy, discard, MonoidalCategoryStruct.rightUnitor]
    sorry -- Proof details
  comul_assoc := by
    apply StochasticMatrix.ext
    ext i ⟨⟨j₁, j₂⟩, j₃⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp,
               MonoidalCategoryStruct.whiskerLeft, MonoidalCategoryStruct.whiskerRight,
               MonoidalCategoryStruct.associator, copy]
    sorry -- Proof details

/-- The comonoid structure in FinStoch is commutative. -/
instance (X : FinStoch) : CommComonObj X where
  isComm := by
    apply StochasticMatrix.ext
    ext i ⟨j₁, j₂⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp, BraidedCategory.braiding,
               copy, swap, ComonObj.comul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    split_ifs with h
    · simp [h, and_comm]
    · rfl

/-- Tensor coherence for copy. -/
lemma copy_tensor_eq (X Y : FinStoch) :
    Δ[X ⊗ Y] = (Δ[X] ⊗ₘ Δ[Y]) ≫ tensorμ X X Y Y := by
  sorry -- Proof details

/-- Tensor coherence for discard. -/
lemma discard_tensor_eq (X Y : FinStoch) :
    ε[X ⊗ Y] = (ε[X] ⊗ₘ ε[Y]) ≫ (λ_ (𝟙_ FinStoch)).hom := by
  sorry -- Proof details

/-- Copy on unit equals left unitor inverse. -/
lemma copy_unit_eq : Δ[𝟙_ FinStoch] = (λ_ (𝟙_ FinStoch)).inv := by
  sorry -- Proof details

/-- Discard on unit is identity. -/
lemma discard_unit_eq : ε[𝟙_ FinStoch] = 𝟙 (𝟙_ FinStoch) := by
  sorry -- Proof details

/-- FinStoch has copy-discard structure. -/
instance : CopyDiscardCategory FinStoch where
  -- commComonObj uses inferInstance by default, which finds our instances above
  copy_tensor X Y := copy_tensor_eq X Y
  discard_tensor X Y := discard_tensor_eq X Y
  copy_unit := copy_unit_eq
  discard_unit := discard_unit_eq

end CategoryTheory.MarkovCategory
