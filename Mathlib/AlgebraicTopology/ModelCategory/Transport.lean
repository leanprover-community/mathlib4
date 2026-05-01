/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Transport a model category via an equivalence

-/

@[expose] public section

namespace HomotopicalAlgebra

open CategoryTheory Limits

variable {C D : Type*} [Category* C] [Category* D] [ModelCategory D]
  [CategoryWithCofibrations C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C]

@[implicit_reducible]
def ModelCategory.transport (e : C ≌ D)
    (h₁ : cofibrations C = (cofibrations D).inverseImage e.functor)
    (h₂ : fibrations C = (fibrations D).inverseImage e.functor)
    (h₃ : weakEquivalences C = (weakEquivalences D).inverseImage e.functor) :
    ModelCategory C := by
  have h₁' : trivialCofibrations C =
      (trivialCofibrations D).inverseImage e.functor := by
    simp only [trivialCofibrations, h₁, h₃]
    rfl
  have h₂' : trivialFibrations C =
      (trivialFibrations D).inverseImage e.functor := by
    simp only [trivialFibrations, h₂, h₃]
    rfl
  have {X Y : C} (f : X ⟶ Y) [hf : Cofibration f] : Cofibration (e.functor.map f) := by
    rw [cofibration_iff] at hf ⊢
    rwa [h₁] at hf
  have {X Y : C} (f : X ⟶ Y) [hf : Fibration f] : Fibration (e.functor.map f) := by
    rw [fibration_iff] at hf ⊢
    rwa [h₂] at hf
  have {X Y : C} (f : X ⟶ Y) [hf : WeakEquivalence f] : WeakEquivalence (e.functor.map f) := by
    rw [weakEquivalence_iff] at hf ⊢
    rwa [h₃] at hf
  exact {
    cm1a := ⟨fun J _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence e.functor⟩
    cm1b := ⟨fun J _ _ ↦ Adjunction.hasColimitsOfShape_of_equivalence e.functor⟩
    cm2 := by rw [h₃]; infer_instance
    cm3a := by rw [h₃]; infer_instance
    cm3b := by rw [h₂]; infer_instance
    cm3c := by rw [h₁]; infer_instance
    cm4a _ _ _ _ _ := by
      rw [← e.functor.hasLiftingProperty_iff_of_isEquivalence]
      infer_instance
    cm4b _ _ _ _ _ := by
      rw [← e.functor.hasLiftingProperty_iff_of_isEquivalence]
      infer_instance
    cm5a := by
      rw [h₁', h₂]
      infer_instance
    cm5b := by
      rw [h₁, h₂']
      infer_instance
  }

end HomotopicalAlgebra
