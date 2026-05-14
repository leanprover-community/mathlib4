/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.Instances
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Transport a model category via an equivalence

Given an equivalence of categories `e : C ≌ D`, we transport
a model category structure on `D` in order to obtain a model
category structure on `C`. More precisely, we assume
that `C` has been equipped with notions of cofibrations, fibrations
and weak equivalences and that these properties of morphisms
are the inverse images of the corresponding properties of
morphisms by the functor `e.functor : C ⥤ D`. Under these
assumptions, we show that the model category axioms for `C`
hold if they hold for `D`.

-/

@[expose] public section

namespace HomotopicalAlgebra

open CategoryTheory Limits

/-- Transport of a model category structure on a category `D` via an equivalence of
categories `e : C ≌ D`. We assume that the category `C` is already endowed
with a `CategoryWithFibrations` instance (and similarly for cofibrations and weak
equivalences), and that the three properties of morphisms (fibrations, cofibrations,
weak equivalences) in `C` coincide with the inverse images by `e.functor : C ⥤ D`
of the corresponding properties of morphisms in `D`. -/
@[implicit_reducible]
def ModelCategory.transport
    {C D : Type*} [Category* C] [Category* D] [ModelCategory D]
    [CategoryWithCofibrations C] [CategoryWithFibrations C]
    [CategoryWithWeakEquivalences C] (e : C ≌ D)
    (h₁ : cofibrations C = (cofibrations D).inverseImage e.functor)
    (h₂ : fibrations C = (fibrations D).inverseImage e.functor)
    (h₃ : weakEquivalences C = (weakEquivalences D).inverseImage e.functor) :
    ModelCategory C := by
  have h₁' : trivialCofibrations C = (trivialCofibrations D).inverseImage e.functor := by
    simp [trivialCofibrations, h₁, h₃]
  have h₂' : trivialFibrations C = (trivialFibrations D).inverseImage e.functor := by
    simp [trivialFibrations, h₂, h₃]
  have {X Y : C} (f : X ⟶ Y) [hf : Cofibration f] : Cofibration (e.functor.map f) := by
    simpa [cofibration_iff, h₁] using hf
  have {X Y : C} (f : X ⟶ Y) [hf : Fibration f] : Fibration (e.functor.map f) := by
    simpa [fibration_iff, h₂] using hf
  have {X Y : C} (f : X ⟶ Y) [hf : WeakEquivalence f] : WeakEquivalence (e.functor.map f) := by
    simpa [weakEquivalence_iff, h₃] using hf
  exact {
    cm1a := ⟨fun _ _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence e.functor⟩
    cm1b := ⟨fun _ _ _ ↦ Adjunction.hasColimitsOfShape_of_equivalence e.functor⟩
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
    cm5a := by rw [h₁', h₂]; infer_instance
    cm5b := by rw [h₁, h₂']; infer_instance }

end HomotopicalAlgebra
