/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# The model category structure on Over categories

-/

universe v u

open CategoryTheory

variable {C : Type u} [Category.{v} C] (S : C)

namespace HomotopicalAlgebra

section

variable [CategoryWithCofibrations C]

instance : CategoryWithCofibrations (Over S) where
  cofibrations := (cofibrations C).over

lemma cofibrations_over_def :
    cofibrations (Over S) = (cofibrations C).over := rfl

lemma cofibrations_over_iff {X Y : Over S} (f : X ⟶ Y) :
    Cofibration f ↔ Cofibration f.left := by
  simp only [cofibration_iff]
  rfl

instance {X Y : Over S} (f : X ⟶ Y) [Cofibration f] : Cofibration f.left := by
  rwa [← cofibrations_over_iff]

instance [(cofibrations C).IsStableUnderRetracts] :
    (cofibrations (Over S)).IsStableUnderRetracts := by
  rw [cofibrations_over_def, MorphismProperty.over_eq_inverseImage]
  infer_instance

end

section

variable [CategoryWithFibrations C]

instance : CategoryWithFibrations (Over S) where
  fibrations := (fibrations C).over

lemma fibrations_over_def :
    fibrations (Over S) = (fibrations C).over := rfl

lemma fibrations_over_iff {X Y : Over S} (f : X ⟶ Y) :
    Fibration f ↔ Fibration f.left := by
  simp only [fibration_iff]
  rfl

instance {X Y : Over S} (f : X ⟶ Y) [Fibration f] : Fibration f.left := by
  rwa [← fibrations_over_iff]

instance [(fibrations C).IsStableUnderRetracts] :
    (fibrations (Over S)).IsStableUnderRetracts := by
  rw [fibrations_over_def, MorphismProperty.over_eq_inverseImage]
  infer_instance

end

section

variable [CategoryWithWeakEquivalences C]

instance : CategoryWithWeakEquivalences (Over S) where
  weakEquivalences := (weakEquivalences C).over

lemma weakEquivalences_over_def :
    weakEquivalences (Over S) = (weakEquivalences C).over := rfl

lemma weakEquivalences_over_iff {X Y : Over S} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence f.left := by
  simp only [weakEquivalence_iff]
  rfl

instance {X Y : Over S} (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence f.left := by
  rwa [← weakEquivalences_over_iff]

instance [(weakEquivalences C).IsStableUnderRetracts] :
    (weakEquivalences (Over S)).IsStableUnderRetracts := by
  rw [weakEquivalences_over_def, MorphismProperty.over_eq_inverseImage]
  infer_instance

end

instance [ModelCategory C] : ModelCategory (Over S) where
  cm2 := sorry
  cm4a := sorry
  cm4b := sorry
  cm5a := sorry
  cm5b := sorry

end HomotopicalAlgebra
