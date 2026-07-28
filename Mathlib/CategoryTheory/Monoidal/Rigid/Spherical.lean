/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Monoidal.Rigid.Trace

/-!
# Spherical monoidal categories

A pivotal category is spherical when its left and right traces agree.

The canonical pivotal structure on a rigid symmetric monoidal category is spherical.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- A pivotal category is spherical when its left and right traces agree. -/
class SphericalCategory (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [RigidCategory C] [PivotalCategory C] : Prop where
  leftTrace_eq_rightTrace {X : C} (f : X ⟶ X) : leftTrace f = rightTrace f

/-- The canonical spherical structure on a rigid symmetric monoidal category. -/
instance symmetricSphericalCategory
    [SymmetricCategory C] : SphericalCategory C where
  leftTrace_eq_rightTrace {X} f := by
    rw [leftTrace, rightTrace, pivotalExactPairing_coevaluation, pivotalExactPairing_evaluation]
    simp only [pivotalIso, PivotalCategory.pivotalIso]
    erw [ExactPairing.coevaluation_comp_rightMate, ExactPairing.rightMate_comp_evaluation]
    simp only [id_whiskerRight, Category.comp_id, whiskerLeft_id, Category.id_comp]
    rw [BraidedCategory.exactPairingSwap_coevaluation, BraidedCategory.exactPairingSwap_evaluation]
    simp [← SymmetricCategory.braiding_swap_eq_inv_braiding]

/-- The trace in a spherical category. -/
@[nolint unusedArguments]
def trace [PivotalCategory C] [SphericalCategory C]
    {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  leftTrace f

section

variable [PivotalCategory C] [SphericalCategory C]

lemma trace_eq_leftTrace {X : C} (f : X ⟶ X) : trace f = leftTrace f := rfl

lemma trace_eq_rightTrace {X : C} (f : X ⟶ X) : trace f = rightTrace f :=
  SphericalCategory.leftTrace_eq_rightTrace f

end

example [SymmetricCategory C]
    {X : C} (f : X ⟶ X) :
    trace f =
      η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by
  rw [trace_eq_rightTrace, rightTrace, pivotalExactPairing_evaluation]
  have h_hom : (pivotalIso.app X).hom =
      (rightDualIso (BraidedCategory.exactPairing_swap X Xᘁ) HasRightDual.exact).hom := rfl
  rw [h_hom]
  dsimp only [rightDualIso]
  erw [ExactPairing.rightMate_comp_evaluation]
  simp only [whiskerLeft_id, Category.id_comp]
  erw [BraidedCategory.exactPairingSwap_evaluation]
  rfl

end CategoryTheory
