/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.CategoryTheory.LiftingProperties.Limits

/-!
# Left and right lifting properties

Given a morphism property `T`, we define the left and right lifting property with respect to `T`.

We show that the left lifting property is stable under retracts, cobase change, coproducts,
and composition, with dual statements for the right lifting property.

-/

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (T : MorphismProperty C)

namespace MorphismProperty

/-- The left lifting property (llp) with respect to a class of morphisms. -/
def llp : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ (g : X ⟶ Y) (_ : T g), HasLiftingProperty f g

/-- The right lifting property (rlp) with respect to a class of morphisms. -/
def rlp : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ (g : X ⟶ Y) (_ : T g), HasLiftingProperty g f

lemma llp.IsStableUnderRetracts : T.llp.IsStableUnderRetracts where
  of_retract h hg _ _ f hf :=
    letI := hg _ hf
    RetractArrow.leftLiftingProperty h f

lemma rlp.IsStableUnderRetracts : T.rlp.IsStableUnderRetracts where
  of_retract h hf _ _ g hg :=
    letI := hf _ hg
    RetractArrow.rightLiftingProperty h g

instance llp.IsStableUnderCobaseChange : T.llp.IsStableUnderCobaseChange where
  of_isPushout h hf _ _ g' hg' :=
    letI := hf _ hg'
    IsPushout.HasLiftingProperty h g'

open IsPullback in
instance rlp.IsStableUnderBaseChange : T.rlp.IsStableUnderBaseChange where
  of_isPullback h hf _ _ f' hf' :=
    letI := hf _ hf'
    IsPullback.HasLiftingProperty h f'

instance llp.IsMultiplicative : T.llp.IsMultiplicative where
  id_mem X _ _ p hp := by infer_instance
  comp_mem i j hi hj _ _ p hp := by
    have := hi _ hp
    have := hj _ hp
    infer_instance

instance rlp.IsMultiplicative : T.rlp.IsMultiplicative where
  id_mem X _ _ p hp := by infer_instance
  comp_mem i j hi hj _ _ p hp := by
    have := hi _ hp
    have := hj _ hp
    infer_instance

lemma llp_IsStableUnderCoproductsOfShape (J : Type*) :
    T.llp.IsStableUnderCoproductsOfShape J := fun _ _ _ _ h₁ h₂ f hf _ _ g hg ↦ {
  sq_hasLift sq :=
    ⟨⟨{ l :=
          letI : ∀ j, HasLiftingProperty (f.app j) g := fun j ↦ hf j g hg
          h₂.desc (Limits.coproductOfShapeLiftingCocone sq)
        fac_left := h₁.hom_ext (by simp)
        fac_right := h₂.hom_ext (by simp)}⟩⟩}

lemma rlp_IsStableUnderProductsOfShape (J : Type*) :
    T.rlp.IsStableUnderProductsOfShape J := fun _ _ _ _ h₁ h₂ f hf _ _ g hg ↦ {
  sq_hasLift sq :=
    ⟨⟨{ l :=
          letI : ∀ j, HasLiftingProperty g (f.app j) := fun j ↦ hf j g hg
          h₁.lift (Limits.productOfShapeLiftingCone sq)
        fac_left := h₁.hom_ext (by simp)
        fac_right := h₂.hom_ext (by simp)}⟩⟩}

end MorphismProperty

end CategoryTheory
