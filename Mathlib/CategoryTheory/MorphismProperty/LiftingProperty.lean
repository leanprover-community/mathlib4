/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.CategoryTheory.LiftingProperties.Limits
import Mathlib.Order.GaloisConnection

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

/-- Given `T : MorphismProperty C`, this is the class of morphisms that have the
left lifting property (llp) with respect to `T`. -/
def llp : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ (g : X ⟶ Y) (_ : T g), HasLiftingProperty f g

/-- Given `T : MorphismProperty C`, this is the class of morphisms that have the
right lifting property (rlp) with respect to `T`. -/
def rlp : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ (g : X ⟶ Y) (_ : T g), HasLiftingProperty g f

lemma llp_of_isIso {A B : C} (i : A ⟶ B) [IsIso i] :
    T.llp i :=
  fun _ _ _ _ ↦ inferInstance

lemma rlp_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    T.rlp f :=
  fun _ _ _ _ ↦ inferInstance

lemma llp_isStableUnderRetracts : T.llp.IsStableUnderRetracts where
  of_retract h hg _ _ f hf :=
    letI := hg _ hf
    h.leftLiftingProperty f

lemma rlp_isStableUnderRetracts : T.rlp.IsStableUnderRetracts where
  of_retract h hf _ _ g hg :=
    letI := hf _ hg
    h.rightLiftingProperty g

instance llp_isStableUnderCobaseChange : T.llp.IsStableUnderCobaseChange where
  of_isPushout h hf _ _ g' hg' :=
    letI := hf _ hg'
    h.hasLiftingProperty g'

open IsPullback in
instance rlp_isStableUnderBaseChange : T.rlp.IsStableUnderBaseChange where
  of_isPullback h hf _ _ f' hf' :=
    letI := hf _ hf'
    h.hasLiftingProperty f'

instance llp_isMultiplicative : T.llp.IsMultiplicative where
  id_mem X _ _ p hp := by infer_instance
  comp_mem i j hi hj _ _ p hp := by
    have := hi _ hp
    have := hj _ hp
    infer_instance

instance rlp_isMultiplicative : T.rlp.IsMultiplicative where
  id_mem X _ _ p hp := by infer_instance
  comp_mem i j hi hj _ _ p hp := by
    have := hi _ hp
    have := hj _ hp
    infer_instance

lemma llp_IsStableUnderCoproductsOfShape (J : Type*) :
    T.llp.IsStableUnderCoproductsOfShape J := by
  apply IsStableUnderCoproductsOfShape.mk
  intro A B _ _ f hf X Y p hp
  have := fun j ↦ hf j _ hp
  infer_instance

lemma rlp_IsStableUnderProductsOfShape (J : Type*) :
    T.rlp.IsStableUnderProductsOfShape J := by
  apply IsStableUnderProductsOfShape.mk
  intro A B _ _ f hf X Y p hp
  have := fun j ↦ hf j _ hp
  infer_instance

lemma le_llp_iff_le_rlp (T' : MorphismProperty C) :
    T ≤ T'.llp ↔ T' ≤ T.rlp :=
  ⟨fun h _ _ _ hp _ _ _ hi ↦ h _ hi _ hp,
    fun h _ _ _ hi _ _ _ hp ↦ h _ hp _ hi⟩

lemma gc_llp_rlp :
    GaloisConnection (OrderDual.toDual (α := MorphismProperty C) ∘ llp)
      (rlp ∘ OrderDual.ofDual) :=
  fun _ _ ↦ le_llp_iff_le_rlp _ _

end MorphismProperty

end CategoryTheory