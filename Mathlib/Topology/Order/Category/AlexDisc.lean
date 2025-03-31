/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Topology.Specialization

/-!
# Category of Alexandrov-discrete topological spaces

This defines `AlexDisc`, the category of Alexandrov-discrete topological spaces with continuous
maps, and proves it's equivalent to the category of preorders.
-/

open CategoryTheory Topology

/-- The category of Alexandrov-discrete spaces. -/
structure AlexDisc extends TopCat where
  [is_alexandrovDiscrete : AlexandrovDiscrete carrier]

namespace AlexDisc

attribute [instance] is_alexandrovDiscrete

instance : CoeSort AlexDisc (Type _) :=
  ⟨fun X => X.toTopCat⟩

instance category : Category AlexDisc :=
  InducedCategory.category toTopCat

instance concreteCategory : ConcreteCategory AlexDisc (C(·, ·)) :=
  InducedCategory.concreteCategory toTopCat

instance instHasForgetToTop : HasForget₂ AlexDisc TopCat := InducedCategory.hasForget₂ toTopCat

-- TODO: generalize to `InducedCategory.forget₂_full`?
instance forgetToTop_full : (forget₂ AlexDisc TopCat).Full where
  map_surjective f := ⟨f, rfl⟩

instance forgetToTop_faithful : (forget₂ AlexDisc TopCat).Faithful where

/-- Construct a bundled `AlexDisc` from the underlying topological space. -/
abbrev of (X : Type*) [TopologicalSpace X] [AlexandrovDiscrete X] : AlexDisc where
  toTopCat := TopCat.of X

lemma coe_of (α : Type*) [TopologicalSpace α] [AlexandrovDiscrete α] : ↥(of α) = α := rfl

@[simp] lemma forgetToTop_of (α : Type*) [TopologicalSpace α] [AlexandrovDiscrete α] :
  (forget₂ AlexDisc TopCat).obj (of α) = TopCat.of α := rfl

@[simp] lemma coe_forgetToTop (X : AlexDisc) : ↥((forget₂ _ TopCat).obj X) = X := rfl

/-- Constructs an equivalence between preorders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : AlexDisc} (e : α ≃ₜ β) : α ≅ β where
  hom := TopCat.ofHom (e : ContinuousMap α β)
  inv := TopCat.ofHom (e.symm : ContinuousMap β α)
  hom_inv_id := by ext; apply e.symm_apply_apply
  inv_hom_id := by ext; apply e.apply_symm_apply

end AlexDisc

/-- Sends a topological space to its specialisation order. -/
@[simps]
def alexDiscEquivPreord : AlexDisc ≌ Preord where
  functor := forget₂ _ _ ⋙ topToPreord
  inverse.obj X := AlexDisc.of (WithUpperSet X)
  inverse.map f := TopCat.ofHom (WithUpperSet.map f.hom)
  unitIso := NatIso.ofComponents fun X ↦ AlexDisc.Iso.mk <| by
    dsimp; exact homeoWithUpperSetTopologyorderIso X
  counitIso := NatIso.ofComponents fun X ↦ Preord.Iso.mk <| by
    dsimp; exact (orderIsoSpecializationWithUpperSetTopology X).symm
