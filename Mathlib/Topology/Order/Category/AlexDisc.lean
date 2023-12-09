/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.PreordCat
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Order.UpperLowerSetTopology

/-!
# Category of Alexandrov-discrete topological spaces

This defines `AlexDisc`, the category of Alexandrov-discrete topological spaces with continuous
maps, and proves it's equivalent to the category of preorders.
-/

open CategoryTheory

/-- Auxiliary typeclass to define the category of Alexandrov-discrete spaces. Do not use this
directly. Use `AlexandrovDiscrete` instead. -/
class AlexandrovDiscreteSpace (α : Type*) extends TopologicalSpace α, AlexandrovDiscrete α

/-- The category of Alexandrov-discrete spaces. -/
def AlexDisc := Bundled AlexandrovDiscreteSpace

namespace AlexDisc

instance instCoeSort : CoeSort AlexDisc Type* := Bundled.coeSort
instance instTopologicalSpace (α : AlexDisc) : TopologicalSpace α := α.2.1
instance instAlexandrovDiscrete (α : AlexDisc) : AlexandrovDiscrete α := α.2.2

instance : BundledHom.ParentProjection @AlexandrovDiscreteSpace.toTopologicalSpace := ⟨⟩

deriving instance LargeCategory for AlexDisc

instance instConcreteCategory : ConcreteCategory AlexDisc := BundledHom.concreteCategory _
instance instHasForgetToTop : HasForget₂ AlexDisc TopCat := BundledHom.forget₂ _ _
instance ForgetToTop.instFull : Full (forget₂ AlexDisc TopCat) := BundledHom.forget₂Full _ _
instance ForgetToTop.instFaithful : Faithful (forget₂ AlexDisc TopCat) where

@[simp] lemma coe_forgetToTop (X : AlexDisc) : ↥((forget₂ _ TopCat).obj X) = X := rfl

/-- Construct a bundled `AlexDisc` from the underlying topological space. -/
def of (α : Type*) [TopologicalSpace α] [AlexandrovDiscrete α] : AlexDisc := ⟨α, ⟨⟩⟩

@[simp] lemma coe_of (α : Type*) [TopologicalSpace α] [AlexandrovDiscrete α] : ↥(of α) = α := rfl
@[simp] lemma forgetToTop_of (α : Type*) [TopologicalSpace α] [AlexandrovDiscrete α] :
  (forget₂ AlexDisc TopCat).obj (of α) = TopCat.of α := rfl

/-- Constructs an equivalence between preorders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : AlexDisc} (e : α ≃ₜ β) : α ≅ β where
  hom := (e : ContinuousMap α β)
  inv := (e.symm : ContinuousMap β α)
  hom_inv_id := FunLike.ext _ _ e.symm_apply_apply
  inv_hom_id := FunLike.ext _ _ e.apply_symm_apply

end AlexDisc
