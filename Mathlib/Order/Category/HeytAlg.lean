/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.BddDistLat
import Mathlib.Order.Heyting.Hom

#align_import order.category.HeytAlg from "leanprover-community/mathlib"@"e8ac6315bcfcbaf2d19a046719c3b553206dac75"

/-!
# The category of Heyting algebras

This file defines `HeytAlg`, the category of Heyting algebras.
-/

set_option linter.uppercaseLean3 false

universe u

open CategoryTheory Opposite Order

/-- The category of Heyting algebras. -/
def HeytAlg :=
  Bundled HeytingAlgebra
#align HeytAlg HeytAlg

namespace HeytAlg

instance : CoeSort HeytAlg Type* :=
  Bundled.coeSort

instance (X : HeytAlg) : HeytingAlgebra X :=
  X.str

/-- Construct a bundled `HeytAlg` from a `HeytingAlgebra`. -/
def of (α : Type*) [HeytingAlgebra α] : HeytAlg :=
  Bundled.of α
#align HeytAlg.of HeytAlg.of

@[simp]
theorem coe_of (α : Type*) [HeytingAlgebra α] : ↥(of α) = α :=
  rfl
#align HeytAlg.coe_of HeytAlg.coe_of

instance : Inhabited HeytAlg :=
  ⟨of PUnit⟩

instance bundledHom : BundledHom HeytingHom where
  toFun α β [HeytingAlgebra α] [HeytingAlgebra β] := (DFunLike.coe : HeytingHom α β → α → β)
  id := @HeytingHom.id
  comp := @HeytingHom.comp
  hom_ext α β [HeytingAlgebra α] [HeytingAlgebra β] := DFunLike.coe_injective
#align HeytAlg.bundled_hom HeytAlg.bundledHom

deriving instance LargeCategory for HeytAlg

-- Porting note: deriving failed.
-- see https://github.com/leanprover-community/mathlib4/issues/5020
instance : ConcreteCategory HeytAlg := by
  dsimp [HeytAlg]
  infer_instance

-- Porting note: No idea why it does not find this instance...
instance {X Y : HeytAlg.{u}} : FunLike (X ⟶ Y) ↑X ↑Y :=
  HeytingHom.instFunLike

-- Porting note: No idea why it does not find this instance...
instance {X Y : HeytAlg.{u}} : HeytingHomClass (X ⟶ Y) ↑X ↑Y :=
  HeytingHom.instHeytingHomClass

@[simps]
instance hasForgetToLat : HasForget₂ HeytAlg BddDistLat where
  forget₂ :=
    { obj := fun X => BddDistLat.of X
      map := fun {X Y} f => (f : BoundedLatticeHom X Y) }
#align HeytAlg.has_forget_to_Lat HeytAlg.hasForgetToLat

/-- Constructs an isomorphism of Heyting algebras from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : HeytAlg.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : HeytingHom _ _)
  inv := (e.symm : HeytingHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
#align HeytAlg.iso.mk HeytAlg.Iso.mk

end HeytAlg
