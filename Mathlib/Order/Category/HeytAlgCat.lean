/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.BddDistLatCat
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
def HeytAlgCat :=
  Bundled HeytingAlgebra
#align HeytAlg HeytAlgCat

namespace HeytAlgCat

instance : CoeSort HeytAlgCat (Type*) :=
  Bundled.coeSort

instance (X : HeytAlgCat) : HeytingAlgebra X :=
  X.str

/-- Construct a bundled `HeytAlgCat` from a `HeytingAlgebra`. -/
def of (α : Type*) [HeytingAlgebra α] : HeytAlgCat :=
  Bundled.of α
#align HeytAlg.of HeytAlgCat.of

@[simp]
theorem coe_of (α : Type*) [HeytingAlgebra α] : ↥(of α) = α :=
  rfl
#align HeytAlg.coe_of HeytAlgCat.coe_of

instance : Inhabited HeytAlgCat :=
  ⟨of PUnit⟩

instance bundledHom : BundledHom HeytingHom where
  toFun α β [HeytingAlgebra α] [HeytingAlgebra β] := (FunLike.coe : HeytingHom α β → α → β)
  id := @HeytingHom.id
  comp := @HeytingHom.comp
  hom_ext α β [HeytingAlgebra α] [HeytingAlgebra β] := FunLike.coe_injective
#align HeytAlg.bundled_hom HeytAlgCat.bundledHom

deriving instance LargeCategory for HeytAlgCat

-- Porting note: deriving failed.
-- see https://github.com/leanprover-community/mathlib4/issues/5020
instance : ConcreteCategory HeytAlgCat := by
  dsimp [HeytAlgCat]
  -- ⊢ ConcreteCategory (Bundled HeytingAlgebra)
  infer_instance
  -- 🎉 no goals

-- Porting note: No idea why it does not find this instance...
instance {X Y : HeytAlgCat.{u}} : HeytingHomClass (X ⟶ Y) ↑X ↑Y :=
  HeytingHom.instHeytingHomClass

@[simps]
instance hasForgetToLat : HasForget₂ HeytAlgCat BddDistLatCat where
  forget₂ :=
    { obj := fun X => BddDistLatCat.of X
      map := fun {X Y} f => (f : BoundedLatticeHom X Y) }
#align HeytAlg.has_forget_to_Lat HeytAlgCat.hasForgetToLat

/-- Constructs an isomorphism of Heyting algebras from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : HeytAlgCat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : HeytingHom _ _)
  inv := (e.symm : HeytingHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
                   -- ⊢ ↑({ toLatticeHom := { toSupHom := { toFun := ↑e, map_sup' := (_ : ∀ (a b : ↑ …
                        -- 🎉 no goals
  inv_hom_id := by ext; exact e.apply_symm_apply _
                   -- ⊢ ↑({ toLatticeHom := { toSupHom := { toFun := ↑(OrderIso.symm e), map_sup' := …
                        -- 🎉 no goals
#align HeytAlg.iso.mk HeytAlgCat.Iso.mk

end HeytAlgCat
