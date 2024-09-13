/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Order.Category.BoolAlg

/-!
# The category of Boolean rings

This file defines `BoolRing`, the category of Boolean rings.

## TODO

Finish the equivalence with `BoolAlg`.
-/


universe u

open CategoryTheory Order

/-- The category of Boolean rings. -/
def BoolRing :=
  Bundled BooleanRing

namespace BoolRing

instance : CoeSort BoolRing Type* :=
  Bundled.coeSort

instance (X : BoolRing) : BooleanRing X :=
  X.str

/-- Construct a bundled `BoolRing` from a `BooleanRing`. -/
def of (α : Type*) [BooleanRing α] : BoolRing :=
  Bundled.of α

@[simp]
theorem coe_of (α : Type*) [BooleanRing α] : ↥(of α) = α :=
  rfl

instance : Inhabited BoolRing :=
  ⟨of PUnit⟩

instance : BundledHom.ParentProjection @BooleanRing.toCommRing :=
  ⟨⟩

-- Porting note: `deriving` `ConcreteCategory` failed, added it manually
-- see https://github.com/leanprover-community/mathlib4/issues/5020
deriving instance LargeCategory for BoolRing

instance : ConcreteCategory BoolRing := by
  dsimp [BoolRing]
  infer_instance

-- Porting note: disabled `simps`
--   Invalid simp lemma BoolRing.hasForgetToCommRing_forget₂_obj_str_add.
--   The given definition is not a constructor application:
--     inferInstance.1
-- @[simps]
instance hasForgetToCommRing : HasForget₂ BoolRing CommRingCat :=
  BundledHom.forget₂ _ _

/-- Constructs an isomorphism of Boolean rings from a ring isomorphism between them. -/
@[simps]
def Iso.mk {α β : BoolRing.{u}} (e : α ≃+* β) : α ≅ β where
  hom := (e : RingHom _ _)
  inv := (e.symm : RingHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

end BoolRing

/-! ### Equivalence between `BoolAlg` and `BoolRing` -/

@[simps]
instance BoolRing.hasForgetToBoolAlg : HasForget₂ BoolRing BoolAlg where
  forget₂ :=
    { obj := fun X => BoolAlg.of (AsBoolAlg X)
      map := fun {X Y} => RingHom.asBoolAlg }

-- Porting note: Added. somehow it does not find this instance.
instance {X : BoolAlg} :
    BooleanAlgebra ↑(BddDistLat.toBddLat (X.toBddDistLat)).toLat :=
  BoolAlg.instBooleanAlgebra _

@[simps]
instance BoolAlg.hasForgetToBoolRing : HasForget₂ BoolAlg BoolRing where
  forget₂ :=
    { obj := fun X => BoolRing.of (AsBoolRing X)
      map := fun {X Y} => BoundedLatticeHom.asBoolRing }

/-- The equivalence between Boolean rings and Boolean algebras. This is actually an isomorphism. -/
@[simps functor inverse]
def boolRingCatEquivBoolAlg : BoolRing ≌ BoolAlg where
  functor := forget₂ BoolRing BoolAlg
  inverse := forget₂ BoolAlg BoolRing
  unitIso := NatIso.ofComponents (fun X => BoolRing.Iso.mk <|
    (RingEquiv.asBoolRingAsBoolAlg X).symm) fun {X Y} f => rfl
  counitIso := NatIso.ofComponents (fun X => BoolAlg.Iso.mk <|
    OrderIso.asBoolAlgAsBoolRing X) fun {X Y} f => rfl
