/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Order.Category.BoolAlg
public import Mathlib.Tactic.CategoryTheory.MkConcreteCategory

/-!
# The category of Boolean rings

This file defines `BoolRing`, the category of Boolean rings.

## TODO

Finish the equivalence with `BoolAlg`.
-/

@[expose] public section


universe u

open CategoryTheory Order

/-- The category of Boolean rings. -/
structure BoolRing where
  /-- Construct a bundled `BoolRing` from a `BooleanRing`. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [booleanRing : BooleanRing carrier]

namespace BoolRing

initialize_simps_projections BoolRing (-booleanRing)

instance : CoeSort BoolRing Type* :=
  ⟨carrier⟩

attribute [coe] carrier

attribute [instance] booleanRing

theorem coe_of (α : Type*) [BooleanRing α] : ↥(of α) = α :=
  rfl

instance : Inhabited BoolRing :=
  ⟨of PUnit⟩

mk_concrete_category BoolRing (· →+* ·) (RingHom.id ·) (RingHom.comp · ·)
  with_of_hom {R S : Type u} [BooleanRing R] [BooleanRing S]
  hom_type (R →+* S) from (of R) to (of S)

@[ext]
lemma hom_ext {R S : BoolRing} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  ConcreteCategory.hom_ext f g <| RingHom.congr_fun hf

instance hasForgetToCommRing : HasForget₂ BoolRing CommRingCat where
  forget₂ :=
    { obj := fun R ↦ CommRingCat.of R
      map := fun f ↦ CommRingCat.ofHom f.hom }

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Constructs an isomorphism of Boolean rings from a ring isomorphism between them. -/
@[simps]
def Iso.mk {α β : BoolRing.{u}} (e : α ≃+* β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

end BoolRing

/-! ### Equivalence between `BoolAlg` and `BoolRing` -/

-- We have to add this instance since Lean doesn't see through `X.toBddDistLat`.
instance {X : BoolAlg} :
    BooleanAlgebra ↑(BddDistLat.toBddLat (X.toBddDistLat)).toLat :=
  BoolAlg.str _

-- We have to add this instance since Lean doesn't see through `R.toBddDistLat`.
instance {R : Type u} [BooleanRing R] :
    BooleanRing (BoolAlg.of (AsBoolAlg ↑R)).toBddDistLat.toBddLat.toLat :=
  inferInstanceAs <| BooleanRing R

@[simps]
instance BoolRing.hasForgetToBoolAlg : HasForget₂ BoolRing BoolAlg where
  forget₂.obj X := .of (AsBoolAlg X)
  forget₂.map f := BoolAlg.ofHom f.hom.asBoolAlg

@[simps]
instance BoolAlg.hasForgetToBoolRing : HasForget₂ BoolAlg BoolRing where
  forget₂.obj X := .of (AsBoolRing X)
  forget₂.map f := BoolRing.ofHom <| BoundedLatticeHom.asBoolRing f.hom

/-- The equivalence between Boolean rings and Boolean algebras. This is actually an isomorphism. -/
@[simps functor inverse]
def boolRingCatEquivBoolAlg : BoolRing ≌ BoolAlg where
  functor := forget₂ BoolRing BoolAlg
  inverse := forget₂ BoolAlg BoolRing
  unitIso := NatIso.ofComponents (fun X => BoolRing.Iso.mk <|
    (RingEquiv.asBoolRingAsBoolAlg X).symm) fun {_ _} _ => rfl
  counitIso := NatIso.ofComponents (fun X => BoolAlg.Iso.mk <|
    OrderIso.asBoolAlgAsBoolRing X) fun {_ _} _ => rfl
