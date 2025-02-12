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
structure BoolRing where
  private mk ::
  /-- The underlying type. -/
  carrier : Type u
  [booleanRing : BooleanRing carrier]

namespace BoolRing

initialize_simps_projections BoolRing (-booleanRing)

instance : CoeSort BoolRing Type* :=
  ⟨carrier⟩

attribute [coe] carrier

attribute [instance] booleanRing

/-- Construct a bundled `BoolRing` from a `BooleanRing`. -/
abbrev of (α : Type*) [BooleanRing α] : BoolRing :=
  ⟨α⟩

theorem coe_of (α : Type*) [BooleanRing α] : ↥(of α) = α :=
  rfl

instance : Inhabited BoolRing :=
  ⟨of PUnit⟩

variable {R} in
/-- The type of morphisms in `BoolRing`. -/
@[ext]
structure Hom (R S : BoolRing) where
  private mk ::
  /-- The underlying ring hom. -/
  hom : R →+* S

instance : Category BoolRing where
  Hom R S := Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom.comp f.hom⟩

@[ext]
lemma hom_ext {R S : BoolRing} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

/-- Typecheck a `RingHom` as a morphism in `BoolRing`. -/
abbrev ofHom {R S : Type u} [BooleanRing R] [BooleanRing S] (f : R →+* S) : of R ⟶ of S :=
  ⟨f⟩

instance : HasForget BoolRing where
  forget :=
    { obj := fun R ↦ R
      map := fun f ↦ f.hom }
  forget_faithful := ⟨fun h ↦ by ext x; simpa using congrFun h x⟩

instance hasForgetToCommRing : HasForget₂ BoolRing CommRingCat where
  forget₂ :=
    { obj := fun R ↦ CommRingCat.of R
      map := fun f ↦ CommRingCat.ofHom f.hom }

/-- Constructs an isomorphism of Boolean rings from a ring isomorphism between them. -/
@[simps]
def Iso.mk {α β : BoolRing.{u}} (e : α ≃+* β) : α ≅ β where
  hom := ⟨e⟩
  inv := ⟨e.symm⟩
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

end BoolRing

/-! ### Equivalence between `BoolAlg` and `BoolRing` -/

-- Porting note: Added. somehow it does not find this instance.
instance {X : BoolAlg} :
    BooleanAlgebra ↑(BddDistLat.toBddLat (X.toBddDistLat)).toLat :=
  BoolAlg.instBooleanAlgebra _

instance {R : Type u} [BooleanRing R] :
    BooleanRing (BoolAlg.of (AsBoolAlg ↑R)).toBddDistLat.toBddLat.toLat :=
  inferInstanceAs <| BooleanRing R

@[simps]
instance BoolRing.hasForgetToBoolAlg : HasForget₂ BoolRing BoolAlg where
  forget₂ :=
    { obj := fun X ↦ BoolAlg.of (AsBoolAlg X)
      map := fun {R S} f ↦ RingHom.asBoolAlg f.hom }

@[simps]
instance BoolAlg.hasForgetToBoolRing : HasForget₂ BoolAlg BoolRing where
  forget₂ :=
    { obj := fun X => BoolRing.of (AsBoolRing X)
      map := fun {_ _} f => BoolRing.ofHom <| BoundedLatticeHom.asBoolRing f }

/-- The equivalence between Boolean rings and Boolean algebras. This is actually an isomorphism. -/
@[simps functor inverse]
def boolRingCatEquivBoolAlg : BoolRing ≌ BoolAlg where
  functor := forget₂ BoolRing BoolAlg
  inverse := forget₂ BoolAlg BoolRing
  unitIso := NatIso.ofComponents (fun X => BoolRing.Iso.mk <|
    (RingEquiv.asBoolRingAsBoolAlg X).symm) fun {_ _} _ => rfl
  counitIso := NatIso.ofComponents (fun X => BoolAlg.Iso.mk <|
    OrderIso.asBoolAlgAsBoolRing X) fun {_ _} _ => rfl
