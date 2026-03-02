/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Order.Category.Lat

/-!
# Category of linear orders

This defines `LinOrd`, the category of linear orders with monotone maps.
-/

@[expose] public section


open CategoryTheory

universe u

namespace LinOrd

set_option backward.privateInPublic true in
/-- The type of morphisms in `LinOrd R`. -/
@[ext]
structure Hom (X Y : LinOrd.{u}) where
  private mk ::
  /-- The underlying `OrderHom`. -/
  hom' : X →o Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category LinOrd.{u} where
  Hom X Y := Hom X Y
  id _ := ⟨OrderHom.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ConcreteCategory LinOrd (· →o ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `LinOrd` back into a `OrderHom`. -/
abbrev Hom.hom {X Y : LinOrd.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := LinOrd) f

/-- Typecheck a `OrderHom` as a morphism in `LinOrd`. -/
abbrev ofHom {X Y : Type u} [LinearOrder X] [LinearOrder Y] (f : X →o Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := LinOrd) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : LinOrd.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

@[deprecated (since := "2026-02-10")] alias coe_id := ConcreteCategory.coe_id
@[deprecated (since := "2026-02-10")] alias coe_comp := ConcreteCategory.coe_comp
@[deprecated (since := "2026-02-10")] alias forget_map := ConcreteCategory.forget_map_eq_coe
@[deprecated (since := "2026-02-10")] alias ext := ConcreteCategory.hom_ext

-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (X : Type u) [LinearOrder X] : (LinOrd.of X : Type u) = X := rfl

@[simp]
lemma hom_id {X : LinOrd} : (𝟙 X : X ⟶ X).hom = OrderHom.id := rfl

@[deprecated (since := "2026-02-10")] alias id_apply := CategoryTheory.id_apply

@[simp]
lemma hom_comp {X Y Z : LinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

@[deprecated (since := "2026-02-10")] alias comp_apply := CategoryTheory.comp_apply
@[deprecated (since := "2026-02-10")] alias hom_ext := ConcreteCategory.ext
@[deprecated (since := "2026-02-10")] alias hom_ofHom := ConcreteCategory.hom_ofHom
@[deprecated (since := "2026-02-10")] alias ofHom_hom := ConcreteCategory.ofHom_hom

@[simp]
lemma ofHom_id {X : Type u} [LinearOrder X] : ofHom OrderHom.id = 𝟙 (of X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type u} [LinearOrder X] [LinearOrder Y] [LinearOrder Z]
    (f : X →o Y) (g : Y →o Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {X Y : Type u} [LinearOrder X] [LinearOrder Y] (f : X →o Y) (x : X) :
    (ofHom f) x = f x := rfl

@[deprecated (since := "2026-02-10")] alias inv_hom_apply := Iso.hom_inv_id_apply
@[deprecated (since := "2026-02-10")] alias hom_inv_apply := Iso.inv_hom_id_apply

instance : Inhabited LinOrd :=
  ⟨of PUnit⟩

instance hasForgetToLat : HasForget₂ LinOrd Lat where
  forget₂.obj X := .of X
  forget₂.map f := Lat.ofHom (OrderHomClass.toLatticeHom _ _ f.hom)

/-- Constructs an equivalence between linear orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : LinOrd.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
def dual : LinOrd ⥤ LinOrd where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `LinOrd` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : LinOrd ≌ LinOrd where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end LinOrd

theorem linOrd_dual_comp_forget_to_Lat :
    LinOrd.dual ⋙ forget₂ LinOrd Lat = forget₂ LinOrd Lat ⋙ Lat.dual :=
  rfl
