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

mk_concrete_category LinOrd (· →o ·) (fun (_ : LinOrd) ↦ OrderHom.id) OrderHom.comp
  with_of_hom {X Y : Type u} [LinearOrder X] [LinearOrder Y]
  hom_type (X →o Y) from (of X) to (of Y)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma coe_id {X : LinOrd} : (𝟙 X : X → X) = id := rfl

@[simp]
lemma coe_comp {X Y Z : LinOrd} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
lemma forget_map {X Y : LinOrd} (f : X ⟶ Y) :
    (forget LinOrd).map f = (f : _ → _) := rfl

@[ext]
lemma ext {X Y : LinOrd} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (X : Type u) [LinearOrder X] : (LinOrd.of X : Type u) = X := rfl

/- Provided for rewriting. -/
lemma id_apply (X : LinOrd) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

/- Provided for rewriting. -/
lemma comp_apply {X Y Z : LinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
lemma hom_ext {X Y : LinOrd} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
lemma ofHom_id {X : Type u} [LinearOrder X] : ofHom OrderHom.id = 𝟙 (of X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type u} [LinearOrder X] [LinearOrder Y] [LinearOrder Z]
    (f : X →o Y) (g : Y →o Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {X Y : Type u} [LinearOrder X] [LinearOrder Y] (f : X →o Y) (x : X) :
    (ofHom f) x = f x := rfl

lemma inv_hom_apply {X Y : LinOrd} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

lemma hom_inv_apply {X Y : LinOrd} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

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
