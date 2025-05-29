/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Order.Category.Lat

/-!
# Category of linear orders

This defines `LinOrd`, the category of linear orders with monotone maps.
-/


open CategoryTheory

universe u

/-- The category of linear orders. -/
structure LinOrd where
  /-- The underlying linearly ordered type. -/
  (carrier : Type*)
  [str : LinearOrder carrier]

attribute [instance] LinOrd.str

initialize_simps_projections LinOrd (carrier → coe, -str)

namespace LinOrd

instance : CoeSort LinOrd (Type _) :=
  ⟨LinOrd.carrier⟩

attribute [coe] LinOrd.carrier

/-- Construct a bundled `LinOrd` from the underlying type and typeclass. -/
abbrev of (X : Type*) [LinearOrder X] : LinOrd := ⟨X⟩

/-- The type of morphisms in `LinOrd R`. -/
@[ext]
structure Hom (X Y : LinOrd.{u}) where
  private mk ::
  /-- The underlying `OrderHom`. -/
  hom' : X →o Y

instance : Category LinOrd.{u} where
  Hom X Y := Hom X Y
  id _ := ⟨OrderHom.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

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

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma coe_id {X : LinOrd} : (𝟙 X : X → X) = id := rfl

@[simp]
lemma coe_comp {X Y Z : LinOrd} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
lemma forget_map {X Y : LinOrd} (f : X ⟶ Y) :
    (forget LinOrd).map f = f := rfl

@[ext]
lemma ext {X Y : LinOrd} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (X : Type u) [LinearOrder X] : (LinOrd.of X : Type u) = X := rfl

@[simp]
lemma hom_id {X : LinOrd} : (𝟙 X : X ⟶ X).hom = OrderHom.id := rfl

/- Provided for rewriting. -/
lemma id_apply (X : LinOrd) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
lemma hom_comp {X Y Z : LinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {X Y Z : LinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
lemma hom_ext {X Y : LinOrd} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
lemma hom_ofHom {X Y : Type u} [LinearOrder X] [LinearOrder Y] (f : X →o Y) :
  (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {X Y : LinOrd} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

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
