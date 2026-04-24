/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Category of preorders

This defines `Preord`, the category of preorders with monotone maps.
-/

@[expose] public section


universe u

open CategoryTheory

/-- The category of preorders. -/
structure Preord where
  /-- Construct a bundled `Preord` from the underlying type and typeclass. -/
  of ::
  /-- The underlying preordered type. -/
  (carrier : Type*)
  [str : Preorder carrier]

attribute [instance] Preord.str

initialize_simps_projections Preord (carrier → coe, -str)

namespace Preord

instance : CoeSort Preord (Type u) :=
  ⟨Preord.carrier⟩

attribute [coe] Preord.carrier

set_option backward.privateInPublic true in
/-- The type of morphisms in `Preord R`. -/
@[ext]
structure Hom (X Y : Preord.{u}) where
  private mk ::
  /-- The underlying `OrderHom`. -/
  hom' : X →o Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category Preord.{u} where
  Hom X Y := Hom X Y
  id _ := ⟨OrderHom.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ConcreteCategory Preord (· →o ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `Preord` back into a `OrderHom`. -/
abbrev Hom.hom {X Y : Preord.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := Preord) f

/-- Typecheck a `OrderHom` as a morphism in `Preord`. -/
abbrev ofHom {X Y : Type u} [Preorder X] [Preorder Y] (f : X →o Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := Preord) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : Preord.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma coe_id {X : Preord} : (𝟙 X : X → X) = id := rfl

@[simp]
lemma coe_comp {X Y Z : Preord} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[deprecated (since := "2026-02-15")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[ext]
lemma ext {X Y : Preord} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (X : Type u) [Preorder X] : (Preord.of X : Type u) = X := rfl

@[simp]
lemma hom_id {X : Preord} : (𝟙 X : X ⟶ X).hom = OrderHom.id := rfl

/- Provided for rewriting. -/
lemma id_apply (X : Preord) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
lemma hom_comp {X Y Z : Preord} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {X Y Z : Preord} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
lemma hom_ext {X Y : Preord} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
lemma hom_ofHom {X Y : Type u} [Preorder X] [Preorder Y] (f : X →o Y) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {X Y : Preord} (f : X ⟶ Y) : ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type u} [Preorder X] : ofHom OrderHom.id = 𝟙 (of X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type u} [Preorder X] [Preorder Y] [Preorder Z]
    (f : X →o Y) (g : Y →o Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {X Y : Type u} [Preorder X] [Preorder Y] (f : X →o Y) (x : X) :
    (ofHom f) x = f x := rfl

lemma inv_hom_apply {X Y : Preord} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

lemma hom_inv_apply {X Y : Preord} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

instance : Inhabited Preord :=
  ⟨of PUnit⟩

/-- Constructs an equivalence between preorders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : Preord.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
def dual : Preord ⥤ Preord where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `Preord` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : Preord ≌ Preord where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end Preord

/-- The embedding of `Preord` into `Cat`.
-/
@[simps]
def preordToCat : Preord.{u} ⥤ Cat where
  obj X := .of X.1
  map f := f.hom.monotone.functor.toCatHom

instance : preordToCat.{u}.Faithful where
  map_injective h := by ext x; exact Functor.congr_obj congr(($h).toFunctor) x

instance : preordToCat.{u}.Full where
  map_surjective {X Y} f := ⟨⟨f.toFunctor.obj,
    @CategoryTheory.Functor.monotone X Y _ _ f.toFunctor⟩, rfl⟩
