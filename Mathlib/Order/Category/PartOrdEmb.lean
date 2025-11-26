/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Johan Commelin
-/
import Mathlib.Order.Category.PartOrd

/-!
# Category of partial orders, with order embeddings as morphisms

This defines `PartOrdEmb`, the category of partial orders with order embeddings
as morphisms.

-/

open CategoryTheory

universe u

/-- The category of partial orders. -/
structure PartOrdEmb where
  /-- The underlying partially ordered type. -/
  (carrier : Type*)
  [str : PartialOrder carrier]

attribute [instance] PartOrdEmb.str

initialize_simps_projections PartOrdEmb (carrier → coe, -str)

namespace PartOrdEmb

instance : CoeSort PartOrdEmb (Type _) :=
  ⟨PartOrdEmb.carrier⟩

attribute [coe] PartOrdEmb.carrier

/-- Construct a bundled `PartOrdEmb` from the underlying type and typeclass. -/
abbrev of (X : Type*) [PartialOrder X] : PartOrdEmb := ⟨X⟩

/-- The type of morphisms in `PartOrdEmb R`. -/
@[ext]
structure Hom (X Y : PartOrdEmb.{u}) where
  private mk ::
  /-- The underlying `OrderEmbedding`. -/
  hom' : X ↪o Y

instance : Category PartOrdEmb.{u} where
  Hom X Y := Hom X Y
  id _ := ⟨RelEmbedding.refl _⟩
  comp f g := ⟨f.hom'.trans g.hom'⟩

instance : ConcreteCategory PartOrdEmb (· ↪o ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `PartOrdEmb` back into a `OrderEmbedding`. -/
abbrev Hom.hom {X Y : PartOrdEmb.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := PartOrdEmb) f

/-- Typecheck a `OrderEmbedding` as a morphism in `PartOrdEmb`. -/
abbrev ofHom {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ↪o Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := PartOrdEmb) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : PartOrdEmb.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma coe_id {X : PartOrdEmb} : (𝟙 X : X → X) = id := rfl

@[simp]
lemma coe_comp {X Y Z : PartOrdEmb} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
lemma forget_map {X Y : PartOrdEmb} (f : X ⟶ Y) :
    (forget PartOrdEmb).map f = f := rfl

@[ext]
lemma ext {X Y : PartOrdEmb} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (X : Type u) [PartialOrder X] : (PartOrdEmb.of X : Type u) = X := rfl

lemma hom_id {X : PartOrdEmb} : (𝟙 X : X ⟶ X).hom = RelEmbedding.refl _ := rfl

/- Provided for rewriting. -/
lemma id_apply (X : PartOrdEmb) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
lemma hom_comp {X Y Z : PartOrdEmb} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom.trans g.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {X Y Z : PartOrdEmb} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

lemma Hom.injective {X Y : PartOrdEmb.{u}} (f : X ⟶ Y) : Function.Injective f :=
  f.hom'.injective

@[ext]
lemma hom_ext {X Y : PartOrdEmb} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
lemma hom_ofHom {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ↪o Y) :
    (ofHom f).hom = f :=
  rfl

@[simp]
lemma ofHom_hom {X Y : PartOrdEmb} (f : X ⟶ Y) : ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type u} [PartialOrder X] : ofHom (RelEmbedding.refl _) = 𝟙 (of X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type u} [PartialOrder X] [PartialOrder Y] [PartialOrder Z]
    (f : X ↪o Y) (g : Y ↪o Z) :
    ofHom (f.trans g) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ↪o Y) (x : X) :
    (ofHom f) x = f x := rfl

lemma inv_hom_apply {X Y : PartOrdEmb} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

lemma hom_inv_apply {X Y : PartOrdEmb} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

instance hasForgetToPartOrd : HasForget₂ PartOrdEmb PartOrd where
  forget₂.obj X := .of X
  forget₂.map f := PartOrd.ofHom f.hom

/-- Constructs an equivalence between partial orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : PartOrdEmb.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
def dual : PartOrdEmb ⥤ PartOrdEmb where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `PartOrdEmb` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : PartOrdEmb ≌ PartOrdEmb where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end PartOrdEmb

theorem partOrdEmb_dual_comp_forget_to_pardOrd :
    PartOrdEmb.dual ⋙ forget₂ PartOrdEmb PartOrd =
      forget₂ PartOrdEmb PartOrd ⋙ PartOrd.dual :=
  rfl
