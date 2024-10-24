/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Subcategories of comma categories defined by morphism properties

Given functors `L : A ⥤ T` and `R : B ⥤ T` and morphism properties `P`, `Q` and `W`
on `T`, A` and `B` respectively, we define the subcategory `P.Comma L R Q W` of
`Comma L R` where

- objects are objects of `Comma L R` with the structural morphism satisfying `P`, and
- morphisms are morphisms of `Comma L R` where the left morphism satisfies `Q` and the
  right morphism satisfies `W`.

For an object `X : T`, this specializes to `P.Over Q X` which is the subcategory of `Over X`
where the structural morphism satisfies `P` and where the horizontal morphisms satisfy `Q`.
Common examples of the latter are e.g. the category of schemes étale (finite, affine, etc.)
over a base `X`. Here `Q = ⊤`.

## Implementation details

- We provide the general constructor `P.Comma L R Q W` to obtain `Over X` and `Under X` as
  special cases of the more general setup.

- Most results are developed only in the case where `Q = ⊤` and `W = ⊤`, but the definition
  is setup in the general case to allow for a later generalization if needed.

-/

namespace CategoryTheory.MorphismProperty

open Limits

section Comma

variable {A : Type*} [Category A] {B : Type*} [Category B] {T : Type*} [Category T]
  (L : A ⥤ T) (R : B ⥤ T)

variable (P : MorphismProperty T) (Q : MorphismProperty A) (W : MorphismProperty B)

/-- `P.Comma L R Q W` is the subcategory of `Comma L R` consisting of
objects `X : Comma L R` where `X.hom` satisfies `P`. The morphisms are given by
morphisms in `Comma L R` where the left one satisfies `Q` and the right one satisfies `W`. -/
@[ext]
protected structure Comma (Q : MorphismProperty A) (W : MorphismProperty B) extends Comma L R where
  prop : P toComma.hom

namespace Comma

variable {L R P Q W}

/-- A morphism in `P.Comma L R Q W` is a morphism in `Comma L R` where the left
hom satisfies `Q` and the right one satisfies `W`. -/
@[ext]
structure Hom (X Y : P.Comma L R Q W) extends CommaMorphism X.toComma Y.toComma where
  prop_hom_left : Q toCommaMorphism.left
  prop_hom_right : W toCommaMorphism.right

/-- The underlying morphism of objects in `Comma L R`. -/
abbrev Hom.hom {X Y : P.Comma L R Q W} (f : Comma.Hom X Y) : X.toComma ⟶ Y.toComma :=
  f.toCommaMorphism

@[simp, nolint simpVarHead]
lemma Hom.hom_mk {X Y : P.Comma L R Q W}
    (f : CommaMorphism X.toComma Y.toComma) (hf) (hg) :
  Comma.Hom.hom ⟨f, hf, hg⟩ = f := rfl

/-- See Note [custom simps projection] -/
def Hom.Simps.hom {X Y : P.Comma L R Q W} (f : X.Hom Y) :
    X.toComma ⟶ Y.toComma :=
  f.hom

initialize_simps_projections Comma.Hom (toCommaMorphism → hom)

/-- The identity morphism of an object in `P.Comma L R Q W`. -/
@[simps]
def id [Q.ContainsIdentities] [W.ContainsIdentities] (X : P.Comma L R Q W) : Comma.Hom X X where
  left := 𝟙 X.left
  prop_hom_left := Q.id_mem X.toComma.left
  prop_hom_right := W.id_mem X.toComma.right

/-- Composition of morphisms in `P.Comma L R Q W`. -/
@[simps]
def Hom.comp [Q.IsStableUnderComposition] [W.IsStableUnderComposition] {X Y Z : P.Comma L R Q W}
    (f : Comma.Hom X Y) (g : Comma.Hom Y Z) :
    Comma.Hom X Z where
  left := f.left ≫ g.left
  right := f.right ≫ g.right
  prop_hom_left := Q.comp_mem _ _ f.prop_hom_left g.prop_hom_left
  prop_hom_right := W.comp_mem _ _ f.prop_hom_right g.prop_hom_right

variable [Q.IsMultiplicative] [W.IsMultiplicative]

variable (L R P Q W) in
instance : Category (P.Comma L R Q W) where
  Hom X Y := X.Hom Y
  id X := X.id
  comp f g := f.comp g

/-- Alternative `ext` lemma for `Comma.Hom`. -/
@[ext]
lemma Hom.ext' {X Y : P.Comma L R Q W} {f g : X ⟶ Y} (h : f.hom = g.hom) :
    f = g := Comma.Hom.ext
  (congrArg CommaMorphism.left h)
  (congrArg CommaMorphism.right h)

@[simp]
lemma id_hom (X : P.Comma L R Q W) : (𝟙 X : X ⟶ X).hom = 𝟙 X.toComma := rfl

@[simp]
lemma comp_hom {X Y Z : P.Comma L R Q W} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- If `i` is an isomorphism in `Comma L R`, it is also a morphism in `P.Comma L R Q W`. -/
@[simps hom]
def homFromCommaOfIsIso [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W}
    (i : X.toComma ⟶ Y.toComma) [IsIso i] :
    X ⟶ Y where
  __ := i
  prop_hom_left := Q.of_isIso i.left
  prop_hom_right := W.of_isIso i.right

instance [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W} (i : X.toComma ⟶ Y.toComma)
    [IsIso i] : IsIso (homFromCommaOfIsIso i) := by
  constructor
  use homFromCommaOfIsIso (inv i)
  constructor <;> ext : 1 <;> simp

/-- Any isomorphism between objects of `P.Comma L R Q W` in `Comma L R` is also an isomorphism
in `P.Comma L R Q W`.  -/
@[simps]
def isoFromComma [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W}
    (i : X.toComma ≅ Y.toComma) : X ≅ Y where
  hom := homFromCommaOfIsIso i.hom
  inv := homFromCommaOfIsIso i.inv

/-- Constructor for isomorphisms in `P.Comma L R Q W` from isomorphisms of the left and right
components and naturality in the forward direction. -/
@[simps!]
def isoMk [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W} (l : X.left ≅ Y.left)
    (r : X.right ≅ Y.right) (h : L.map l.hom ≫ Y.hom = X.hom ≫ R.map r.hom := by aesop_cat) :
    X ≅ Y :=
  isoFromComma (CategoryTheory.Comma.isoMk l r h)

variable (L R P Q W)

/-- The forgetful functor. -/
@[simps]
def forget : P.Comma L R Q W ⥤ Comma L R where
  obj X := X.toComma
  map f := f.hom

instance : (forget L R P Q W).Faithful where
  map_injective := Comma.Hom.ext'

variable {L R P Q W}

instance {X Y : P.Comma L R Q W} (f : X ⟶ Y) [IsIso f] : IsIso f.hom :=
  (forget L R P Q W).map_isIso f

lemma hom_homFromCommaOfIsIso [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W}
    (i : X ⟶ Y) [IsIso i.hom] :
    homFromCommaOfIsIso i.hom = i :=
  rfl

lemma inv_hom {X Y : P.Comma L R Q W} (f : X ⟶ Y) [IsIso f] : (inv f).hom = inv f.hom := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← comp_hom, IsIso.hom_inv_id, id_hom]

variable (L R P Q W)

instance [Q.RespectsIso] [W.RespectsIso] : (forget L R P Q W).ReflectsIsomorphisms where
  reflects f hf := by
    simp only [forget_obj, forget_map] at hf
    rw [← hom_homFromCommaOfIsIso f]
    infer_instance

/-- The forgetful functor from the full subcategory of `Comma L R` defined by `P` is
fully faithful. -/
def forgetFullyFaithful : (forget L R P ⊤ ⊤).FullyFaithful where
  preimage {X Y} f := ⟨f, trivial, trivial⟩

instance : (forget L R P ⊤ ⊤).Full :=
  Functor.FullyFaithful.full (forgetFullyFaithful L R P)

end Comma

end Comma

section Over

variable {T : Type*} [Category T]

/-- Given a morphism property `P` on a category `C` and an object `X : C`, this is the
subcategory of `Over X` defined by `P` where morphisms satisfy `Q`. -/
protected abbrev Over (P Q : MorphismProperty T) (X : T) : Type _ :=
  P.Comma (Functor.id T) (Functor.fromPUnit X) Q ⊤

variable (P Q : MorphismProperty T) [Q.IsMultiplicative] (X : T)

/-- Construct a morphism in `P.Over Q X` from a morphism in `Over X`. -/
@[simps hom]
def Over.Hom.mk {A B : P.Over Q X} (f : A.toComma ⟶ B.toComma) (hf : Q f.left) : A ⟶ B where
  __ := f
  prop_hom_left := hf
  prop_hom_right := trivial

/-- The forgetful functor from the full subcategory of `Over X` defined by `P` to `Over X`. -/
protected abbrev Over.forget : P.Over Q X ⥤ Over X :=
  Comma.forget (Functor.id T) (Functor.fromPUnit X) P Q ⊤

end Over

section Under

variable {T : Type*} [Category T]

/-- Given a morphism property `P` on a category `C` and an object `X : C`, this is the
subcategory of `Under X` defined by `P` where morphisms satisfy `Q`. -/
protected abbrev Under (P Q : MorphismProperty T) (X : T) : Type _ :=
  P.Comma (Functor.fromPUnit X) (Functor.id T) ⊤ Q

variable (P Q : MorphismProperty T) [Q.IsMultiplicative] (X : T)

/-- Construct a morphism in `P.Under Q X` from a morphism in `Under.X`. -/
@[simps hom]
def Under.Hom.mk {A B : P.Under Q X} (f : A.toComma ⟶ B.toComma) (hf : Q f.right) : A ⟶ B where
  __ := f
  prop_hom_left := trivial
  prop_hom_right := hf

/-- The forgetful functor from the full subcategory of `Under X` defined by `P` to `Under X`. -/
protected abbrev Under.forget : P.Under Q X ⥤ Under X :=
  Comma.forget (Functor.fromPUnit X) (Functor.id T) P ⊤ Q

end Under

end CategoryTheory.MorphismProperty
