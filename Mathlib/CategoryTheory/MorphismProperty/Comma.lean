/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Comma.Over.Basic
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

lemma costructuredArrow_iso_iff (P : MorphismProperty T) [P.RespectsIso]
    {L : A ⥤ T} {X : T} {f g : CostructuredArrow L X} (e : f ≅ g) :
    P f.hom ↔ P g.hom :=
  P.comma_iso_iff e

lemma over_iso_iff (P : MorphismProperty T) [P.RespectsIso] {X : T} {f g : Over X} (e : f ≅ g) :
    P f.hom ↔ P g.hom :=
  P.comma_iso_iff e

section

variable {W : MorphismProperty T} {X : T}

/-- The object property on `Comma L R` induced by a morphism property. -/
def commaObj (W : MorphismProperty T) : ObjectProperty (Comma L R) :=
  fun f ↦ W f.hom

@[simp] lemma commaObj_iff (Y : Comma L R) : W.commaObj L R Y ↔ W Y.hom := .rfl

instance [W.RespectsIso] : (W.commaObj L R).IsClosedUnderIsomorphisms where
  of_iso {X Y} e h := by
    rwa [commaObj_iff, ← W.cancel_left_of_respectsIso (L.map e.hom.left), e.hom.w,
      W.cancel_right_of_respectsIso]

/-- The object property on `CostructuredArrow L X` induced by a morphism property. -/
def costructuredArrowObj (W : MorphismProperty T) : ObjectProperty (CostructuredArrow L X) :=
  fun f ↦ W f.hom

@[simp] lemma costructuredArrowObj_iff (Y : CostructuredArrow L X) :
    W.costructuredArrowObj L Y ↔ W Y.hom := .rfl

instance [W.RespectsIso] : (W.costructuredArrowObj L (X := X)).IsClosedUnderIsomorphisms :=
  inferInstanceAs <| (W.commaObj _ _).IsClosedUnderIsomorphisms

/-- The object property on `StructuredArrow X R` induced by a morphism property. -/
def structuredArrowObj (W : MorphismProperty T) : ObjectProperty (StructuredArrow X R) :=
  fun f ↦ W f.hom

@[simp] lemma structuredArrowObj_iff (Y : StructuredArrow X R) :
    W.structuredArrowObj R Y ↔ W Y.hom := .rfl

instance [W.RespectsIso] : (W.structuredArrowObj L (X := X)).IsClosedUnderIsomorphisms :=
  inferInstanceAs <| (W.commaObj _ _).IsClosedUnderIsomorphisms

/-- The morphism property on `Over X` induced by a morphism property on `C`. -/
def over (W : MorphismProperty T) {X : T} : MorphismProperty (Over X) := fun _ _ f ↦ W f.left

@[simp] lemma over_iff {Y Z : Over X} (f : Y ⟶ Z) : W.over f ↔ W f.left := .rfl

/-- The morphism property on `Under X` induced by a morphism property on `C`. -/
def under (W : MorphismProperty T) {X : T} : MorphismProperty (Under X) := fun _ _ f ↦ W f.right

@[simp] lemma under_iff {Y Z : Under X} (f : Y ⟶ Z) : W.under f ↔ W f.right := .rfl

/-- The object property on `Over X` induced by a morphism property. -/
def overObj (W : MorphismProperty T) {X : T} : ObjectProperty (Over X) := fun f ↦ W f.hom

@[simp] lemma overObj_iff (Y : Over X) : W.overObj Y ↔ W Y.hom := .rfl

instance [W.RespectsIso] : (W.overObj (X := X)).IsClosedUnderIsomorphisms :=
  inferInstanceAs <| (W.commaObj _ _).IsClosedUnderIsomorphisms

/-- The object property on `Under X` induced by a morphism property. -/
def underObj (W : MorphismProperty T) {X : T} : ObjectProperty (Under X) := fun f ↦ W f.hom

@[simp] lemma underObj_iff (Y : Under X) : W.underObj Y ↔ W Y.hom := .rfl

instance [W.RespectsIso] : (W.underObj (X := X)).IsClosedUnderIsomorphisms :=
  inferInstanceAs <| (W.commaObj _ _).IsClosedUnderIsomorphisms

end

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
lemma Hom.hom_mk {X Y : P.Comma L R Q W} (f : CommaMorphism X.toComma Y.toComma) (hf) (hg) :
    Comma.Hom.hom ⟨f, hf, hg⟩ = f := rfl

lemma Hom.hom_left {X Y : P.Comma L R Q W} (f : Comma.Hom X Y) : f.hom.left = f.left := rfl

lemma Hom.hom_right {X Y : P.Comma L R Q W} (f : Comma.Hom X Y) : f.hom.right = f.right := rfl

/-- See Note [custom simps projection] -/
def Hom.Simps.hom {X Y : P.Comma L R Q W} (f : X.Hom Y) :
    X.toComma ⟶ Y.toComma :=
  f.hom

initialize_simps_projections Comma.Hom (toCommaMorphism → hom)

/-- The identity morphism of an object in `P.Comma L R Q W`. -/
@[simps]
def id [Q.ContainsIdentities] [W.ContainsIdentities] (X : P.Comma L R Q W) : Comma.Hom X X where
  left := 𝟙 X.left
  right := 𝟙 X.right
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

lemma toCommaMorphism_eq_hom {X Y : P.Comma L R Q W} (f : X ⟶ Y) : f.toCommaMorphism = f.hom := rfl

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

@[reassoc]
lemma comp_left {X Y Z : P.Comma L R Q W} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).left = f.left ≫ g.left := rfl

@[reassoc]
lemma comp_right {X Y Z : P.Comma L R Q W} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).right = f.right ≫ g.right := rfl

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
in `P.Comma L R Q W`. -/
@[simps]
def isoFromComma [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W}
    (i : X.toComma ≅ Y.toComma) : X ≅ Y where
  hom := homFromCommaOfIsIso i.hom
  inv := homFromCommaOfIsIso i.inv

/-- Constructor for isomorphisms in `P.Comma L R Q W` from isomorphisms of the left and right
components and naturality in the forward direction. -/
@[simps!]
def isoMk [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W} (l : X.left ≅ Y.left)
    (r : X.right ≅ Y.right) (h : L.map l.hom ≫ Y.hom = X.hom ≫ R.map r.hom := by cat_disch) :
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

section

variable {L R}

@[simp]
lemma eqToHom_left {X Y : P.Comma L R Q W} (h : X = Y) :
    (eqToHom h).left = eqToHom (by rw [h]) := by
  subst h
  rfl

@[simp]
lemma eqToHom_right {X Y : P.Comma L R Q W} (h : X = Y) :
    (eqToHom h).right = eqToHom (by rw [h]) := by
  subst h
  rfl

end

section

variable {P P' : MorphismProperty T} {Q Q' : MorphismProperty A} {W W' : MorphismProperty B}
  (hP : P ≤ P') (hQ : Q ≤ Q') (hW : W ≤ W')

variable [Q.IsMultiplicative] [Q'.IsMultiplicative] [W.IsMultiplicative] [W'.IsMultiplicative]

/-- Weaken the conditions on all components. -/
def changeProp : P.Comma L R Q W ⥤ P'.Comma L R Q' W' where
  obj X := ⟨X.toComma, hP _ X.2⟩
  map f := ⟨f.toCommaMorphism, hQ _ f.2, hW _ f.3⟩

/-- Weakening the condition on the structure morphisms is fully faithful. -/
def fullyFaithfulChangeProp :
    (changeProp (Q := Q) (W := W) L R hP le_rfl le_rfl).FullyFaithful where
  preimage f := ⟨f.toCommaMorphism, f.2, f.3⟩

instance : (changeProp L R hP hQ hW).Faithful where
  map_injective {X Y} f g h := by ext : 1; exact congr($(h).hom)

instance : (changeProp (Q := Q) (W := W) L R hP le_rfl le_rfl).Full :=
  (fullyFaithfulChangeProp ..).full

end

section Functoriality

variable {L R P Q W}
variable {L₁ L₂ L₃ : A ⥤ T} {R₁ R₂ R₃ : B ⥤ T}

/-- Lift a functor `F : C ⥤ Comma L R` to the subcategory `P.Comma L R Q W` under
suitable assumptions on `F`. -/
@[simps obj_toComma map_hom]
def lift {C : Type*} [Category C] (F : C ⥤ Comma L R)
    (hP : ∀ X, P (F.obj X).hom)
    (hQ : ∀ {X Y} (f : X ⟶ Y), Q (F.map f).left)
    (hW : ∀ {X Y} (f : X ⟶ Y), W (F.map f).right) :
    C ⥤ P.Comma L R Q W where
  obj X :=
    { __ := F.obj X
      prop := hP X }
  map {X Y} f :=
    { __ := F.map f
      prop_hom_left := hQ f
      prop_hom_right := hW f }

variable (R) in
/-- A natural transformation `L₁ ⟶ L₂` induces a functor `P.Comma L₂ R Q W ⥤ P.Comma L₁ R Q W`. -/
@[simps!]
def mapLeft (l : L₁ ⟶ L₂) (hl : ∀ X : P.Comma L₂ R Q W, P (l.app X.left ≫ X.hom)) :
    P.Comma L₂ R Q W ⥤ P.Comma L₁ R Q W :=
  lift (forget _ _ _ _ _ ⋙ CategoryTheory.Comma.mapLeft R l) hl
    (fun f ↦ f.prop_hom_left) (fun f ↦ f.prop_hom_right)

variable (L) in
/-- A natural transformation `R₁ ⟶ R₂` induces a functor `P.Comma L R₁ Q W ⥤ P.Comma L R₂ Q W`. -/
@[simps!]
def mapRight (r : R₁ ⟶ R₂) (hr : ∀ X : P.Comma L R₁ Q W, P (X.hom ≫ r.app X.right)) :
    P.Comma L R₁ Q W ⥤ P.Comma L R₂ Q W :=
  lift (forget _ _ _ _ _ ⋙ CategoryTheory.Comma.mapRight L r) hr
    (fun f ↦ f.prop_hom_left) (fun f ↦ f.prop_hom_right)

end Functoriality

end Comma

end Comma

section Over

variable {T : Type*} [Category T] (P Q : MorphismProperty T) (X : T) [Q.IsMultiplicative]

/-- Given a morphism property `P` on a category `C` and an object `X : C`, this is the
subcategory of `Over X` defined by `P` where morphisms satisfy `Q`. -/
protected abbrev Over : Type _ :=
  P.Comma (Functor.id T) (Functor.fromPUnit.{0} X) Q ⊤

/-- The forgetful functor from the full subcategory of `Over X` defined by `P` to `Over X`. -/
protected abbrev Over.forget : P.Over Q X ⥤ Over X :=
  Comma.forget (Functor.id T) (Functor.fromPUnit.{0} X) P Q ⊤

instance : (Over.forget P ⊤ X).Faithful := inferInstanceAs <| (Comma.forget _ _ _ _ _).Faithful
instance : (Over.forget P ⊤ X).Full := inferInstanceAs <| (Comma.forget _ _ _ _ _).Full

variable {P Q X}

/-- Construct a morphism in `P.Over Q X` from a morphism in `Over.X`. -/
@[simps hom]
def Over.Hom.mk {A B : P.Over Q X} (f : A.toComma ⟶ B.toComma) (hf : Q f.left) : A ⟶ B where
  __ := f
  prop_hom_left := hf
  prop_hom_right := trivial

variable (Q) in
/-- Make an object of `P.Over Q X` from a morphism `f : A ⟶ X` and a proof of `P f`. -/
@[simps hom left]
protected def Over.mk {A : T} (f : A ⟶ X) (hf : P f) : P.Over Q X where
  left := A
  right := ⟨⟨⟩⟩
  hom := f
  prop := hf

/-- Make a morphism in `P.Over Q X` from a morphism in `T` with compatibilities. -/
@[simps hom]
protected def Over.homMk {A B : P.Over Q X} (f : A.left ⟶ B.left)
    (w : f ≫ B.hom = A.hom := by cat_disch) (hf : Q f := by trivial) : A ⟶ B where
  __ := CategoryTheory.Over.homMk f w
  prop_hom_left := hf
  prop_hom_right := trivial

/-- Make an isomorphism in `P.Over Q X` from an isomorphism in `T` with compatibilities. -/
@[simps! hom_left inv_left]
protected def Over.isoMk [Q.RespectsIso] {A B : P.Over Q X} (f : A.left ≅ B.left)
    (w : f.hom ≫ B.hom = A.hom := by cat_disch) : A ≅ B :=
  Comma.isoMk f (Discrete.eqToIso' rfl)

@[ext]
lemma Over.Hom.ext {A B : P.Over Q X} {f g : A ⟶ B} (h : f.left = g.left) : f = g := by
  ext
  · exact h
  · simp

@[reassoc]
lemma Over.w {A B : P.Over Q X} (f : A ⟶ B) :
    f.left ≫ B.hom = A.hom := by
  simp

end Over

section Under

variable {T : Type*} [Category T] (P Q : MorphismProperty T) (X : T) [Q.IsMultiplicative]

/-- Given a morphism property `P` on a category `C` and an object `X : C`, this is the
subcategory of `Under X` defined by `P` where morphisms satisfy `Q`. -/
protected abbrev Under : Type _ :=
  P.Comma (Functor.fromPUnit.{0} X) (Functor.id T) ⊤ Q

/-- The forgetful functor from the full subcategory of `Under X` defined by `P` to `Under X`. -/
protected abbrev Under.forget : P.Under Q X ⥤ Under X :=
  Comma.forget (Functor.fromPUnit.{0} X) (Functor.id T) P ⊤ Q

instance : (Under.forget P ⊤ X).Faithful := inferInstanceAs <| (Comma.forget _ _ _ _ _).Faithful
instance : (Under.forget P ⊤ X).Full := inferInstanceAs <| (Comma.forget _ _ _ _ _).Full

variable {P Q X}

/-- Construct a morphism in `P.Under Q X` from a morphism in `Under.X`. -/
@[simps hom]
def Under.Hom.mk {A B : P.Under Q X} (f : A.toComma ⟶ B.toComma) (hf : Q f.right) : A ⟶ B where
  __ := f
  prop_hom_left := trivial
  prop_hom_right := hf

variable (Q) in
/-- Make an object of `P.Under Q X` from a morphism `f : A ⟶ X` and a proof of `P f`. -/
@[simps hom left]
protected def Under.mk {A : T} (f : X ⟶ A) (hf : P f) : P.Under Q X where
  left := ⟨⟨⟩⟩
  right := A
  hom := f
  prop := hf

/-- Make a morphism in `P.Under Q X` from a morphism in `T` with compatibilities. -/
@[simps hom]
protected def Under.homMk {A B : P.Under Q X} (f : A.right ⟶ B.right)
    (w : A.hom ≫ f = B.hom := by cat_disch) (hf : Q f := by trivial) : A ⟶ B where
  __ := CategoryTheory.Under.homMk f w
  prop_hom_left := trivial
  prop_hom_right := hf

/-- Make an isomorphism in `P.Under Q X` from an isomorphism in `T` with compatibilities. -/
@[simps! hom_right inv_right]
protected def Under.isoMk [Q.RespectsIso] {A B : P.Under Q X} (f : A.right ≅ B.right)
    (w : A.hom ≫ f.hom = B.hom := by cat_disch) : A ≅ B :=
  Comma.isoMk (Discrete.eqToIso' rfl) f

@[ext]
lemma Under.Hom.ext {A B : P.Under Q X} {f g : A ⟶ B} (h : f.right = g.right) : f = g := by
  ext
  · simp
  · exact h

@[reassoc]
lemma Under.w {A B : P.Under Q X} (f : A ⟶ B) :
    A.hom ≫ f.right = B.hom := by
  simp

end Under

end CategoryTheory.MorphismProperty
