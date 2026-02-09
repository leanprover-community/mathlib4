/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johannes Hölzl, Reid Barton, Sean Leather, Yury Kudryashov, Anne Baanen, Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Concrete categories

A concrete category is a category `C` where the objects and morphisms correspond with types and
(bundled) functions between these types. We define concrete categories using
`class ConcreteCategory`. To convert an object to a type, write `ToType`. To convert a morphism
to a (bundled) function, write `hom`.

Each concrete category `C` comes with a canonical faithful functor `forget C : C ⥤ Type*`,
see the file `Mathlib.CategoryTheory.ConcreteCategory.Forget`

## Implementation notes

We do not use `CoeSort` to convert objects in a concrete category to types, since this would lead
to elaboration mismatches between results taking a `[ConcreteCategory C]` instance and specific
types `C` that hold a `ConcreteCategory C` instance: the first gets a literal `CoeSort.coe` and
the second gets unfolded to the actual `coe` field.

`ToType` and `ToHom` are `abbrev`s so that we do not need to copy over instances such as `Ring`
or `RingHomClass` respectively.

## References

See [Ahrens and Lumsdaine, *Displayed Categories*][ahrens2017] for
related work.
-/

@[expose] public section


assert_not_exists CategoryTheory.CommSq CategoryTheory.Adjunction

universe w w' v v' v'' u u' u''

namespace CategoryTheory

section ConcreteCategory

/-- A concrete category is a category `C` where objects correspond to types and morphisms to
(bundled) functions between those types.

In other words, it has a fixed faithful functor `forget : C ⥤ Type`.

Note that `ConcreteCategory` potentially depends on three independent universe levels,
* the universe level `w` appearing in `forget : C ⥤ Type w`
* the universe level `v` of the morphisms (i.e. we have a `Category.{v} C`)
* the universe level `u` of the objects (i.e `C : Type u`)
They are specified that order, to avoid unnecessary universe annotations.
-/
class ConcreteCategory (C : Type u) [Category.{v} C]
    (FC : outParam <| C → C → Type*) {CC : outParam <| C → Type w}
    [outParam <| ∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] where
  /-- Convert a morphism of `C` to a bundled function. -/
  (hom : ∀ {X Y}, (X ⟶ Y) → FC X Y)
  /-- Convert a bundled function to a morphism of `C`. -/
  (ofHom : ∀ {X Y}, FC X Y → (X ⟶ Y))
  (hom_ofHom : ∀ {X Y} (f : FC X Y), hom (ofHom f) = f := by cat_disch)
  (ofHom_hom : ∀ {X Y} (f : X ⟶ Y), ofHom (hom f) = f := by cat_disch)
  (id_apply : ∀ {X} (x : CC X), hom (𝟙 X) x = x := by cat_disch)
  (comp_apply : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) (x : CC X),
    hom (f ≫ g) x = hom g (hom f x) := by cat_disch)

export ConcreteCategory (id_apply comp_apply)
attribute [simp] ConcreteCategory.hom_ofHom ConcreteCategory.ofHom_hom

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type w}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]

/-- `ToType X` converts the object `X` of the concrete category `C` to a type.

This is an `abbrev` so that instances on `X` (e.g. `Ring`) do not need to be redeclared.
-/
@[nolint unusedArguments] -- Need the instance to trigger unification that finds `CC`.
abbrev ToType [ConcreteCategory C FC] := CC

/-- `ToHom X Y` is the type of (bundled) functions between objects `X Y : C`.

This is an `abbrev` so that instances (e.g. `RingHomClass`) do not need to be redeclared.
-/
@[nolint unusedArguments] -- Need the instance to trigger unification that finds `FC`.
abbrev ToHom [ConcreteCategory C FC] := FC

variable [ConcreteCategory C FC]

namespace ConcreteCategory

/-- We can apply morphisms of concrete categories by first casting them down
to the base functions.
-/
instance {X Y : C} : CoeFun (X ⟶ Y) (fun _ ↦ ToType X → ToType Y) where
  coe f := hom f

/-- A non-instance `FunLike` instance on `X ⟶ Y`. -/
abbrev _root_.CategoryTheory.HasForget.instFunLike {X Y : C} :
    FunLike (X ⟶ Y) (ToType X) (ToType Y) where
  coe f := f
  coe_injective' f g h := by
    rw [← ofHom_hom f, ← ofHom_hom g]
    simp_all

/--
`ConcreteCategory.hom` bundled as an `Equiv`.
-/
def homEquiv {X Y : C} : (X ⟶ Y) ≃ ToHom X Y where
  toFun := hom
  invFun := ofHom
  left_inv := ofHom_hom
  right_inv := hom_ofHom

lemma hom_bijective {X Y : C} : Function.Bijective (hom : (X ⟶ Y) → ToHom X Y) :=
  homEquiv.bijective

lemma hom_injective {X Y : C} : Function.Injective (hom : (X ⟶ Y) → ToHom X Y) :=
  hom_bijective.injective

lemma hom_surjective {X Y : C} : Function.Surjective (hom : (X ⟶ Y) → ToHom X Y) :=
  hom_bijective.surjective

/-- In any concrete category, we can test equality of morphisms by pointwise evaluations. -/
@[ext] lemma ext {X Y : C} {f g : X ⟶ Y} (h : hom f = hom g) : f = g :=
  hom_injective h

lemma coe_ext {X Y : C} {f g : X ⟶ Y} (h : ⇑(hom f) = ⇑(hom g)) : f = g :=
  ext (DFunLike.coe_injective h)

lemma ext_apply {X Y : C} {f g : X ⟶ Y} (h : ∀ x, f x = g x) : f = g :=
  ext (DFunLike.ext _ _ h)

/-- In any concrete category, we can test equality of morphisms by pointwise evaluations. -/
@[ext low]
theorem hom_ext {X Y : C} (f g : X ⟶ Y) (w : ∀ x : ToType X, f x = g x) : f = g := by
  apply ConcreteCategory.ext_apply
  exact w

/-- Analogue of `congr_fun h x`,
when `h : f = g` is an equality between morphisms in a concrete category.
-/
theorem congr_hom {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : ToType X) : f x = g x :=
  congrFun (congrArg (fun k : X ⟶ Y => (k : ToType X → ToType Y)) h) x

theorem coe_id {X : C} : (𝟙 X : ToType X → ToType X) = id := by
  ext
  simp [ConcreteCategory.id_apply]

theorem coe_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : ToType X → ToType Z) = g ∘ f := by
  ext
  simp [ConcreteCategory.comp_apply]

@[simp] theorem _root_.CategoryTheory.id_apply {X : C} (x : ToType X) :
    (𝟙 X : ToType X → ToType X) x = x := by
  simp [ConcreteCategory.id_apply]

@[simp] theorem _root_.CategoryTheory.comp_apply {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : ToType X) : (f ≫ g) x = g (f x) := by
  simp [ConcreteCategory.comp_apply]

@[deprecated (since := "2026-02-06")] alias _root_.CategoryTheory.comp_apply' :=
  _root_.CategoryTheory.comp_apply

theorem congr_arg {X Y : C} (f : X ⟶ Y) {x x' : ToType X} (h : x = x') : f x = f x' :=
  congrArg (f : ToType X → ToType Y) h

end ConcreteCategory

theorem hom_id {X : C} : (𝟙 X : ToType X → ToType X) = id := by
  ext
  simp

theorem hom_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : ToType X → ToType Z) = g ∘ f := by
  ext
  simp

open ConcreteCategory

instance InducedCategory.concreteCategory {C : Type u} {D : Type u'} [Category.{v'} D]
    {FD : D → D → Type*} {CD : D → Type w} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory.{w} D FD] (f : C → D) :
    ConcreteCategory (InducedCategory D f) (fun X Y => FD (f X) (f Y)) where
  hom f := hom f.hom
  ofHom g := homMk (ofHom g)
  hom_ofHom _ := hom_ofHom _
  ofHom_hom _ := by ext; simp [ofHom_hom]
  comp_apply _ _ _ := ConcreteCategory.comp_apply _ _ _
  id_apply _ := ConcreteCategory.id_apply _

open ObjectProperty in
instance FullSubcategory.concreteCategory {C : Type u} [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type w} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory.{w} C FC]
    (P : ObjectProperty C) : ConcreteCategory P.FullSubcategory (fun X Y => FC X.1 Y.1) where
  hom f := hom f.hom
  ofHom g := homMk (ofHom g)
  hom_ofHom _ := hom_ofHom _
  ofHom_hom _ := by ext; simp [ofHom_hom]
  comp_apply _ _ _ := ConcreteCategory.comp_apply _ _ _
  id_apply _ := ConcreteCategory.id_apply _

end ConcreteCategory

variable {C : Type u} [Category.{v} C]
variable {D : Type*} [Category* D] {FD : outParam <| D → D → Type*}
    {CD : outParam <| D → Type w}
    [outParam <| ∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]

@[simp]
lemma NatTrans.naturality_apply {F G : C ⥤ D} (φ : F ⟶ G) {X Y : C} (f : X ⟶ Y)
    (x : ToType (F.obj X)) :
    φ.app Y (F.map f x) = G.map f (φ.app X x) := by
  simp [← CategoryTheory.comp_apply]

end CategoryTheory
