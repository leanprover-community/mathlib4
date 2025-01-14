/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johannes Hölzl, Reid Barton, Sean Leather, Yury Kudryashov
-/
import Mathlib.CategoryTheory.Types

/-!
# Concrete categories

A concrete category is a category `C` where the objects and morphisms correspond with types and
(bundled) functions between these types. We define concrete categories using
`class ConcreteCategory`. To convert an object to a type, write `ToHom`. To convert a morphism
to a (bundled) function, write `hom`.

Each concrete category `C` comes with a canonical faithful functor `forget C : C ⥤ Type*`,
see `class HasForget`. In particular, we impose no restrictions on the category `C`, so `Type`
has the identity forgetful functor.

We say that a concrete category `C` admits a *forgetful functor* to a concrete category `D`, if it
has a functor `forget₂ C D : C ⥤ D` such that `(forget₂ C D) ⋙ (forget D) = forget C`, see
`class HasForget₂`.  Due to `Faithful.div_comp`, it suffices to verify that `forget₂.obj` and
`forget₂.map` agree with the equality above; then `forget₂` will satisfy the functor laws
automatically, see `HasForget₂.mk'`.

Two classes helping construct concrete categories in the two most
common cases are provided in the files `BundledHom` and
`UnbundledHom`, see their documentation for details.

## Implementation notes

Previously, `ConcreteCategory` had the same definition as now `HasForget`; the coercion of
objects/morphisms to types/functions was defined as `(forget C).obj` and `(forget C).map`
respectively. This leads to defeq issues since existing `CoeFun` and `FunLike` instances provide
their own casts. We replace this with a less bundled `ConcreteCategory` that does not directly
use these coercions.

We do not use `CoeSort` to convert objects in a concrete category to types, since this would lead
to elaboration mismatches between results taking a `[ConcreteCategory C]` instance and specific
types `C` that hold a `ConcreteCategory C` instance: the first gets a literal `CoeSort.coe` and
the second gets unfolded to the actual `coe` field.

`ToType` and `ToHom` are `abbrev`s so that we do not need to copy over instances such as `Ring`
or `RingHomClass` respectively.

Since `X → Y` is not a `FunLike`, the category of types is not a `ConcreteCategory`, but it does
have a `HasForget` instance.

## References

See [Ahrens and Lumsdaine, *Displayed Categories*][ahrens2017] for
related work.
-/


assert_not_exists CategoryTheory.CommSq CategoryTheory.Adjunction

universe w w' v v' v'' u u' u''

namespace CategoryTheory

/-- Class for categories `C` with a fixed faithful functor `forget : C ⥤ Type`.

This forgetful functor should not be used to cast objects or morphisms to
types or functions respectively: see `ConcreteCategory` for that.

Note that `HasForget` potentially depends on three independent universe levels,
* the universe level `w` appearing in `forget : C ⥤ Type w`
* the universe level `v` of the morphisms (i.e. we have a `Category.{v} C`)
* the universe level `u` of the objects (i.e `C : Type u`)
They are specified that order, to avoid unnecessary universe annotations.
-/
class HasForget (C : Type u) [Category.{v} C] where
  /-- We have a functor to Type -/
  protected forget : C ⥤ Type w
  /-- That functor is faithful -/
  [forget_faithful : forget.Faithful]

attribute [inline, reducible] HasForget.forget
attribute [instance] HasForget.forget_faithful

/-- The forgetful functor from a concrete category to `Type u`. -/
abbrev forget (C : Type u) [Category.{v} C] [HasForget.{w} C] : C ⥤ Type w :=
  HasForget.forget

-- this is reducible because we want `forget (Type u)` to unfold to `𝟭 _`
@[instance] abbrev HasForget.types : HasForget.{u, u, u+1} (Type u) where
  forget := 𝟭 _

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
  (hom_ofHom : ∀ {X Y} (f : FC X Y), hom (ofHom f) = f := by aesop_cat)
  (ofHom_hom : ∀ {X Y} (f : X ⟶ Y), ofHom (hom f) = f := by aesop_cat)
  (id_apply : ∀ {X} (x : CC X), hom (𝟙 X) x = x := by aesop_cat)
  (comp_apply : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) (x : CC X),
    hom (f ≫ g) x = hom g (hom f x) := by aesop_cat)

export ConcreteCategory (id_apply comp_apply)

section

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type w}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory C FC]

/-- `ToType X` converts the object `X` of the concrete category `C` to a type.

This is an `abbrev` so that instances on `X` (e.g. `Ring`) do not need to be redeclared.
-/
abbrev ToType [ConcreteCategory C FC] := CC

/-- `ToHom X Y` is the type of (bundled) functions between objects `X Y : C`.

This is an `abbrev` so that instances (e.g. `RingHomClass`) do not need to be redeclared.
-/
abbrev ToHom [ConcreteCategory C FC] := FC

namespace ConcreteCategory

/- TODO: or should we prime all the `CC`/`FC` based fields and copy them over with `ToType`/`ToFun`?
/-- Convert a morphism of `C` to a bundled function. -/
abbrev hom {X Y : C} : (X ⟶ Y) → ToHom X Y := hom'

/-- Convert a bundled function to a morphism of `C`. -/
abbrev ofHom {X Y : C} : ToHom X Y → (X ⟶ Y) := ofHom'

lemma hom_ofHom {X Y : C} (f : ToHom X Y) : hom (ofHom f) = f := hom_ofHom' f

lemma ofHom_hom {X Y : C} (f : X ⟶ Y) : ofHom (hom f) = f := ofHom_hom' f

lemma id_apply {X : C} (x : ToType X) : hom (𝟙 X) x = x := id_apply' x
lemma comp_apply {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (x : ToType X) :
    hom (f ≫ g) x = hom g (hom f x) := comp_apply' f g x
-/

attribute [simp] id_apply comp_apply

/-- We can apply morphisms of concrete categories by first casting them down
to the base functions.
-/
instance {X Y : C} : CoeFun (X ⟶ Y) (fun _ ↦ ToType X → ToType Y) where
  coe f := hom f

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

@[ext] lemma hom_ext {X Y : C} {f g : X ⟶ Y} (h : hom f = hom g) : f = g :=
  hom_injective h

lemma coe_ext {X Y : C} {f g : X ⟶ Y} (h : ⇑(hom f) = ⇑(hom g)) : f = g :=
  hom_ext (DFunLike.coe_injective h)

lemma ext_apply {X Y : C} {f g : X ⟶ Y} (h : ∀ x, f x = g x) : f = g :=
  hom_ext (DFunLike.ext _ _ h)

-- TODO: this inheritance is not forgetful, so we can't make `forget Type`
-- reducibly defeq to the identity functor.
instance toHasForget : HasForget C where
  forget.obj := ToType
  forget.map f := ⇑(hom f)
  forget_faithful.map_injective h := coe_ext h

end ConcreteCategory

section

variable (C)

/-- Build a coercion to functions out of `HasForget`.

The intended usecase is to provide a `FunLike` instance in `HasForget.toConcreteCategory`.
See that definition for the considerations in making this an instance.
-/
abbrev HasForget.toFunLike [HasForget C] (X Y : C) :
    FunLike (X ⟶ Y) ((forget C).obj X) ((forget C).obj Y) where
  coe := (forget C).map
  coe_injective' _ _ h := Functor.Faithful.map_injective h

attribute [local instance] HasForget.toFunLike
/-- Build a concrete category out of `HasForget`.

The intended usecase is to prove theorems referencing only `(forget C)`
and not `(forget C).obj X` nor `(forget C).map f`: those should be written
as `ToType X` and `ConcreteCategory.hom f` respectively.
-/
abbrev HasForget.toConcreteCategory [HasForget C] :
    ConcreteCategory C (· ⟶ ·) where
  hom f := f
  ofHom f := f
  id_apply := congr_fun ((forget C).map_id _)
  comp_apply _ _ := congr_fun ((forget C).map_comp _ _)

attribute [local instance] HasForget.toConcreteCategory

/-- Check that the new `ConcreteCategory` has the same forgetful functor as we started with. -/
example [inst : HasForget C] :
    @forget C _ ((HasForget.toConcreteCategory _).toHasForget) = @forget C _ inst := by
  with_reducible_and_instances rfl

/--
Note that the `ConcreteCategory` and `HasForget` instances here differ from `forget_map_eq_coe`.
-/
theorem forget_eq_ConcreteCategory_hom [HasForget C] {X Y : C} (f : X ⟶ Y) :
  (forget C).map f = @ConcreteCategory.hom _ _ _ _ _ (HasForget.toConcreteCategory C) _ _ f := rfl

end

theorem forget_obj (X : C) : (forget C).obj X = ToType X := rfl

@[simp]
theorem forget_map_eq_coe {X Y : C} (f : X ⟶ Y) : (forget C).map f = f := rfl

/-- Analogue of `congr_fun h x`,
when `h : f = g` is an equality between morphisms in a concrete category.
-/
theorem congr_hom {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : ToType X) : f x = g x :=
  congrFun (congrArg (fun k : X ⟶ Y => (k : ToType X → ToType Y)) h) x

protected theorem congr_arg {X Y : C} (f : X ⟶ Y) {x x' : ToType X} (h : x = x') : f x = f x' :=
  congrArg (f : ToType X → ToType Y) h

theorem coe_id {X : C} : (𝟙 X : ToType X → ToType X) = id :=
  (forget _).map_id X

theorem coe_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : ToType X → ToType Z) = g ∘ f :=
  (forget _).map_comp f g

/-- Variation of `ConcreteCategory.comp_apply` that uses `forget` instead. -/
theorem comp_apply' {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (x : ToType X) :
    (forget C).map (f ≫ g) x = (forget C).map g ((forget C).map f x) := comp_apply f g x

@[deprecated (since := "2024-12-10")]
alias ConcreteCategory.congr_hom := congr_hom
@[deprecated (since := "2024-12-10")]
alias ConcreteCategory.congr_arg := congr_arg

end

/-- `HasForget₂ C D`, where `C` and `D` are both categories with forgetful functors, provides a
functor `forget₂ C D : C ⥤ D` and a proof that `forget₂ ⋙ (forget D) = forget C`.
-/
class HasForget₂ (C : Type u) (D : Type u') [Category.{v} C] [HasForget.{w} C]
  [Category.{v'} D] [HasForget.{w} D] where
  /-- A functor from `C` to `D` -/
  forget₂ : C ⥤ D
  /-- It covers the `ConcreteCategory.forget` for `C` and `D` -/
  forget_comp : forget₂ ⋙ forget D = forget C := by aesop

/-- The forgetful functor `C ⥤ D` between categories with forgetful functors for which we have an
instance `HasForget₂ C`. -/
abbrev forget₂ (C : Type u) (D : Type u') [Category.{v} C] [HasForget.{w} C]
    [Category.{v'} D] [HasForget.{w} D] [HasForget₂ C D] : C ⥤ D :=
  HasForget₂.forget₂

lemma forget₂_comp_apply
    {C : Type u} [Category.{v} C] {FC : C → C → Type*} {cC : C → Type w}
    [∀ X Y, FunLike (FC X Y) (cC X) (cC Y)]
    {D : Type u'} [Category.{v'} D] {G : D → D → Type*} {cD : D → Type w}
    [∀ X Y, FunLike (G X Y) (cD X) (cD Y)]
    [ConcreteCategory C FC] [ConcreteCategory D G]
    [HasForget₂ C D] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : cD ((forget₂ C D).obj X)) :
    ((forget₂ C D).map (f ≫ g) x) =
      (forget₂ C D).map g ((forget₂ C D).map f x) := by
  rw [Functor.map_comp, comp_apply]

instance forget₂_faithful (C : Type u) (D : Type u') [Category.{v} C] [HasForget.{w} C]
    [Category.{v'} D] [HasForget.{w} D] [HasForget₂ C D] : (forget₂ C D).Faithful :=
  HasForget₂.forget_comp.faithful_of_comp

instance InducedCategory.concreteCategory {C : Type u} {D : Type u'}
    [Category.{v'} D] [HasForget.{w} D] (f : C → D) :
      HasForget (InducedCategory D f) where
  forget := inducedFunctor f ⋙ forget D

instance InducedCategory.hasForget₂ {C : Type u} {D : Type u'} [Category.{v} D]
    [HasForget.{w} D] (f : C → D) : HasForget₂ (InducedCategory D f) D where
  forget₂ := inducedFunctor f
  forget_comp := rfl

instance FullSubcategory.concreteCategory {C : Type u} [Category.{v} C] [HasForget.{w} C]
    (Z : C → Prop) : HasForget (FullSubcategory Z) where
  forget := fullSubcategoryInclusion Z ⋙ forget C

instance FullSubcategory.hasForget₂ {C : Type u} [Category.{v} C] [HasForget.{w} C]
    (Z : C → Prop) : HasForget₂ (FullSubcategory Z) C where
  forget₂ := fullSubcategoryInclusion Z
  forget_comp := rfl

/-- In order to construct a “partially forgetting” functor, we do not need to verify functor laws;
it suffices to ensure that compositions agree with `forget₂ C D ⋙ forget D = forget C`.
-/
def HasForget₂.mk' {C : Type u} {D : Type u'} [Category.{v} C] [HasForget.{w} C]
    [Category.{v'} D] [HasForget.{w} D]
    (obj : C → D) (h_obj : ∀ X, (forget D).obj (obj X) = (forget C).obj X)
    (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y} {f : X ⟶ Y}, HEq ((forget D).map (map f)) ((forget C).map f)) :
    HasForget₂ C D where
  forget₂ := Functor.Faithful.div _ _ _ @h_obj _ @h_map
  forget_comp := by apply Functor.Faithful.div_comp

/-- Composition of `HasForget₂` instances. -/
@[reducible]
def HasForget₂.trans (C : Type u) [Category.{v} C] [HasForget.{w} C]
    (D : Type u') [Category.{v'} D] [HasForget.{w} D]
    (E : Type u'') [Category.{v''} E] [HasForget.{w} E]
    [HasForget₂ C D] [HasForget₂ D E] : HasForget₂ C E where
  forget₂ := CategoryTheory.forget₂ C D ⋙ CategoryTheory.forget₂ D E
  forget_comp := by
    show (CategoryTheory.forget₂ _ D) ⋙ (CategoryTheory.forget₂ D E ⋙ CategoryTheory.forget E) = _
    simp only [HasForget₂.forget_comp]

/-- Every forgetful functor factors through the identity functor. This is not a global instance as
    it is prone to creating type class resolution loops. -/
def hasForgetToType (C : Type u) [Category.{v} C] [HasForget.{w} C] :
    HasForget₂ C (Type w) where
  forget₂ := forget C
  forget_comp := Functor.comp_id _

@[simp]
lemma NatTrans.naturality_apply {C D : Type*} [Category C] [Category D] {G : D → D → Type*}
    {cD : D → Type w} [∀ X Y, FunLike (G X Y) (cD X) (cD Y)] [ConcreteCategory D G]
    {F G : C ⥤ D} (φ : F ⟶ G) {X Y : C} (f : X ⟶ Y) (x : cD (F.obj X)) :
    φ.app Y (F.map f x) = G.map f (φ.app X x) := by
  simpa only [Functor.map_comp] using congr_fun ((forget D).congr_map (φ.naturality f)) x

end CategoryTheory
