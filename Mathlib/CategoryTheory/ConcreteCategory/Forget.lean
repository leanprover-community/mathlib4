/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johannes Hölzl, Reid Barton, Sean Leather, Yury Kudryashov
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Types.Basic

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

## Implementation notes

We are currently switching over from `HasForget` to a new class `ConcreteCategory`,
see Zulip thread: https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Concrete.20category.20class.20redesign

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

@[expose] public section

namespace CategoryTheory

universe w u

variable (C : Type*) [Category* C] {FC : outParam <| C → C → Type*} {CC : outParam <| C → Type w}
    [outParam <| ∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]

def forget : C ⥤ Type w where
  obj X := ToType X
  map f := f

instance : (forget C).Faithful where
  map_injective h := by
    ext
    exact DFunLike.coe_injective h

variable {C}

theorem forget_map_eq_coe {X Y : C} (f : X ⟶ Y) : (forget C).map f = (f : _ → _) := rfl

theorem forget_obj (X : C) : (forget C).obj X = ToType X := rfl

/-- Analogue of `congr_fun h x`,
when `h : f = g` is an equality between morphisms in a concrete category.
-/
protected theorem congr_fun {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : ToType X) : f x = g x :=
  congrFun (congrArg (fun k : X ⟶ Y => (k : ToType X → ToType Y)) h) x

/-- Analogue of `congr_arg f h`,
when `h : x = x'` is an equality between elements of objects in a concrete category.
-/
protected theorem congr_arg {X Y : C} (f : X ⟶ Y) {x x' : ToType X} (h : x = x') : f x = f x' :=
  congrArg (f : ToType X → ToType Y) h

section ForgetTwo

variable (C)

variable (D : Type*) [Category* D] {FD : outParam <| D → D → Type*}
    {CD : outParam <| D → Type w}
    [outParam <| ∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]

/-- `HasForget₂ C D`, where `C` and `D` are both concrete categories, provides a functor
`forget₂ C D : C ⥤ D` and a proof that `forget₂ ⋙ (forget D) = forget C`.
-/
class HasForget₂ where
  /-- A functor from `C` to `D` -/
  forget₂ : C ⥤ D
  /-- It covers the `HasForget.forget` for `C` and `D` -/
  forget_comp : forget₂ ⋙ forget D = forget C := by aesop

/-- The forgetful functor `C ⥤ D` between concrete categories for which we have an instance
`HasForget₂ C`. -/
abbrev forget₂ [HasForget₂ C D] : C ⥤ D :=
  HasForget₂.forget₂

variable {C D}

lemma forget₂_comp_apply [HasForget₂ C D] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : ToType <| (forget₂ C D).obj X) :
    ((forget₂ C D).map (f ≫ g) x) = (forget₂ C D).map g ((forget₂ C D).map f x) := by
  rw [Functor.map_comp, CategoryTheory.comp_apply]

instance forget₂_faithful [HasForget₂ C D] : (forget₂ C D).Faithful :=
  HasForget₂.forget_comp.faithful_of_comp

instance InducedCategory.hasForget₂ (f : C → D) : HasForget₂ (InducedCategory D f) D where
  forget₂ := inducedFunctor f
  forget_comp := rfl

instance FullSubcategory.hasForget₂ (P : ObjectProperty C) : HasForget₂ P.FullSubcategory C where
  forget₂ := P.ι
  forget_comp := rfl

/-- In order to construct a “partially forgetting” functor, we do not need to verify functor laws;
it suffices to ensure that compositions agree with `forget₂ C D ⋙ forget D = forget C`.
-/
def HasForget₂.mk' (obj : C → D) (h_obj : ∀ X, (forget D).obj (obj X) = (forget C).obj X)
    (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y} {f : X ⟶ Y}, (forget D).map (map f) ≍ (forget C).map f) :
    HasForget₂ C D where
  forget₂ := Functor.Faithful.div _ _ _ @h_obj _ @h_map
  forget_comp := by apply Functor.Faithful.div_comp

/-- Composition of `HasForget₂` instances. -/
@[reducible]
def HasForget₂.trans (E : Type*) [Category* E] {FE : outParam <| E → E → Type*}
    {CE : outParam <| E → Type w}
    [outParam <| ∀ X Y, FunLike (FE X Y) (CE X) (CE Y)] [ConcreteCategory.{w} E FE]
    [HasForget₂ C D] [HasForget₂ D E] : HasForget₂ C E where
  forget₂ := CategoryTheory.forget₂ C D ⋙ CategoryTheory.forget₂ D E
  forget_comp := by
    change (CategoryTheory.forget₂ _ D) ⋙ (CategoryTheory.forget₂ D E ⋙ CategoryTheory.forget E) = _
    simp only [HasForget₂.forget_comp]

lemma ConcreteCategory.forget₂_comp_apply [HasForget₂ C D] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : ToType ((forget₂ C D).obj X)) :
    ((forget₂ C D).map (f ≫ g) x) =
      (forget₂ C D).map g ((forget₂ C D).map f x) := by
  rw [Functor.map_comp, ConcreteCategory.comp_apply]

-- end ForgetTwo

instance hom_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    IsIso (C := Type _) ⇑(ConcreteCategory.hom f) :=
  ((forget C).mapIso (asIso f)).isIso_hom

-- /-- A `FunLike` instance on plain functions, in order to instantiate a `ConcreteCategory` structure
-- on the category of types.

-- This is not an instance (yet) because that would require a lot of downstream fixes.

-- See note [reducible non-instances].
-- -/
-- abbrev
instance Types.instFunLike : ∀ X Y : Type u, FunLike (X ⟶ Y) X Y := by
  intro X Y
  exact {
    coe f := f
    coe_injective' := fun _ _ _ ↦ by assumption }

-- attribute [local instance] Types.instFunLike

-- /-- The category of types is concrete, using the identity functor.

-- This is not an instance (yet) because that would require a lot of downstream fixes.

-- See note [reducible non-instances].
-- -/
-- abbrev
instance Types.instConcreteCategory : ConcreteCategory (Type u) (fun X Y => X ⟶ Y) where
  hom f := f
  ofHom f := f
  hom_ofHom := by cat_disch
  ofHom_hom := by cat_disch
  id_apply {X} x := by
    change 𝟙 X x = _ -- ???
    simp

@[simps]
def _root_.FunLike.ofFaithful {C : Type*} [Category* C] (F : C ⥤ Type w) [F.Faithful] (X Y : C) :
    FunLike (X ⟶ Y) (F.obj X) (F.obj Y) where
  coe f := F.map f
  coe_injective' := F.map_injective

def ConcreteCategory.ofForget {C : Type*} [Category* C] (F : C ⥤ Type w) [F.Faithful] :
    letI := FunLike.ofFaithful F
    ConcreteCategory C (fun X Y ↦ X ⟶ Y) :=
  letI := FunLike.ofFaithful F
  {
    hom f := f
    ofHom f := f }

@[simp]
lemma NatTrans.naturality_apply {F G : C ⥤ D} (φ : F ⟶ G) {X Y : C} (f : X ⟶ Y)
    (x : ToType (F.obj X)) :
    φ.app Y (F.map f x) = G.map f (φ.app X x) := by
  simpa only [Functor.map_comp] using congr_fun ((forget D).congr_map (φ.naturality f)) x

-- end CategoryTheory
