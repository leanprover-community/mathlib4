/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johannes Hölzl, Reid Barton, Sean Leather, Yury Kudryashov, Anne Baanen, Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Types.Basic
/-!
# Forgetful functors

A concrete category is a category `C` where the objects and morphisms correspond with types and
(bundled) functions between these types, see the file
`Mathlib.CategoryTheory.ConcreteCategory.Basic`

Each concrete category `C` comes with a canonical faithful functor `forget C : C ⥤ Type*`.
We impose no restrictions on the category `C`, so `Type` has the identity forgetful functor.

We say that a concrete category `C` admits a *forgetful functor* to a concrete category `D`, if it
has a functor `forget₂ C D : C ⥤ D` such that `(forget₂ C D) ⋙ (forget D) = forget C`, see
`class HasForget₂`.  Due to `Faithful.div_comp`, it suffices to verify that `forget₂.obj` and
`forget₂.map` agree with the equality above; then `forget₂` will satisfy the functor laws
automatically, see `HasForget₂.mk'`.

We say that a concrete category `C` admits a *forgetful functor* to a concrete category `D`, if it
has a functor `forget₂ C D : C ⥤ D` such that `(forget₂ C D) ⋙ (forget D) = forget C`, see
`class HasForget₂`.  Due to `Faithful.div_comp`, it suffices to verify that `forget₂.obj` and
`forget₂.map` agree with the equality above; then `forget₂` will satisfy the functor laws
automatically, see `HasForget₂.mk'`.

## References

See [Ahrens and Lumsdaine, *Displayed Categories*][ahrens2017] for
related work.
-/

@[expose] public section

namespace CategoryTheory

universe w u

variable (C : Type*) [Category* C] {FC : outParam <| C → C → Type*} {CC : outParam <| C → Type w}
    [outParam <| ∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]

/-- The forgetful functor from a concrete category to the category of types. -/
def forget : C ⥤ Type w where
  obj X := ToType X
  map f := f

instance : (forget C).Faithful where
  map_injective h := ConcreteCategory.coe_ext h

variable {C}

@[simp]
theorem ConcreteCategory.forget_map_eq_coe {X Y : C} (f : X ⟶ Y) :
    (forget C).map f = (f : _ → _) :=
  rfl

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
  /-- It covers the `forget` for `C` and `D` -/
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


variable (C D) in
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
  rw [Functor.map_comp, CategoryTheory.comp_apply]

instance hom_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    IsIso (C := Type _) ⇑(ConcreteCategory.hom f) :=
  ((forget C).mapIso (asIso f)).isIso_hom

instance Types.instFunLike : ∀ X Y : Type u, FunLike (X ⟶ Y) X Y := by
  intro X Y
  exact {
    coe f := f
    coe_injective' := fun _ _ _ ↦ by assumption }

instance Types.instConcreteCategory : ConcreteCategory (Type u) (fun X Y => X ⟶ Y) where
  hom f := f
  ofHom f := f

@[simp]
lemma Types.hom_eq_coe {X Y : Type u} (f : X ⟶ Y) : (ConcreteCategory.hom f) = f := rfl

@[simp]
lemma NatTrans.naturality_apply {F G : C ⥤ D} (φ : F ⟶ G) {X Y : C} (f : X ⟶ Y)
    (x : ToType (F.obj X)) :
    φ.app Y (F.map f x) = G.map f (φ.app X x) := by
  simpa only [Functor.map_comp] using congr_fun ((forget D).congr_map (φ.naturality f)) x

end CategoryTheory
