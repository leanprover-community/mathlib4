/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison
Ported by: Scott Morrison

! This file was ported from Lean 3 source module category_theory.functor.basic
! leanprover-community/mathlib commit 8350c34a64b9bc3fc64335df8006bffcadc7baa6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.Reassoc

/-!
# Functors

Defines a functor between categories, extending a `Prefunctor` between quivers.

Introduces notation `C ⥤ D` for the type of all functors from `C` to `D`.
(Unfortunately the `⇒` arrow (`\functor`) is taken by core,
but in mathlib4 we should switch to this.)
-/


namespace CategoryTheory

-- declare the `v`'s first; see note [CategoryTheory universes].
universe v v₁ v₂ v₃ u u₁ u₂ u₃

section

/-- `Functor C D` represents a functor between categories `C` and `D`.

To apply a functor `F` to an object use `F.obj X`, and to a morphism use `F.map f`.

The axiom `map_id` expresses preservation of identities, and
`map_comp` expresses functoriality.

See <https://stacks.math.columbia.edu/tag/001B>.
-/
structure Functor (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
    extends Prefunctor C D : Type max v₁ v₂ u₁ u₂ where
  /-- A functor preserves identity morphisms. -/
  map_id : ∀ X : C, map (𝟙 X) = 𝟙 (obj X) := by aesop_cat
  /-- A functor preserves composition. -/
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g := by aesop_cat

#align category_theory.functor CategoryTheory.Functor
#align category_theory.functor.map_comp CategoryTheory.Functor.map_comp
#align category_theory.functor.map_id CategoryTheory.Functor.map_id

/-- The prefunctor between the underlying quivers. -/
add_decl_doc Functor.toPrefunctor
#align category_theory.functor.to_prefunctor CategoryTheory.Functor.toPrefunctor

/--
This unexpander will pretty print `F.obj X` properly.
Without this, we would have `Prefunctor.obj F.toPrefunctor X`.
-/
@[app_unexpander Prefunctor.obj] def
  unexpandFunctorObj : Lean.PrettyPrinter.Unexpander
  | `($_ $(F).toPrefunctor $(X)*)  => set_option hygiene false in `($(F).obj $(X)*)
  | _                           => throw ()

/--
This unexpander will pretty print `F.map f` properly.
Without this, we would have `Prefunctor.map F.toPrefunctor f`.
-/
@[app_unexpander Prefunctor.map] def
  unexpandFunctorMap : Lean.PrettyPrinter.Unexpander
  | `($_ $(F).toPrefunctor $(X)*)  => set_option hygiene false in `($(F).map $(X)*)
  | _                           => throw ()

end

/-- Notation for a functor between categories. -/
-- A functor is basically a function, so give ⥤ a similar precedence to → (25).
-- For example, `C × D ⥤ E` should parse as `(C × D) ⥤ E` not `C × (D ⥤ E)`.
infixr:26 " ⥤ " => Functor -- type as \func

attribute [simp] Functor.map_id
-- We intentionally don't add `simp` to the `reassoc` lemma,
-- which is only useful for rewriting backwards.
attribute [reassoc, simp] Functor.map_comp
#align category_theory.functor.map_comp_assoc CategoryTheory.Functor.map_comp_assoc

namespace Functor

section

variable (C : Type u₁) [Category.{v₁} C]

initialize_simps_projections Functor

-- We don't use `@[simps]` here because we want `C` implicit for the simp lemmas.
/-- `𝟭 C` is the identity functor on a category `C`. -/
protected def id : C ⥤ C where
  obj X := X
  map f := f
#align category_theory.functor.id CategoryTheory.Functor.id

/-- Notation for the identity functor on a category. -/
notation "𝟭" => Functor.id -- Type this as `\sb1`

instance : Inhabited (C ⥤ C) :=
  ⟨Functor.id C⟩

variable {C}

@[simp]
theorem id_obj (X : C) : (𝟭 C).obj X = X := rfl
#align category_theory.functor.id_obj CategoryTheory.Functor.id_obj

@[simp]
theorem id_map {X Y : C} (f : X ⟶ Y) : (𝟭 C).map f = f := rfl
#align category_theory.functor.id_map CategoryTheory.Functor.id_map

end

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- `F ⋙ G` is the composition of a functor `F` and a functor `G` (`F` first, then `G`).
-/
@[simps obj]
def comp (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)
#align category_theory.functor.comp CategoryTheory.Functor.comp
#align category_theory.functor.comp_obj CategoryTheory.Functor.comp_obj

/-- Notation for composition of functors. -/
infixr:80 " ⋙ " => comp

@[simp]
theorem comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y : C} (f : X ⟶ Y) :
  (F ⋙ G).map f = G.map (F.map f) := rfl
#align category_theory.functor.comp_map CategoryTheory.Functor.comp_map

-- These are not simp lemmas because rewriting along equalities between functors
-- is not necessarily a good idea.
-- Natural isomorphisms are also provided in `whiskering.lean`.
protected theorem comp_id (F : C ⥤ D) : F ⋙ 𝟭 D = F := by cases F; rfl
#align category_theory.functor.comp_id CategoryTheory.Functor.comp_id

protected theorem id_comp (F : C ⥤ D) : 𝟭 C ⋙ F = F := by cases F; rfl
#align category_theory.functor.id_comp CategoryTheory.Functor.id_comp

@[simp]
theorem map_dite (F : C ⥤ D) {X Y : C} {P : Prop} [Decidable P]
    (f : P → (X ⟶ Y)) (g : ¬P → (X ⟶ Y)) :
    F.map (if h : P then f h else g h) = if h : P then F.map (f h) else F.map (g h) := by
  aesop_cat
#align category_theory.functor.map_dite CategoryTheory.Functor.map_dite

-- Porting note: `to_prefunctor_obj` and `to_prefunctor_map` are now tautologies,
-- so have not been ported.

@[simp]
theorem toPrefunctor_comp (F : C ⥤ D) (G : D ⥤ E) :
    F.toPrefunctor.comp G.toPrefunctor = (F ⋙ G).toPrefunctor := rfl
#align category_theory.functor.to_prefunctor_comp CategoryTheory.Functor.toPrefunctor_comp

end

end Functor

end CategoryTheory
