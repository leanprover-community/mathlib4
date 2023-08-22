/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Functor.Basic

#align_import category_theory.functor.functorial from "leanprover-community/mathlib"@"afad8e438d03f9d89da2914aa06cb4964ba87a18"

/-!
# Unbundled functors, as a typeclass decorating the object-level function.
-/


namespace CategoryTheory

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v v₁ v₂ v₃ u u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

-- Perhaps in the future we could redefine `Functor` in terms of this, but that isn't the
-- immediate plan.
/-- An unbundled functor. -/
class Functorial (F : C → D) : Type max v₁ v₂ u₁ u₂ where
  /-- A functorial map extends to an action on morphisms. -/
  map' : ∀ {X Y : C}, (X ⟶ Y) → (F X ⟶ F Y)
  /-- A functorial map preserves identities. -/
  map_id' : ∀ X : C, map' (𝟙 X) = 𝟙 (F X) := by aesop_cat
  /-- A functorial map preserves composition of morphisms. -/
  map_comp' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map' (f ≫ g) = map' f ≫ map' g := by
    aesop_cat
#align category_theory.functorial CategoryTheory.Functorial
#align category_theory.functorial.map CategoryTheory.Functorial.map'

/-- If `F : C → D` (just a function) has `[Functorial F]`,
we can write `map F f : F X ⟶ F Y` for the action of `F` on a morphism `f : X ⟶ Y`.
-/
def map (F : C → D) [Functorial.{v₁, v₂} F] {X Y : C} (f : X ⟶ Y) : F X ⟶ F Y :=
  Functorial.map'.{v₁, v₂} f
#align category_theory.map CategoryTheory.map

@[simp]
theorem map'_as_map {F : C → D} [Functorial.{v₁, v₂} F] {X Y : C} {f : X ⟶ Y} :
    Functorial.map'.{v₁, v₂} f = map F f :=
  rfl
#align category_theory.map_as_map CategoryTheory.map'_as_map

@[simp]
theorem Functorial.map_id {F : C → D} [Functorial.{v₁, v₂} F] {X : C} : map F (𝟙 X) = 𝟙 (F X) :=
  Functorial.map_id' X
#align category_theory.functorial.map_id CategoryTheory.Functorial.map_id

@[simp]
theorem Functorial.map_comp {F : C → D} [Functorial.{v₁, v₂} F] {X Y Z : C} {f : X ⟶ Y}
    {g : Y ⟶ Z} : map F (f ≫ g) = map F f ≫ map F g :=
  Functorial.map_comp' f g
#align category_theory.functorial.map_comp CategoryTheory.Functorial.map_comp

namespace Functor

/-- Bundle a functorial function as a functor.
-/
def of (F : C → D) [I : Functorial.{v₁, v₂} F] : C ⥤ D :=
  { I with obj := F
           map := map F }
#align category_theory.functor.of CategoryTheory.Functor.of

end Functor

instance (F : C ⥤ D) : Functorial.{v₁, v₂} F.obj :=
  { F with map' := F.map }

@[simp]
theorem map_functorial_obj (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : map F.obj f = F.map f :=
  rfl
#align category_theory.map_functorial_obj CategoryTheory.map_functorial_obj

instance functorial_id : Functorial.{v₁, v₁} (id : C → C) where map' f := f
#align category_theory.functorial_id CategoryTheory.functorial_id

section

variable {E : Type u₃} [Category.{v₃} E]

-- This is no longer viable as an instance in Lean 3.7,
-- #lint reports an instance loop
-- Will this be a problem?
/-- `G ∘ F` is a functorial if both `F` and `G` are.
-/
def functorial_comp (F : C → D) [Functorial.{v₁, v₂} F] (G : D → E) [Functorial.{v₂, v₃} G] :
    Functorial.{v₁, v₃} (G ∘ F) :=
  { Functor.of F ⋙ Functor.of G with map' := fun f => map G (map F f) }
#align category_theory.functorial_comp CategoryTheory.functorial_comp

end

end CategoryTheory
