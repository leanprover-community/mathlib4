/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive

/-!
# Unbundled functors, as a typeclass decorating the object-level function.
-/

@[expose] public section


namespace CategoryTheory

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v v₁ v₂ v₃ u u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

-- Perhaps in the future we could redefine `Functor` in terms of this, but that isn't the
-- immediate plan.
/-- An unbundled functor. -/
class Functorial (F : C → D) : Type max v₁ v₂ u₁ u₂ where
  /-- If `F : C → D` (just a function) has `[Functorial F]`,
  we can write `map F f : F X ⟶ F Y` for the action of `F` on a morphism `f : X ⟶ Y`. -/
  map (F) : ∀ {X Y : C}, (X ⟶ Y) → (F X ⟶ F Y)
  /-- A functorial map preserves identities. -/
  map_id : ∀ {X : C}, map (𝟙 X) = 𝟙 (F X) := by cat_disch
  /-- A functorial map preserves composition of morphisms. -/
  map_comp : ∀ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}, map (f ≫ g) = map f ≫ map g := by
    cat_disch

attribute [simp, grind =] Functorial.map_id Functorial.map_comp
export Functorial (map)

namespace Functor

/-- Bundle a functorial function as a functor.
-/
def of (F : C → D) [I : Functorial.{v₁, v₂} F] : C ⥤ D :=
  { I with obj := F
           map := Functorial.map F }

end Functor

instance (F : C ⥤ D) : Functorial.{v₁, v₂} F.obj :=
  { F with map := F.map }

@[simp, grind =]
theorem map_functorial_obj (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : map F.obj f = F.map f :=
  rfl

instance functorial_id : Functorial.{v₁, v₁} (id : C → C) where map f := f

section

variable {E : Type u₃} [Category.{v₃} E]

-- This is no longer viable as an instance in Lean 3.7,
-- #lint reports an instance loop
-- Will this be a problem?
/-- `G ∘ F` is a functorial if both `F` and `G` are.
-/
@[implicit_reducible]
def functorial_comp (F : C → D) [Functorial.{v₁, v₂} F] (G : D → E) [Functorial.{v₂, v₃} G] :
    Functorial.{v₁, v₃} (G ∘ F) :=
  { Functor.of F ⋙ Functor.of G with map := fun f => map G (map F f) }

end

end CategoryTheory
