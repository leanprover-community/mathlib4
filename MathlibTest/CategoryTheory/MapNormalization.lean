module

public import Mathlib.Tactic.CategoryTheory.Map

open CategoryTheory

namespace Tests.MapNormalization

universe v u vD uD

variable {C : Type u} [Category.{v} C]

abbrev Arrow (x y : C) := x ⟶ y

abbrev Same {x y : C} (f g : Arrow x y) := f = g

@[map]
lemma alias_eq {x y : C} (f g : Arrow x y) (h : Same f g) : Same f g := h

example {x y : C} (f g : Arrow x y) (h : Same f g)
    {D : Type uD} [Category.{vD} D] (F : C ⥤ D) : F.map f = F.map g :=
  alias_eq_map f g h F

example {x y : C} (f g : Arrow x y) (h : Same f g)
    {D : Type uD} [Category.{vD} D] (F : C ⥤ D) : F.map f = F.map g := by
  exact (map_of% h) F

example {x y : C} (f g : Arrow x y) (h : Same f g)
    {D : Type uD} [Category.{vD} D] (F : C ⥤ D) : F.map f = F.map g := by
  rw [map_of% alias_eq]
  exact h

-- Reduction must expose binders as well as the final equality.
abbrev AllSame (x y : C) := ∀ (f g : Arrow x y), Same f g → Same f g

@[map]
lemma under_binders (x y : C) : AllSame x y := fun _ _ h => h

example {x y : C} (f g : Arrow x y) (h : Same f g)
    {D : Type uD} [Category.{vD} D] (F : C ⥤ D) : F.map f = F.map g :=
  under_binders_map x y f g h F

-- A let-bound proposition also reduces to an equality.
example {x y : C} (f g : Arrow x y) (h : let p := Same f g; p)
    {D : Type uD} [Category.{vD} D] (F : C ⥤ D) : F.map f = F.map g := by
  exact (map_of% h) F

end Tests.MapNormalization
