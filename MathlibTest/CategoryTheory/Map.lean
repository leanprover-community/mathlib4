module

public import Mathlib.Tactic.CategoryTheory.Map

open CategoryTheory

namespace Tests.Map

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

@[map]
lemma comp_map {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) :
    f ≫ g = h := w

/--
info: Tests.Map.comp_map_map.{u✝, v✝, u_1, u_2} {C : Type u_1} [Category.{u_2, u_1} C] {x y z : C} (f : x ⟶ y) (g : y ⟶ z)
  (h : x ⟶ z) (w : f ≫ g = h) {D : Type u✝} [instD : Category.{v✝, u✝} D] (F : C ⥤ D) : F.map f ≫ F.map g = F.map h
-/
#guard_msgs in
#check comp_map_map

/-!
`map_of%` pushes `Functor.map` through an equality and applies `simp only [Functor.map_comp]` on each
side.
-/
example {x y z : C} {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z)
    (w : f ≫ g = h) : F.map f ≫ F.map g = F.map h := by
  exact (map_of% w) F

end Tests.Map
