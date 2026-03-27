module

public import Mathlib.Tactic.CategoryTheory.Map

open CategoryTheory

@[expose] public section

namespace Tests.MapSimp

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

@[map (attr := simp)]
lemma comp_map_simp {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) :
    f ≫ g = h := w

end Tests.MapSimp
