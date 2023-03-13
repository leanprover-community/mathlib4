import Mathlib.Tactic.Rewrites
import Mathlib

example (f : α → β) (L M : List α) : (L ++ M).map f = L.map f ++ M.map f := by
  rewrites!

open CategoryTheory

example [Category C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ 𝟙 _ ≫ g = f ≫ g := by
  rewrites!

example [Group G] (h : G) : 1 * h = h := by
  rewrites!

example [Group G] (g h : G) : g * g⁻¹ * h = h := by
  rewrites -- the right answer is not the first solution, so we can't use rewrites!
  rw [mul_inv_self]
  rw [one_mul]
