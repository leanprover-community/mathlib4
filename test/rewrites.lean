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
  /- Prints:
  rw [@Semigroup.mul_assoc]
  -- g * (g⁻¹ * h) = h
  rw [@mul_assoc]
  -- g * (g⁻¹ * h) = h
  rw [@mul_left_eq_self]
  -- g * g⁻¹ = 1
  rw [@mul_inv_self]
  -- 1 * h = h
  rw [@mul_right_inv]
  -- 1 * h = h
  rw [← @division_def]
  -- g / g * h = h
  rw [← @div_eq_mul_inv]
  -- g / g * h = h
  rw [← @DivInvMonoid.div_eq_mul_inv]
  -- g / g * h = h
  rw [@inv_eq_one_div]
  -- g * (1 / g) * h = h
  rw [← @mulRightEmbedding_apply]
  -- ↑(mulRightEmbedding h) (g * g⁻¹) = h
  -/
  rw [mul_inv_self]
  rw [one_mul]
