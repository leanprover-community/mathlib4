module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Tactic.CategoryTheory.Map

open CategoryTheory

/-- info: CategoryTheory.homOfLE_comp_map.{u✝, v✝, u_1} {X : Type u_1} [Preorder X] {x y z : X} (h : x ≤ y) (k : y ≤ z)
  {D : Type u✝} [instD : Category.{v✝, u✝} D] (F : X ⥤ D) : F.map (homOfLE h) ≫ F.map (homOfLE k) = F.map (homOfLE ⋯) -/
#guard_msgs in
#check CategoryTheory.homOfLE_comp_map
