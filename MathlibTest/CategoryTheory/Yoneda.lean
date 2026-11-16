module

import Mathlib.CategoryTheory.Yoneda

/-!
# Tests for the unification hints of `Mathlib/CategoryTheory/Yoneda.lean`

When a unification hint is declared, Lean only checks that its two sides unify, which they may do by
identifying the objects of the hint (lean4#8982). Each hint is checked here as a proposition: with
its constraints solved by `X' := X` and `Y' := Y`, its two sides are definitionally equal.
-/

open CategoryTheory

variable {C : Type*} [Category* C]

example (X Y : C) : yoneda_obj_obj_eq_hom X X Y Y := fun _ _ ↦ rfl
example (X : C) (Y : Cᵒᵖ) : yoneda_obj_obj_eq_hom' X X Y Y := fun _ _ ↦ rfl
example (X Y : C) : uliftYoneda_obj_obj_eq_hom X X Y Y := fun _ _ ↦ rfl
example (X : C) (Y : Cᵒᵖ) : uliftYoneda_obj_obj_eq_hom' X X Y Y := fun _ _ ↦ rfl
example (X Y : C) : coyoneda_obj_obj_eq_hom X X Y Y := fun _ _ ↦ rfl
example (X : C) (Y : Cᵒᵖ) : coyoneda_obj_obj_eq_hom' X X Y Y := fun _ _ ↦ rfl
example (X Y : C) : uliftCoyoneda_obj_obj_eq_hom X X Y Y := fun _ _ ↦ rfl
example (X : Cᵒᵖ) (Y : C) : uliftCoyoneda_obj_obj_eq_hom' X X Y Y := fun _ _ ↦ rfl
