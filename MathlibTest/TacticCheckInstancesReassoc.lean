import Mathlib.Tactic.CategoryTheory.Reassoc

set_option linter.tacticCheckInstances true

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-! reassoc on a clean lemma, no warning expected. -/

#guard_msgs in
@[reassoc]
lemma clean_lem {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    f ≫ g = h := w


/-! a semireducible alias used for `.implicit`-ill-typed equation -/

def MyHom (X Y : C) : Type v := X ⟶ Y

/--
warning: generated lemma alias_lem_assoc is not type-correct at `.implicit` transparency; consider marking some of the following as `@[implicit_reducible]`:
  Quiver.Hom
  MyHom

Note: This linter can be disabled with `set_option linter.tacticCheckInstances false`
-/
#guard_msgs in
@[reassoc]
lemma alias_lem {X Y Z : C} (f : MyHom X Y) (g : Y ⟶ Z) (h : MyHom X Z)
    (w : (f : X ⟶ Y) ≫ g = h) :
    (f : X ⟶ Y) ≫ g = h := w

/-! marking the offenders `@[implicit_reducible]` silences the warning -/

set_option allowUnsafeReducibility true
attribute [implicit_reducible] Quiver.Hom MyHom

#guard_msgs in
@[reassoc]
lemma alias_lem2 {X Y Z : C} (f : MyHom X Y) (g : Y ⟶ Z) (h : MyHom X Z)
    (w : (f : X ⟶ Y) ≫ g = h) :
    (f : X ⟶ Y) ≫ g = h := w
