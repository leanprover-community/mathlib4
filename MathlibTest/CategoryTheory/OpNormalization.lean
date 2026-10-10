module

public import Mathlib.Tactic.CategoryTheory.Op

open CategoryTheory

namespace Tests.OpNormalization

universe v u

variable {C : Type u} [Category.{v} C]

abbrev Arrow (x y : C) := x ⟶ y

abbrev Same {x y : C} (f g : Arrow x y) := f = g

@[op]
lemma alias_eq {x y : C} (f g : Arrow x y) (h : Same f g) : Same f g := h

example {x y : C} (f g : Arrow x y) (h : Same f g) : f.op = g.op :=
  alias_eq_op f g h

example {x y : C} (f g : Arrow x y) (h : Same f g) : f.op = g.op := by
  exact op_of% h

example {x y : C} (f g : Arrow x y) (h : Same f g) : f.op = g.op := by
  rw [op_of% alias_eq]
  exact h

-- Reduction must expose binders as well as the final equality.
abbrev AllSame (x y : C) := ∀ (f g : Arrow x y), Same f g → Same f g

@[op]
lemma under_binders (x y : C) : AllSame x y := fun _ _ h => h

example {x y : C} (f g : Arrow x y) (h : Same f g) : f.op = g.op :=
  under_binders_op x y f g h

-- A let-bound proposition also reduces to an equality.
example {x y : C} (f g : Arrow x y) (h : let p := Same f g; p) : f.op = g.op := by
  exact op_of% h

end Tests.OpNormalization
