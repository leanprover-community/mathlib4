import Mathlib

/-!
Test that `exact?` now also tries all un-indexable lemmas in a second pass.
-/

/-- error: `exact?` could not close the goal. -/
#guard_msgs in
example {α : Sort u} (h : Prop) [Decidable h] {x y : α} {p : α → Prop} (hx : h → p x) (hy : ¬h → p y) :
    p (if h then x else y) := by
  exact? -star

/--
info: Try this:
  [apply] exact iteInduction hx hy
-/
#guard_msgs in
example {α : Sort u} (h : Prop) [Decidable h] {x y : α} {p : α → Prop} (hx : h → p x) (hy : ¬h → p y) :
    p (if h then x else y) := by
  exact?

/-- error: `exact?` could not close the goal. -/
#guard_msgs in
example [Subsingleton α] (x y : α) : x = y := by
  exact? -star

/--
info: Try this:
  [apply] exact of_decide_eq_true rfl
-/
#guard_msgs in
example [Subsingleton α] (x y : α) : x = y := by
  exact?
