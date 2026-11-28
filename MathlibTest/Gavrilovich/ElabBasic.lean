import Mathlib.Tactic.Gavrilovich.Elab.Basic

/-! Tests of the minimal diagram elaborator and delaborator
(`Mathlib.Tactic.Gavrilovich.Elab.Basic`):
one box, printed back on one row. -/

open Gavrilovich

/-- info: ⌜o → c⌟ : TopCat -/
#guard_msgs in #check ⌜o → c⌟

/-- info: ⌜a=b  c⌟ : TopCat -/
#guard_msgs in #check ⌜a=b  c⌟

/-- info: ⌜a → c ← b⌟ : TopCat -/
#guard_msgs in #check ⌜a → c ← b⌟

/-! The type of points is printed as the diagram too. -/

/-- info: fun x => x : ⌜o → c⌟ → ⌜o → c⌟ -/
#guard_msgs in #check fun x : ⌜o → c⌟ => x

/-- info: Space [["c"], ["o"]] [(1, 0)] : TopCat -/
#guard_msgs in set_option pp.gavDiagrams false in #check ⌜o → c⌟

/-! Drawings of the same space are the same term. -/

example : ⌜o → c⌟ = ⌜c ← o⌟ := rfl
example : ⌜a=b → c⌟ = ⌜b=a → c⌟ := rfl

/-! Errors. -/

/-- error: a diagram must currently be a single box (a space) -/
#guard_msgs in #check ⌜a⌟ ⇢ ⌜b⌟

/--
error: ascriptions `(=…)` are only for the boxes of a morphism, whose points are matched by the names before them
-/
#guard_msgs in #check ⌜a(=b)⌟
