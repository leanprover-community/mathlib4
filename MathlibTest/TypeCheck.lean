import Mathlib.Tactic.TypeCheck

set_option linter.unusedTactic false

/-- A term where `inferType` returns `Prop`, but which does not type check. -/
elab "wrong" : term =>
  return Lean.mkApp2 (.const ``id [.zero]) (.sort .zero) (.app (.sort .zero) (.sort .zero))

/--
info: Type
---
info: Bool
---
info: Nat
---
info: Nat
---
info: Prop
---
info: Prop
---
info: Nat → Nat
---
info: List Nat
-/
#guard_msgs in
example : True := by
  type_check Nat -- Type
  type_check Bool.true -- Bool
  type_check nat_lit 1 -- Nat
  type_check (1 : Nat) -- Nat
  type_check (True :) -- Prop
  type_check ∀ x y : Nat, x = y -- Prop
  type_check fun x : Nat => 2 * x + 1 -- Nat -> Nat
  type_check [1]
  fail_if_success type_check wrong
  trivial
