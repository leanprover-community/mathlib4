import Mathlib.Tactic.Linter.EllipsisPlaceholders

set_option linter.style.ellipsisPlaceholders true
set_option linter.unusedVariables false
-- Unit tests use a lower threshold than the default (`4`).
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2

/-!
Smoke-test the linter on patterns resembling real mathlib code (e.g. `Foo.bar _ _ _`).
-/

def mathlibStyleThree {α β γ : Type u} (_x : α) (_y : β) (_z : γ) : Nat := 0
def mathlibStyleWithMid {α β γ : Type u} (x : α) (y : β) (_z : γ) : α := x
def fourArg (a : Nat) (b : Nat) (c : Nat) (d : Nat) : Nat := a + b + c + d

-- Real mathlib pattern: three implicit type args as trailing holes
/--
warning: Replace 3 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
#check mathlibStyleThree _ _ _

-- Middle hole: greedy `..` would change meaning
#guard_msgs(drop warning, drop info) in
#check mathlibStyleWithMid _ 0 _

#guard_msgs(drop warning, drop info) in
#check mathlibStyleThree 0 _ 0

-- Named arg before trailing holes (common in mathlib)
/--
warning: Replace 2 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
#check fourArg 1 (b := 2) _ _
