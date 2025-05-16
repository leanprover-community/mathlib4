import Mathlib.Tactic.Linter.TextBased

/-!
Unit tests for the module name case check in the text-based linters.
-/

open Mathlib.Linter.TextBased

/-- Some unit tests for `modulesNotUpperCamelCase` -/
def testModulesNotUpperCamelCase : IO Unit := do
  assert!((← modulesNotUpperCamelCase #[]) == 0)
  assert!((← modulesNotUpperCamelCase #[`Mathlib.Fine]) == 0)
  assert!((← modulesNotUpperCamelCase #[`Mathlib.AlsoFine_]) == 0)
  assert!((← modulesNotUpperCamelCase #[`Mathlib.NotFine_.Foo]) == 1)

  assert!((← modulesNotUpperCamelCase #[`bad_module]) == 1)
  assert!((← modulesNotUpperCamelCase #[`GoodName, `bad_module, `bad_module]) == 2)
  assert!((← modulesNotUpperCamelCase #[`Mathlib.BadModule__]) == 1)
  assert!((← modulesNotUpperCamelCase #[`Mathlib.lowerCase]) == 1)
  assert!((← modulesNotUpperCamelCase #[`Mathlib.snake_case]) == 1)

/--
info: error: module name 'Mathlib.NotFine_.Foo' is not in 'UpperCamelCase': it should be 'Mathlib.NotFine.Foo' instead
error: module name 'bad_module' is not in 'UpperCamelCase': it should be 'BadModule' instead
error: module name 'bad_module' is not in 'UpperCamelCase': it should be 'BadModule' instead
error: module name 'bad_module' is not in 'UpperCamelCase': it should be 'BadModule' instead
error: module name 'Mathlib.BadModule__' is not in 'UpperCamelCase': it should be 'Mathlib.BadModule_' instead
error: module name 'Mathlib.lowerCase' is not in 'UpperCamelCase': it should be 'Mathlib.LowerCase' instead
error: module name 'Mathlib.snake_case' is not in 'UpperCamelCase': it should be 'Mathlib.SnakeCase' instead
-/
#guard_msgs in
#eval testModulesNotUpperCamelCase
