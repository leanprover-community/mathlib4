module
public import Mathlib.Tactic.Linter.ForbiddenExposedHead
public import Batteries.Tactic.Lint.Frontend
public import Mathlib.Logic.Nonempty

/-- A docstring -/
@[expose] public noncomputable def anExposedDef : Nat := Classical.choice inferInstance
/-- A docstring -/
public noncomputable def aNonExposedDef : Nat := Classical.choice inferInstance
/-- A docstring -/
noncomputable def aPrivateNonExposedDef : Nat := Classical.choice inferInstance

@[expose] public noncomputable def anotherExposedDef : Nat := Nonempty.some inferInstance

/--
error: -- Found 3 errors in 3 declarations (plus 2 automatically generated ones) in the current file with 14 linters

/- The `docBlame` linter reports:
DEFINITIONS ARE MISSING DOCUMENTATION STRINGS:
This linter can be disabled with `@[nolint docBlame]`. -/
#check anotherExposedDef /- definition missing documentation string -/

/- The `forbiddenExposed` linter reports:
FOUND exposed definitions with a forbidden head symbol
This linter can be disabled with `@[nolint forbiddenExposed]`. -/
#check anExposedDef /- The definition `anExposedDef` is exposed and has
        `Classical.choice` as head symbol of its body. Please mark this definition with `@[no_expose]` or move it in a non-exposed section
        and provide specification lemmas for this definition. -/
#check anotherExposedDef /- The definition `anotherExposedDef` is exposed and has
        `Nonempty.some` as head symbol of its body. Please mark this definition with `@[no_expose]` or move it in a non-exposed section
        and provide specification lemmas for this definition. -/
-/
#guard_msgs in
#lint
