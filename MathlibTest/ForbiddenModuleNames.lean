import Mathlib.Tactic.Linter.TextBased

/-!
# Unit tests for the module name compatibility checks in the text-based linter
-/

open Lean.Linter Mathlib.Linter.TextBased

/-- Some unit tests for `modulesOSForbidden` -/
def testModulesOSForbidden : IO Unit := do
  -- Explicitly enable the linter, although it is enabled by default.
  let opts : LinterOptions := {
    toOptions := linter.modulesUpperCamelCase.set {} true
    linterSets := {}
  }

  assert!((← modulesOSForbidden opts #[]) == 0)
  assert!((← modulesOSForbidden opts #[`Mathlib.Aux.Foo, `Mathlib.Algebra.Con]) == 2)
  assert!((← modulesOSForbidden opts #[`Mathlib.Foo.Bar, `Aux.Algebra.Con.Bar]) == 1)
  assert!((← modulesOSForbidden opts #[`Com1.prn.Aux, `LPT.Aux]) == 2)
  assert!((← modulesOSForbidden opts #[`Mathlib.Foo.«Foo*»]) == 1)
  assert!((← modulesOSForbidden opts #[`Mathlib.«B>ar<»]) == 1)
  assert!((← modulesOSForbidden opts #[`Mathlib.«Bar!»]) == 1)
  assert!((← modulesOSForbidden opts #[`Mathlib.«Qu<x!!»]) == 1)

/--
info: error: module name 'Mathlib.Aux.Foo' contains component '[Aux]', which is forbidden in Windows filenames.
error: module name 'Mathlib.Algebra.Con' contains component '[Con]', which is forbidden in Windows filenames.
error: module name 'Aux.Algebra.Con.Bar' contains components '[Aux, Con]', which are forbidden in Windows filenames.
error: module name 'Com1.prn.Aux' contains components '[Com1, prn, Aux]', which are forbidden in Windows filenames.
error: module name 'LPT.Aux' contains component '[Aux]', which is forbidden in Windows filenames.
error: module name 'Mathlib.Foo.«Foo*»' contains character '[*]', which is forbidden in Windows filenames.
error: module name 'Mathlib.«B>ar<»' contains characters '[>, <]', which are forbidden in Windows filenames.
error: module name 'Mathlib.Bar!' contains forbidden character '!'
error: module name 'Mathlib.«Qu<x!!»' contains forbidden character '!'
error: module name 'Mathlib.«Qu<x!!»' contains character '[<]', which is forbidden in Windows filenames.
-/
#guard_msgs in
#eval testModulesOSForbidden
