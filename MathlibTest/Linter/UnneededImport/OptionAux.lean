-- A module that declares an option. A `set_option` of that option is the only reference a
-- scenario file makes to this module.
module

public meta import Lean.Elab.Command

/-! # A module that declares an option -/

meta section

open Lean

/-- An option that the `unneededImport` linter tests set. -/
public register_option mathlibTest.unneededImportAux : Bool := {
  defValue := false
  descr := "an option that the unneededImport linter tests set"
}
