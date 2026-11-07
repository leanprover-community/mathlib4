-- A leaf module for the `unneededImport` linter tests: it declares one constant and imports
-- nothing from Mathlib, so its import closure is under the control of these tests.
module

public section

/-! # A leaf module with a single constant -/

/-- A constant that a scenario file uses to mark this module as needed. -/
def MathlibTest.UnneededImport.leafValue : Nat := 37
