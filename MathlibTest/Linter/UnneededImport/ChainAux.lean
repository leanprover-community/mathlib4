-- A module whose import closure covers `LeafAux`, so a scenario file can import both and
-- exercise the coverage of one direct import by another.
module

public import MathlibTest.Linter.UnneededImport.LeafAux

public section

/-! # A module that imports the leaf module -/

/-- A constant of this module, distinct from the constant of the leaf module. -/
def MathlibTest.UnneededImport.chainValue : Nat := MathlibTest.UnneededImport.leafValue + 1
