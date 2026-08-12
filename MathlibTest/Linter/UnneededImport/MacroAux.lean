-- A module that provides a command macro. The expansion names a constant of `LeafAux`, which
-- this module does not import: the use site resolves the name. A scenario file then declares
-- through the macro, so the declaration of the command, and not its syntax, uses the leaf module.
module

public section

/-! # A module that provides a declaring macro -/

/-- Declares a theorem about the `leafValue` constant of `LeafAux`. The identifiers carry no
macro scopes, so the use site resolves them. -/
macro "declare_leaf_refl" : command => do
  let name := Lean.mkIdent `MathlibTest.UnneededImport.leafValueRefl
  let leaf := Lean.mkIdent `MathlibTest.UnneededImport.leafValue
  `(theorem $name : $leaf = $leaf := rfl)
