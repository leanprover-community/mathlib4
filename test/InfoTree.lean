import Mathlib.Util.InfoTree

open Lean Meta

#eval declInfoTrees `Mathlib.Data.Subtype

#eval allTacticsInModule' `Mathlib.Data.Subtype

#eval do
  let types ← reflInDecl `Mathlib.Data.Subtype `Subtype.restrict_apply
  types.mapM fun t => do ppExpr t

-- #eval tactics2 `Set.exists_chain_of_le_chainHeight
