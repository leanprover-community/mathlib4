import Mathlib.Util.InfoTree

open Lean Meta

#eval moduleInfoTrees' `Mathlib.Data.Subtype

#eval moduleDeclInfoTrees' `Mathlib.Data.Subtype

#eval allTacticsInModule' `Mathlib.Data.Subtype

#eval reflInDecl `Mathlib.Data.Subtype `Subtype.restrict_apply


-- #eval tactics2 `Set.exists_chain_of_le_chainHeight
