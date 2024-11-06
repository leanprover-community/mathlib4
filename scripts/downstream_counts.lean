import Lean
import ImportGraph.Imports
import Mathlib.Data.Nat.Defs

open Lean

def downstreamCount (importGraph : NameMap (Array Name)) (fileNames : Array Name) : Array Nat :=
  fileNames.map fun fileName ↦
    let ds := importGraph.downstreamOf {fileName}
    let downDeps : NameSet := ds.fold (init := {}) fun a b _c => a.insert b --append (.ofArray c)
    --dbg_trace fileName
    --dbg_trace (downDeps.erase fileName).toArray
    (downDeps.erase fileName).size

abbrev fils : Array Name := #[
  -- insert module names here
]

run_cmd
  let ig := (← getEnv).importGraph
  for f in fils do
    dbg_trace (downstreamCount ig #[f]).getD 0 0
