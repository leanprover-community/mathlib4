import Lean
import ImportGraph.Imports
import Mathlib.Logic.Function.Defs

open Lean

def downstreamCount (importGraph : NameMap (Array Name)) (fileNames : Array Name) : Array Nat :=
  fileNames.map fun fileName ↦
    let ds := importGraph.downstreamOf {fileName}
    let downDeps : NameSet := ds.fold (init := {}) fun a _ c => a.append (.ofArray c)
    (downDeps.erase fileName).size

abbrev fils : Array Name := #[
  -- insert module names here
]

run_cmd
  dbg_trace downstreamCount (← getEnv).importGraph fils
