import Mathlib.Util.Frontend
import Mathlib.Util.InfoTree.ToJson
import Cli

open Lean Elab IO Meta
open Cli System

/-- A custom command-line argument parser that allows either relative paths to Lean files,
(e.g. `Mathlib/Topology/Basic.lean`) or the module name (e.g. `Mathlib.Topology.Basic`). -/
instance : ParseableType Name where
  name     := "Name"
  parse? s :=
    if s.endsWith ".lean" then
      some <| (s : FilePath).withExtension "" |>.components.foldl Name.mkStr Name.anonymous
    else
      String.toName s

-- Next two declarations borrowed from `runLinter.lean`.
instance : ToExpr FilePath where
  toTypeExpr := mkConst ``FilePath
  toExpr path := mkApp (mkConst ``FilePath.mk) (toExpr path.1)

elab "compileTimeSearchPath" : term =>
  return toExpr (← searchPathRef.get)

structure InfoTreeExport where
  name : Name
  trees : List Json
deriving ToJson

def exportInfoTree (args : Cli.Parsed) : IO UInt32 := do
    searchPathRef.set compileTimeSearchPath
    let target := args.positionalArg! "module" |>.as! Name
    let (_, _, trees) ← compileModule target
    let mut trees := trees
    if args.hasFlag "tactics" then
      trees := (trees.map InfoTree.retainTacticInfo).join
    if args.hasFlag "original" then
      trees := (trees.map InfoTree.retainOriginal).join
    if args.hasFlag "substantive" then
      trees := (trees.map InfoTree.retainSubstantive).join
    let json ← trees.mapM fun t => t.toJson none
    IO.println <| toJson <| InfoTreeExport.mk target json
    return 0


/-- Setting up command line options and help text for `lake exe export_infotree`. -/
def export_infotree : Cmd := `[Cli|
  export_infotree VIA exportInfoTree; ["0.0.1"]
  "Export the InfoTrees for a file as JSON."

  FLAGS:
    "tactics";      "Only export TacticInfo nodes."
    "original";     "Skip nodes with synthetic syntax."
    "substantive";  "Skip tactic combinators."

  ARGS:
    module : Name; "Lean module to compile and export InfoTrees."
]

/-- `lake exe export_infotree` -/
def main (args : List String) : IO UInt32 :=
  export_infotree.validate args

-- To run on all of Mathlib:
-- IFS=$'\n'; for line in `cat Mathlib.lean`; do mod=${line#import }; echo $mod; time lake exe export_infotree $mod --tactics --original --substantive > $mod.json; done
