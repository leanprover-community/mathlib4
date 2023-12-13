/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Util.Imports
import Mathlib.Lean.CoreM
import Mathlib.Lean.Data.NameMap
import Mathlib.Lean.IO.Process
import Mathlib.Lean.Name
import Std.Lean.Util.Path
import Cli

/-!
# `lake exe graph`

This is a replacement for Lean 3's `leanproject import-graph` tool.
-/

open Cli

open Lean Meta

/-- Write an import graph, represented as a `NameMap (Array Name)` to the ".dot" graph format. -/
def asDotGraph (graph : NameMap (Array Name)) (header := "import_graph") : String := Id.run do
  let mut lines := #[s!"digraph \"{header}\" " ++ "{"]
  for (n, is) in graph do
    for i in is do
      lines := lines.push s!"  \"{i}\" -> \"{n}\";"
  lines := lines.push "}"
  return "\n".intercalate lines.toList

open Lean Core System

open IO.FS IO.Process Name in
/-- Implementation of the import graph command line program. -/
def importGraphCLI (args : Cli.Parsed) : IO UInt32 := do
  let to := match args.flag? "to" with
  | some to => to.as! ModuleName
  | none => `Mathlib -- autodetect the main module from the `lakefile.lean`?
  let from? := match args.flag? "from" with
  | some fr => some <| fr.as! ModuleName
  | none => none
  searchPathRef.set compile_time_search_path%
  let dotFile ← unsafe withImportModules #[{module := to}] {} (trustLevel := 1024) fun env => do
    let mut graph := env.importGraph
    if let .some f := from? then
      graph := graph.downstreamOf (NameSet.empty.insert f)
    if ¬(args.hasFlag "include-deps") then
      let p := getModule to
      graph := graph.filterMap (fun n i =>
        if p.isPrefixOf n then (i.filter (isPrefixOf p)) else none)
    if args.hasFlag "exclude-meta" then
      let filterMeta : Name → Bool := fun n => (
        isPrefixOf `Mathlib.Tactic n ∨
        isPrefixOf `Mathlib.Lean n ∨
        isPrefixOf `Mathlib.Mathport n ∨
        isPrefixOf `Mathlib.Util n)
      graph := graph.filterGraph filterMeta (replacement := `«Mathlib.Tactics»)
    if args.hasFlag "reduce" then
      graph := graph.transitiveReduction
    return asDotGraph graph
  match args.variableArgsAs! String with
  | #[] => writeFile "import_graph.dot" dotFile
  | outputs => for o in outputs do
     let fp : FilePath := o
     match fp.extension with
     | none
     | "dot" => writeFile fp dotFile
     | some ext => try
        _ ← runCmdWithInput "dot" #["-T" ++ ext, "-o", o] dotFile
      catch ex =>
        IO.eprintln s!"Error occurred while writing out {fp}."
        IO.eprintln s!"Make sure you have `graphviz` installed and the file is writable."
        throw ex
  return 0

/-- Setting up command line options and help text for `lake exe graph`. -/
def graph : Cmd := `[Cli|
  graph VIA importGraphCLI; ["0.0.1"]
  "Generate representations of a Lean import graph." ++
  "By default generates the import graph up to `Mathlib`." ++
  "If you are working in a downstream project, use `lake exe graph --to MyProject`."

  FLAGS:
    reduce;               "Remove transitively redundant edges."
    to : ModuleName;      "Only show the upstream imports of the specified module."
    "from" : ModuleName;  "Only show the downstream dependencies of the specified module."
    "exclude-meta";       "Exclude any files starting with `Mathlib.[Tactic|Lean|Util|Mathport]`."
    "include-deps";       "Include used files from other projects (e.g. lake packages)"

  ARGS:
    ...outputs : String;  "Filename(s) for the output. " ++
      "If none are specified, generates `import_graph.dot`. " ++
      "Automatically chooses the format based on the file extension. " ++
      "Currently `.dot` is supported, " ++
      "and if you have `graphviz` installed then any supported output format is allowed."
]

/-- `lake exe graph` -/
def main (args : List String) : IO UInt32 :=
  graph.validate args
