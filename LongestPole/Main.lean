/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import ImportGraph.CurrentModule
import ImportGraph.Imports
import Mathlib.Data.String.Defs
import Mathlib.Util.FormatTable
import Cli
import LongestPole.RadarJson

/-!
# `lake exe pole`

Longest pole analysis for Mathlib build times.
-/


open Cli
open Lean Meta

/-- Runs a terminal command and retrieves its output -/
def runCmd (cmd : String) (args : Array String) (throwFailure := true) : IO String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  if out.exitCode != 0 && throwFailure then throw <| IO.userError out.stderr
  else return out.stdout

def runCurl (args : Array String) (throwFailure := true) : IO String := do
  runCmd "curl" args throwFailure

namespace RadarAPI

def getRunInfoJson (chash : String) (repo : String := "mathlib4") : IO String :=
  runCurl #[s!"https://radar.lean-lang.org/api/compare/{repo}/parent/{chash}/"]

def getRunInfo (chash : String) : IO JsonGet := do
  let r ← getRunInfoJson chash
  let j ← match Json.parse r with
  | .error e => throw <| IO.userError s!"Could not parse radar JSON: {e}\n{r}"
  | .ok j => pure j
  match fromJson? j with
  | .error e => throw <| IO.userError s!"Could not parse radar JSON: {e}\n{j}"
  | .ok v => pure v

def JsonGet.instructions (info : JsonGet) : NameMap Float := Id.run do
  let mut r : NameMap Float := ∅
  for comparison in info.comparison.metrics do
    let module := some comparison.metric
      |>.bind (·.dropPrefix? "build/module/") |>.map (·.toString)
      |>.bind (·.dropSuffix? "//instructions") |>.map (·.toName)
    if let some m := module then
      if let some v := comparison.second then
        r := r.insert m (v / 10 ^ 6)
  return r

def instructions (chash : String) : IO (NameMap Float) :=
  return (← getRunInfo chash).instructions

end RadarAPI

def headSha : IO String := return (← runCmd "git" #["rev-parse", "HEAD"]).trim

/-- Given `NameMap`s indicating how many instructions are in each file and which files are imported
by which others, returns a new `NameMap` of the cumulative instructions taken in the longest pole
of imports including that file. -/
partial def cumulativeInstructions (instructions : NameMap Float) (graph : NameMap (Array Name)) :
    NameMap Float :=
  graph.foldl (init := ∅) fun m n _ => go n m
where
  -- Helper which adds the entry for `n` to `m` if it's not already there.
  go (n : Name) (m : NameMap Float) : NameMap Float :=
    if m.contains n then
      m
    else
      let parents := graph.get! n
      -- Add all parents to the map first
      let m := parents.foldr (init := m) fun parent m => go parent m
      -- Determine the maximum cumulative instruction count among the parents
      let t := (parents.map fun parent => m.get! parent).foldr max 0
      m.insert n (instructions.getD n 0 + t)

/-- Given `NameMap`s indicating how many instructions are in each file and which files are imported
by which others, returns a new `NameMap` indicating the last of the parents of each file that would
be built in a totally parallel setting. -/
def slowestParents (cumulative : NameMap Float) (graph : NameMap (Array Name)) :
    NameMap Name :=
  graph.foldl (init := ∅) fun m n parents =>
    match parents.toList with
    -- If there are no parents, return the file itself
    | [] => m
    | h :: t => Id.run do
      let mut slowestParent := h
      for parent in t do
        if cumulative.get! parent > cumulative.get! slowestParent then
          slowestParent := parent
      return m.insert n slowestParent

/-- Given `NameMap`s indicating how many instructions are in each file and which files are imported
by which others, returns a new `NameMap` indicating the total instructions taken to compile the
file, including all instructions in transitively imported files.
-/
def totalInstructions (instructions : NameMap Float) (graph : NameMap (Array Name)) :
    NameMap Float :=
  let transitive := graph.transitiveClosure
  transitive.filterMap
    fun n s => some <| s.foldl (init := instructions.getD n 0)
      fun t n' => t + (instructions.getD n' 0)

/-- Convert a float to a string with a fixed number of decimal places. -/
def Float.toStringDecimals (r : Float) (digits : Nat) : String :=
  match r.toString.splitToList (· = '.') with
  | [a, b] => a ++ "." ++ b.take digits
  | _ => r.toString

open System in
-- Lines of code is obviously a `Nat` not a `Float`,
-- but we're using it here as a very rough proxy for instruction count.
def countLOC (modules : List Name) : IO (NameMap Float) := do
  let mut r := {}
  for m in modules do
    if let some fp ← Lean.SearchPath.findModuleWithExt [s!".{FilePath.pathSeparator}"] "lean" m
    then
      let src ← IO.FS.readFile fp
      r := r.insert m (src.toList.count '\n').toFloat
  return r

/-- Implementation of the longest pole command line program. -/
def longestPoleCLI (args : Cli.Parsed) : IO UInt32 := do
  let to ← match args.flag? "to" with
  | some to => pure <| to.as! ModuleName
  | none => ImportGraph.getCurrentModule -- autodetect the main module from the `lakefile.lean`
  searchPathRef.set (← addSearchPathFromEnv (← getBuiltinSearchPath (← findSysroot)))
  -- It may be reasonable to remove this again after https://github.com/leanprover/lean4/pull/6325
  unsafe enableInitializersExecution
  unsafe withImportModules #[{module := to}] {} (trustLevel := 1024) fun env => do
    let graph := env.importGraph
    let sha ← headSha
    IO.eprintln s!"Analyzing {to} at {sha}"
    let instructions ← if args.hasFlag "loc" then
      countLOC (graph.toList.map (·.1))
    else
      RadarAPI.instructions sha
    let cumulative := cumulativeInstructions instructions graph
    let total := totalInstructions instructions graph
    let slowest := slowestParents cumulative graph
    let mut table := #[]
    let mut n := some to
    while hn : n.isSome do
      let n' := n.get hn
      let i := instructions.getD n' 0
      let c := cumulative.get! n'
      let t := total.get! n'
      let r := (t / c).toStringDecimals 2
      table := table.push #[n.get!.toString, toString i.toUInt64, toString c.toUInt64, r]
      n := slowest.find? n'
    let instructionsHeader := if args.hasFlag "loc" then "LoC" else "instructions"
    IO.println (formatTable
                  #["file", instructionsHeader, "cumulative", "parallelism"]
                  table
                  #[Alignment.left, Alignment.right, Alignment.right, Alignment.center])
  return 0

/-- Setting up command line options and help text for `lake exe pole`. -/
def pole : Cmd := `[Cli|
  pole VIA longestPoleCLI; ["0.0.1"]
  "Calculate the longest pole for building Mathlib (or downstream projects).\n\
  Use as `lake exe pole` or `lake exe pole --to MyProject.MyFile`.\n\n\
  Prints a sequence of imports starting at the target.\n\
  For each file, prints the cumulative instructions (in billions)\n\
  assuming infinite parallelism, and the speed-up factor over sequential processing."

  FLAGS:
    to : ModuleName;      "Calculate the longest pole to the specified module."
    loc;                  "Use lines of code instead of radar instruction counts."
]

/-- `lake exe pole` -/
def main (args : List String) : IO UInt32 :=
  pole.validate args
