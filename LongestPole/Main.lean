/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import ImportGraph
import Mathlib.Data.String.Defs
import Mathlib.Util.FormatTable
import Batteries.Lean.Util.Path
import Cli
import LongestPole.SpeedCenterJson

/-!
# `lake exe pole`

Longest pole analysis for Mathlib build times.
-/


open Cli
open Lean Meta

/-- Runs a terminal command and retrieves its output -/
def runCmd (cmd : String) (args : Array String) (throwFailure := true) : IO String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  if out.exitCode != 0 && throwFailure then throw $ IO.userError out.stderr
  else return out.stdout

def runCurl (args : Array String) (throwFailure := true) : IO String := do
  runCmd "curl" args throwFailure

def mathlib4RepoId : String := "e7b27246-a3e6-496a-b552-ff4b45c7236e"

namespace SpeedCenterAPI

def runJson (hash : String) (repoId : String := mathlib4RepoId) : IO String :=
  runCurl #[s!"http://speed.lean-fro.org/mathlib4/api/run/{repoId}?hash={hash}"]

def getRunResponse (hash : String) : IO RunResponse := do
  let r ← runJson hash
  match Json.parse r with
  | .error e => throw <| IO.userError s!"Could not parse speed center JSON: {e}\n{r}"
  | .ok j => match fromJson? j with
    | .ok v => pure v
    | .error e => match fromJson? j with
      | .ok (v : ErrorMessage) =>
        IO.eprintln s!"http://speed.lean-fro.org says: {v.message}"
        IO.eprintln s!"Try moving to an older commit?"
        IO.Process.exit 1
      | .error _ => throw <| IO.userError s!"Could not parse speed center JSON: {e}\n{j}"

def RunResponse.instructions (response : RunResponse) :
    NameMap Float := Id.run do
  let mut r : NameMap Float := ∅
  for m in response.run.result.measurements do
    let n := m.dimension.benchmark
    if n.startsWith "~" then
      r := r.insert (n.drop 1).toName m.value
  return r

def instructions (run : String) : IO (NameMap Float) :=
  return (← getRunResponse run).instructions

end SpeedCenterAPI

def headSha : IO String := return (← runCmd "git" #["rev-parse", "HEAD"]).trim

/-- Given `NameMap`s indicating how many instructions are in each file and which files are imported
by which others, returns a new `NameMap` of the cumulative instructions taken in the longest pole
of imports including that file. -/
partial def cumulativeInstructions (instructions : NameMap Float) (graph : NameMap (Array Name)) :
    NameMap Float :=
  graph.fold (init := ∅) fun m n _ => go n m
where
  -- Helper which adds the entry for `n` to `m` if it's not already there.
  go (n : Name) (m : NameMap Float) : NameMap Float :=
    if m.contains n then
      m
    else
      let parents := graph.find! n
      -- Add all parents to the map first
      let m := parents.foldr (init := m) fun parent m => go parent m
      -- Determine the maximum cumulative instruction count among the parents
      let t := (parents.map fun parent => (m.find! parent)).foldr max 0
      m.insert n (instructions.findD n 0 + t)

/-- Given `NameMap`s indicating how many instructions are in each file and which files are imported
by which others, returns a new `NameMap` indicating the last of the parents of each file that would
be built in a totally parallel setting. -/
def slowestParents (cumulative : NameMap Float) (graph : NameMap (Array Name)) :
    NameMap Name :=
  graph.fold (init := ∅) fun m n parents =>
    match parents.toList with
    -- If there are no parents, return the file itself
    | [] => m
    | h :: t => Id.run do
      let mut slowestParent := h
      for parent in t do
        if cumulative.find! parent > cumulative.find! slowestParent then
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
    fun n s => some <| s.fold (init := instructions.findD n 0)
      fun t n' => t + (instructions.findD n' 0)

/-- Convert a float to a string with a fixed number of decimal places. -/
def Float.toStringDecimals (r : Float) (digits : Nat) : String :=
  match r.toString.split (· = '.') with
  | [a, b] => a ++ "." ++ b.take digits
  | _ => r.toString

/-- Implementation of the longest pole command line program. -/
def longestPoleCLI (args : Cli.Parsed) : IO UInt32 := do
  let to ← match args.flag? "to" with
  | some to => pure <| to.as! ModuleName
  | none => ImportGraph.getCurrentModule -- autodetect the main module from the `lakefile.lean`
  searchPathRef.set compile_time_search_path%
  unsafe withImportModules #[{module := to}] {} (trustLevel := 1024) fun env => do
    let graph := env.importGraph
    let sha ← headSha
    IO.eprintln s!"Analyzing {to} at {sha}"
    let instructions ← SpeedCenterAPI.instructions (sha)
    let cumulative := cumulativeInstructions instructions graph
    let total := totalInstructions instructions graph
    let slowest := slowestParents cumulative graph
    let mut table := #[]
    let mut n := some to
    while hn : n.isSome do
      let n' := n.get hn
      let i := instructions.findD n' 0
      let c := cumulative.find! n'
      let t := total.find! n'
      let r := (t / c).toStringDecimals 2
      table := table.push #[n.get!.toString, toString (i/10^6 |>.toUInt64), toString (c/10^6 |>.toUInt64), r]
      n := slowest.find? n'
    IO.println (formatTable
                  #["file", "instructions", "cumulative", "parallelism"]
                  table
                  #[Alignment.left, Alignment.right, Alignment.right, Alignment.center])
  return 0

/-- Setting up command line options and help text for `lake exe pole`. -/
def pole : Cmd := `[Cli|
  pole VIA longestPoleCLI; ["0.0.1"]
  "Calculate the longest pole for building Mathlib (or downstream projects).\n" ++
  "Use as `lake exe pole` or `lake exe pole --to MyProject.MyFile`.\n\n" ++
  "Prints a sequence of imports starting at the target.\n" ++
  "For each file, prints the cumulative instructions (in billions)\n" ++
  "assuming infinite parallelism, and the speed-up factor over sequential processing."

  FLAGS:
    to : ModuleName;      "Calculate the longest pole to the specified module."
]

/-- `lake exe pole` -/
def main (args : List String) : IO UInt32 :=
  pole.validate args
