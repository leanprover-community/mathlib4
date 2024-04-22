/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import ImportGraph
import Mathlib.Data.String.Defs
import Std.Lean.Util.Path
import Cli

/-!
# `lake exe pole`

Longest pole analysis for Mathlib build times.
-/

set_option autoImplicit true

open Cli

open Lean Meta

open Lean Core System

/-- Runs a terminal command and retrieves its output -/
def runCmd (cmd : String) (args : Array String) (throwFailure := true) : IO String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  if out.exitCode != 0 && throwFailure then throw $ IO.userError out.stderr
  else return out.stdout

def runCurl (args : Array String) (throwFailure := true) : IO String := do
  runCmd "curl" args throwFailure

def SpeedCenterAPI.RunJson (hash : String) : IO String :=
  -- e7b27246-a3e6-496a-b552-ff4b45c7236e is the `repo_id` for the `mathlib4` repository.
  runCurl #["http://speed.lean-fro.org/mathlib4/api/run/e7b27246-a3e6-496a-b552-ff4b45c7236e?hash=" ++ hash]

structure SpeedCenterAPI.CommitSource where
  repo_id : String
  hash : String
deriving ToJson, FromJson

structure SpeedCenterAPI.Source where
  source : SpeedCenterAPI.CommitSource
deriving ToJson, FromJson

structure SpeedCenterAPI.Dimension where
  benchmark : String
  metric : String
  unit : String
deriving ToJson, FromJson

structure SpeedCenterAPI.Measurement where
  dimension : SpeedCenterAPI.Dimension
  value : Float
deriving ToJson, FromJson

structure SpeedCenterAPI.Result where
  measurements : List SpeedCenterAPI.Measurement
deriving ToJson, FromJson

structure SpeedCenterAPI.Run where
  id : String
  source : SpeedCenterAPI.Source
  result : SpeedCenterAPI.Result
deriving ToJson, FromJson

structure SpeedCenterAPI.RunResponse where
  run : SpeedCenterAPI.Run
deriving ToJson, FromJson

structure SpeedCenterAPI.Message where
  repo_id : String
  message : String
  commit_hash : String
deriving ToJson, FromJson

def SpeedCenterAPI.RunResponse.instructions (response : SpeedCenterAPI.RunResponse) :
    NameMap Float := Id.run do
  let mut r : NameMap Float := ∅
  for m in response.run.result.measurements do
    let n := m.dimension.benchmark
    if n.startsWith "~" then
      r := r.insert (n.drop 1).toName m.value
  return r

def SpeedCenterAPI.getRunResponse (hash : String) : IO SpeedCenterAPI.RunResponse := do
  let r ← SpeedCenterAPI.RunJson hash
  match Json.parse r with
  | .error e => throw <| IO.userError s!"Could not parse speed center JSON: {e}\n{r}"
  | .ok j => match fromJson? j with
    | .ok v => pure v
    | .error e => match fromJson? j with
      | .ok (v : SpeedCenterAPI.Message) =>
        IO.eprintln s!"http://speed.lean-fro.org says: {v.message}"
        IO.eprintln s!"Try moving to an older commit?"
        IO.Process.exit 1
      | .error _ => throw <| IO.userError s!"Could not parse speed center JSON: {e}\n{j}"

def headSha : IO String := return (← runCmd "git" #["rev-parse", "HEAD"]).trim

def SpeedCenterAPI.Instructions (run : String) : IO (NameMap Float) :=
  return (← SpeedCenterAPI.getRunResponse run).instructions

partial def cumulativeInstructions (instructions : NameMap Float) (graph : NameMap (Array Name)) :
    NameMap Float :=
  graph.fold (init := ∅) fun m n _ => go n m
where
  go (n : Name) (m : NameMap Float) : NameMap Float :=
    if m.contains n then
      m
    else
      let parents := graph.find! n
      let m := parents.foldr (init := m) fun n' m => go n' m
      let t := (parents.map fun n' => (m.find! n')).foldr max 0
      m.insert n ((instructions.find? n).getD 0 + t)

def slowestParents (cumulative : NameMap Float) (graph : NameMap (Array Name)) :
    NameMap Name :=
  graph.fold (init := ∅) fun m n parents =>
    match parents.toList with
    | [] => m
    | h :: t => Id.run do
      let mut r := h
      for n' in t do
        if cumulative.find! n' > cumulative.find! r then
          r := n'
      return m.insert n r

def totalInstructions (instructions : NameMap Float) (graph : NameMap (Array Name)) :
    NameMap Float :=
  let transitive := graph.transitiveClosure
  transitive.filterMap fun n s => some <| s.fold (init := (instructions.find? n).getD 0)
    fun t n' => t + ((instructions.find? n').getD 0)

/-- Convert a float to a string with a fixed number of decimal places. -/
def Float.toStringDecimals (r : Float) (digits : Nat) : String :=
  match r.toString.split (· = '.') with
  | [a, b] => a ++ "." ++ b.take digits
  | _ => r.toString

open IO.FS IO.Process Name in
/-- Implementation of the longest pole command line program. -/
def longestPoleCLI (args : Cli.Parsed) : IO UInt32 := do
  let to := match args.flag? "to" with
  | some to => to.as! ModuleName
  | none => `Mathlib -- autodetect the main module from the `lakefile.lean`?
  let sha := headSha
  searchPathRef.set compile_time_search_path%
  let _ ← unsafe withImportModules #[{module := to}] {} (trustLevel := 1024) fun env => do
    let graph := env.importGraph
    IO.eprintln s!"Analyzing {to} at {<- sha}"
    let instructions ← SpeedCenterAPI.Instructions (← sha)
    let cumulative := cumulativeInstructions instructions graph
    let total := totalInstructions instructions graph
    let slowest := slowestParents cumulative graph
    let mut table := #[]
    let mut n := some to
    while n != none do
      let i := instructions.find! n.get!
      let c := cumulative.find! n.get!
      let t := total.find! n.get!
      let r := (t / c).toStringDecimals 2
      table := table.push (n.get!, i/10^6 |>.toUInt64, c/10^6 |>.toUInt64, r)
      n := slowest.find? n.get!
    let widest := table.map (·.1.toString.length) |>.toList.maximum?.getD 0
    IO.println s!"{"file".rightpad widest} | instructions | (cumulative) | parallelism"
    IO.println s!"{"".rightpad widest '-'} | ------------ | ------------ | -----------"
    for (name, inst, cumu, speedup) in table do
      IO.println s!"{name.toString.rightpad widest} | {(toString inst).leftpad 12} | {(toString cumu).leftpad 12} | x{speedup}"
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
