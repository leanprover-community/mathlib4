/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Util.Imports
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

def speedCenterRunJson (run : String) : IO String :=
  runCurl #["http://speed.lean-fro.org/mathlib4/api/run/" ++ run]

def speedCenterRecentRunsJson : IO String :=
  runCurl #["http://speed.lean-fro.org/mathlib4/api/recent/runs?n=1000"]

structure SpeedCenterSource_1 where
  repo_id : String
  hash : String
deriving ToJson, FromJson

structure SpeedCenterSource_2 where
  source : SpeedCenterSource_1
deriving ToJson, FromJson

structure SpeedCenterRun_1 where
  id : String
  source : SpeedCenterSource_2
deriving ToJson, FromJson

structure SpeedCenterRun_2 where
  run : SpeedCenterRun_1
deriving ToJson, FromJson

structure SpeedCenterRuns where
  runs : List SpeedCenterRun_2
deriving ToJson, FromJson

structure SpeedCenterDimension where
  benchmark : String
  metric : String
  unit : String
deriving ToJson, FromJson

structure SpeedCenterMeasurement where
  dimension : SpeedCenterDimension
  value : Float
deriving ToJson, FromJson

structure SpeedCenterResult where
  measurements : List SpeedCenterMeasurement
deriving ToJson, FromJson

structure SpeedCenterRun_3 where
  id : String
  source : SpeedCenterSource_2
  result : SpeedCenterResult
deriving ToJson, FromJson

structure SpeedCenterRunResponse where
  run : SpeedCenterRun_3
deriving ToJson, FromJson

def SpeedCenterRunResponse.instructions (response : SpeedCenterRunResponse) :
    NameMap Float := Id.run do
  let mut r : NameMap Float := ∅
  for m in response.run.result.measurements do
    let n := m.dimension.benchmark
    if n.startsWith "~" then
      r := r.insert (n.drop 1).toName m.value
  return r

def speedCenterRunResponse (run : String) : IO SpeedCenterRunResponse := do
  let r ← speedCenterRunJson run
  match Json.parse r with
  | .error e => throw <| IO.userError s!"Could not parse speed center JSON: {e}\n{r}"
  | .ok j => match fromJson? j with
    | .ok v => pure v
    | .error e => throw <| IO.userError s!"Could not parse speed center JSON: {e}\n{j}"

/-- Look up recent speed center runs, return as HashMap of commit shas to speed center ids. -/
def speedCenterRuns : IO (List (String × String)) := do
  let r ← speedCenterRecentRunsJson
  match Json.parse r with
  | .error e => throw <| IO.userError s!"Could not parse speed center JSON: {e}\n{r}"
  | .ok j => match fromJson? j with
    | .ok (v : SpeedCenterRuns) => return v.runs.map fun m => (m.run.source.source.hash, m.run.id)
    | .error e => throw <| IO.userError s!"Could not parse speed center JSON: {e}\n{j}"

def runForThisCommit : IO String := do
  let hash := (← runCmd "git" #["rev-parse", "HEAD"]).trim
  let runs ← speedCenterRuns
  match runs.find? (·.1 = hash) with
  | none =>
    let table := "\n".intercalate <| runs.take 10 |>.map fun r => r.1 ++ " " ++ r.2
    IO.eprintln s!"Could not find speed center run for commit {hash}."
    IO.eprintln "Try one of these commits?"
    IO.eprintln table
    IO.Process.exit 1
  | some (_, r) => return r

def speedCenterInstructions (run : String) : IO (NameMap Float) :=
  return (← speedCenterRunResponse run).instructions

partial def cumulativeInstructions (instructions : NameMap Float) (graph : NameMap (Array Name)) :
    NameMap Float :=
  graph.fold (init := ∅) fun m n _ => go n m
where
  go (n : Name) (m : NameMap Float) : NameMap Float :=
    if m.contains n then
      m
    else
      let parents := (graph.find? n).getD #[]
      let m := parents.foldr (init := m) fun n' m => go n' m
      let t := (parents.map fun n' => (m.find? n').getD 0).foldr max 0
      m.insert n ((instructions.find? n).getD 0 + t)

def slowestParents (cumulative : NameMap Float) (graph : NameMap (Array Name)) :
    NameMap Name :=
  graph.fold (init := ∅) fun m n parents =>
    match parents.toList with
    | [] => m
    | h :: t => Id.run do
      let mut r := h
      for n' in t do
        if (cumulative.find? n').getD 0 > (cumulative.find? r).getD 0 then
          r := n'
      return m.insert n r

open IO.FS IO.Process Name in
/-- Implementation of the longest pole command line program. -/
def longestPoleCLI (args : Cli.Parsed) : IO UInt32 := do
  let to := match args.flag? "to" with
  | some to => to.as! ModuleName
  | none => `Mathlib -- autodetect the main module from the `lakefile.lean`?
  searchPathRef.set compile_time_search_path%
  let _ ← unsafe withImportModules #[{module := to}] {} (trustLevel := 1024) fun env => do
    let graph := env.importGraph
    let instructions ← speedCenterInstructions (← runForThisCommit)
    let cumulative := cumulativeInstructions instructions graph
    let slowest := slowestParents cumulative graph
    let mut n := some to
    while n != none do
      IO.println s!"{n.get!} {(cumulative.find! n.get!)/10^9 |>.toUInt64}"
      n := slowest.find? n.get!
    return graph
  return 0

/-- Setting up command line options and help text for `lake exe pole`. -/
def pole : Cmd := `[Cli|
  pole VIA longestPoleCLI; ["0.0.1"]
  "Calculate the longest pole for building Mathlib (or downstream projects)." ++
  "Use as `lake exe pole` or `lake exe pole --to MyProject.MyFile`." ++
  "Reports cumulative instructions (in billions) assuming infinite parallelism."

  FLAGS:
    to : ModuleName;      "Calculate the longest pole to the specified module."
]

/-- `lake exe pole` -/
def main (args : List String) : IO UInt32 :=
  pole.validate args
