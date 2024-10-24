/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import ImportGraph
import Mathlib.Util.FormatTable
import Batteries.Data.List.Basic
import LongestPole.Rectangles
import Cli

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

def countDecls (modules : Array Name) : CoreM (Array Nat) := do
  let env ← getEnv
  let mut counts := Array.mkArray modules.size 0
  for (n, _) in env.constants.map₁ do
    if ! n.isInternal then
    if let some m := env.getModuleFor? n then
      if let some i := modules.indexOf? m then
        counts := counts.modify i (· + 1)
  return counts

/-- Implementation of `lake exe unused` -/
def unusedImportsCLI (args : Cli.Parsed) : IO UInt32 := do
  let modules := (args.variableArgsAs! ModuleName).toList
  if modules.isEmpty then
    IO.eprintln
      "No modules specified, please specify at least two modules on the command line."
    return 1

  -- Should we sort the modules?
  -- The code below assumes that it is "deeper files first", as reported by `lake exe pole`.

  searchPathRef.set compile_time_search_path%
  let (unused, _) ← unsafe withImportModules #[{module := `Mathlib}] {} (trustLevel := 1024)
    fun env => Prod.fst <$> Core.CoreM.toIO
        (ctx := { fileName := "<CoreM>", fileMap := default }) (s := { env := env }) do
      let unused ← unusedTransitiveImports modules
      let counts ← countDecls modules.toArray
      return (unused, counts)

  let headings := #["#", "module"] ++ ((List.range' 1 modules.length).map toString)
  let rows := modules.mapIdx fun i m =>
    let data := (unused.lookup m).getD []
    #[toString (i + 1), m.toString] ++
      modules.map fun m' => if data.contains m' then "x" else ""
  IO.println "Writing table to unused.md."
  IO.FS.writeFile "unused.md" (formatTable headings rows.toArray)

  let data := unused.bind fun (m, u) => u.map fun n => (modules.indexOf m, modules.indexOf n)
  let rectangles := maximalRectangles data
    |>.map (fun r => (r, r.area))
    |>.mergeSort (fun r₁ r₂ => r₁.2 > r₂.2)
    |>.take 10

  for (i, (r, _)) in rectangles.enum do
    IO.println
      s!"lake exe graph --from {modules[r.top]!} --to {modules[r.right - 1]!} unused{i}.pdf"

  return 0

/-- Setting up command line options and help text for `lake exe unused`. -/
def unused : Cmd := `[Cli|
  unused VIA unusedImportsCLI; ["0.0.1"]
  "Determine unused imports amongst a given set of modules.\n\
   Produces a table with rows and columns indexed by the specified modules,\n\
   with an 'x' in row A, column B if module A imports module B,\n\
   but does not make any transitive use of constants defined in B."

  ARGS:
    ...modules : ModuleName; "Modules to check for unused imports."
]

/-- `lake exe pole` -/
def main (args : List String) : IO UInt32 :=
  unused.validate args
