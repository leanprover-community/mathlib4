/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Cli
import Batteries.Data.List.Basic
import ImportGraph.Imports
import LongestPole.Rectangles
import Mathlib.Util.FormatTable

/-!
# `lake exe unused`

A tool for library-scale analysis of unused imports.

`lake exe unused module_1 module_2 ... module_n` will generate a markdown table with rows and
columns indexed 1 through n, with an `x` in `(i, j)` if `module_i` transitively imports `module_j`,
but makes no direct use of the declarations there.

(This is often an indication that some *intermediate* file `module_k` could be split into two parts,
one that needs `module_j`, and another that is needed by `module_i`, thereby removing the transitive
import of `module_j` into `module_i`.)

The tool further identifies large rectangles of `x`s in this table, and suggests `lake exe graph`
commands that can show the dependency structure from the unused import up to the earliest file which
"unnecessarily" transitively imports it.

`scripts/unused_in_pole.sh module` (or no argument for all of Mathlib), will calculate the current
longest pole in Mathlib (note for this you need to be on a commit on which the speed center has
run), and then feed that list of modules into `lake exe unused`.

Demo video at https://youtu.be/PVj_FHGwhUI
-/


open Cli

open Lean Name

def Core.withImportModules (modules : Array Name) {α} (f : CoreM α) : IO α := do
  unsafe Lean.withImportModules (modules.map (fun m => {module := m})) {} (trustLevel := 1024)
    fun env => Prod.fst <$> Core.CoreM.toIO
        (ctx := { fileName := "<CoreM>", fileMap := default }) (s := { env := env }) do f

/-- Implementation of `lake exe unused` -/
def unusedImportsCLI (args : Cli.Parsed) : IO UInt32 := do
  let output := args.flag! "output" |>.as! String
  let n := args.flag! "n" |>.as! Nat
  let to? := (args.flag? "to").map (·.as! ModuleName)

  -- Should we sort the modules?
  -- The code below assumes that it is "deeper files first", as reported by `lake exe pole`.

  searchPathRef.set compile_time_search_path%
  Core.withImportModules #[to?.getD `Mathlib] do
    let mut modules := (args.variableArgsAs! ModuleName).toList

    let includeLean := args.hasFlag "include-lean"
    let includeStd := args.hasFlag "include-std" || includeLean
    let includeDeps := args.hasFlag "include-deps" || includeStd
    let excludeMeta := args.hasFlag "exclude-meta"

    match to? with
    | some _ =>
      if modules.isEmpty then
        modules := (← getEnv).header.moduleNames |>.toList
        if excludeMeta then
          -- Mathlib-specific exclusion of tactics
          let filterMathlibMeta : Name → Bool := fun n => (
            isPrefixOf `Mathlib.Tactic n ∨
            isPrefixOf `Mathlib.Lean n ∨
            isPrefixOf `Mathlib.Mathport n ∨
            isPrefixOf `Mathlib.Util n)
          modules := modules.filter fun n => ¬ filterMathlibMeta n
        let filter (n : Name) : Bool :=
          (`Mathlib).isPrefixOf n ||
          bif isPrefixOf `Std n then includeStd else
          bif isPrefixOf `Lean n || isPrefixOf `Init n then includeLean else
          includeDeps
        modules := modules.filter filter
      else
        IO.eprintln "Cannot specify both --to and specific modules."
        return 1
    | none =>
      if modules.isEmpty then
        IO.eprintln
          "No modules specified, please specify at least two modules on the command line."
        return 1
      if excludeMeta then IO.eprintln "--exclude-meta flag is ignored without --to."
      if includeLean then IO.eprintln "--include-lean flag is ignored without --to."
      else if includeStd then IO.eprintln "--include-std flag is ignored without --to."
      else if includeDeps then IO.eprintln "--include-deps flag is ignored without --to."

    let transitiveImports := (← getEnv).importGraph.transitiveClosure

    modules := modules.mergeSort fun m₁ m₂ => m₁.toString < m₂.toString
    modules := modules.mergeSort fun m₁ m₂ => ((transitiveImports.find? m₁).getD {}).contains m₂

    let unused ← unusedTransitiveImports modules (verbose := true)

    let headings := #["#", "module"] ++ ((List.range' 1 modules.length).map toString)
    let rows := modules.mapIdx fun i m =>
      let data := (unused.lookup m).getD []
      #[toString (i + 1), m.toString] ++
        modules.map fun m' => if data.contains m' then "x" else ""
    IO.println s!"Writing table to {output}."
    IO.FS.writeFile output (formatTable headings rows.toArray)

    let data := unused.bind fun (m, u) => u.map fun n => (modules.indexOf m, modules.indexOf n)
    let rectangles := maximalGeneralizedRectangles (NatNatSet.ofList modules.length data)
      |>.map (fun r => (r, r.area))
      -- Prefer rectangles with larger areas.
      |>.mergeSort (fun r₁ r₂ => r₁.2 > r₂.2)
      |>.take n

    for (i, (r, _)) in rectangles.enum do
      let from_ := ",".intercalate (r.xs.map fun i => modules[i]!.toString)
      let to_ := ",".intercalate (r.ys.map fun i => modules[i]!.toString)
      let excludeMetaFlag := if excludeMeta then "--exclude-meta " else ""
      IO.println
        s!"lake exe graph --from {from_} --to {to_} {excludeMetaFlag}unused{i}.pdf"

    return 0

/-- Setting up command line options and help text for `lake exe unused`. -/
def unused : Cmd := `[Cli|
  unused VIA unusedImportsCLI; ["0.0.1"]
  "Determine unused imports amongst a given set of modules.\n\
   Produces a table with rows and columns indexed by the specified modules,\n\
   with an 'x' in row A, column B if module A imports module B,\n\
   but does not make any transitive use of constants defined in B.
   This table is written to `unused.md`, and a number of `lake exe graph` commands are printed
   to visualize the largest rectangles of unused imports."

  FLAGS:
    output : String; "Write the table to a given file instead of `unused.md`."
    n : Nat;         "Number of `lake exe graph` commands to print."
    to : ModuleName; "Process all modules up to the specified module."
    "exclude-meta";  "Exclude any files starting with `Mathlib.[Tactic|Lean|Util|Mathport]`."
    "include-deps";  "Include used files from other libraries (not including Lean itself and `std`)"
    "include-std";   "Include used files from the Lean standard library (implies `--include-deps`)"
    "include-lean";  "Include used files from Lean itself \
                        (implies `--include-deps` and `--include-std`)"

  ARGS:
    ...modules : ModuleName; "Modules to check for unused imports."

  EXTENSIONS:
    author "mhuisi";
    defaultValues! #[("output", "unused.md"), ("n", "10")]
]

/-- `lake exe unused` -/
def main (args : List String) : IO UInt32 :=
  unused.validate args
