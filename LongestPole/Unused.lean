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
open Lean

/-- Count the number of declarations in each module. -/
def countDecls (modules : Array Name) : CoreM (Array Nat) := do
  let env ← getEnv
  let mut counts := Array.replicate modules.size 0
  let moduleIndices := Std.HashMap.ofList <| modules.zipIdx.toList
  for (n, _) in env.constants.map₁ do
    if ! n.isInternal then
    if let some m := env.getModuleFor? n then
      if let some i := moduleIndices[m]? then
        counts := counts.modify i (· + 1)
  return counts

/-- Implementation of `lake exe unused` -/
def unusedImportsCLI (args : Cli.Parsed) : IO UInt32 := do
  let output := args.flag! "output" |>.as! String
  let n := args.flag! "n" |>.as! Nat
  let modules := (args.variableArgsAs! ModuleName).toList
  if modules.isEmpty then
    IO.eprintln
      "No modules specified, please specify at least two modules on the command line."
    return 1

  -- Should we sort the modules?
  -- The code below assumes that it is "deeper files first", as reported by `lake exe pole`.

  searchPathRef.set compile_time_search_path%
  -- It may be reasonable to remove this again after https://github.com/leanprover/lean4/pull/6325
  unsafe enableInitializersExecution
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
  IO.println s!"Writing table to {output}."
  IO.FS.writeFile output (formatTable headings rows.toArray)

  let data := unused.flatMap fun (m, u) => u.map fun n => (modules.idxOf m, modules.idxOf n)
  let rectangles := maximalRectangles data
    |>.map (fun r => (r, r.area))
    -- Prefer rectangles with larger areas.
    |>.mergeSort (fun r₁ r₂ => r₁.2 > r₂.2)
    -- The `lake exe graph` command we print only depends on the top-right corner, so deduplicate.
    |>.pwFilter (fun r₁ r₂ => (r₁.1.top, r₂.1.right) ≠ (r₂.1.top, r₁.1.right))
    |>.take n

  for ((r, _), i) in rectangles.zipIdx do
    -- We use `--from top` so that the graph starts at the module immediately *before*
    -- the block of unused imports. This is useful for deciding how a split should be made.
    -- We use `--to (right-1)` so that the graph ends at the earliest of the modules
    -- which do not make use of any of the unused block.
    -- Note that this means that the later modules which do not use the block are not displayed,
    -- and in particular it is not possible to see from the graph the size of the later block
    -- which makes no use of the earlier unused block.
    -- Perhaps modifying `to` to allow multiple modules, and highlighting all of these in some way,
    -- would be a useful addition.
    let from_idx := min r.top (modules.length - 1)
    let to_idx := r.right - 1
    IO.println
      s!"lake exe graph --from {modules[from_idx]!} --to {modules[to_idx]!} unused{i}.pdf"

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
    n : Nat; "Number of `lake exe graph` commands to print."

  ARGS:
    ...modules : ModuleName; "Modules to check for unused imports."

  EXTENSIONS:
    author "mhuisi";
    defaultValues! #[("output", "unused.md"), ("n", "10")]
]

/-- `lake exe unused` -/
def main (args : List String) : IO UInt32 :=
  unused.validate args
