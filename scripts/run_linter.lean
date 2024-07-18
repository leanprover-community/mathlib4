import Batteries.Tactic.Lint
import Batteries.Data.Array.Basic
import Batteries.Data.List.Basic
import Batteries.Lean.Util.Path
import Cli.Basic

set_option autoImplicit true

/-!
Michael's fork of the batteries `runLinter` script:
allow configuring which linters to run, as an experiment.
-/
open Lean Core Elab Command Std.Tactic.Lint
open System (FilePath)

/-- The list of `nolints` pulled from the `nolints.json` file -/
abbrev NoLints := Array (Name × Name)

/-- Read the given file path and deserialize it as JSON. -/
def readJsonFile (α) [FromJson α] (path : System.FilePath) : IO α := do
  let _ : MonadExceptOf String IO := ⟨throw ∘ IO.userError, fun x _ ↦ x⟩
  liftExcept <| fromJson? <|← liftExcept <| Json.parse <|← IO.FS.readFile path

/-- Serialize the given value `a : α` to the file as JSON. -/
def writeJsonFile [ToJson α] (path : System.FilePath) (a : α) : IO Unit :=
  IO.FS.writeFile path <| toJson a |>.pretty

open Cli

unsafe def runLinterCli (args : Cli.Parsed) : IO UInt32 := do
  let only := (args.flag? "only_run").map fun val ↦ (val.value.splitOn " ")
  let exclude := (args.flag? "never_run").map fun val ↦ (val.value.splitOn " ")
  let add := (args.flag? "always_run").map fun val ↦ (val.value.splitOn " ")
  let print := args.hasFlag "print_linters"
  let update := args.hasFlag "update"
  let updateOnlyRemove := args.hasFlag "update_only_remove"
  -- "only" and "exclude" are contradictory: error if both are provided
  -- also error if "add" and "exclude" overlap.
  if only.isSome && exclude.isSome then
    IO.println "invalid arguments: the options '--only_run' and '--never_run' \
      are incompatible: please do not specify both"
    IO.Process.exit 2
  else if let some add := add then
    if let some exclude := exclude then
      let overlap := add.filter fun s ↦ exclude.contains s
      if overlap.length > 0 then
        IO.println s!"invalid arguments: the linter(s) {overlap} cannot be both added and excluded"
        IO.Process.exit 2
    else if let some only := only then
      let contradictory := add.filter fun s ↦ !only.contains s
      if contradictory.length > 0 then
        IO.println s!"invalid arguments: the linter(s) {contradictory} are supposed to be \
          both always and not run"
        IO.Process.exit 2
  if update && updateOnlyRemove then
    IO.println "invalid arguments: the options '--update' and '--update_only_remove' \
      are mutually exclusive: please do not specify both"
    IO.Process.exit 2
  let some module := match args.flag? "module" with
      | some mod =>
        match mod.value.toName with
        | .anonymous => none
        | name => some name
      | none => some `Mathlib
    | IO.eprintln "invalid input: --module must be an existing module, \
        such as 'Mathlib.Data.List.Basic'" *> IO.Process.exit 1
  searchPathRef.set compile_time_search_path%
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    -- run `lake build module` (and ignore result) if the file hasn't been built yet
    let child ← IO.Process.spawn {
      cmd := (← IO.getEnv "LAKE").getD "lake"
      args := #["build", s!"+{module}"]
      stdin := .null
    }
    _ ← child.wait
  let nolintsFile : FilePath := "scripts" / "nolints.json"
  let nolints ← if ← nolintsFile.pathExists then
    readJsonFile NoLints nolintsFile
  else
    pure #[]
  withImportModules #[{module}] {} (trustLevel := 1024) fun env ↦
    let ctx := { fileName := "", fileMap := default }
    let state := { env }
    Prod.fst <$> (CoreM.toIO · ctx state) do
      let decls ← getDeclsInPackage module.getRoot
      -- Configure the list of linters to run, as needed.
      let defaultLinters ← getChecks (slow := true)
        (runOnly := only.map fun names ↦ names.map (·.toName))
        (runAlways := add.map fun names ↦ names.map (·.toName))
      let linters := if updateOnlyRemove then
        -- Determine all unique linters which are mentioned in the `nolints` file.
        let all := (nolints.map fun nol ↦ nol.1).qsort (·.toString < ·.toString)
        let uniqueLinters := (all.toList).pwFilter (·.toString ≠ ·.toString)
        defaultLinters.filter fun lint ↦ uniqueLinters.contains lint.name
      else
        match exclude with
        | some exclude => defaultLinters.filter (!exclude.contains ·.name.toString)
        | none => defaultLinters
      if print then
        IO.println s!"The following {linters.size} linter(s) were configured to run: \
          {linters.map fun l ↦ l.name}"
        IO.Process.exit 0

      let results ← lintCore decls linters
      if update then
        writeJsonFile (α := NoLints) nolintsFile <|
          .qsort (lt := fun (a, b) (c, d) ↦ a.lt c || (a == c && b.lt d)) <|
          .flatten <| results.map fun (linter, decls) ↦
          decls.fold (fun res decl _ ↦ res.push (linter.name, decl)) #[]
      let results := results.map fun (linter, decls) ↦
        .mk linter <| nolints.foldl (init := decls) fun decls (linter', decl') ↦
          if linter.name == linter' then decls.erase decl' else decls
      let failed := results.any (!·.2.isEmpty)
      if failed then
        let fmtResults ←
          formatLinterResults results decls (groupByFilename := true) (useErrorFormat := true)
            s!"in {module}" (runSlowLinters := true) .medium linters.size
        IO.print (← fmtResults.toString)
        IO.Process.exit 1
      else
        IO.println "-- Linting passed."
  return 0

/-- Setting up command line options and help text for `lake exe myRunLinter`. -/
unsafe def runLinter : Cmd := `[Cli|
  lint_style VIA runLinterCli; ["0.0.1"]
  "Runs the linters on all declarations in the given module (or `Mathlib` by default)."

  FLAGS:
    only_run : Array String;  "Only run these named linters"
    never_run : Array String; "Do not run these named linters"
    always_run : Array String;
      "Always run these named linters, regardless of whether they are enabled by default"
    print_linters; "Print the list of all discovered/configured linters and exit"

    update;     "Update the `nolints` file to remove any declarations \
                that no longer need to be nolinted.
                If the 'only_linters', 'exclude_linters' or 'add_linters' flags are passed,
                this will only add entries for these linters: the nolints file could be missing
                further entries. Use with care!"
    update_only_remove; "Like --update, but only run linters which have entries in the nolints file\
      This can be much faster, but will by design only *remove* entries, never add any."

    module : String; "Run the linters on a given module: if omitted, will run on all modules in Mathlib"
]

/-- The entry point to the `lake exe run_linter` command. -/
unsafe def main (args : List String) : IO UInt32 := do runLinter.validate args
