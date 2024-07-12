import Batteries.Tactic.Lint
import Batteries.Data.Array.Basic
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

-- TODO: this was copy-pasted from Batteries.Tactic.Lint.Frontend;
-- this modification should be changed back there
/-- `getChecks slow extra use_only` produces a list of linters.
`extras` is a list of names that should resolve to declarations with type `linter`.
If `useOnly` is true, it only uses the linters in `extra`.
Otherwise, it uses all linters in the environment tagged with `@[env_linter]`.
If `slow` is false, it only uses the fast default tests. -/
def getChecksNew (slow : Bool) (useOnly : Bool) : CoreM (Array NamedLinter) := do
  let mut result := #[]
  unless useOnly do
    for (name, declName, dflt) in batteriesLinterExt.getState (← getEnv) do
      if dflt then
        let linter ← getLinter name declName
        if slow || linter.isFast then
          let _ := Inhabited.mk linter
          result := result.binInsert (·.name.lt ·.name) linter
  pure result

open Cli

unsafe def runLinterCli (args : Cli.Parsed) : IO UInt32 := do
  let only := (args.flag? "only_linters").map fun val ↦ (val.value.splitOn " ")
  let exclude := (args.flag? "exclude_linters").map fun val ↦ (val.value.splitOn " ")
  let add := (args.flag? "add_linters").map fun val ↦ (val.value.splitOn " ")
  -- "only" and "add" are contradictory: error if both are provided
  if only.isSome && add.isSome then
    IO.println "The options '--only_linters' and '--add_linters' are incompatible:\
      please do not specify both"
    IO.Process.exit 2
  else if only.isSome && exclude.isSome then
    IO.println "The options '--only_linters' and '--exclude_linters' are incompatible:\
      please do not specify both"
    IO.Process.exit 2
  if add.isSome then
    IO.println "Attention: the --add_linters flag has not been implemente yet, at it requires \
      some changes to 'batteries'"
  let print := args.hasFlag "print_linters"
  let update := args.hasFlag "update"
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
  let nolintsFile : FilePath := "scripts/nolints.json"
  let nolints ← if ← nolintsFile.pathExists then
    readJsonFile NoLints nolintsFile
  else
    pure #[]
  withImportModules #[{module}] {} (trustLevel := 1024) fun env ↦
    let ctx := { fileName := "", fileMap := default }
    let state := { env }
    Prod.fst <$> (CoreM.toIO · ctx state) do
      let decls ← getDeclsInPackage module.getRoot
      let mut linters ← getChecksNew (slow := true) (useOnly := false)
      -- Modify the list of linters to run, if configured so.
      if let some only := only then
        linters := linters.filter fun lint ↦ only.contains lint.name.toString
      else if let some exclude := exclude then
        linters := linters.filter fun lint ↦ !exclude.contains lint.name.toString
      -- TODO: add_linters is not implemented yet; requires re-adding an `extra` parameter to `getChecks`
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
    only_linters : Array String;  "Only run these named linters"
    exclude_linters : Array String; "Do not run these named linters"
    add_linters : Array String; "Run these linters *in addition* to the default set"
    print_linters; "Print the list of all discovered/configured linters and exit"

    update;     "Update the `nolints` file to remove any declarations \
                that no longer need to be nolinted.
                If the 'only_linters', 'exclude_linters' or 'add_linters' flags are passed,
                this will only add entries for these linters: the nolints file could be missing
                further entries. Use with care!"

    module : String;   "Run the linters on a given module: if omitted, will run on all modules in Mathlib"
]

/-- The entry point to the `lake exe myRunLinter` command. -/
unsafe def main (args : List String) : IO UInt32 := do runLinter.validate args
