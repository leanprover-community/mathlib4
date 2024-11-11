/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Cli.Basic
import Batteries.Tactic.Lint
import Batteries.Data.String.Matcher
import Lean.Elab.ParseImportsFast

/-!
# Better automatic migrations for lean upgrades: file splits and moves

`lake exe bump-imports --from 4.12.0 --to 4.13.0` (tries to) adjust imports
of modules in mathlib which were split, moved or deleted between the `4.12.0` and `4.13.0` tags.

This tool is currently experimental and a proof of concepts;
its list of migrations (defined in `migrations.json`) is EXTREMELY incomplete!

## TODO

- make migrations more complete: ideally, would so automatically
  - find all commits which should have migrations
    e.g., look for every commit modifying Mathlib.lean, and among those each commit whose
    diff includes some deletion (or so)
  - determine if a commit is deleting a file (only deletions), moves it or splits it
  - generate the right migration for it; add to `migrations.json`
(for now, we are generating such entries by hand as-needed)

- make more configurable: parse and validate the from and to options
- make project name configurable

- make more flexible: allow specifying tags which are not the stable release, or even arbitrary
commit hashes. (In this case, the `cycle` field can be removed from migrations.)
This could happen later, but even without that feature, this tool could be helpful...
(long-term: add as a script to mathlib, and save migrations there. Would that work?)

- TODO: add remaining TODOs here :-)

-/

open Cli System.FilePath

open Lean

-- copy-pasted from batteries' `runLinter`
/-- Read the given file path and deserialize it as JSON. -/
def readJsonFile (α) [FromJson α] (path : System.FilePath) : IO α := do
  let _ : MonadExceptOf String IO := ⟨throw ∘ IO.userError, fun x _ => x⟩
  liftExcept <| fromJson? <|← liftExcept <| Json.parse <|← IO.FS.readFile path

-- copy-pasted from batteries' runLinter
/-- Serialize the given value `a : α` to the file as JSON. -/
def writeJsonFile (α) [ToJson α] (path : System.FilePath) (a : α) : IO Unit :=
  IO.FS.writeFile path <| toJson a |>.pretty.push '\n'

-- FIXME: derive FromJson, ToJson (with the right format) for typed migrations,
-- instead of hand-rolling their conversion here!
structure UntypedMigration where
  type: String
  commit_sha1: String
  -- There are three kinds of migration, with different additional data.
  -- Right now, I'm shoe-horning that into two uniforms fields.
  -- "old" is the file that is deleted (or moved way, or split)
  -- "new" is empty (for a deletion), a single file (for a move) or a list of files (for a split).
  -- Better ways of enforcing this are welcome!
  old: String
  new: Array String
deriving FromJson, ToJson

inductive MigrationKind
  /-- A file was simply deleted: delete that import (and warn the user) -/
  | DeleteFile (module : Name)
  /-- A file was moved: simply replace the import -/
  | MoveFile (old new : Name)
  /-- A file was split into several: expand the import to all files, and tell that user that
  shaking imports could be useful -/
  | SplitFile (old : Name) (into : Array Name)
deriving Inhabited

-- Note: we assume each migration describes a single file move/split.
-- If one commit performs several such splits, we generate several migrations (for now).
structure Migration where
  /-- The full hash of the commit: currently 40 charaters (hexadecimal), computed by SHA-1 -/
  -- It is validated that the string is of this form, but currently not reflected in the type.
  commit_sha1: String
  /-- The kind of migration: if there was an added, deleted, moved file,
  together with the details of that change. -/
  type: MigrationKind
deriving Inhabited

-- Very auxiliary output, but is sufficient to validate the the parsing is correct.
instance : ToString MigrationKind where
  toString mig := match mig with
  | .DeleteFile mod => s!"file deletion: {mod}"
  | .MoveFile old new => s!"file move: {old} -> {new}"
  | .SplitFile old new => s!"file split: {old} -> {", ".intercalate (new.toList.map (·.toString))}"

instance : ToString Migration where
  toString mig := s!"commit {mig.commit_sha1}, details {mig.type}"

def moduleNameToName (name : String) : Name :=
  match name.split (· == '.') with
  | [a] => Name.mkStr1 a
  | [a, b] => Name.mkStr2 a b
  | [a, b, c] => Name.mkStr3 a b c
  | [a, b, c, d] => Name.mkStr4 a b c d
  | [a, b, c, d, e] => Name.mkStr5 a b c d e
  | [a, b, c, d, e, f] => Name.mkStr6 a b c d e f
  | [a, b, c, d, e, f, g] => Name.mkStr7 a b c d e f g
  | [a, b, c, d, e, f, g, h] => Name.mkStr8 a b c d e f g h
  | _ => Name.mkSimple "ERROR: tried to construct a module name with more than 8 components"

/-- Convert a file path (as a `String`) to a module name:
  assumes the path starts with the root module. -/
def stringToModuleName (s : String) : Name := Id.run do
  -- We split by all path separators. This is not perfect, but should be reasonably robust.
  -- Remove the extension `.lean`, though!
  return match (s.dropRight 5).split (pathSeparators.contains ·) with
  | [a] => Name.mkStr1 a
  | [a, b] => Name.mkStr2 a b
  | [a, b, c] => Name.mkStr3 a b c
  | [a, b, c, d] => Name.mkStr4 a b c d
  | [a, b, c, d, e] => Name.mkStr5 a b c d e
  | [a, b, c, d, e, f] => Name.mkStr6 a b c d e f
  | [a, b, c, d, e, f, g] => Name.mkStr7 a b c d e f g
  | [a, b, c, d, e, f, g, h] => Name.mkStr8 a b c d e f g h
  | _ => Name.mkSimple "ERROR: tried to construct a module name with more than 8 components"

-- FIXME: move to batteries!
def String.strip (s : String) :=
  s.dropRightWhile (·.isWhitespace) |>.dropWhile (·.isWhitespace)

def readAdhocFile : IO (Array Migration) := do
  let mut migrations := #[]
  let mut current_sha := none
  let lines ← IO.FS.lines "some_splits_since_Oct24.txt"
  for line in lines do
    if line.strip == "" then continue
    else if line.startsWith "--" then
      current_sha := none
    else if line.strip.all (fun c ↦ "abcdef01234567890".contains c) then
      -- assert current_sha is None
      -- assert len(line.strip()) == 40
      -- Looks like a SHA
      current_sha := some line.strip
    else
      match line.splitOn " -> " with
      | [old, new_files] =>
        -- The ad hoc file entries are already module names.
        if new_files.strip == "" then
          let m := MigrationKind.DeleteFile (moduleNameToName old)
          migrations := migrations.push <| Migration.mk current_sha.get! m
        else if new_files.containsSubstr ", " then
          let new_modules := new_files.strip.splitOn ", " |>.map moduleNameToName
          let m := MigrationKind.SplitFile (moduleNameToName old) new_modules.toArray
          migrations := migrations.push <| Migration.mk current_sha.get! m
        else
          let new_module := new_files.strip.splitOn ", " |>.map moduleNameToName |>.get! 0
          let m := MigrationKind.MoveFile (moduleNameToName old) new_module
          migrations := migrations.push <| Migration.mk current_sha.get! m
      | [] | [_] | _ => let _ := 42 -- invalid input
  return migrations

def automaticallyClassifiedMigrations : IO (Array Migration) := do
  let mut mig := #[]
  let lines ← IO.FS.lines "output.txt"
  for line in lines do
    -- We only consider the lines describing the commit hash.
    if line.startsWith " Mathlib.lean | " then continue
    else if line.startsWith " 1 file changed, " && (line.containsSubstr "deletion" || line.containsSubstr "insertion") then
      continue
    let hash := (line.splitOn " ").get! 0
    if hash.length != 40 then
      dbg_trace s!"something unexpected happened: line {line} should contain a commit hash..."
    let diff ← IO.Process.output { cmd := "git", args := #["show", hash, "Mathlib.lean"] }
    if diff.exitCode != 0 then
      IO.println s!"error: git show {hash} Mathlib.lean returned an error"
      continue
    let interesting_lines := (diff.stdout.splitOn "\n").filter (fun line ↦
      (line.startsWith "-" || line.startsWith "+") && !(line.containsSubstr "Mathlib.lean")
    )
    let added := interesting_lines.filter (·.startsWith "+") |>.drop ("+import ".length)
    let removed := interesting_lines.filter (·.startsWith "-") |>.drop ("-import ".length)
    match (removed.length, added.length) with
    | (0, 0) =>
      dbg_trace "error: parsing returned *no* additions or deletions; something is off!"
      dbg_trace hash
    | (0, _) => continue -- just additions, not interesting
    | (_, 0) =>
      -- Just deletions, easy to parse.
      mig := mig.append (removed.toArray.map (fun rem ↦
        Migration.mk hash (MigrationKind.DeleteFile (moduleNameToName rem))
      ))
    | (1, 1) => -- file is moved
      mig := mig.push <| Migration.mk hash <| MigrationKind.MoveFile
        (moduleNameToName (removed.get! 0)) (moduleNameToName (added.get! 0))
    | (1, _) => -- one file is split
      mig := mig.push <| Migration.mk hash <| MigrationKind.SplitFile
        (moduleNameToName (removed.get! 0)) (added.toArray.map moduleNameToName)
    | _ => dbg_trace hash -- interesting cases
  return mig

-- Assumes `cycle` and `commit_sha1` very validated. Does not enforce this.
def Migration.from_untyped (untyped : UntypedMigration) (type : MigrationKind) : Migration :=
    { commit_sha1 := untyped.commit_sha1, type := type}

-- copy-pasted from Mathlib's lint-style script
/-- Parse all imports in a text file at `path` and return just their names:
this is just a thin wrapper around `Lean.parseImports'`.
Omit `Init (which is part of the prelude). -/
def findImports (path : System.FilePath) : IO (Array Name) := do
  return (← Lean.parseImports' (← IO.FS.readFile path) path.toString)
    |>.map (fun imp ↦ imp.module) |>.erase `Init


/-- Whether a migration applies to a given module. -/
def migrationApplies (mig : Migration) (module : Name) : Bool :=
  match mig.type with
  | MigrationKind.DeleteFile mod => module == mod
  | MigrationKind.MoveFile mod _ => module == mod
  | MigrationKind.SplitFile mod _ => module == mod

/-- Apply a sequence of import-adjust migrations (in a given order) to a sequence of imports.
  Write information about changes made to standard output. Return the adjusted imports.
  `module` is only used for error reporting; it should be the name of the module containing these imports. -/
def applyImportMigrations (module : Name)
    (migrations: Array Migration) (imports : Array Name) : IO ((Array Name) × UInt32) := do
  let mut adjustedImports := #[]
  let mut numChanged : UInt32 := 0
  for mig in migrations do
    let mut adjusted := #[]
    let mut changed := false
    for imp in imports do
      if !migrationApplies mig imp then
        adjusted := adjusted.push imp
        continue
      match mig.type with
      | MigrationKind.DeleteFile _ =>
        IO.println s!"{module}: migration triggered; deleting import {imp}"
        numChanged := numChanged + 1
        changed := true
      | MigrationKind.MoveFile _ new =>
        IO.println s!"{module}: migration triggered; replacing import {imp} by {new}"
        adjusted := adjusted.push new
        numChanged := numChanged + 1
        changed := true
      | MigrationKind.SplitFile _ new =>
        IO.println s!"{module}: migration triggered, splitting import {imp} \
          into multiple imports {new}. Please review the new imports; you may be able to trim them."
        adjusted := adjusted.append new
        numChanged := numChanged + 1
        changed := true
    if changed then adjustedImports := adjusted
  return (adjustedImports, numChanged)


/-- Return the number of migrations applied to a file. -/
def applyMigrations (migrations : Array Migration) (module : Name) : IO UInt32 := do
  let path := System.mkFilePath (module.components.map fun n ↦ n.toString)|>.addExtension "lean"
  let imports ← findImports path
  let (changedImports, n) := ← applyImportMigrations module migrations imports
  -- Future: add other migrations here, which don't just change the imports
  if n > 0 then
    IO.println s!"trace: about to write out changes to module {module}"
    let currentContent := ← IO.FS.lines path
    let mut importsAdded := false
    let mut newLines := #[]
    for line in currentContent do
      if line.startsWith "import " then
        if !importsAdded then
          newLines := newLines.append <| (changedImports.map (s!"import {·}"))
          importsAdded := true
      else
        newLines := newLines.push line
    IO.FS.writeFile path ("\n".intercalate newLines.toList ++ "\n")
  return n

/-- Parse a version string of the form "4.N.M", and return the major version N (or `none`, if invalid). -/
def parseMajorVersion (input : String) : Option Nat :=
  match input |>.splitOn "." with
   | [] | [_] | [_, _] => none
   | [four?, nPart, mPart] =>
    if four? != "4" then none else
    match (String.toNat? nPart, String.toNat? mPart) with
    | (some n, some _m) => some n
    | _ => none
   | _ => none

/-- Implementation of the `bump-imports` command line program. -/
def bumpImportsCli (args : Cli.Parsed) : IO UInt32 := do
  let bumpFrom : String := (args.flag? "from").map (·.value) |>.getD "4.12.0"
  let bumpTo : String := (args.flag? "to").map (·.value) |>.getD "4.13.0"
  let projectName := args.positionalArg! "project" |>.value

  -- Validate the values passed in for "from" and "to".
  -- Both should be strings of the form "4.N.M", for integers N and M.
  let mut fromMajorVersion := 0
  match parseMajorVersion bumpFrom with
  | none =>
    IO.println "invalid input: --from should have the form 4.N.M, for some N and M"
    return 2
  | some n => fromMajorVersion := n
  let mut toMajorVersion := 0
  match parseMajorVersion bumpTo with
  | none =>
    IO.println "invalid input: --to should have the form 4.N.M, for some N and M"
    return 2
  | some n => toMajorVersion := n
  if toMajorVersion <= fromMajorVersion then
    IO.println "invalid input: --from version should be less than --to"
    return 1

  if fromMajorVersion > 12 then
    IO.println "warning: currently, there are no migrations from versions >= 4.13 forward\
      Feel free to contribute some yourself!"
    return 0
  else if toMajorVersion < 13 then
    IO.println "warning: currently, there are no migrations to versions < 4.13 forward\
      Feel free to contribute some yourself!"
    return 0

  -- These are merely advisory.
  if fromMajorVersion < 12 || 13 < fromMajorVersion then
    IO.println "note: currently, there are only migrations from 4.12.0 to 4.13.0\
      Feel free to contribute additional migrations!"

  -- Find all migrations which apply to the current range of commits.
  let untypedMigrations ← readJsonFile (Array UntypedMigration) (System.mkFilePath ["migrations.json"])

  -- Parse the data into some typed representation.
  let mut migrations : Array Migration := #[]
  for mig in untypedMigrations do
    if mig.commit_sha1.length != 40 then
      IO.println "invalid migration: the 'commit_sha1' should be the full SHA1 sha, i.e. 40 hexadecimal characters"
      continue
    else if mig.commit_sha1.any (fun c ↦ !"abcdef0123456789".contains c) then
      IO.println s!"invalid migration: the commit sha {mig.commit_sha1}' should be 40 hexadecimal characters"
      continue
    match mig.type with
    | "delete_file" =>
      if mig.new.size > 0 then
        IO.println "invalid migration: deletions should specify *no* files as 'new'"
        continue
      let type := MigrationKind.DeleteFile (stringToModuleName mig.old)
      migrations := migrations.push (Migration.from_untyped mig type)
    | "split_file" =>
      if mig.new.size < 2 then
        IO.println "invalid migration: splits should specify at least two new files"
        continue
      let type := MigrationKind.SplitFile (stringToModuleName mig.old) (mig.new.map stringToModuleName)
      migrations := migrations.push (Migration.from_untyped mig type)
    | "move_file" =>
      if mig.new.size != 1 then
        IO.println "invalid migration: moves should specify exactly one new file"
        continue
      let type := MigrationKind.MoveFile (stringToModuleName mig.old) (stringToModuleName mig.new[0]!)
      migrations := migrations.push (Migration.from_untyped mig type)
    | _ =>
      IO.println s!"invalid migration: migration type {mig.type} is not known"
      continue

  -- Read in additional migrations, already parsed as typed.
  let extraTypedMigrations ← readAdhocFile
  migrations := migrations.append extraTypedMigrations
  IO.println s!"info: input data is well-formed, found {migrations.size} typed migration(s)"

  let moreExtra ← automaticallyClassifiedMigrations

  -- Extract all mathlib commits between the specified commits.
  -- FUTURE: do this automatically? or add further look-up files? Un-hard-code `from` and `to`!
  let allMathlibCommits := (← IO.FS.lines "commits412-413.txt").filter (!·.startsWith "-- ")
  -- Basic validation of the file contents.
  let badLines := allMathlibCommits.filter
    (fun l ↦ l.length != 40 || l.any (fun c ↦ !"abcdef0123456789".contains c))
  if badLines.size > 0 then
    IO.println s!"error parsing file 'commits412-413.txt', the lines(s) {badLines} \
      do not contain full SHA1 commit hashes"

  -- Filter out any migrations which do not apply to a commit in this list.
  let applicableMigrations := migrations.filter (allMathlibCommits.contains ·.commit_sha1)
  -- FIXME: fix application order of the migrations --- want to use the order of their commits!

  -- Find all files in the project: parse {projectName}.lean.
  let imports ← findImports s!"{projectName}.lean"
  let mut numberTotalChanges := 0
  -- For now, we assume that we can fix each file separately.
  for module in imports do
    numberTotalChanges := numberTotalChanges + (← applyMigrations applicableMigrations module)
  IO.println s!"success: applied {numberTotalChanges} individual migration(s)"
  return 0


/-- Setting up command line options and help text for `lake exe bump-imports`. -/
-- so far, no help options or so: perhaps that is fine?
def bumpImports : Cmd := `[Cli|
  «bump-imports» VIA bumpImportsCli; ["0.0.1"]
  "Try to adjust imports of any mathlib module that is directly imported, and which was
  deleted, moved or split in the time window of the attempted mathlib bump.
  Very much EXPERIMENTAL and a PROTOTYPE."

  FLAGS:
    «from» : String;  "Mathlib tag from which to upgrade. currently ignored (hard-coded to 4.12.0)"
    to : String;  "Mathlib tag to which to upgrade. currently ignored (hard-coded to 4.13.0)"

  ARGS:
    project: String; "Name of the current project, e.g. 'Carleson'"

]

/-- The entry point to the `lake exe bump-imports` command. -/
def main (args : List String) : IO UInt32 := do bumpImports.validate args
