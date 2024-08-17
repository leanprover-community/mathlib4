/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command

/-!
The file with the attribute and the basic API
-/

open Lean

namespace AutoLabel

/-- `getLast n` takes as input a name `n` and return the last (string) component, if there is one,
returning the empty string `""` otherwise. -/
def getLast : Name → String
  | .str _ s => s
  | _ => ""

/-- A `Label` is the main structure for converting a folder into a `t-`label.
* The `label` field is the actual GitHub label.
* The `dirs` field is the array of all "root paths" such that a modification in a file contained
  in one of these paths should be labeled by `label`.
* The `exclusions` field is the array of all "root paths" that are excluded, among the
  ones that start with the ones in `dirs`.

It is not really intended to be used directly.
The command `add_label` manages `Label`s: it creates them and adds them to the `Environment`.
-/
structure Label where
  /-- The GitHub label.  This is expected to be in the form `t-label-name-kebab-case]`. -/
  label : String
  /-- The array of "root paths". -/
  dirs : Array System.FilePath
  /-- The array of paths that satisfy the `dirs` constraint, but are nonetheless excluded.
  This gives finer control: for instance, all `Tactic` modifications should get the `t-meta` label,
  *except* for the `Tactic/Linter` modifications that should get the `t-linter` label.
  Most of the times, this field is empty. -/
  exclusions : Array System.FilePath

namespace Label
open System.FilePath (pathSeparator) in
/--
`findLabel? l modifiedFile` takes as input a `Label` `l` and a string `modifiedFile` and checks
if there is a string in `l.dirs` that is a prefix to `s`.
If it finds (at least) one, then it returns `some l.label`, otherwise it returns `none`.
-/
def findLabel? (l : Label) (modifiedFile : String) : Option String :=
  -- check that the path does not match any of the forbidden ones in `exclusions`
  if (l.exclusions.map fun d => d.toString.isPrefixOf modifiedFile).any (·) then
    none
  -- if the path is not excluded, then check if it is among the ones allowed in `dirs`.
  else if (l.dirs.map fun d => d.toString.isPrefixOf modifiedFile).any (·) then
  some l.label else none

/--
`findLabels ls modifiedFile` takes as input an array of  `Label`s `ls` and a string `modifiedFile`
and returns all the applicable labels among `ls` for `modifiedFile`.
-/
def findLabels (ls : Array Label) (modifiedFile : String) : Array String :=
  ls.filterMap (findLabel? · modifiedFile)

/--
`getLabels ls gitDiff` takes as input an array of  `Label`s `ls` and an array of strings
`gitDiff` and returns all the labels among `ls` that are applicable to some entry of ` applicable`.
-/
def getLabels (ls : Array Label) (gitDiff : Array String) : HashSet String :=
  HashSet.empty.insertMany (gitDiff.foldl (· ++ findLabels ls ·) #[])

/-- Defines the `labelsExt` extension for adding the `Name` of a `Label` to the environment. -/
initialize labelsExt :
    PersistentEnvExtension Label Label (Array Label) ←
  let addEntryFn := .push
  registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn := (pure <| .flatten ·)
    addEntryFn
    exportEntriesFn := id --fun es => es.foldl (fun a _ e => a.push e) #[]
  }

/--
`formatIdsToDirs dirs` takes as input an array of identifiers `dirs` and converts them
to an array of paths.
It assumes that the identifiers are in `snake_case.with_several.parts`, in converts them to
`Mathlib.SnakeCase.WithSeveral.Parts.` and finally replaces `.` by the path-separator, e.g. `/`.
-/
def formatIdsToDirs (dirs : TSyntaxArray `ident) : Array System.FilePath :=
  dirs.map fun d =>
    let str := (d.getId.toString.splitOn "_").foldl (· ++ ·.capitalize) ""
    -- we prepend `Mathlib` and we append an "empty" segment at the end to ensure that
    -- the path ends with the path separator (e.g. `/`).
    -- This means that, for instance, `Algebra` does not match `AlgebraicGeometry`
    System.mkFilePath (["Mathlib"] ++ str.splitOn "." ++ [""])

/-- The simplest way to add a label is to use `add_label label_name`. This adds
* `t-label-name` as a label and
* `LabelName` as root folder,
meaning that any change to `Mathlib.LabelName` will be labeled by `t-label-name`.

If you want to customize the root folders that are relevant to your label, you can use
`add_label label_name dirs: d₁ d₂ ... dₙ`.  This adds
* `t-label-name` as a label and
* `Mathlib.d₁, Mathlib.d₂, ..., Mathlib.dₙ` as root folders.

Finally, if you also want to filter out of the previous root folders some subfolders, you can use
`add_label label_name dirs: d₁ d₂ ... dₙ exclusions: e₁ e₂ ... eₘ`.  This adds
* `t-label-name` as a label and
* `Mathlib.d₁, Mathlib.d₂, ..., Mathlib.dₙ` as root folders, unless the folder matches
* `Mathlib.e₁, Mathlib.e₂, ..., Mathlib.eₘ`.

The helper command `check_labels` displays all the labels that have already been declared.
-/
syntax (name := addLabelStx)
  "add_label " ident ("dirs: " ident*)? ("exclusions: " ident*)? : command

open Elab.Command in
@[inherit_doc addLabelStx]
elab_rules : command
  | `(command| add_label $id dirs: $dirs* exclusions: $excs*) => do
    setEnv <| labelsExt.addEntry (← getEnv)
      { label := "t-" ++ id.getId.toString.replace "_" "-"
        dirs := formatIdsToDirs dirs
        exclusions := formatIdsToDirs excs }
  | `(command| add_label $id dirs: $dirs*) => do
    elabCommand (← `(command| add_label $id dirs: $dirs* exclusions:))
  | `(command| add_label $id) => do
    elabCommand (← `(command| add_label $id dirs: $id))
/--
`check_labels` is a helper command to `add_labels`.
It displays all the labels that have already been declared.
-/
elab "check_labels" : command => do
  for l in labelsExt.getState (← getEnv) do
    logInfo m!"label: {l.label}\ndirs: {l.dirs}\nexclusions: {l.exclusions}"

/--
`produceLabels env gitDiffs` takes as input an `Environment` `env` and a string `gitDiffs`.
It assumes that `gitDiffs` is a line-break-separate list of paths to files.
It uses the paths to check if any of the labels in the environment is applicable.
It returns the sorted array of the applicable labels with no repetitions.
-/
def produceLabels (env : Environment) (gitDiffs : String) : Array String :=
  let hash := getLabels (labelsExt.getState env) <| (gitDiffs.splitOn "\n").toArray
  hash.toArray.qsort (· < ·)

/--
`produce_labels "A/B/C.lean⏎D/E.lean"` takes as input a string, assuming that it is a
line-break-separated list of paths to files.
It uses the paths to check if any of the labels in the environment is applicable.
It prints the sorted array of the applicable labels with no repetitions.
-/
elab tk:"produce_labels " st:str : command => do
  logInfoAt tk m!"{produceLabels (← getEnv) st.getString}"

end AutoLabel.Label
