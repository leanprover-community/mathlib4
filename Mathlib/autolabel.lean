import Lean

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
 -/
structure Label where
  /-- The GitHub label.  By default, it is filled in by `t-[Label name]` with the automatic
  replacement of underscores (`_`) in the name with dashes (`-`). -/
  label : String := by exact "t-" ++ (getLast decl_name%).replace "_" "-"
  /-- The array of "root paths".  By default, it is filled in with the singleton array consisting
  of the `[label name]` in UpperCamelCase. -/
  dirs : Array String := by exact #[((getLast decl_name%).splitOn "_").foldl (· ++ ·.capitalize) ""]
  /-- The array of paths that satisfy the `dirs` constraint, but are nonetheless excluded.
  This gives finer control: for instance, all `Tactic` modifications should get the `t-meta` label,
  *except* for the `Tactic/Linter` modifications that should get the `t-linter` label.
  By default, it is filled in with the empty array. -/
  exclusions : Array String := #[]

namespace Label

/--
`findLabel? l modifiedFile` takes as input a `Label` `l` and a string `modifiedFile` and checks
if there is a string in `l.dirs` that is a prefix to `s`.
If it finds (at least) one, then it returns `some l.label`, otherwise it returns `none`.
-/
def findLabel? (l : Label) (modifiedFile : String) : Option String :=
  if (l.dirs.map (·.isPrefixOf modifiedFile)).any (·) then some l.label else none

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
def getLabels (ls : Array Label) (gitDiff : Array String) : Array String :=
  gitDiff.foldl (· ++ findLabels ls ·) #[]

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
  "add_label " ident ("label: " ident*)? ("dirs: " ident*)? ("exclusions: " ident*)? : command

@[inherit_doc addLabelStx]
elab_rules : command
    | `(command| add_label $id) => do
      setEnv <| labelsExt.addEntry (← getEnv) {
        label := "t-" ++ id.getId.toString.replace "_" "-"
        dirs := #[(id.getId.toString.splitOn "_").foldl (· ++ ·.capitalize) ""]
      }
    | `(command| add_label $id dirs: $dirs*) => do
      setEnv <| labelsExt.addEntry (← getEnv) {
        label := "t-" ++ id.getId.toString.replace "_" "-"
        dirs := dirs.map fun d => (d.getId.toString.splitOn "_").foldl (· ++ ·.capitalize) ""
      }
    | `(command| add_label $id dirs: $dirs* exclusions: $excs*) => do
      setEnv <| labelsExt.addEntry (← getEnv) {
        label := "t-" ++ id.getId.toString.replace "_" "-"
        dirs := dirs.map fun d => (d.getId.toString.splitOn "_").foldl (· ++ ·.capitalize) ""
        exclusions := excs.map (·.getId.toString)
      }
/--
`check_labels` is a helper command to `add_labels`.
It displays all the labels that have already been declared.
-/
elab "check_labels" : command => do
  for l in labelsExt.getState (← getEnv) do
    logInfo m!"label: {l.label}\ndirs: {l.dirs}\nexclusions: {l.exclusions}"

end AutoLabel.Label
