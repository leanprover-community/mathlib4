import Lean
import Batteries
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

/-- A `NamedLabel` is a label associated to a particular declaration. -/
structure NamedLabel extends Label where
  /-- The name of the named label. This is just the declaration name without the namespace. -/
  name : Name
  /-- The label declaration name -/
  declName : Name

/-- Gets a label by declaration name. -/
def getLabel (name declName : Name) : CoreM NamedLabel := unsafe
  return { ← evalConstCheck Label ``Label declName with name, declName }

namespace Label

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

open Lean Elab Command

syntax "add_label " ident ("label: " ident*)? ("dirs: " ident*)? ("exclusions: " ident*)? : command

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

elab "check_labels" : command => do
  let le := labelsExt.getState (← getEnv)
  for l in le do
    logInfo m!"label: {l.label}\ndirs: {l.dirs}\nexclusions: {l.exclusions}"

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
