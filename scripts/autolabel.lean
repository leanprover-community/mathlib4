/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Damiano Testa
-/
import Lean.Elab.Command

/-!
# Automatic labelling of PRs

This file contains the basic definitions, the environment extension and the API commands
to automatically assign a GitHub label to a PR.

The heuristic used to assign a label is to assign labels to certain folder inside `Mathlib/`
and assign a label to a PR if the PR modifies files within the corresponding folders.

Ultimately, this produces a `HashMap String String` that takes a string representing a path
to a modified file and returns the corresponding GitHub label.

Since the labels are independent of the modified file, we define a `PersistentEnvExtension`
that keeps track of an array of `Label`s.

## The `Label` structure

A `Label` is a structure containing
* the GitHub label (as a `String`);
* the array of folders associated to the given label (as an `Array String`);
* the array of folders that forbid a given label, even though a path may satisfy the conditions
  implied by `dirs` (as an `Array String`).

For example, the files in the `Tactic` folder should be labelled as `t-meta`,
except the ones in `Tactic/Linter` that should be labelled `t-linter`.
This would be encoded by
```lean
{ Label.label      := "t-meta"
  Label.dirs       := #["Tactic"]
  Label.exclusions := #["Tactic/Linter"] }`
```
a term of type `Label`.

## The `add_label` command

Since `Label`s are managed by an environment extension, there is a user command to add them.
Thus, the previous label would be added using
```
add_label meta dirs: Tactic exclusions Tactic.Linter
```
The "strings" are passed as identifiers, so that the path-separators `/` should be entered as `.`.
The prefix `t-` in front of `meta` is automatically added by `add_label`.

Look at the documentation for `add_label` for further shortcuts.

## Further commands

The file also defines the commands `check_labels` and `produce_labels(!)? str`.
They display what `Label`s are currently present in the environment and they test-run the automatic
application of the labels to user-input/`git diff` output.
These commands are mostly intended as "debugging commands", even though
`produce_labels "git"` is used in the `autolabel` CI action.

See the doc-strings of `check_labels` and `produce_labels` for more details.
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
  exclusions : Array System.FilePath := #[]
  deriving BEq, Hashable

def mathlibLabels : Std.HashSet Label := Std.HashSet.ofList [
  { label := "t-algebra",
    dirs := #[
      "Mathlib" / "FieldTheory",
      "Mathlib" /" RingTheory",
      "Mathlib" / "GroupTheory",
      "Mathlib" / "RepresentationTheory",
      "Mathlib" / "LinearAlgebra" ]},
  { label := "t-algebraic_geometry",
    dirs := #[
      "Mathlib" / "AlgebraicGeometry",
      "Mathlib" / "Geometry.RingedSpace" ]},
  { label := "t-analysis",
    dirs := #[
      "Mathlib" / "Analysis"]},
  { label := "t-category_theory",
    dirs := #[
      "Mathlib" / "CategoryTheory"]},
  { label := "t-combinatorics",
    dirs := #[
      "Mathlib" / "Combinatorics"]},
  { label := "t-computability",
    dirs := #[
      "Mathlib" / "Computability"]},
  { label := "t-condensed",
    dirs := #[
      "Mathlib" / "Data"]},
  { label := "t-data",
    dirs := #[
      "Mathlib" / "DifferentialGeometry"]},
  { label := "t-differential-geometry",
    dirs := #[
      "Mathlib" / "Geometry" / "Manifold" ]},
  { label := "t-dynamics",
    dirs := #[
      "Mathlib" / "Dynamics"]},
  { label := "t-euclidean_geometry",
    dirs := #[
      "Mathlib" / "Geometry" / "Euclidean" ] },
  { label := "t-linter",
    dirs := #[
      "Mathlib" / "Tactic" / "Linter" ]},
  { label := "t-logic",
    dirs := #[
      "Mathlib" / "Logic",
      "Mathlib" / "ModelTheory" ]},
  { label := "t-measure-probability",
    dirs := #[
      "Mathlib" / "MeasureTheory",
      "Mathlib" / "Probability",
      "Mathlib" / "InformationTheory" ]},
  { label := "t-meta",
    dirs := #[
      "Mathlib" / "Tactic" ],
    exclusions := #[
      "Mathlib" / "Tactic" / "Linter" ]},
  { label := "t-number-theory",
    dirs := #[
      "Mathlib" / "NumberTheory"]},
  { label := "t-order",
    dirs := #[
      "Mathlib" / "Order"]},
  { label := "t-set-theory",
    dirs := #[
      "Mathlib" / "SetTheory"]},
  { label := "t-topology",
    dirs := #[
      "Mathlib" / "Topology",
      "Mathlib" / "AlgebraicTopology" ]}]

namespace Label

open System.FilePath (pathSeparator) in
/--
`findLabel? label modifiedFile` takes as input a `Label` `label` and a string `modifiedFile` and checks
if there is a string in `label.dirs` that is a prefix to `s`.
If it finds (at least) one, then it returns `some l.label`, otherwise it returns `none`.
-/
def findLabel? (label : Label) (modifiedFile : String) : Option String :=
  -- check that the path does not match any of the forbidden ones in `exclusions`
  if (label.exclusions.map fun d => d.toString.isPrefixOf modifiedFile).any (·) then
    none
  -- if the path is not excluded, then check if it is among the ones allowed in `dirs`.
  else if (label.dirs.map fun d => d.toString.isPrefixOf modifiedFile).any (·) then
  some label.label else none

/-- `addAllLabels gitDiffs ls` takes as input an array of string `gitDiffs` and an `HashSet` of
`Label`s `ls`.
It returns the `HashMap` that assigns to each entry of `gitDiffs` the `.label` field from the
appropriate `Label` in `ls`. -/
def addAllLabels (gitDiffs : Array String) (ls : Std.HashSet Label) : Std.HashMap String String :=
  Id.run do
  let mut tot := {}
  for l in ls do
    for modifiedFile in gitDiffs do
      if let some lab := findLabel? l modifiedFile then
        tot := tot.insert modifiedFile lab
  return tot


-- System.mkFilePath (["Mathlib"] ++ d.getString!.splitOn "." ++ [""]



/--
`getMatchingLabels dirs` assumes that `dirs` is an array of paths to folders.

It return a `HashMap`, which contains one entry per label defined in `mathlibLabels`.
The key is the corresponding `.label` field and the value all directories from `dirs`
which fall into that label's domain.
-/
def getMatchingLabels (dirs : Array String) : Std.HashMap String (Array String) :=
  let hash := addAllLabels dirs mathlibLabels
  let grouped := dirs.groupByKey (hash.get? · |>.getD "")
  let matched := grouped.erase ""
  let unmatched := ((grouped.get? "").getD #[]).filter (!·.isEmpty)
  if unmatched.isEmpty then
      matched
    else
      matched.insert "unlabeled" unmatched

-- /--
-- `produceLabels env gitDiffs` takes as input an `Environment` `env` and a string `gitDiffs`.
-- It assumes that `gitDiffs` is a line-break-separate list of paths to files.
-- It uses the paths to check if any of the labels in the environment is applicable.
-- It returns the sorted array of the applicable labels with no repetitions.
-- -/
-- def produceLabels (gitDiffs : String) : Array String :=
--   let grouped := labelsToFiles gitDiffs
--   ((grouped.toArray.map Prod.fst).filter (· != "")).qsort (· < ·)

-- /--
-- `produce_labels "A/B/C.lean⏎D/E.lean"` takes as input a string, assuming that it is a
-- line-break-separated list of paths to files.
-- It uses the paths to check if any of the labels in the environment are applicable.
-- It prints the sorted, comma-separated string of the applicable labels with no repetitions.

-- `produce_labels! "A/B/C.lean⏎D/E.lean"`, with the `!` flag, displays, for each label,
-- the paths that have that label.

-- Finally, if the input string is `"git"`, then `produce_labels "git"`/`produce_labels! "git"`
-- use the output of `git diff --name-only master...HEAD`, instead of literally `"git"`,
-- to show what labels would get assigned to the current modifications.
-- -/
-- elab (name := produceLabelsCmd) tk:"produce_labels" lab:("!")? st:(ppSpace str) : command => do
--   let str := ← if st.getString != "git" then return st.getString else
--     IO.Process.run { cmd := "git", args := #["diff", "--name-only", "origin/master...HEAD"] }
--   let labToFiles := (labelsToFiles str).toArray.qsort (·.1 < ·.1)
--   match lab with
--     | some _ => logInfoAt tk m!"{labToFiles}"
--     | none =>
--       let labels := ((labToFiles.map Prod.fst).filter (· != "unlabeled")).toList
--       if labels.isEmpty then
--         logInfoAt tk m!"No applicable label."
--       else
--         logInfoAt tk m!"Applicable labels: {String.intercalate "," labels}"

-- @[inherit_doc produceLabelsCmd]
-- macro "produce_labels! " st:str : command => `(produce_labels ! $st)

end Label
end AutoLabel

open IO AutoLabel.Label in

unsafe def main : IO Unit := do
  IO.println "[autolabel]: starting…"
  let gitDiff ← IO.Process.run {
    cmd := "git",
    args := #["diff", "--name-only", "origin/master...HEAD"] }
  -- IO.println s!"[autolabel]: {gitDiff}"

  let dirs := (gitDiff.splitOn "\n").toArray
  let labels' := getMatchingLabels dirs |>.toArray.qsort (·.1 < ·.1)
  let labels := ((labels'.map Prod.fst).filter (· != "unlabeled")).toList

  if labels.isEmpty then
    println s!"No applicable label."
  else
    println s!"Applicable labels: {String.intercalate "," labels}"

  IO.println "[autolabel]: done"

  --CoreM.withImportModules #[`Mathlib, `Archive]
  --    (searchPath := compile_time_search_path%) (trustLevel := 1024) do
    -- let decls := (←getEnv).constants
    -- let results ← databases.mapM (fun p => processDb decls p)
    -- if results.any id then
  IO.Process.exit 0

--produce_labels! "git"
