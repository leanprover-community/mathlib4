/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Damiano Testa
-/
import Lean.Elab.Command

/-!
# Automatic labelling of PRs

This file contains the script to automatically assign a GitHub label to a PR.

`AutoLabel.mathlibLabels` contains an assignment of github labels to folders inside
the mathlib repository. The script uses `git diff` to determine which files
a PR modifies and then finds all labels that should be added based on these changes.

For the time being, the script only adds a label if it finds a single unique label
that would apply. If multiple labels are found, nothing happens.

## Tests

Additionally, the script does a few consistency checks:

- it ensures all paths in specified in `AutoLabel.mathlibLabels` exist
- It makes sure all subfolders of `Mathlib/` belong to at least one label.
  there is `AutoLabel.mathlibUnlabelled` to add exceptions for this test.

-/

open Lean System

namespace AutoLabel

/--
A `Label` consists of the
* The `label` field is the actual GitHub label name.
* The `dirs` field is the array of all "root paths" such that a modification in a file contained
  in one of these paths should be labelled with `label`.
* The `exclusions` field is the array of all "root paths" that are excluded, among the
  ones that start with the ones in `dirs`.
  Any modifications to a file in an excluded path is ignored for the purposes of labelling.
-/
structure Label where
  /-- The label name as it appears on github -/
  label : String
  /-- Array of paths which fall under this label. e.g. `"Mathlib" / "Algebra"`.

  For a label of the form `t-set-theory` this defaults to `#["Mathlib" / "SetTheory"]`. -/
  dirs : Array FilePath := if label.startsWith "t-" then
      #["Mathlib" / ("".intercalate (label.splitOn "-" |>.drop 1 |>.map .capitalize))]
    else #[]
  /-- Array of paths which should be excluded.
  Any modifications to a file in an excluded path are ignored for the purposes of labelling. -/
  exclusions : Array FilePath := #[]
  deriving BEq, Hashable

/--
Mathlib labels and their corresponding folders. Add new labels and folders here!
-/
def mathlibLabels : Array Label := #[
  { label := "t-algebra",
    dirs := #[
      "Mathlib" / "Algebra",
      "Mathlib" / "FieldTheory",
      "Mathlib" / "RingTheory",
      "Mathlib" / "GroupTheory",
      "Mathlib" / "RepresentationTheory",
      "Mathlib" / "LinearAlgebra"] },
  { label := "t-algebraic-geometry",
    dirs := #[
      "Mathlib" / "AlgebraicGeometry",
      "Mathlib" / "Geometry" / "RingedSpace"] },
  { label := "t-analysis" },
  { label := "t-category-theory" },
  { label := "t-combinatorics" },
  { label := "t-computability" },
  { label := "t-condensed" },
  { label := "t-data" },
  { label := "t-differential-geometry",
    dirs := #["Mathlib" / "Geometry" / "Manifold"] },
  { label := "t-dynamics" },
  { label := "t-euclidean-geometry",
    dirs := #["Mathlib" / "Geometry" / "Euclidean"] },
  { label := "t-linter",
    dirs := #["Mathlib" / "Tactic" / "Linter"] },
  { label := "t-logic",
    dirs := #[
      "Mathlib" / "Logic",
      "Mathlib" / "ModelTheory"] },
  { label := "t-measure-probability",
    dirs := #[
      "Mathlib" / "MeasureTheory",
      "Mathlib" / "Probability",
      "Mathlib" / "InformationTheory"] },
  { label := "t-meta",
    dirs := #[
      "Mathlib" / "Control",
      "Mathlib" / "Lean",
      "Mathlib" / "Mathport",
      "Mathlib" / "Tactic",
      "Mathlib" / "Util"],
    exclusions := #["Mathlib" / "Tactic" / "Linter"] },
  { label := "t-number-theory" },
  { label := "t-order" },
  { label := "t-set-theory" },
  { label := "t-topology",
    dirs := #[
      "Mathlib" / "Topology",
      "Mathlib" / "AlgebraicTopology"] },
  { label := "CI",
    dirs := #[".github" / "workflows"] },
  { label := "IMO",
    dirs := #["Archive" / "Imo"] } ]

/-- Exceptions inside `Mathlib/` which are not covered by any label. -/
def mathlibUnlabelled : Array FilePath := #[
    "Mathlib" / "Deprecated",
    "Mathlib" / "Init",
    "Mathlib" / "Testing" ]

/-- Checks if the folder `path` lies inside the folder `dir`. -/
def _root_.System.FilePath.isPrefixOf (dir path : FilePath) : Bool :=
  -- use `dir / ""` to prevent partial matching of folder names
  (dir / "").normalize.toString.isPrefixOf (path / "").normalize.toString

/--
Return all names of labels in `mathlibLabels` which match
at least one of the `files`.

* `files`: array of relative paths starting from the mathlib root directory.
-/
def getMatchingLabels (files : Array FilePath) : Array String :=
  let applicable := mathlibLabels.filter fun label ↦
    -- first exclude all files the label excludes,
    -- then see if any file remains included by the label
    let notExcludedFiles := files.filter fun file ↦
      label.exclusions.all (!·.isPrefixOf file)
    label.dirs.any (fun dir ↦ notExcludedFiles.any (dir.isPrefixOf ·))
  -- return sorted list of label names
  applicable.map (·.label) |>.qsort (· < ·)

/-!
Testing the functionality of the declarations defined in this script
-/
section Tests

-- Test `FilePath.isPrefixOf`
#guard ("Mathlib" / "Algebra" : FilePath).isPrefixOf ("Mathlib" / "Algebra" / "Basic.lean")

-- Test `FilePath.isPrefixOf` does not trigger on partial prefixes
#guard ! ("Mathlib" / "Algebra" : FilePath).isPrefixOf ("Mathlib" / "AlgebraicGeometry")

#guard getMatchingLabels #[] == #[]
-- Test default value for `label.dirs` works
#guard getMatchingLabels #["Mathlib" / "SetTheory" / "ZFC"] == #["t-set-theory"]
-- Test exclusion
#guard getMatchingLabels #["Mathlib" / "Tactic"/ "Abel.lean"] == #["t-meta"]
#guard getMatchingLabels #["Mathlib" / "Tactic"/ "Linter" / "Lint.lean"] == #["t-linter"]
#guard getMatchingLabels #[
  "Mathlib" / "Tactic"/ "Linter" / "Lint.lean",
  "Mathlib" / "Tactic" / "Abel.lean" ] == #["t-linter", "t-meta"]

/-- Testing function to ensure the labels defined in `mathlibLabels` cover all
subfolders of `Mathlib/`. -/
partial def findUncoveredPaths (path : FilePath) (exceptions : Array FilePath := #[]) :
    IO <| Array FilePath := do
  let mut notMatched : Array FilePath := #[]
  -- all directories inside `path`
  let subDirs ← (← path.readDir).map (·.path) |>.filterM (do FilePath.isDir ·)
  for dir in subDirs do
    -- if the sub directory is not matched by a label,
    -- we go recursively into it
    if (getMatchingLabels #[dir]).size == 0 then
      notMatched := notMatched ++ (← findUncoveredPaths dir exceptions)
  -- a directory should be flagged if none of its sub-directories is matched by a label
  -- note: we assume here the base directory, i.e. "Mathlib" is never matched by a label,
  -- therefore we skip this test.
  if notMatched.size == subDirs.size then
    if exceptions.contains path then
      return #[]
    else
      return #[path]
  else
    return notMatched

end Tests

end AutoLabel

open IO AutoLabel in

/-- `args` is expected to have length 1, and the first argument is the PR number.

## Exit codes:

- `0`: success
- `1`: invalid arguments provided
- `2`: invalid labels defined
- `3`: labels do not cover all of `Mathlib/`
-/
unsafe def main (args : List String): IO Unit := do
  if args.length > 1 then
    println s!"autolabel: invalid number of arguments ({args.length}). Please run without \
    arguments or provide the target PR's number as single argument!"
    IO.Process.exit 1
  let prNumber? := args[0]?

  -- test: validate that all paths in `mathlibLabels` actually exist
  let mut valid := true
  for label in mathlibLabels do
    for dir in label.dirs do
      unless ← FilePath.pathExists dir do
        println s!"error: directory {dir} does not exist! (from label {label.label})"
        valid := false
    for dir in label.exclusions do
      unless ← FilePath.pathExists dir do
        println s!"error: excluded directory {dir} does not exist! (from label {label.label})"
        valid := false
  unless valid do
    IO.Process.exit 2

  -- test: validate that the labels cover all of the `Mathlib/` folder
  let notMatchedPaths ← findUncoveredPaths "Mathlib" (exceptions := mathlibUnlabelled)
  if notMatchedPaths.size > 0 then
    println s!"error: the following paths inside `Mathlib/` are not covered \
    by any label:\n\n{notMatchedPaths}\n\nPlease modify `mathlibLabels` in \
    `scripts/autolabel.lean` accordingly!"
    IO.Process.exit 3

  -- get the modified files
  let gitDiff ← IO.Process.run {
    cmd := "git",
    args := #["diff", "--name-only", "origin/master...HEAD"] }
  let modifiedFiles : Array FilePath := (gitDiff.splitOn "\n").toArray.map (⟨·⟩)

  -- find labels covering the modified files
  let labels := getMatchingLabels modifiedFiles

  match labels with
  | #[] =>
    println s!"No applicable labels found!"
  | #[label] =>
    println s!"Exactly one label found: {label}"
    match prNumber? with
    | some n =>
      let _ ← IO.Process.run {
        cmd := "gh",
        args := #["pr", "edit", n, "--add-label", label] }
      println s!"Added label: {label}"
    | none =>
      println s!"No PR-number provided, skipping adding labels. \
      (call `lake exe autolabel 150602` to add the labels to PR `150602`)"
  | labels =>
    println s!"Multiple labels found: {labels}"
    println s!"Not adding any label."
  IO.Process.exit 0
