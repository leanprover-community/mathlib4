/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Damiano Testa
-/
import Lean.Elab.Command

/-!
# Automatic labelling of PRs

This file contains the script to automatically assign a GitHub label to a PR.

## Label definition

The mapping from GitHub labels to Mathlib folders is done in this file and
needs to be updated here if necessary:

* `AutoLabel.mathlibLabels` contains an assignment of GitHub labels to folders inside
  the mathlib repository. If no folder is specified, a label like `t-set-theory` will be
  interpreted as matching the folder `"Mathlib" / "SetTheory"`.
* `AutoLabel.mathlibUnlabelled` contains subfolders of `Mathlib/` which are deliberately
  left without topic label.

## lake exe autolabel

`lake exe autolabel` uses `git diff --name-only origin/master...HEAD` to determine which
files have been modified and then finds all labels which should be added based on these changes.
These are printed for testing purposes.

`lake exe autolabel [NUMBER]` will further try to add the applicable labels
to the PR specified. This requires the **GitHub CLI** `gh` to be installed!
Example: `lake exe autolabel 10402` for PR https://github.com/leanprover-community/mathlib4/pull/10402.

For the time being, the script only adds a label if it finds a **single unique label**
which would apply. If multiple labels are found, nothing happens.

## Workflow

There is a mathlib workflow `.github/workflows/add_label_from_diff.yaml` which executes
this script automatically.

Currently it is set to run only one time when a PR is created.

## Tests

Additionally, the script does a few consistency checks:

- it ensures all paths in specified in `AutoLabel.mathlibLabels` exist
- It makes sure all subfolders of `Mathlib/` belong to at least one label.
  There is `AutoLabel.mathlibUnlabelled` to add exceptions for this test.

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
  /-- The label name as it appears on GitHub -/
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
  { label := "t-convex-geometry",
    dirs := #["Mathlib" / "Geometry" / "Convex"] },
  { label := "t-data"
    dirs := #[
      "Mathlib" / "Control",
      "Mathlib" / "Data",] },
  { label := "t-differential-geometry",
    dirs := #["Mathlib" / "Geometry" / "Manifold"] },
  { label := "t-dynamics" },
  { label := "t-euclidean-geometry",
    dirs := #["Mathlib" / "Geometry" / "Euclidean"] },
  { label := "t-geometric-group-theory",
    dirs := #["Mathlib" / "Geometry" / "Group"] },
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
    dirs := #[".github"] },
  { label := "IMO",
    dirs := #["Archive" / "Imo"] },
  { label := "dependency-bump",
    dirs := #["lake-manifest.json"] } ]

/-- Exceptions inside `Mathlib/` which are not covered by any label. -/
def mathlibUnlabelled : Array FilePath := #[
    "Mathlib" / "Deprecated",
    "Mathlib" / "Init",
    "Mathlib" / "Testing",
    "Mathlib" / "Std" ]

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

-- Test targeting a file instead of a directory
#guard getMatchingLabels #["lake-manifest.json"] == #["dependency-bump"]

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

/--
Create a message which GitHub CI parses as annotation and displays at the specified file.

Note: `file` is duplicated below so that it is also visible in the plain text output.

* `type`: "error" or "warning"
* `file`: file where the annotation should be displayed
* `title`: title of the annotation
* `message`: annotation message
-/
def githubAnnotation (type file title message : String) : String :=
  s!"::{type} file={file},title={title}::{file}: {message}"

end AutoLabel

open IO AutoLabel in

/-- `args` is expected to have length 0 or 1, where the first argument is the PR number.

If a PR number is provided, the script requires GitHub CLI `gh` to be installed in order
to add the label to the PR.

## Exit codes:

- `0`: success
- `1`: invalid arguments provided
- `2`: invalid labels defined
- `3`: ~labels do not cover all of `Mathlib/`~ (unused; only emitting warning)
-/
unsafe def main (args : List String): IO UInt32 := do
  if args.length > 1 then
    println s!"::error:: autolabel: invalid number of arguments ({args.length}), \
    expected at most 1. Please run without arguments or provide the target PR's \
    number as a single argument!"
    return 1
  let prNumber? := args[0]?

  -- test: validate that all paths in `mathlibLabels` actually exist
  let mut valid := true
  for label in mathlibLabels do
    for dir in label.dirs do
      unless ← FilePath.pathExists dir do
        -- print github annotation error
        println <| AutoLabel.githubAnnotation "error" "scripts/autolabel.lean"
          s!"Misformatted `{ ``AutoLabel.mathlibLabels }`"
          s!"directory '{dir}' does not exist but is included by label '{label.label}'. \
          Please update `{ ``AutoLabel.mathlibLabels }`!"
        valid := false
    for dir in label.exclusions do
      unless ← FilePath.pathExists dir do
        -- print github annotation error
        println <| AutoLabel.githubAnnotation "error" "scripts/autolabel.lean"
          s!"Misformatted `{ ``AutoLabel.mathlibLabels }`"
          s!"directory '{dir}' does not exist but is excluded by label '{label.label}'. \
          Please update `{ ``AutoLabel.mathlibLabels }`!"
        valid := false
  unless valid do
    return 2

  -- test: validate that the labels cover all of the `Mathlib/` folder
  let notMatchedPaths ← findUncoveredPaths "Mathlib" (exceptions := mathlibUnlabelled)
  if notMatchedPaths.size > 0 then
    -- print github annotation warning
    -- note: only emitting a warning because the workflow is only triggered on the first commit
    -- of a PR and could therefore lead to unexpected behaviour if a folder was created later.
    println <| AutoLabel.githubAnnotation "warning" "scripts/autolabel.lean"
      s!"Incomplete `{ ``AutoLabel.mathlibLabels }`"
      s!"the following paths inside `Mathlib/` are not covered \
      by any label: {notMatchedPaths} Please modify `AutoLabel.mathlibLabels` accordingly!"
    -- return 3

  -- get the modified files
  println "Computing 'git diff --name-only origin/master...HEAD'"
  let gitDiff ← IO.Process.run {
    cmd := "git",
    args := #["diff", "--name-only", "origin/master...HEAD"] }
  println s!"---\n{gitDiff}\n---"
  let modifiedFiles : Array FilePath := (gitDiff.splitOn "\n").toArray.map (⟨·⟩)

  -- find labels covering the modified files
  let labels := getMatchingLabels modifiedFiles

  println s!"::notice::Applicable labels: {labels}"

  match labels with
  | #[] =>
    println s!"::warning::no label to add"
  | #[label] =>
    match prNumber? with
    | some n =>
      let labelsPresent ← IO.Process.run {
        cmd := "gh"
        args := #["pr", "view", n, "--json", "labels", "--jq", ".labels .[] .name"]}
      let labels := labelsPresent.split (· == '\n')
      let autoLabels := mathlibLabels.map (·.label)
      match labels.filter autoLabels.contains with
      | [] => -- if the PR does not have a label that this script could add, then we add a label
        let _ ← IO.Process.run {
          cmd := "gh",
          args := #["pr", "edit", n, "--add-label", label] }
        println s!"::notice::added label: {label}"
      | t_labels_already_present =>
        println s!"::notice::Did not add label '{label}', since {t_labels_already_present} \
                  were already present"
    | none =>
      println s!"::warning::no PR-number provided, not adding labels. \
      (call `lake exe autolabel 150602` to add the labels to PR `150602`)"
  | _ =>
    println s!"::notice::not adding multiple labels: {labels}"
  return 0
