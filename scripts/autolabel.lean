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
the mathlib repository. The sctript uses `git diff` to determine which files
a PR modifies and then finds all labels that should be added based on these changes.

For the time being, the script only adds a label if it finds a single unique label
that would apply. If multiple labels are found, nothing happens.
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
  /-- Array of paths which fall under this label. e.g. `"Mathlib" / "Algebra"` -/
  dirs : Array FilePath
  /-- Array of paths which should be excluded.
  Any modifications to a file in an excluded path is ignored for the purposes of labelling. -/
  exclusions : Array FilePath := #[]
  deriving BEq, Hashable

/--
Mathlib Labels and their corresponding folders. Add new labels and folders here!
-/
def mathlibLabels : Array Label := #[
  { label := "t-algebra",
    dirs := #[
      "Mathlib" / "FieldTheory",
      "Mathlib" / " RingTheory",
      "Mathlib" / "GroupTheory",
      "Mathlib" / "RepresentationTheory",
      "Mathlib" / "LinearAlgebra"] },
  { label := "t-algebraic-geometry",
    dirs := #[
      "Mathlib" / "AlgebraicGeometry",
      "Mathlib" / "Geometry" / "RingedSpace"] },
  { label := "t-analysis",
    dirs := #["Mathlib" / "Analysis"] },
  { label := "t-category-theory",
    dirs := #["Mathlib" / "CategoryTheory"] },
  { label := "t-combinatorics",
    dirs := #["Mathlib" / "Combinatorics"] },
  { label := "t-computability",
    dirs := #["Mathlib" / "Computability"] },
  { label := "t-condensed",
    dirs := #["Mathlib" / "Condensed"] },
  { label := "t-data",
    dirs := #["Mathlib" / "Data"] },
  { label := "t-differential-geometry",
    dirs := #["Mathlib" / "Geometry" / "Manifold"] },
  { label := "t-dynamics",
    dirs := #["Mathlib" / "Dynamics"] },
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
    dirs := #["Mathlib" / "Tactic"],
    exclusions := #["Mathlib" / "Tactic" / "Linter"] },
  { label := "t-number-theory",
    dirs := #["Mathlib" / "NumberTheory"] },
  { label := "t-order",
    dirs := #["Mathlib" / "Order"] },
  { label := "t-set-theory",
    dirs := #["Mathlib" / "SetTheory"] },
  { label := "t-topology",
    dirs := #[
      "Mathlib" / "Topology",
      "Mathlib" / "AlgebraicTopology"] },
  { label := "CI",
    dirs := #[".github" / "workflows"] }]

/--
Return all labels from `mathlibLabels` which are matching at least one of the `files`.

* `files`: array of relative paths starting from the mathlib project directory.
-/
def getMatchingLabels (files : Array FilePath) : Array Label :=
  mathlibLabels.filter fun label =>
    -- modified files which are not excluded by the label
    let notExcludedFiles := files.filter fun file =>
      label.exclusions.map (!·.toString.isPrefixOf file.toString) |>.all (·)

    -- return `true` if any of the label's dirs prefixes any of the modified files.
    label.dirs.map (fun dir =>
      notExcludedFiles.map (dir.toString.isPrefixOf ·.toString) |>.any (·)) |>.any (·)

end AutoLabel

open IO AutoLabel in

/-- `args` is expected to have length 1, and the first argument is the PR number. -/
unsafe def main (args : List String): IO Unit := do
  let prNumber? := args[0]?
  let gitDiff ← IO.Process.run {
    cmd := "git",
    args := #["diff", "--name-only", "origin/master...HEAD"] }

  let modifiedFiles : Array FilePath := (gitDiff.splitOn "\n").toArray.map (⟨·⟩)
  let labels := getMatchingLabels modifiedFiles |>.map (·.label) |>.qsort (· < ·)

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
