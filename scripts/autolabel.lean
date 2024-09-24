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
* The `label` field is the actual GitHub label.
* The `dirs` field is the array of all "root paths" such that a modification in a file contained
  in one of these paths should be labeled by `label`.
* The `exclusions` field is the array of all "root paths" that are excluded, among the
  ones that start with the ones in `dirs`.
-/
structure Label where
  /-- The label name as it appears on github -/
  label : String
  /-- Array of paths which fall under this label. e.g. `"Mathlib" / "Algebra"` -/
  dirs : Array FilePath
  /-- Array of (sub)-paths which should be excluded -/
  exclusions : Array FilePath := #[]
  deriving BEq, Hashable

/--
Mathlib Labels and their corresponding folders. Add new labels and folders here!
-/
def mathlibLabels : Array Label := #[
  { label := "t-algebra",
    dirs :=
      #[{ toString := "Mathlib" } / { toString := "FieldTheory" },
        { toString := "Mathlib" } / { toString := " RingTheory" },
        { toString := "Mathlib" } / { toString := "GroupTheory" },
        { toString := "Mathlib" } / { toString := "RepresentationTheory" },
        { toString := "Mathlib" } / { toString := "LinearAlgebra" }] },
  { label := "t-algebraic-geometry",
    dirs :=
      #[{ toString := "Mathlib" } / { toString := "AlgebraicGeometry" },
        { toString := "Mathlib" } / { toString := "Geometry.RingedSpace" }] },
  { label := "t-analysis",
    dirs :=
      #[{ toString := "Mathlib" } / { toString := "Analysis" }] },
  { label := "t-category-theory",
    dirs :=
      #[{ toString := "Mathlib" } / { toString := "CategoryTheory" }] },
  { label := "t-combinatorics",
    dirs :=
      #[{ toString := "Mathlib" } / { toString := "Combinatorics" }] },
  { label := "t-computability",
    dirs :=
      #[{ toString := "Mathlib" } / { toString := "Computability" }] },
  { label := "t-condensed",
    dirs :=
      #[{ toString := "Mathlib" } / { toString := "Condensed" }] },
  { label := "t-data",
    dirs :=
      #[{ toString := "Mathlib" } / { toString := "Data" }] },
  { label := "t-differential-geometry",
    dirs :=
      #[{ toString := "Mathlib" } / { toString := "DifferentialGeometry" },
        { toString := "Mathlib" } / { toString := "Geometry" } / { toString := "Manifold" }] },
  { label := "t-dynamics",
    dirs :=
      #[{ toString := "Mathlib" } / { toString := "Dynamics" }] },
  { label := "t-euclidean-geometry",
    dirs :=
      #[{ toString := "Mathlib" } / { toString := "Geometry" } / { toString := "Euclidean" }] },
  { label := "t-linter",
    dirs :=
      #[{ toString := "Mathlib" } / { toString := "Tactic" } / { toString := "Linter" }] },
  { label := "t-logic",
    dirs :=
      #[{ toString := "Mathlib" } / { toString := "Logic" },
        { toString := "Mathlib" } / { toString := "ModelTheory" }] },
  { label := "t-measure-probability",
    dirs :=
      #[{ toString := "Mathlib" } / { toString := "MeasureTheory" },
        { toString := "Mathlib" } / { toString := "Probability" },
        { toString := "Mathlib" } / { toString := "InformationTheory" }] },
  { label := "t-meta",
    dirs :=
      #[{ toString := "Mathlib" } / { toString := "Tactic" }],
    exclusions :=
      #[{ toString := "Mathlib" } / { toString := "Tactic" } / { toString := "Linter" }] },
  { label := "t-number-theory",
    dirs :=
      #[{ toString := "Mathlib" } / { toString := "NumberTheory" }] },
  { label := "t-order",
    dirs :=
      #[{ toString := "Mathlib" } / { toString := "Order" }] },
  { label := "t-set-theory",
    dirs :=
      #[{ toString := "Mathlib" } / { toString := "SetTheory" }] },
  { label := "t-topology",
    dirs :=
      #[{ toString := "Mathlib" } / { toString := "Topology" },
        { toString := "Mathlib" } / { toString := "AlgebraicTopology" }] },
  { label := "CI",
    dirs :=
      #[{ toString := ".github" } / { toString := "workflows" }] }]


#print mathlibLabels

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
