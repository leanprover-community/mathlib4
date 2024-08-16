/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.autolabel

/-!
Add all the label and the script.
-/

namespace AutoLabel.Label

add_label algebra dirs: Algebra FieldTheory RingTheory GroupTheory RepresentationTheory LinearAlgebra
add_label algebraic_geometry dirs: AlgebraicGeometry Geometry.RingedSpace
add_label analysis
add_label category_theory
add_label combinatorics
add_label computability
add_label condensed
add_label data
add_label differential_geometry dirs: Geometry.Manifold
add_label dynamics
add_label euclidean_geometry dirs: Geometry.Euclidean
add_label linter dirs: Tactic.Linter
add_label logic dirs: Logic ModelTheory
add_label measure_probability dirs: MeasureTheory Probability InformationTheory
add_label meta dirs: Tactic exclusions: Tactic.Linter
add_label number_theory
add_label order
add_label set_theory
add_label topology dirs: Topology AlgebraicTopology

--check_labels

/-- info: [t-algebra, t-algebraic-geometry, t-linter, t-meta, t-set-theory] -/
#guard_msgs in
produce_labels "Mathlib/SetTheory/Ordinals/Basic.lean
Mathlib/SetTheory/Ordinals/Basic.lean
Mathlib/AlgebraicGeometry/Ordinals/Basic.lean
Mathlib/Algebra/Ordinals/Basic.lean
Mathlib/Tactic/Linarith/Basic.lean
Mathlib/Tactic/Linter/Basic.lean

"

/-- info: [t-linter, t-set-theory] -/
#guard_msgs in
produce_labels "Mathlib/SetTheory/Ordinals/Basic.lean
Mathlib/Tactic/Linter/Basic.lean"

/-- info: [t-meta, t-set-theory] -/
#guard_msgs in
produce_labels "Mathlib/SetTheory/Ordinals/Basic.lean
Mathlib/Tactic/Linarith/Basic.lean"

open Lean Elab
run_cmd
  let out ← IO.Process.run { cmd := "git", args := #["diff", "--name-only", "master"] }
--  dbg_trace out
  let labels := produceLabels (← getEnv) out
  let number := 15849
  let csLabs := String.intercalate "," labels.toList
  --dbg_trace (s!"gh issue edit {number} '" ++ (String.intercalate "," labels.toList).push '\'')
  let gh : IO.Process.SpawnArgs := {
    cmd := "gh"
-- gh issue edit "$NUMBER" --add-label "$LABELS"
    args := #["issue", "edit", s!"{number}", "--add-label", csLabs] }
  --IO.Process.run gh
end AutoLabel.Label
