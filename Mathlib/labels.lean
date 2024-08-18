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

/--
info: label: t-algebra
dirs: [Mathlib/Algebra/,
 Mathlib/FieldTheory/,
 Mathlib/RingTheory/,
 Mathlib/GroupTheory/,
 Mathlib/RepresentationTheory/,
 Mathlib/LinearAlgebra/]
exclusions: []
---
info: label: t-algebraic-geometry
dirs: [Mathlib/AlgebraicGeometry/, Mathlib/Geometry/RingedSpace/]
exclusions: []
---
info: label: t-analysis
dirs: [Mathlib/Analysis/]
exclusions: []
---
info: label: t-category-theory
dirs: [Mathlib/CategoryTheory/]
exclusions: []
---
info: label: t-combinatorics
dirs: [Mathlib/Combinatorics/]
exclusions: []
---
info: label: t-computability
dirs: [Mathlib/Computability/]
exclusions: []
---
info: label: t-condensed
dirs: [Mathlib/Condensed/]
exclusions: []
---
info: label: t-data
dirs: [Mathlib/Data/]
exclusions: []
---
info: label: t-differential-geometry
dirs: [Mathlib/Geometry/Manifold/]
exclusions: []
---
info: label: t-dynamics
dirs: [Mathlib/Dynamics/]
exclusions: []
---
info: label: t-euclidean-geometry
dirs: [Mathlib/Geometry/Euclidean/]
exclusions: []
---
info: label: t-linter
dirs: [Mathlib/Tactic/Linter/]
exclusions: []
---
info: label: t-logic
dirs: [Mathlib/Logic/, Mathlib/ModelTheory/]
exclusions: []
---
info: label: t-measure-probability
dirs: [Mathlib/MeasureTheory/, Mathlib/Probability/, Mathlib/InformationTheory/]
exclusions: []
---
info: label: t-meta
dirs: [Mathlib/Tactic/]
exclusions: [Mathlib/Tactic/Linter/]
---
info: label: t-number-theory
dirs: [Mathlib/NumberTheory/]
exclusions: []
---
info: label: t-order
dirs: [Mathlib/Order/]
exclusions: []
---
info: label: t-set-theory
dirs: [Mathlib/SetTheory/]
exclusions: []
---
info: label: t-topology
dirs: [Mathlib/Topology/, Mathlib/AlgebraicTopology/]
exclusions: []
-/
#guard_msgs in
check_labels "t-"

/--
info: label: t-meta
dirs: [Mathlib/Tactic/]
exclusions: [Mathlib/Tactic/Linter/]
-/
#guard_msgs in
check_labels "t-met"

/-- info: [t-algebra, t-algebraic-geometry, t-linter, t-meta, t-set-theory] -/
#guard_msgs in
produce_labels "Mathlib/SetTheory/Ordinals/Basic.lean
Mathlib/SetTheory/Ordinals/Basic.lean
Mathlib/AlgebraicGeometry/Ordinals/Basic.lean
Mathlib/Algebra/Ordinals/Basic.lean
Mathlib/Tactic/Linarith/Basic.lean
Mathlib/Tactic/Linter/Basic.lean
Mathlib/Tactic/Linter/AnotherOne.lean
Mathlib/Tactic/MoreTactics/Basic.lean

"

/--
info:
[(t-algebra, [Mathlib/Algebra/Ordinals/Basic.lean]),
 (t-algebraic-geometry, [Mathlib/AlgebraicGeometry/Ordinals/Basic.lean]),
 (t-linter, [Mathlib/Tactic/Linter/Basic.lean, Mathlib/Tactic/Linter/AnotherOne.lean]),
 (t-meta, [Mathlib/Tactic/Linarith/Basic.lean, Mathlib/Tactic/MoreTactics/Basic.lean]),
 (t-set-theory, [Mathlib/SetTheory/Ordinals/Basic.lean, Mathlib/SetTheory/Ordinals/Basic.lean])]
-/
#guard_msgs in
produce_labels! "Mathlib/SetTheory/Ordinals/Basic.lean
Mathlib/SetTheory/Ordinals/Basic.lean
Mathlib/AlgebraicGeometry/Ordinals/Basic.lean
Mathlib/Algebra/Ordinals/Basic.lean
Mathlib/Tactic/Linarith/Basic.lean
Mathlib/Tactic/Linter/Basic.lean
Mathlib/Tactic/Linter/AnotherOne.lean
Mathlib/Tactic/MoreTactics/Basic.lean

"
/-- info: [t-linter, t-set-theory] -/
#guard_msgs in
produce_labels "Mathlib/SetTheory/Ordinals/Basic.lean
Mathlib/Tactic/Linter/Basic.lean"

/-- info: [t-meta, t-set-theory] -/
#guard_msgs in
produce_labels "Mathlib/SetTheory/Ordinals/Basic.lean
Mathlib/Tactic/Linarith/Basic.lean"

produce_labels! "git"

open Lean Elab.Command in
/-- `run_cmd outputLabels` examines the diff with master and reports the appropriate labels. -/
def outputLabels : CommandElabM Unit := do
  let gitArgs := #["diff", "--name-only", "master...HEAD"]
  let out ← IO.Process.run { cmd := "git", args := gitArgs }
  let labels := produceLabels (← getEnv) out
  let csLabs := String.intercalate "," labels.toList
  dbg_trace csLabs

/-remove me during CI
run_cmd outputLabels
--/
end AutoLabel.Label
