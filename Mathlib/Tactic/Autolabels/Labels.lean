/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Tactic.Autolabels.EnvExtension

/-!
# Autolabels

This file contains the labels that the PR auto-labelling script uses.
-/

namespace AutoLabel.Label

add_label algebra dirs:
  Algebra FieldTheory RingTheory GroupTheory RepresentationTheory LinearAlgebra
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

end AutoLabel.Label
