/-
Copyright (c) 2026 Hang Lu Su, Katerina Hristova. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su, Katerina Hristova
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# The Gromov product

The Gromov product of `y` and `z` with respect to `x` in a pseudometric space is
`(y, z)_x = (dist x y + dist x z - dist y z) / 2`.

## Main definitions

* `Metric.gromovProduct x y z`: the Gromov product of `y` and `z` with respect to `x`.

## Tags

Gromov product
-/

@[expose] public section

namespace Metric

variable {X : Type*} [PseudoMetricSpace X]

/-- The Gromov product of `y` and `z` with respect to `x`. -/
noncomputable def gromovProduct (x y z : X) : ℝ := (dist x y + dist x z - dist y z) / 2

lemma gromovProduct_comm (x y z : X) : gromovProduct x y z = gromovProduct x z y := by
  grind [gromovProduct, dist_comm]

lemma gromovProduct_nonneg (x y z : X) : 0 ≤ gromovProduct x y z := by
  grind [gromovProduct, dist_triangle_left y z x]

lemma gromovProduct_le_dist_left (x y z : X) : gromovProduct x y z ≤ dist x y := by
  grind [gromovProduct, dist_triangle x y z]

lemma gromovProduct_le_dist_right (x y z : X) : gromovProduct x y z ≤ dist x z := by
  rw [gromovProduct_comm]
  exact gromovProduct_le_dist_left x z y

@[simp]
lemma gromovProduct_self_left (x y : X) : gromovProduct x x y = 0 := by
  simp [gromovProduct]

@[simp]
lemma gromovProduct_self_right (x y : X) : gromovProduct x y x = 0 := by
  simp [gromovProduct, dist_comm]

@[simp]
lemma gromovProduct_self_centre (x y : X) : gromovProduct x y y = dist x y := by
  simp [gromovProduct]

@[simp]
lemma gromovProduct_add_gromovProduct (x y z : X) : gromovProduct x y z + gromovProduct z y x =
    dist x z := by
  grind [gromovProduct, dist_comm]

end Metric
