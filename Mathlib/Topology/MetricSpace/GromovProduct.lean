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

## Implementation notes

We intentionally omit grind tags which would introduce `dist` terms in general proofs about
`gromovProduct`, to avoid introducing the dist-theory.
In proofs where it is useful to convert `gromovProduct` to a `dist`, users should feel free to add
the relevant lemmas to the `grind [...]` list in an application.
-/

public section

namespace Metric

variable {X : Type*} [PseudoMetricSpace X] (x y z : X)

/-- The Gromov product of `y` and `z` with respect to `x`. -/
noncomputable def gromovProduct : ℝ := (dist x y + dist x z - dist y z) / 2

lemma gromovProduct_eq : gromovProduct x y z = (dist x y + dist x z - dist y z) / 2 := by rfl

lemma gromovProduct_comm : gromovProduct x y z = gromovProduct x z y := by
  grind [gromovProduct_eq, dist_comm]

grind_pattern gromovProduct_comm => gromovProduct x y z where y =/= z

@[grind! .]
lemma gromovProduct_nonneg : 0 ≤ gromovProduct x y z := by
  grind [gromovProduct_eq, dist_triangle_left y z x]

lemma gromovProduct_le_dist_left : gromovProduct x y z ≤ dist x y := by
  grind [gromovProduct_eq, dist_triangle x y z]

lemma gromovProduct_le_dist_right : gromovProduct x y z ≤ dist x z := by
  grind [gromovProduct_le_dist_left]

@[simp, grind =]
lemma gromovProduct_self_left : gromovProduct x x y = 0 := by
  simp [gromovProduct_eq]

@[simp, grind =]
lemma gromovProduct_self_right : gromovProduct x y x = 0 := by
  simp [gromovProduct_eq, dist_comm]

@[simp]
lemma gromovProduct_self : gromovProduct x y y = dist x y := by
  simp [gromovProduct_eq]

lemma gromovProduct_add_gromovProduct₁₃ : gromovProduct x y z + gromovProduct z y x = dist x z := by
  grind [gromovProduct_eq, dist_comm]

lemma gromovProduct_add_gromovProduct₁₂ : gromovProduct x y z + gromovProduct y x z = dist x y := by
  grind [gromovProduct_eq, dist_comm]

end Metric
