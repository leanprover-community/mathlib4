/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Geometry.Euclidean.Altitude

/-!
# Volume of a simplex

This file defines the volume of a simplex as `Affine.Simplex.volume`. It is kept thin and all lemmas
are put to `Mathlib.Geometry.Euclidean.Volume.MeasureSimplex` (for connection to the volume measure)
and `Mathlib.Geometry.Euclidean.Volume.Basic` (for lemmas outside of measure theory).
-/

@[expose] public section

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- The volume of a `n`-dimensional simplex, internally defined using base-and-height formula
from the 0-th vertex.

See also:
* `Affine.Simplex.volume_eq_euclideanHausdorffMeasure_real_closedInterior` for connection between
  the defintion and the volume measure.
* `Affine.Simplex.volume_eq` for base-and-height formula from any vertex. -/
noncomputable
def Affine.Simplex.volume {n : ℕ} (s : Simplex ℝ P n) : ℝ := match n with
| 0 => 1
| n + 1 => (↑(n + 1))⁻¹ * s.height 0 * (s.faceOpposite 0).volume
