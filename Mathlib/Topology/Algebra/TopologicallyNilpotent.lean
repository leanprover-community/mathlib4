/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.RingTheory.Ideal.Basic

/-! # Topologically nilpotent elements

Let `M` be a monoid with zero `M`, endowed with a topology.

* `IsTopologicallyNilpotent a` says that `a : M` is *topologically nilpotent*,
ie, its powers converge to zero.

* `IsTopologicallyNilpotent.map`:
The image of a topologically nilpotent element under a continuous morphism of
monoids with zero endowed with a topology is topologically nilpotent.

* `IsTopologicallyNilpotent.zero`: `0` is topologically nilpotent.
-/

open Filter

open scoped Topology

/-- In a monoid with zero endowed with a topology,
  an element is topologically nilpotent if its powers converge to `0`. -/
def IsTopologicallyNilpotent
    {R : Type*} [MonoidWithZero R] [TopologicalSpace R] (a : R) : Prop :=
  Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0)

namespace IsTopologicallyNilpotent

variable {R S : Type*} [TopologicalSpace R] [MonoidWithZero R]
  [MonoidWithZero S] [TopologicalSpace S]

/-- The image of a topologically nilpotent element under a continuous morphism
  is topologically nilpotent -/
theorem map {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S]
    {φ : F} (hφ : Continuous φ) {a : R} (ha : IsTopologicallyNilpotent a) :
    IsTopologicallyNilpotent (φ a) := by
  unfold IsTopologicallyNilpotent at ha ⊢
  simp_rw [← map_pow]
  exact (map_zero φ ▸  hφ.tendsto 0).comp ha

/-- `0` is topologically nilpotent -/
theorem zero :
    IsTopologicallyNilpotent (0 : R) := tendsto_atTop_of_eventually_const (i₀ := 1)
    (fun _ hi => by rw [zero_pow (Nat.ne_zero_iff_zero_lt.mpr hi)])

end IsTopologicallyNilpotent
