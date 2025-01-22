/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.RingTheory.Ideal.Basic

/-! # Topologicall nilpotent elements -/

open Filter

open scoped Topology

/-- An element is topologically nilpotent if its powers converge to `0`. -/
def IsTopologicallyNilpotent
    {R : Type*} [MonoidWithZero R] [TopologicalSpace R] (a : R) : Prop :=
  Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0)

namespace IsTopologicallyNilpotent

variable {R S : Type*} [TopologicalSpace R] [TopologicalSpace S]

theorem map [MonoidWithZero R] [MonoidWithZero S]
    {φ : R →*₀ S} (hφ : Continuous φ) {a : R} (ha : IsTopologicallyNilpotent a) :
    IsTopologicallyNilpotent (φ a) := by
  unfold IsTopologicallyNilpotent at ha ⊢
  simp_rw [← map_pow]
  exact (map_zero φ ▸  hφ.tendsto 0).comp ha

theorem zero [MonoidWithZero R] :
    IsTopologicallyNilpotent (0 : R) := tendsto_atTop_of_eventually_const (i₀ := 1)
    (fun _ hi => by rw [zero_pow (Nat.ne_zero_iff_zero_lt.mpr hi)])

end IsTopologicallyNilpotent
