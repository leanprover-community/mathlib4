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

Let `R` be a commutative ring with a linear topology.

* `IsTopologicallyNilpotent.mul_left`: if `a : R` is topologically nilpotent,
then `a*b` is topologically nilpotent.

* `IsTopologicallyNilpotent.mul_right`: if `a : R` is topologically nilpotent,
then `a * b` is topologically nilpotent.

* `IsTopologicallyNilpotent.add`: if `a b : R` are topologically nilpotent,
then `a + b` is topologically nilpotent.

-/

open Filter

open scoped Topology

/-- An element is topologically nilpotent if its powers converge to `0`. -/
def IsTopologicallyNilpotent
    {R : Type*} [MonoidWithZero R] [TopologicalSpace R] (a : R) : Prop :=
  Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0)

namespace IsTopologicallyNilpotent

section MonoidWithZero

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

end MonoidWithZero

-- TODO : Ring, under commutation property

section CommRing

variable {R : Type*} [TopologicalSpace R] [CommRing R] [IsLinearTopology R R]

/-- If `a` is topologically nilpotent, then `a * b` is topologically nilpotent. -/
theorem mul_right {a : R} (ha : IsTopologicallyNilpotent a) (b : R) :
    IsTopologicallyNilpotent (a * b) := by
  intro v hv
  rw [IsLinearTopology.hasBasis_ideal.mem_iff] at hv
  rcases hv with ⟨I, I_mem_nhds, I_subset⟩
  specialize ha I_mem_nhds
  simp only [mem_map, mem_atTop_sets, ge_iff_le, Set.mem_preimage, SetLike.mem_coe] at ha ⊢
  rcases ha with ⟨n, ha⟩
  use n
  intro m hm
  rw [mul_pow]
  exact  I_subset (I.mul_mem_right _ (ha m hm))

/-- If `b` is topologically nilpotent, then `a * b` is topologically nilpotent. -/
 theorem mul_left (a : R) {b : R} (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a * b) :=
  mul_comm a b ▸ mul_right hb a

/-- If `a` and `b` are topologically nilpotent, then `a + b` is topologically nilpotent. -/
theorem add {a b : R} (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a + b) := by
  intro v hv
  rw [IsLinearTopology.hasBasis_ideal.mem_iff] at hv
  rcases hv with ⟨I, I_mem_nhds, I_subset⟩
  specialize ha I_mem_nhds
  specialize hb I_mem_nhds
  simp only [mem_map, mem_atTop_sets, ge_iff_le, Set.mem_preimage, SetLike.mem_coe] at ha hb ⊢
  rcases ha with ⟨na, ha⟩
  rcases hb with ⟨nb, hb⟩
  exact ⟨na + nb, fun m hm ↦
    I_subset (I.add_pow_mem_of_pow_mem_of_le (ha na le_rfl) (hb nb le_rfl)
      (le_trans hm (Nat.le_add_right _ _)))⟩

end CommRing

end IsTopologicallyNilpotent
