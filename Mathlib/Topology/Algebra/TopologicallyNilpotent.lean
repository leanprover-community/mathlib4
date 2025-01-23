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
  exact (map_zero φ ▸ hφ.tendsto 0).comp ha

/-- `0` is topologically nilpotent -/
theorem zero : IsTopologicallyNilpotent (0 : R) :=
  tendsto_atTop_of_eventually_const (i₀ := 1)
    (fun _ hi => by rw [zero_pow (Nat.ne_zero_iff_zero_lt.mpr hi)])

theorem exists_pow_mem_of_mem_nhds {a : R} (ha : IsTopologicallyNilpotent a)
    {v : Set R} (hv : v ∈ 𝓝 0) :
    ∃ n, a ^ n ∈ v := by
  specialize ha hv
  simp only [mem_map, mem_atTop_sets, ge_iff_le, Set.mem_preimage] at ha
  obtain ⟨n, hn⟩ := ha
  exact ⟨n, hn n (le_refl n)⟩

end MonoidWithZero

section Ring

variable {R : Type*} [TopologicalSpace R] [Ring R]

/-- If `a` and `b` commute and `a` is topologically nilpotent,
  then `a * b` is topologically nilpotent. -/
theorem mul_right_of_commute [IsLinearTopology Rᵐᵒᵖ R]
    {a b : R} (ha : IsTopologicallyNilpotent a) (hab : Commute a b) :
    IsTopologicallyNilpotent (a * b) := by
  intro v hv
  rw [(IsLinearTopology.hasBasis_submodule Rᵐᵒᵖ).mem_iff] at hv
  rcases hv with ⟨I, I_mem_nhds, I_subset⟩
  specialize ha I_mem_nhds
  simp only [mem_map, mem_atTop_sets, ge_iff_le, Set.mem_preimage, SetLike.mem_coe] at ha ⊢
  rcases ha with ⟨n, ha⟩
  use n
  intro m hm
  rw [hab.mul_pow]
  exact I_subset (I.smul_mem _ (ha m hm))

/-- If `a` and `b` commute and `b` is topologically nilpotent,
  then `a * b` is topologically nilpotent. -/
 theorem mul_left_of_commute [IsLinearTopology R R] {a b : R}
    (hb : IsTopologicallyNilpotent b) (hab : Commute a b) :
    IsTopologicallyNilpotent (a * b) := by
  intro v hv
  rw [IsLinearTopology.hasBasis_ideal.mem_iff] at hv
  rcases hv with ⟨I, I_mem_nhds, I_subset⟩
  specialize hb I_mem_nhds
  simp only [mem_map, mem_atTop_sets, ge_iff_le, Set.mem_preimage, SetLike.mem_coe] at hb ⊢
  rcases hb with ⟨n, hb⟩
  use n
  intro m hm
  rw [hab.mul_pow]
  exact I_subset (I.mul_mem_left _ (hb m hm))

/-- If `a` and `b` are topologically nilpotent and commute,
  then `a + b` is topologically nilpotent. -/
theorem add_of_commute [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R]
    {a b : R} (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b)
    (h : Commute a b) :
    IsTopologicallyNilpotent (a + b) := fun v ↦ by
  rw [IsLinearTopology.hasBasis_twoSidedIdeal.mem_iff]
  rintro ⟨I, I_mem_nhds, I_subset⟩
  specialize ha I_mem_nhds
  specialize hb I_mem_nhds
  simp only [mem_map, mem_atTop_sets, ge_iff_le, Set.mem_preimage, SetLike.mem_coe] at ha hb ⊢
  rcases ha with ⟨na, ha⟩
  rcases hb with ⟨nb, hb⟩
  use na + nb
  intro m hm
  apply I_subset
  simp only [SetLike.mem_coe]
  exact I.add_pow_mem_of_pow_mem_of_le (ha na le_rfl) (hb nb le_rfl)
      (le_trans hm (Nat.le_add_right _ _)) h

end Ring

-- TODO : treat general rings, for commuting elements

section CommRing

variable {R : Type*} [TopologicalSpace R] [CommRing R] [IsLinearTopology R R]

/-- If `a` is topologically nilpotent, then `a * b` is topologically nilpotent. -/
theorem mul_right {a : R} (ha : IsTopologicallyNilpotent a) (b : R) :
    IsTopologicallyNilpotent (a * b) := fun v hv ↦ by
  simp_rw [mul_pow]
  exact IsLinearTopology.tendsto_mul_zero_of_left _ _ ha hv

/-- If `b` is topologically nilpotent, then `a * b` is topologically nilpotent. -/
 theorem mul_left (a : R) {b : R} (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a * b) :=
  -- hb.mul_left_of_commute (Commute.all a b)
  mul_comm a b ▸ hb.mul_right a

/-- If `a` and `b` are topologically nilpotent, then `a + b` is topologically nilpotent. -/
theorem add {a b : R} (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a + b) := fun v ↦ by
  rw [IsLinearTopology.hasBasis_ideal.mem_iff]
  rintro ⟨I, I_mem_nhds, I_subset⟩
  obtain ⟨na, ha⟩ := ha.exists_pow_mem_of_mem_nhds I_mem_nhds
  obtain ⟨nb, hb⟩ := hb.exists_pow_mem_of_mem_nhds I_mem_nhds
  simp only [mem_map, Filter.HasBasis.mem_iff Filter.atTop_basis, true_and]
  exact ⟨na + nb, fun m hm ↦ I_subset <|
    I.add_pow_mem_of_pow_mem_of_le ha hb (le_trans hm (Nat.le_add_right _ _))⟩

end CommRing

end IsTopologicallyNilpotent
