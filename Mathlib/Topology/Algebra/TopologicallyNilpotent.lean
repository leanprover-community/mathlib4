/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Nilpotent.Defs

/-! # Topologically nilpotent elements

Let `M` be a monoid with zero `M`, endowed with a topology.

* `IsTopologicallyNilpotent a` says that `a : M` is *topologically nilpotent*,
  i.e., its powers converge to zero.

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

These lemmas are actually deduced from their analogues for commuting elements of rings.

-/

open Filter

open scoped Topology

/-- An element is topologically nilpotent if its powers converge to `0`. -/
def IsTopologicallyNilpotent
    {R : Type*} [MonoidWithZero R] [TopologicalSpace R] (a : R) : Prop :=
  Tendsto (a ^ ·) atTop (𝓝 0)

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

theorem _root_.IsNilpotent.isTopologicallyNilpotent {a : R} (ha : IsNilpotent a) :
    IsTopologicallyNilpotent a := by
  obtain ⟨n, hn⟩ := ha
  apply tendsto_atTop_of_eventually_const (i₀ := n)
  intro i hi
  rw [← Nat.add_sub_of_le hi, pow_add, hn, zero_mul]

theorem exists_pow_mem_of_mem_nhds {a : R} (ha : IsTopologicallyNilpotent a)
    {v : Set R} (hv : v ∈ 𝓝 0) :
    ∃ n, a ^ n ∈ v :=
  (ha.eventually_mem hv).exists

end MonoidWithZero

section Ring

variable {R : Type*} [TopologicalSpace R] [Ring R]

/-- If `a` and `b` commute and `a` is topologically nilpotent,
  then `a * b` is topologically nilpotent. -/
theorem mul_right_of_commute [IsLinearTopology Rᵐᵒᵖ R]
    {a b : R} (ha : IsTopologicallyNilpotent a) (hab : Commute a b) :
    IsTopologicallyNilpotent (a * b) := by
  simp_rw [IsTopologicallyNilpotent, hab.mul_pow]
  exact IsLinearTopology.tendsto_mul_zero_of_left _ _ ha

/-- If `a` and `b` commute and `b` is topologically nilpotent,
  then `a * b` is topologically nilpotent. -/
theorem mul_left_of_commute [IsLinearTopology R R] {a b : R}
    (hb : IsTopologicallyNilpotent b) (hab : Commute a b) :
    IsTopologicallyNilpotent (a * b) := by
  simp_rw [IsTopologicallyNilpotent, hab.mul_pow]
  exact IsLinearTopology.tendsto_mul_zero_of_right _ _ hb

/-- If `a` and `b` are topologically nilpotent and commute,
  then `a + b` is topologically nilpotent. -/
theorem add_of_commute [IsLinearTopology R R] {a b : R}
    (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b) (h : Commute a b) :
    IsTopologicallyNilpotent (a + b) := by
  simp only [IsTopologicallyNilpotent, atTop_basis.tendsto_iff IsLinearTopology.hasBasis_ideal,
    true_and]
  intro I I_mem_nhds
  obtain ⟨na, ha⟩ := ha.exists_pow_mem_of_mem_nhds I_mem_nhds
  obtain ⟨nb, hb⟩ := hb.exists_pow_mem_of_mem_nhds I_mem_nhds
  exact ⟨na + nb, fun m hm ↦
    I.add_pow_mem_of_pow_mem_of_le_of_commute ha hb (le_trans hm (Nat.le_add_right _ _)) h⟩

end Ring

section CommRing

variable {R : Type*} [TopologicalSpace R] [CommRing R] [IsLinearTopology R R]

/-- If `a` is topologically nilpotent, then `a * b` is topologically nilpotent. -/
theorem mul_right {a : R} (ha : IsTopologicallyNilpotent a) (b : R) :
    IsTopologicallyNilpotent (a * b) :=
  ha.mul_right_of_commute (Commute.all ..)

/-- If `b` is topologically nilpotent, then `a * b` is topologically nilpotent. -/
theorem mul_left (a : R) {b : R} (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a * b) :=
  hb.mul_left_of_commute (Commute.all ..)

/-- If `a` and `b` are topologically nilpotent, then `a + b` is topologically nilpotent. -/
theorem add {a b : R} (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a + b) :=
  ha.add_of_commute hb (Commute.all ..)

variable (R) in
/-- The topological nilradical of a ring with a linear topology -/
@[simps]
def _root_.topologicalNilradical : Ideal R where
  carrier := {a | IsTopologicallyNilpotent a}
  add_mem' := add
  zero_mem' := zero
  smul_mem' := mul_left

theorem mem_topologicalNilradical_iff {a : R} :
    a ∈ topologicalNilradical R ↔ IsTopologicallyNilpotent a := by
  simp [topologicalNilradical]

end CommRing

end IsTopologicallyNilpotent
