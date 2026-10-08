/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.Topology.Algebra.PowerBounded

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

Let `R` be a semiring, endowed with a topology, that has continuous multiplication.

* `IsTopologicallyNilpotent.of_pow`: if `a ^ m` is topologically nilpotent, then so is `a`.

Let `R` be a semiring, endowed with a topology.

* `IsTopologicallyNilpotent.isPowerBounded`: topologically nilpotent elements are power bounded.

Let `R` be a commutative ring, endowed with a topology.

* `IsTopologicallNilpotent.mul_left_of_powerBounded` : if `a : R` is topologically nilpotent and
  `b : R` is power bounded then `b * a` is topologically nilpotent.

* `IsTopologicallNilpotent.mul_right_of_powerBounded` : if `a : R` is topologically nilpotent and
  `b : R` is power bounded then `a * b` is topologically nilpotent.

Note the above mul lemmas do not rely on any linear topology, but restrict the element we are
multiplying by to be power bounded.

Let `S` be a ring such that `R` is an `S`-module and `R` has the `S`-linear topology and `R` now
has continuous multiplication.

The key examples will be:
    · `S = R`: i.e., we have `[IsLinearTopology R R]`
    · `S = ℤ`: which can be infered from `[Ring R] [TopologicalSpace R] [NonarchimedeanRing R]`

* `IsTopologicallyNilpotent.add'`: if `a b` are topologically nilpotent then so is `a + b`.

Note the requirement of continuous multiplication, means that this does not imply the above `.add`.

-/

@[expose] public section

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

/-- If `a` and `b` commute and `b` is topologically nilpotent,
  then `a * b` is topologically nilpotent. -/
theorem smul_of_commute (S : Type*) [Ring S] [Module S R] [IsLinearTopology S R]
    [IsScalarTower S R R] {a : S} {b : R} (hb : IsTopologicallyNilpotent b)
    (hab : ∀ n, (a • b) ^ n = a ^ n • b ^ n) : IsTopologicallyNilpotent (a • b) := by
  simp_rw [IsTopologicallyNilpotent, hab]
  exact IsLinearTopology.tendsto_smul_zero (R := S) _ _ hb

/-- If `a` and `b` commute and `a` is topologically nilpotent,
  then `a * b` is topologically nilpotent. -/
theorem mul_right_of_commute [IsLinearTopology Rᵐᵒᵖ R]
    {a b : R} (ha : IsTopologicallyNilpotent a) (hab : Commute a b) :
    IsTopologicallyNilpotent (a * b) := by
  simp_rw [IsTopologicallyNilpotent, hab.mul_pow]
  exact IsLinearTopology.tendsto_mul_zero_of_left _ _ ha

/-- If `a` and `b` commute and `b` is topologically nilpotent,
  then `a * b` is topologically nilpotent. -/
theorem mul_left_of_commute [IsLinearTopology R R] {a b : R} (hb : IsTopologicallyNilpotent b)
    (hab : Commute a b) : IsTopologicallyNilpotent (a * b) :=
  smul_of_commute R hb (fun n ↦ by simp only [smul_eq_mul, hab.mul_pow])

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

section ContinuousMul

open TopologicalRing

variable {R : Type*} [Semiring R] [TopologicalSpace R] [ContinuousMul R]

/-- If `a ^ m` for positive `m` is topologically nilpotent, then so is `a`. -/
theorem of_pow {a : R} {m : ℕ} (hm : 0 < m)
    (ha : IsTopologicallyNilpotent (a ^ m)) : IsTopologicallyNilpotent a := by
  intro U hU
  obtain ⟨V, hV, hSV⟩ := (isBounded_finite (Set.finite_range fun i : Fin m ↦ a ^ (i : ℕ))) U hU
  obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.mp (ha hV)
  refine Filter.mem_atTop_sets.mpr ⟨m * N, fun n hn ↦ ?_⟩
  rw [Set.mem_preimage, show a ^ n = (a ^ m) ^ (n / m) * a ^ (n % m) by
    rw [← pow_mul, ← pow_add, add_comm, Nat.mod_add_div]]
  exact hSV (Set.mul_mem_mul (hN _ ((Nat.le_div_iff_mul_le hm).mpr (by linarith)))
    ⟨⟨n % m, Nat.mod_lt n hm⟩, rfl⟩)

end ContinuousMul

section PowerBounded

section Semiring

variable {R : Type*} [Semiring R] [TopologicalSpace R]

open PowerBounded TopologicalRing

/-- Topologically nilpotent elements are power bounded. -/
theorem isPowerBounded [ContinuousMul R] {a : R} (ha : IsTopologicallyNilpotent a) :
    IsPowerBounded a := by
  intro U hU
  have : (fun p : R × R ↦ p.1 * p.2) ⁻¹' U ∈ 𝓝 ((0 : R), (0 : R)) :=
    continuous_mul.continuousAt.preimage_mem_nhds (by simp [hU])
  rw [nhds_prod_eq] at this
  obtain ⟨U₁, hU₁, U₂, hU₂, hprod⟩ := Filter.mem_prod_iff.mp this
  obtain ⟨N, hN⟩ := (ha.eventually hU₂).exists_forall_of_atTop
  choose V hV_mem hV_sub using (fun (i : Fin N) ↦ isBounded_singleton (a ^ (i : ℕ)) U hU)
  refine ⟨U₁ ∩ ⋂ i, V i, inter_mem hU₁ (Filter.iInter_mem.mpr hV_mem), ?_⟩
  intro x hx
  obtain ⟨c, hc, _, ⟨n, rfl⟩, rfl⟩ := Set.mem_mul.mp hx
  by_cases hn : n < N
  · exact hV_sub ⟨n, hn⟩ (Set.mem_mul.mpr ⟨c, Set.mem_iInter.mp hc.2 ⟨n, hn⟩, a ^ n, rfl, rfl⟩)
  · exact hprod (Set.mk_mem_prod hc.1 (hN n (by omega)))

/-- Product of power-bounded and topologically nilpotent is topologically nilpotent. -/
theorem mul_left_of_commute_isPowerBounded {a b : R} (h : Commute a b) (ha : IsPowerBounded a)
    (hb : IsTopologicallyNilpotent b) : IsTopologicallyNilpotent (a * b) := by
  intro U hU
  obtain ⟨V, hV, hSV⟩ := ha U hU
  rw [Filter.mem_map, h]
  refine Filter.mem_of_superset (Filter.mem_map.mp (hb hV)) ?_
  simp_rw [Commute.mul_pow h.symm]
  exact fun n hn ↦ (hSV (Set.mul_mem_mul hn ⟨n, rfl⟩))

/-- Product of topologically nilpotent and power bounded is topologically nilpotent. -/
theorem mul_right_of_commute_isPowerBounded {a b : R} (h : Commute a b)
    (ha : IsTopologicallyNilpotent a) (hb : IsPowerBounded b) :
    IsTopologicallyNilpotent (a * b) := by
  rw [h]
  exact mul_left_of_commute_isPowerBounded h.symm hb ha

end Semiring

section Ring

variable {R : Type*} [Ring R] [TopologicalSpace R]

/-- If `a` and `b` are topologically nilpotent and commute,
  then `a + b` is topologically nilpotent. -/
theorem add_of_commute' (S : Type*) [Ring S] [Module S R] [IsLinearTopology S R] {a b : R}
    [ContinuousMul R] (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b)
    (h : Commute a b) : IsTopologicallyNilpotent (a + b) := by
  intro U hU
  obtain ⟨V, hV_mem, hVU⟩ := (IsLinearTopology.hasBasis_submodule S).mem_iff.mp hU
  obtain ⟨W₁, hW₁_mem, hW₁_sub⟩ := IsTopologicallyNilpotent.isPowerBounded ha _ hV_mem
  obtain ⟨W₂, hW₂_mem, hW₂_sub⟩ := IsTopologicallyNilpotent.isPowerBounded hb _ hV_mem
  obtain ⟨Na, hNa⟩ := (ha.eventually hW₂_mem).exists_forall_of_atTop
  obtain ⟨Nb, hNb⟩ := (hb.eventually hW₁_mem).exists_forall_of_atTop
  refine Filter.mem_atTop_sets.mpr ⟨Na + Nb, fun n hn ↦ ?_⟩
  apply hVU
  simp_rw [SetLike.mem_coe, h.add_pow]
  refine V.toAddSubgroup.sum_mem fun k _ ↦ ?_
  rw [(Nat.cast_commute _ _).symm, ← nsmul_eq_mul]
  refine V.toAddSubgroup.nsmul_mem ?_ _
  by_cases hkNa : Na ≤ k
  · exact hW₂_sub (Set.mul_mem_mul (hNa k hkNa) ⟨n - k, rfl⟩)
  · rw [((h.pow_left k).pow_right (n - k)).eq]
    exact hW₁_sub (Set.mul_mem_mul (hNb (n - k) (by omega)) ⟨k, rfl⟩)

end Ring

section CommRing

variable {R : Type*} [CommRing R] [TopologicalSpace R]

open PowerBounded

/-- Product of power-bounded and topologically nilpotent is topologically nilpotent. -/
theorem mul_left_of_isPowerBounded {a b : R} (ha : IsPowerBounded a)
    (hb : IsTopologicallyNilpotent b) : IsTopologicallyNilpotent (a * b) :=
  mul_left_of_commute_isPowerBounded (Commute.all ..) ha hb

/-- Product of topologically nilpotent and power bounded is topologically nilpotent. -/
theorem mul_right_of_isPowerBounded {a b : R} (ha : IsTopologicallyNilpotent a)
    (hb : IsPowerBounded b) : IsTopologicallyNilpotent (a * b) :=
  mul_right_of_commute_isPowerBounded (Commute.all ..) ha hb

theorem add' (S : Type*) [Ring S] [Module S R] [IsLinearTopology S R] {a b : R} [ContinuousMul R]
    (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a + b) :=
  add_of_commute' S ha hb (Commute.all ..)

variable [IsTopologicalRing R]

variable (S : Type*) [Ring S] [Module S R] [IsLinearTopology S R]

theorem subset_powerBoundedSubring :
    {a : R | IsTopologicallyNilpotent a} ⊆ PowerBounded.subring R (S := S) :=
  fun _ ↦ isPowerBounded

/-- The topological nilradical as an ideal of `PowerBounded.subring`. -/
def _root_.PowerBounded.topologicalNilradical : Ideal ↥(PowerBounded.subring R (S := S)) where
  carrier := Set.range (Set.inclusion (subset_powerBoundedSubring S))
  add_mem' := by
    simp only [Set.mem_range, Subtype.exists, Set.inclusion_mk, forall_exists_index, Subtype.forall,
      Subtype.mk.injEq, AddMemClass.mk_add_mk, exists_prop, exists_eq_right]
    intro _ _ _ _ _ hx rfl _ hy rfl
    simp_rw [Set.mem_setOf_eq] at ⊢ hx hy
    exact add_of_commute' S hx hy (Commute.all ..)
  zero_mem' := by simpa using zero
  smul_mem' := by
    simp only [Set.mem_range, Subtype.exists, Set.inclusion_mk, smul_eq_mul, forall_exists_index,
      Subtype.forall, Subtype.mk.injEq, MulMemClass.mk_mul_mk, exists_prop, exists_eq_right]
    intro _ hb _ _ _ hx rfl
    simp_rw [Set.mem_setOf_eq] at ⊢ hx
    exact mul_left_of_commute_isPowerBounded (Commute.all ..) hb hx

theorem mem_PowerBounded.topologicalNilradical_iff (x : ↥(PowerBounded.subring R (S := S))) :
    x ∈ PowerBounded.topologicalNilradical S ↔ IsTopologicallyNilpotent (x : R) :=
  ⟨by rintro ⟨⟨_, _⟩, rfl⟩; assumption, fun hx ↦ ⟨⟨_, hx⟩, rfl⟩⟩

/-- The residue field of power bounded elements quotiented by the topological nilradical. -/
def _root_.PowerBounded.residueField :=
  ↥(PowerBounded.subring R (S := S)) ⧸ (PowerBounded.topologicalNilradical S)

end CommRing

end PowerBounded

end IsTopologicallyNilpotent
