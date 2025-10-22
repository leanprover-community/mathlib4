/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Topological closure of the submonoid closure

In this file we prove several versions of the following statement:
if `G` is a compact topological group and `s : Set G`,
then the topological closures of `Submonoid.closure s` and `Subgroup.closure s` are equal.

The proof is based on the following observation, see `mapClusterPt_self_zpow_atTop_pow`:
each `x^m`, `m : ℤ` is a limit point (`MapClusterPt`) of the sequence `x^n`, `n : ℕ`, as `n → ∞`.
-/

open Filter Function Set
open scoped Topology

variable {G : Type*}

@[to_additive]
theorem mapClusterPt_atTop_zpow_iff_pow [DivInvMonoid G] [TopologicalSpace G] {x y : G} :
    MapClusterPt x atTop (y ^ · : ℤ → G) ↔ MapClusterPt x atTop (y ^ · : ℕ → G) := by
  simp_rw [MapClusterPt, ← Nat.map_cast_int_atTop, map_map, comp_def, zpow_natCast]

variable [Group G] [TopologicalSpace G] [CompactSpace G] [IsTopologicalGroup G]

@[to_additive]
theorem mapClusterPt_self_zpow_atTop_pow (x : G) (m : ℤ) :
    MapClusterPt (x ^ m) atTop (x ^ · : ℕ → G) := by
  obtain ⟨y, hy⟩ : ∃ y, MapClusterPt y atTop (x ^ · : ℤ → G) :=
    exists_clusterPt_of_compactSpace _
  rw [← mapClusterPt_atTop_zpow_iff_pow]
  have H : MapClusterPt (x ^ m) (atTop.curry atTop) ↿(fun a b ↦ x ^ (m + b - a)) := by
    have : ContinuousAt (fun yz ↦ x ^ m * yz.2 / yz.1) (y, y) := by fun_prop
    simpa only [comp_def, ← zpow_sub, ← zpow_add, div_eq_mul_inv, Prod.map, mul_inv_cancel_right]
      using (hy.curry_prodMap hy).continuousAt_comp this
  suffices Tendsto ↿(fun a b ↦ m + b - a) (atTop.curry atTop) atTop from H.of_comp this
  refine Tendsto.curry <| .of_forall fun a ↦ ?_
  simp only [sub_eq_add_neg] -- TODO: add `Tendsto.atTop_sub_const` etc
  exact tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_left atTop m tendsto_id)

@[to_additive]
theorem mapClusterPt_one_atTop_pow (x : G) : MapClusterPt 1 atTop (x ^ · : ℕ → G) := by
  simpa using mapClusterPt_self_zpow_atTop_pow x 0

@[to_additive]
theorem mapClusterPt_self_atTop_pow (x : G) : MapClusterPt x atTop (x ^ · : ℕ → G) := by
  simpa using mapClusterPt_self_zpow_atTop_pow x 1

@[to_additive]
theorem mapClusterPt_atTop_pow_tfae (x y : G) :
    List.TFAE [
      MapClusterPt x atTop (y ^ · : ℕ → G),
      MapClusterPt x atTop (y ^ · : ℤ → G),
      x ∈ closure (range (y ^ · : ℕ → G)),
      x ∈ closure (range (y ^ · : ℤ → G)),
    ] := by
  tfae_have 2 ↔ 1 := mapClusterPt_atTop_zpow_iff_pow
  tfae_have 3 → 4 := by
    refine fun h ↦ closure_mono (range_subset_iff.2 fun n ↦ ?_) h
    exact ⟨n, zpow_natCast _ _⟩
  tfae_have 4 → 1 := by
    refine fun h ↦ closure_minimal ?_ isClosed_setOf_clusterPt h
    exact range_subset_iff.2 (mapClusterPt_self_zpow_atTop_pow _)
  tfae_have 1 → 3 := by
    rw [mem_closure_iff_clusterPt]
    exact (ClusterPt.mono · (le_principal_iff.2 range_mem_map))
  tfae_finish

@[to_additive]
theorem mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers {x y : G} :
    MapClusterPt x atTop (y ^ · : ℕ → G) ↔ x ∈ (Subgroup.zpowers y).topologicalClosure :=
  (mapClusterPt_atTop_pow_tfae x y).out 0 3

@[to_additive (attr := simp)]
theorem mapClusterPt_inv_atTop_pow {x y : G} :
    MapClusterPt x⁻¹ atTop (y ^ · : ℕ → G) ↔ MapClusterPt x atTop (y ^ · : ℕ → G) := by
  simp only [mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers, inv_mem_iff]

@[to_additive]
theorem closure_range_zpow_eq_pow (x : G) :
    closure (range (x ^ · : ℤ → G)) = closure (range (x ^ · : ℕ → G)) := by
  ext y
  exact (mapClusterPt_atTop_pow_tfae y x).out 3 2

@[to_additive]
theorem denseRange_zpow_iff_pow {x : G} :
    DenseRange (x ^ · : ℤ → G) ↔ DenseRange (x ^ · : ℕ → G) := by
  simp only [DenseRange, dense_iff_closure_eq, closure_range_zpow_eq_pow]

@[to_additive]
theorem topologicalClosure_subgroupClosure_toSubmonoid (s : Set G) :
    (Subgroup.closure s).toSubmonoid.topologicalClosure =
      (Submonoid.closure s).topologicalClosure := by
  refine le_antisymm ?_ (closure_mono <| Subgroup.le_closure_toSubmonoid _)
  refine Submonoid.topologicalClosure_minimal _ ?_ isClosed_closure
  rw [Subgroup.closure_toSubmonoid, Submonoid.closure_le]
  refine union_subset (Submonoid.subset_closure.trans subset_closure) fun x hx ↦ ?_
  refine closure_mono (Submonoid.powers_le.2 (Submonoid.subset_closure <| Set.mem_inv.1 hx)) ?_
  rw [Submonoid.coe_powers, ← closure_range_zpow_eq_pow, ← Subgroup.coe_zpowers,
    ← Subgroup.topologicalClosure_coe, SetLike.mem_coe, ← inv_mem_iff]
  exact subset_closure <| Subgroup.mem_zpowers _

@[to_additive]
theorem closure_submonoidClosure_eq_closure_subgroupClosure (s : Set G) :
    closure (Submonoid.closure s : Set G) = closure (Subgroup.closure s) :=
  congrArg SetLike.coe (topologicalClosure_subgroupClosure_toSubmonoid s).symm

@[to_additive]
theorem dense_submonoidClosure_iff_subgroupClosure {s : Set G} :
    Dense (Submonoid.closure s : Set G) ↔ Dense (Subgroup.closure s : Set G) := by
  simp only [dense_iff_closure_eq, closure_submonoidClosure_eq_closure_subgroupClosure]
