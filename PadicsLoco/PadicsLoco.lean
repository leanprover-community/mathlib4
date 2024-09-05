/-
Copyright (c) 2024 Jou Glasheen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jou Glasheen, Kevin Buzzard
-/

import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Local compactness of the p-adic numbers

In this file, we prove that `Z_[p]` is totally bounded and compact,
and that `ℚ_[p]` is locally compact.

## Main results

- `PadicInt.totally_bounded` : The set of p-adic integers `ℤ_[p]` is totally bounded.
- `PadicInt.is_compact` : The set of p-adic integers `ℤ_[p]` is a compact topological space.
- `Padic.locally_compact_space` : The set of p-adic numbers ℚ_[p] is a locally compact topological
                                  space.

## Notation

 - `p` : Is a natural prime.

## References

Gouvêa, F. Q. (2020) p-adic Numbers An Introduction. 3rd edition.
  Cham, Springer International Publishing
-/

variable (p : ℕ) [Fact (Nat.Prime p)]

namespace PadicInt

/-- The set of p-adic integers `ℤ_[p]` is totally bounded. -/
theorem totallyBounded_univ : TotallyBounded (univ : Set ℤ_[p]) := by
  refine Metric.totallyBounded_iff.mpr (fun ε hε ↦ ?_)
  obtain ⟨k, hk⟩ := exists_pow_neg_lt p hε
  refine ⟨Nat.cast '' Finset.range (p ^ k), Set.toFinite _, fun z _ ↦ ?_⟩
  simp only [PadicInt, Set.mem_iUnion, Metric.mem_ball, exists_prop, Set.exists_mem_image]
  refine ⟨z.appr k, ?_, ?_⟩
  · simpa only [Finset.mem_coe, Finset.mem_range] using z.appr_lt k
  · exact (((z - z.appr k).norm_le_pow_iff_mem_span_pow k).mpr (z.appr_spec k)).trans_lt hk

/--The set of p-adic integers `ℤ_[p]` is a compact topological space,
where (p : ℕ) [Fact (Nat.Prime p)].-/
  theorem is_compact : IsCompact (Set.univ : Set ℤ_[p]) := by
    apply isCompact_iff_totallyBounded_isComplete.2
    constructor
    · exact totally_bounded p
    · exact complete_univ

open Metric

lemma closed_ball_at_zero : (closedBall 0 1) = {x : ℚ_[p] | ‖x‖ ≤ 1} := by
    refine Set.ext ?h
    intros x
    constructor
    · simp only [mem_closedBall, dist_zero_right, Set.mem_setOf_eq, imp_self]
    · simp only [Set.mem_setOf_eq, mem_closedBall, dist_zero_right, imp_self]

lemma nhd_zero : {x | ‖x‖ ≤ 1} ∈ nhds (0 : ℚ_[p]) := by
  have ob : IsOpen (closedBall (0 : ℚ_[p]) (1)) := by
    have : (1 : ℝ)  ≠ 0 := Ne.symm (zero_ne_one' ℝ)
    apply IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) this
  refine IsOpen.mem_nhds ?hs ?hx
  · rw [← closed_ball_at_zero]
    exact ob
  · refine Set.singleton_subset_iff.mp ?h.left.hx.a
    refine Set.subset_setOf.mpr ?h.left.hx.a.a
    intros x hx
    simp only [Multiset.mem_singleton, Set.mem_singleton_iff] at hx
    rw [hx]
    refine (Padic.norm_le_one_iff_val_nonneg 0).mpr ?h.left.hx.a.a.a
    simp only [Padic.valuation_zero, le_refl]

end PadicInt

namespace Padic
open PadicInt

/--The set of p-adic numbers `ℚ_[p]` is a locally compact topological space,
where (p : ℕ) [Fact (Nat.Prime p)].-/
theorem locally_compact_space :
    LocallyCompactSpace ℚ_[p] := by
  have ex : ∃ U ∈ nhds (0 : ℚ_[p]), IsCompact U := by
    use ((↑) : ℤ_[p] → ℚ_[p])'' (Set.univ : Set ℤ_[p])
    simp only [Set.image_univ, Subtype.range_coe_subtype]
    constructor
    · exact nhd_zero p
    · refine isCompact_iff_compactSpace.mpr ?h.right.a
      refine { isCompact_univ := ?h.right.a.isCompact_univ }
      apply is_compact
  rcases ex with ⟨U, hu1, hu2⟩
  apply IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup
  · convert hu2
  · convert hu1

end Padic
