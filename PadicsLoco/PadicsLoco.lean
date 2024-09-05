/-
Copyright (c) 2024 Jou Glasheen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jou Glasheen, Kevin Buzzard
-/

import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Padics totally bounded, compact, locally compact

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

/--The set of p-adic integers `ℤ_[p]` is totally bounded, where (p : ℕ) [Fact (Nat.Prime p)].-/
theorem totally_bounded :
    TotallyBounded (Set.univ : Set ℤ_[p]) := by
  apply Metric.totallyBounded_iff.2
  intros ε he
  apply PadicInt.exists_pow_neg_lt p at he
  rcases he with ⟨k , hk⟩
  let t0 := Finset.range ((p ^ k) : ℕ)
  let t : Set ℤ_[p] := ((↑) : ℕ → ℤ_[p])'' t0
  use t
  constructor
  · exact Set.toFinite t
  · intros z _
    simp only [PadicInt, Set.mem_iUnion, Metric.mem_ball, exists_prop]
    use ((↑) : ℕ → ℤ_[p]) (PadicInt.appr z k)
    constructor
    · refine (Set.mem_image Nat.cast ↑t0 ((z.appr k) : ℤ_[p])).mpr ?h.left.a
      simp only [Finset.mem_coe, Nat.cast_inj]
      refine exists_eq_right.mpr ?h.left.a.a
      refine Finset.mem_range.mpr ?h.left.a.a.a
      exact PadicInt.appr_lt z k
    · have h1 : dist z ((z.appr k) : ℤ_[p]) ≤ (p ^ (- (k : ℤ ))) := by
        have h3 : (z ) - ↑(z.appr k) ∈ Ideal.span {(p  : ℤ_[p]) ^ k} := PadicInt.appr_spec k z
        have h4 : ‖(z) - ↑(z.appr k)‖  ≤ (p : ℝ) ^ (- k : ℤ) :=
          (PadicInt.norm_le_pow_iff_mem_span_pow (z - ((z.appr k) : ℤ_[p])) k).mpr h3
        exact h4
      exact lt_of_le_of_lt h1 hk

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
