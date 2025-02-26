/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov, Aaron Liu
-/
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Separation.GDelta

/-!
# `Gδ` sets and metrizable spaces

## Main results
We prove that metrizable spaces are T6.
We prove that the continuity set of a function from a topological space to a metrizable space is a
Gδ set.

-/

variable {X : Type*} [TopologicalSpace X]
open TopologicalSpace Metric Set

section Metrizable

instance (priority := 500) [PseudoMetrizableSpace X] : PerfectlyNormalSpace X where
  normal s t hs ht hst := by
    letI := pseudoMetrizableSpacePseudoMetric
    by_cases hee : s = ∅ ∨ t = ∅
    · obtain rfl | rfl := hee <;> simp
    apply separatedNhds_iff_disjoint.mpr
    rw [not_or] at hee
    obtain ⟨hse, hte⟩ := hee
    rw [← ne_eq, ← nonempty_iff_ne_empty] at hse hte
    have hdj : Disjoint (Set.Ioi (0 : ℝ)) (Set.Iio 0) := by
      rw [Set.disjoint_iff, Ioi_inter_Iio, Ioo_eq_empty (lt_irrefl 0)]
    have hg := (continuous_infDist_pt t).sub (continuous_infDist_pt s)
    apply Filter.disjoint_of_disjoint_of_mem
      (hdj.preimage fun p ↦ infDist p t - infDist p s)
    · apply (isOpen_Ioi.preimage hg).mem_nhdsSet.mpr
      intro x hx
      rw [mem_preimage, infDist_zero_of_mem hx, sub_zero,
        mem_Ioi, ← ht.not_mem_iff_infDist_pos hte]
      exact hst.not_mem_of_mem_left hx
    · apply (isOpen_Iio.preimage hg).mem_nhdsSet.mpr
      intro x hx
      rw [mem_preimage, infDist_zero_of_mem hx, zero_sub,
        mem_Iio, neg_neg_iff_pos, ← hs.not_mem_iff_infDist_pos hse]
      exact hst.not_mem_of_mem_right hx
  closed_gdelta s hs := by
    letI := pseudoMetrizableSpacePseudoMetric
    by_cases he : s = ∅
    · exact he ▸ IsGδ.empty
    rw [← ne_eq, ← nonempty_iff_ne_empty] at he
    have := Nonempty.to_subtype he
    use Set.range fun (n : Nat) ↦ {p | infDist p s < (n + 1 : ℝ)⁻¹}
    constructor
    · rintro _ ⟨n, rfl⟩
      conv_rhs =>
        dsimp
        enter [1, p]
        rw [infDist_eq_iInf, ciInf_lt_iff ⟨0, fun _ ⟨_, h⟩ ↦ h ▸ dist_nonneg⟩]
        simp only [← mem_ball]
        rw [← mem_iUnion, ← biUnion_eq_iUnion s fun i _ ↦ ball i (n + 1 : ℝ)⁻¹]
      rw [setOf_mem_eq]
      exact isOpen_biUnion fun _ _ ↦ isOpen_ball
    · constructor
      · apply countable_range
      · apply subset_antisymm
        · rintro x hx _ ⟨n, rfl⟩
          simp_rw [mem_setOf, infDist_zero_of_mem hx, inv_pos]
          exact n.cast_add_one_pos
        · intro x hx
          rw [← hs.closure_eq, mem_closure_iff_infDist_zero he]
          apply infDist_nonneg.eq_or_gt.resolve_right
          intro hpos
          rw [sInter_range, mem_iInter] at hx
          specialize hx ⌊(infDist x s)⁻¹⌋₊
          rw [mem_setOf, lt_inv_comm₀ hpos (by positivity)] at hx
          have hcf := Nat.ceil_le_floor_add_one (Metric.infDist x s)⁻¹
          rw [← @Nat.cast_le ℝ, Nat.cast_add, Nat.cast_one] at hcf
          exact (not_le_of_lt (hcf.trans_lt hx) (Nat.le_ceil _))

instance (priority := 500) [MetrizableSpace X] : T6Space X where

end Metrizable

section ContinuousAt
variable {Y : Type*} [TopologicalSpace Y]

theorem IsGδ.setOf_continuousAt [PseudoMetrizableSpace Y] (f : X → Y) :
    IsGδ { x | ContinuousAt f x } := by
  letI := pseudoMetrizableSpacePseudoMetric
  obtain ⟨U, _, hU⟩ := (@uniformity_hasBasis_open_symmetric Y _).exists_antitone_subbasis
  simp only [Uniform.continuousAt_iff_prod, nhds_prod_eq]
  simp only [(nhds_basis_opens _).prod_self.tendsto_iff hU.toHasBasis,
    forall_prop_of_true, setOf_forall]
  refine .iInter fun k ↦ IsOpen.isGδ <| isOpen_iff_mem_nhds.2 fun x ↦ ?_
  rintro ⟨s, ⟨hsx, hso⟩, hsU⟩
  filter_upwards [IsOpen.mem_nhds hso hsx] with _ hy using ⟨s, ⟨hy, hso⟩, hsU⟩

end ContinuousAt
