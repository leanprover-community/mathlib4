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

instance (priority := 100) [PseudoMetrizableSpace X] : NormalSpace X where
  normal s t hs ht hst := by
    let _ := pseudoMetrizableSpacePseudoMetric X
    by_cases hee : s = ∅ ∨ t = ∅
    · obtain rfl | rfl := hee <;> simp
    simp only [not_or, ← ne_eq, ← nonempty_iff_ne_empty] at hee
    obtain ⟨hse, hte⟩ := hee
    let g (p : X) := infDist p t - infDist p s
    have hg : Continuous g := by fun_prop
    refine ⟨g ⁻¹' (Ioi 0), g ⁻¹' (Iio 0), isOpen_Ioi.preimage hg, isOpen_Iio.preimage hg,
      fun x hx ↦ ?_, fun x hx ↦ ?_, Ioi_disjoint_Iio_same.preimage g⟩
    · simp [g, infDist_zero_of_mem hx,
        (ht.notMem_iff_infDist_pos hte).mp (hst.notMem_of_mem_left hx)]
    · simp [g, infDist_zero_of_mem hx,
        (hs.notMem_iff_infDist_pos hse).mp (hst.notMem_of_mem_right hx)]

instance (priority := 500) [PseudoMetrizableSpace X] : PerfectlyNormalSpace X where
  closed_gdelta s hs := by
    let _ := pseudoMetrizableSpacePseudoMetric X
    rcases (@uniformity_hasBasis_open X _).exists_antitone_subbasis with ⟨U, hUo, hU, -⟩
    rw [← hs.closure_eq, ← hU.biInter_biUnion_ball]
    refine .biInter (to_countable _) fun n _ => IsOpen.isGδ ?_
    exact isOpen_biUnion fun x _ => UniformSpace.isOpen_ball _ (hUo _).2

instance (priority := 100) [MetrizableSpace X] : T4Space X where

instance (priority := 500) [MetrizableSpace X] : T6Space X where

end Metrizable

section ContinuousAt
variable {Y : Type*} [TopologicalSpace Y]

theorem IsGδ.setOf_continuousAt [PseudoMetrizableSpace Y] (f : X → Y) :
    IsGδ { x | ContinuousAt f x } := by
  let _ := pseudoMetrizableSpacePseudoMetric Y
  obtain ⟨U, _, hU⟩ := (@uniformity_hasBasis_open_symmetric Y _).exists_antitone_subbasis
  simp only [Uniform.continuousAt_iff_prod, nhds_prod_eq]
  simp only [(nhds_basis_opens _).prod_self.tendsto_iff hU.toHasBasis,
    forall_prop_of_true, setOf_forall]
  refine .iInter fun k ↦ IsOpen.isGδ <| isOpen_iff_mem_nhds.2 fun x ↦ ?_
  rintro ⟨s, ⟨hsx, hso⟩, hsU⟩
  filter_upwards [IsOpen.mem_nhds hso hsx] with _ hy using ⟨s, ⟨hy, hso⟩, hsU⟩

end ContinuousAt
