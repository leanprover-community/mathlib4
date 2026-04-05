/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov, Aaron Liu
-/
module

public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Separation.GDelta

/-!
# `Gδ` sets and metrizable spaces

## Main results
We prove that metrizable spaces are T6.
We prove that the continuity set of a function from a topological space to a metrizable space is a
Gδ set.

-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X]
open TopologicalSpace Set

section Metrizable

instance (priority := 100) [PseudoMetrizableSpace X] : NormalSpace X :=
  (@UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity X
    (pseudoMetrizableSpaceUniformity X)
    (pseudoMetrizableSpaceUniformity_countably_generated X)).toNormalSpace

instance (priority := 500) [PseudoMetrizableSpace X] : PerfectlyNormalSpace X where
  closed_gdelta s hs := by
    let := pseudoMetrizableSpaceUniformity X
    have := pseudoMetrizableSpaceUniformity_countably_generated X
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
  let := pseudoMetrizableSpaceUniformity Y
  have := pseudoMetrizableSpaceUniformity_countably_generated Y
  obtain ⟨U, _, hU⟩ := (@uniformity_hasBasis_open_symmetric Y _).exists_antitone_subbasis
  simp only [Uniform.continuousAt_iff_prod, nhds_prod_eq]
  simp only [(nhds_basis_opens _).prod_self.tendsto_iff hU.toHasBasis,
    forall_prop_of_true, setOf_forall]
  refine .iInter fun k ↦ IsOpen.isGδ <| isOpen_iff_mem_nhds.2 fun x ↦ ?_
  rintro ⟨s, ⟨hsx, hso⟩, hsU⟩
  filter_upwards [IsOpen.mem_nhds hso hsx] with _ hy using ⟨s, ⟨hy, hso⟩, hsU⟩

end ContinuousAt
