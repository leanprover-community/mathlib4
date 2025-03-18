/-
Copyright (c) 2025 Hannah Scholz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Scholz
-/
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Topology.ContinuousOn

/-!
# Topological properties of partial equivalences

-/

open Set

namespace PartialEquiv

/-- A partial equivalence that is continuous on the source and the target restricts to a
homeomorphism. -/
@[simps]
def toHomeomorph {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] (e : PartialEquiv α β)
    (he1 : ContinuousOn e e.source) (he2 : ContinuousOn e.symm e.target) :
    e.source ≃ₜ e.target where
  toFun := e.toEquiv
  invFun := e.toEquiv.symm
  left_inv := e.toEquiv.symm_apply_apply
  right_inv := e.toEquiv.apply_symm_apply
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (e.source.restrict e)
    rw [← continuousOn_iff_continuous_restrict]
    exact he1
  continuous_invFun := by
    apply Continuous.subtype_mk
    change Continuous (e.target.restrict e.symm)
    rw [← continuousOn_iff_continuous_restrict]
    exact he2

/-- A partial equivalence that is continuous on both source and target and where the source and the
target are closed is a closed map when restricting to the source. -/
lemma isClosed_of_isClosed_preimage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : PartialEquiv X Y) (h1 : ContinuousOn e e.source) (h2 : ContinuousOn e.symm e.target)
    (he1 : IsClosed e.target) (he2 : IsClosed e.source) (A : Set Y) (hAe : A ⊆ e.target)
    (hA : IsClosed (e.source ∩ e ⁻¹' A)) : IsClosed A := by
  rw [← inter_eq_right.2 hAe, ← he1.inter_preimage_val_iff,
    ← (e.toHomeomorph h1 h2).isClosed_preimage,
    he2.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed]
  convert hA
  ext
  simp [PartialEquiv.toEquiv, and_comm]

end PartialEquiv
