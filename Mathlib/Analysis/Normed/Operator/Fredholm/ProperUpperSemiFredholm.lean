/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# A properness criterion for an operator being upper-semi-Fredholm
-/

@[expose] public section

open Topology Set Metric

namespace ContinuousLinearMap

section ClosedEmbeddingOfRestrict

section Def

variable {𝕜 E F : Type*} [CommRing 𝕜] [AddCommGroup E] [AddCommGroup F]
  [Module 𝕜 E] [Module 𝕜 F] [TopologicalSpace E] [TopologicalSpace F]

variable (𝕜 E F) in
class IsClosedEmbeddingOfRestrict : Prop where
  isClosedEmbedding_of_restrict : ∀ {f : E →L[𝕜] F} {V : Set E}, V ∈ 𝓝 0 →
    IsClosedEmbedding (Set.restrict V f) → IsClosedEmbedding f

export IsClosedEmbeddingOfRestrict (isClosedEmbedding_of_restrict)

theorem IsClosedEmbeddingOfRestrict.mk_of_hasBasis {ι : Type*}
    {p : ι → Prop} {s : ι → Set E} (hs : (𝓝 0).HasBasis p s)
    (h_closed : ∀ i, p i → IsClosed (s i))
    (H : ∀ {f : E →L[𝕜] F} {i : ι}, p i →
      IsClosedEmbedding (Set.restrict (s i) f) → IsClosedEmbedding f) :
    IsClosedEmbeddingOfRestrict 𝕜 E F where
  isClosedEmbedding_of_restrict {f V} V_mem hV := by
    rcases hs.mem_iff.mp V_mem with ⟨i, hpi, si_sub_V⟩
    have : IsClosedEmbedding (inclusion si_sub_V) :=
      .of_comp .subtypeVal (h_closed i hpi).isClosedEmbedding_subtypeVal
    exact H hpi (hV.comp this)

end Def

section Banach

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]

instance : IsClosedEmbeddingOfRestrict 𝕜 E F := by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc₁⟩
  refine .mk_of_hasBasis nhds_basis_closedBall (fun _ _ ↦ isClosed_closedBall)
    fun {f ε} ε_pos H ↦ ?_
  replace H : ∀ R > 0, IsClosedEmbedding (Set.restrict (closedBall 0 R) f) := sorry -- rescaling
  suffices IsClosed (Set.range f) from sorry -- Open mapping theorem
  refine IsSeqClosed.isClosed fun y ly hy y_tendsto ↦ ?_
  choose x hx using hy
  sorry

end Banach

end ClosedEmbeddingOfRestrict

end ContinuousLinearMap
