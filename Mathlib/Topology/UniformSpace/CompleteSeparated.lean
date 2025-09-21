/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Theory of complete separated uniform spaces.

This file is for elementary lemmas that depend on both Cauchy filters and separation.
-/


open Filter

open Topology Filter

variable {α β : Type*}

/-- In a separated space, a complete set is closed. -/
theorem IsComplete.isClosed [UniformSpace α] [T0Space α] {s : Set α} (h : IsComplete s) :
    IsClosed s :=
  isClosed_iff_clusterPt.2 fun a ha => by
    let f := 𝓝[s] a
    have : Cauchy f := cauchy_nhds.mono' ha inf_le_left
    rcases h f this inf_le_right with ⟨y, ys, fy⟩
    rwa [(tendsto_nhds_unique' ha inf_le_left fy : a = y)]

theorem IsUniformEmbedding.isClosedEmbedding [UniformSpace α] [UniformSpace β] [CompleteSpace α]
    [T0Space β] {f : α → β} (hf : IsUniformEmbedding f) :
    IsClosedEmbedding f :=
  ⟨hf.isEmbedding, hf.isUniformInducing.isComplete_range.isClosed⟩

namespace IsDenseInducing

open Filter

variable [TopologicalSpace α] {β : Type*} [TopologicalSpace β]
variable {γ : Type*} [UniformSpace γ] [CompleteSpace γ] [T0Space γ]

theorem continuous_extend_of_cauchy {e : α → β} {f : α → γ} (de : IsDenseInducing e)
    (h : ∀ b : β, Cauchy (map f (comap e <| 𝓝 b))) : Continuous (de.extend f) :=
  de.continuous_extend fun b => CompleteSpace.complete (h b)

end IsDenseInducing
