/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Topology.UniformSpace.UniformEmbedding

#align_import topology.uniform_space.complete_separated from "leanprover-community/mathlib"@"b363547b3113d350d053abdf2884e9850a56b205"

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
#align is_complete.is_closed IsComplete.isClosed

theorem UniformEmbedding.toClosedEmbedding [UniformSpace α] [UniformSpace β] [CompleteSpace α]
    [T0Space β] {f : α → β} (hf : UniformEmbedding f) :
    ClosedEmbedding f :=
  ⟨hf.embedding, hf.toUniformInducing.isComplete_range.isClosed⟩

namespace DenseInducing

open Filter

variable [TopologicalSpace α] {β : Type*} [TopologicalSpace β]
variable {γ : Type*} [UniformSpace γ] [CompleteSpace γ] [T0Space γ]

theorem continuous_extend_of_cauchy {e : α → β} {f : α → γ} (de : DenseInducing e)
    (h : ∀ b : β, Cauchy (map f (comap e <| 𝓝 b))) : Continuous (de.extend f) :=
  de.continuous_extend fun b => CompleteSpace.complete (h b)
#align dense_inducing.continuous_extend_of_cauchy DenseInducing.continuous_extend_of_cauchy

end DenseInducing
