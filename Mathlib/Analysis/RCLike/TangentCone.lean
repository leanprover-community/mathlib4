/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.TangentCone
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Instances.RealVectorSpace

/-! # Relationships between unique differentiability over `ℝ` and `ℂ`

A set of unique differentiability for `ℝ` is also a set of unique differentiability for `ℂ`
(or for a general field satisfying `IsRCLikeNormedField 𝕜`).
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [h𝕜 : IsRCLikeNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
{s : Set E} {x : E}

theorem tangentConeAt_real_subset_isRCLikeNormedField :
    tangentConeAt ℝ s x ⊆ tangentConeAt 𝕜 s x := by
  letI := h𝕜.rclike
  rintro y ⟨c, d, d_mem, c_lim, hcd⟩
  let c' : ℕ → 𝕜 := fun n ↦ c n
  refine ⟨c', d, d_mem, by simpa [c'] using c_lim, ?_⟩
  convert hcd using 2 with n
  simp [c']

theorem UniqueDiffWithinAt.of_real (hs : UniqueDiffWithinAt ℝ s x) :
    UniqueDiffWithinAt 𝕜 s x := by
  refine ⟨?_, hs.mem_closure⟩
  letI : RCLike 𝕜 := h𝕜.rclike
  apply hs.dense_tangentConeAt.mono
  have : (Submodule.span ℝ (tangentConeAt ℝ s x) : Set E)
      ⊆ (Submodule.span 𝕜 (tangentConeAt ℝ s x)) := Submodule.span_subset_span _ _ _
  exact this.trans (Submodule.span_mono tangentConeAt_real_subset_isRCLikeNormedField)

theorem UniqueDiffOn.of_real (hs : UniqueDiffOn ℝ s) :
    UniqueDiffOn 𝕜 s :=
  fun x hx ↦ (hs x hx).of_real

/-- In a real or complex vector space, a convex set with nonempty interior is a set of unique
differentiability. -/
theorem uniqueDiffWithinAt_convex_of_isRCLikeNormedField
    (conv : Convex ℝ s) (hs : (interior s).Nonempty) (hx : x ∈ closure s) :
    UniqueDiffWithinAt 𝕜 s x :=
  UniqueDiffWithinAt.of_real (uniqueDiffWithinAt_convex conv hs hx)

/-- In a real or complex vector space, a convex set with nonempty interior is a set of unique
differentiability. -/
theorem uniqueDiffOn_convex_of_isRCLikeNormedField
    (conv : Convex ℝ s) (hs : (interior s).Nonempty) : UniqueDiffOn 𝕜 s :=
  UniqueDiffOn.of_real (uniqueDiffOn_convex conv hs)
