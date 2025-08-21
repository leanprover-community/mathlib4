/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.Dual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Metric NormedSpace Function

open scoped Topology

local notation3 "E**" => StrongDual ℝ (StrongDual ℝ E)

/- Goldstine lemma (see Brezis, Chapter § 3.5, Lemma 3.4) says that the unit ball in the double
dual of a Banach space (**FAE: I suspect completeness is not needed) ** is the closure, with respect
to the weak topology `σ(E**, E*)` induced by the canonical pairing `E** × E* → ℝ`, of the image of
the unit ball in  `E`. Observe that, for any topological `𝕜`-module `M`, `strongDualPairing 𝕜 M` is
the pairing whose *first* variable is in `M*` and the second is in `M`. -/
lemma goldstine : closure (X := (WeakBilin (strongDualPairing ℝ (StrongDual ℝ E))))
  (inclusionInDoubleDual ℝ E '' (ball 0 1)) = ball (0 : E**) 1 := by sorry

lemma surjective_iff_ball_le_range {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} : Surjective f ↔ ∃ s : Set F, ∃ ρ > 0, ball 0 ρ ≤ Set.range f := by
  sorry

set_option linter.style.commandStart false

/- Milman-Pettis theorem: every uniformly convex Banach (**FAE: Complete Needed?**) space is\
reflexive. For the time being, we state this property as the surjectivity of
`inclusionInDoubleDual`,
but it must be proven that for normed space this is equivalent to `includionInDoubleDual` being
a homeomorphism. -/
theorem surjective_of_uniformConvexSpace [UniformConvexSpace E] :
    Surjective (inclusionInDoubleDual ℝ E) := by
  let 𝒰₁ := ((inclusionInDoubleDual ℝ E) '' (ball 0 1)) -- image in `E**` of the unit ball in `E`
  let X := (WeakBilin (strongDualPairing ℝ (StrongDual ℝ E))) -- `E**` with the weak topology
  rw [surjective_iff_ball_le_range]
  refine ⟨ball 0 1, _, zero_lt_one, ?_⟩
  intro φ hφ
  let ε := infDist φ 𝒰₁
  have hφ_mem {V : Set _} (hV_mem : φ ∈ V) (hV : IsOpen (X := X) V) : φ ∈ closure V ∩ 𝒰₁ := by
    -- have := mem_closure_iff_infDist_zero **FAE: Use later!**
    apply hV.inter_closure (X := X) (t := 𝒰₁)
    · apply Set.mem_inter hV_mem
      rw [goldstine]
      exact hφ
    · simp
      constructor
      · sorry
      · sorry
  sorry
    -- · apply mem_closure
