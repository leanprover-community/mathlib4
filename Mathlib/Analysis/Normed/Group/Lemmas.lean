/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Further lemmas about normed groups

This file contains further lemmas about normed groups, requiring heavier imports than
`Mathlib/Analysis/Normed/Group/Basic.lean`.

## TODO

- Move lemmas from `Basic` to other places, including this file.

-/

variable {E : Type*} [SeminormedAddCommGroup E]
open NNReal Topology

theorem eventually_nnnorm_sub_lt (x₀ : E) {ε : ℝ≥0} (ε_pos : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ‖x - x₀‖₊ < ε :=
  (continuousAt_id.sub continuousAt_const).nnnorm (gt_mem_nhds <| by simpa)

theorem eventually_norm_sub_lt (x₀ : E) {ε : ℝ} (ε_pos : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ‖x - x₀‖ < ε :=
  (continuousAt_id.sub continuousAt_const).norm (gt_mem_nhds <| by simpa)
