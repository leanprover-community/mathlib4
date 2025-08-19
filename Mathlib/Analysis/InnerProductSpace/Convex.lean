/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/

import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Convexity properties of inner product spaces

## Main results

- `InnerProductSpace.toUniformConvexSpace`: an inner product space is a uniformly convex space.

## Tags

inner product space, Hilbert space, norm

-/


noncomputable section

open RCLike Real Filter Topology ComplexConjugate Finsupp
open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

-- See note [lower instance priority]
instance (priority := 100) InnerProductSpace.toUniformConvexSpace : UniformConvexSpace F :=
  ⟨fun ε hε ↦ by
    refine
      ⟨2 - √(4 - ε ^ 2), sub_pos_of_lt <| (sqrt_lt' zero_lt_two).2 ?_, fun x hx y hy hxy ↦ ?_⟩
    · norm_num
      exact pow_pos hε _
    rw [sub_sub_cancel]
    refine le_sqrt_of_sq_le ?_
    rw [sq, eq_sub_iff_add_eq.2 (parallelogram_law_with_norm ℝ x y), ← sq ‖x - y‖, hx, hy]
    ring_nf
    gcongr⟩

