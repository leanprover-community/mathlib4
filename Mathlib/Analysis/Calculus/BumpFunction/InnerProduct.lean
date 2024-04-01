/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

#align_import analysis.calculus.bump_function_inner from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Smooth bump functions in inner product spaces

In this file we prove that a real inner product space has smooth bump functions,
see `hasContDiffBump_of_innerProductSpace`.

## Keywords

smooth function, bump function, inner product space
-/

open Function Real
open scoped Topology

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Porting note: this definition was hidden inside the next instance.
/-- A base bump function in an inner product space. This construction works in any space with a
norm smooth away from zero but we do not have a typeclass for this. -/
noncomputable def ContDiffBumpBase.ofInnerProductSpace : ContDiffBumpBase E where
  toFun R x := smoothTransition ((R - ‖x‖) / (R - 1))
  mem_Icc _ _ := ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  symmetric _ _ := by simp only [norm_neg]
  smooth := by
    rintro ⟨R, x⟩ ⟨hR : 1 < R, -⟩
    apply ContDiffAt.contDiffWithinAt
    rw [← sub_pos] at hR
    rcases eq_or_ne x 0 with rfl | hx
    · have A : ContinuousAt (fun p : ℝ × E ↦ (p.1 - ‖p.2‖) / (p.1 - 1)) (R, 0) :=
        (continuousAt_fst.sub continuousAt_snd.norm).div
          (continuousAt_fst.sub continuousAt_const) hR.ne'
      have B : ∀ᶠ p in 𝓝 (R, (0 : E)), 1 ≤ (p.1 - ‖p.2‖) / (p.1 - 1) :=
        A.eventually <| le_mem_nhds <| (one_lt_div hR).2 <| sub_lt_sub_left (by simp) _
      refine (contDiffAt_const (c := 1)).congr_of_eventuallyEq <| B.mono fun _ ↦
        smoothTransition.one_of_one_le
    · refine smoothTransition.contDiffAt.comp _ (ContDiffAt.div ?_ ?_ hR.ne')
      · exact contDiffAt_fst.sub (contDiffAt_snd.norm ℝ hx)
      · exact contDiffAt_fst.sub contDiffAt_const
  eq_one R hR x hx := smoothTransition.one_of_one_le <| (one_le_div <| sub_pos.2 hR).2 <|
    sub_le_sub_left hx _
  support R hR := by
    ext x
    rw [mem_support, Ne, smoothTransition.zero_iff_nonpos, not_le, mem_ball_zero_iff]
    simp [div_pos_iff, sq_lt_sq, abs_of_pos (one_pos.trans hR), hR, hR.not_lt]

/-- Any inner product space has smooth bump functions. -/
instance (priority := 100) hasContDiffBump_of_innerProductSpace : HasContDiffBump E :=
  ⟨⟨.ofInnerProductSpace E⟩⟩
#align has_cont_diff_bump_of_inner_product_space hasContDiffBump_of_innerProductSpace
