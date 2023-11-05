/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.FieldTheory.Tower
import Mathlib.Data.IsROrC.Basic

#align_import data.is_R_or_C.lemmas from "leanprover-community/mathlib"@"468b141b14016d54b479eb7a0fff1e360b7e3cf6"

/-! # Further lemmas about `IsROrC` -/


variable {K E : Type*} [IsROrC K]

namespace Polynomial

open Polynomial

theorem ofReal_eval (p : ℝ[X]) (x : ℝ) : (↑(p.eval x) : K) = aeval (↑x) p :=
  (@aeval_algebraMap_apply_eq_algebraMap_eval ℝ K _ _ _ x p).symm

end Polynomial

namespace FiniteDimensional

open Classical

open IsROrC

library_note "IsROrC instance"/--
This instance generates a type-class problem with a metavariable `?m` that should satisfy
`IsROrC ?m`. Since this can only be satisfied by `ℝ` or `ℂ`, this does not cause problems. -/


/-- An `IsROrC` field is finite-dimensional over `ℝ`, since it is spanned by `{1, I}`. -/
-- Porting note: was @[nolint dangerous_instance]
instance isROrC_to_real : FiniteDimensional ℝ K :=
  ⟨⟨{1, I}, by
      rw [eq_top_iff]
      intro a _
      rw [Finset.coe_insert, Finset.coe_singleton, Submodule.mem_span_insert]
      refine' ⟨re a, im a • I, _, _⟩
      · rw [Submodule.mem_span_singleton]
        use im a
      simp [re_add_im a, Algebra.smul_def, algebraMap_eq_ofReal]⟩⟩

variable (K E)
variable [NormedAddCommGroup E] [NormedSpace K E]

/-- A finite dimensional vector space over an `IsROrC` is a proper metric space.

This is not an instance because it would cause a search for `FiniteDimensional ?x E` before
`IsROrC ?x`. -/
theorem proper_isROrC [FiniteDimensional K E] : ProperSpace E := by
  letI : NormedSpace ℝ E := RestrictScalars.normedSpace ℝ K E
  letI : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ K E
  infer_instance

variable {E}

instance IsROrC.properSpace_submodule (S : Submodule K E) [FiniteDimensional K S] :
    ProperSpace S :=
  proper_isROrC K S

end FiniteDimensional

namespace IsROrC

@[simp, isROrC_simps]
theorem reClm_norm : ‖(reClm : K →L[ℝ] ℝ)‖ = 1 := by
  apply le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _)
  convert ContinuousLinearMap.ratio_le_op_norm (reClm : K →L[ℝ] ℝ) (1 : K)
  simp

@[simp, isROrC_simps]
theorem conjCle_norm : ‖(@conjCle K _ : K →L[ℝ] K)‖ = 1 :=
  (@conjLie K _).toLinearIsometry.norm_toContinuousLinearMap

@[simp, isROrC_simps]
theorem ofRealClm_norm : ‖(ofRealClm : ℝ →L[ℝ] K)‖ = 1 :=
  -- Porting note: the following timed out
  -- LinearIsometry.norm_toContinuousLinearMap ofRealLi
  LinearIsometry.norm_toContinuousLinearMap _

end IsROrC
