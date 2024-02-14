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
#align polynomial.of_real_eval Polynomial.ofReal_eval

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
  ⟨{1, I}, by
    suffices ∀ x : K, ∃ a b : ℝ, a • 1 + b • I = x by
      simpa [Submodule.eq_top_iff', Submodule.mem_span_pair]
    exact fun x ↦ ⟨re x, im x, by simp [real_smul_eq_coe_mul]⟩⟩
#align finite_dimensional.is_R_or_C_to_real FiniteDimensional.isROrC_to_real

variable (K E)
variable [NormedAddCommGroup E] [NormedSpace K E]

/-- A finite dimensional vector space over an `IsROrC` is a proper metric space.

This is not an instance because it would cause a search for `FiniteDimensional ?x E` before
`IsROrC ?x`. -/
theorem proper_isROrC [FiniteDimensional K E] : ProperSpace E := by
  letI : NormedSpace ℝ E := RestrictScalars.normedSpace ℝ K E
  letI : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ K E
  infer_instance
#align finite_dimensional.proper_is_R_or_C FiniteDimensional.proper_isROrC

variable {E}

instance IsROrC.properSpace_submodule (S : Submodule K E) [FiniteDimensional K S] :
    ProperSpace S :=
  proper_isROrC K S
#align finite_dimensional.is_R_or_C.proper_space_submodule FiniteDimensional.IsROrC.properSpace_submodule

end FiniteDimensional

namespace IsROrC

@[simp, isROrC_simps]
theorem reCLM_norm : ‖(reCLM : K →L[ℝ] ℝ)‖ = 1 := by
  apply le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _)
  convert ContinuousLinearMap.ratio_le_opNorm (reCLM : K →L[ℝ] ℝ) (1 : K)
  simp
#align is_R_or_C.re_clm_norm IsROrC.reCLM_norm

@[simp, isROrC_simps]
theorem conjCLE_norm : ‖(@conjCLE K _ : K →L[ℝ] K)‖ = 1 :=
  (@conjLIE K _).toLinearIsometry.norm_toContinuousLinearMap
#align is_R_or_C.conj_cle_norm IsROrC.conjCLE_norm

@[simp, isROrC_simps]
theorem ofRealCLM_norm : ‖(ofRealCLM : ℝ →L[ℝ] K)‖ = 1 :=
  -- Porting note: the following timed out
  -- LinearIsometry.norm_toContinuousLinearMap ofRealLI
  LinearIsometry.norm_toContinuousLinearMap _
#align is_R_or_C.of_real_clm_norm IsROrC.ofRealCLM_norm

end IsROrC

namespace Polynomial

open ComplexConjugate in
lemma aeval_conj (p : ℝ[X]) (z : K) : aeval (conj z) p = conj (aeval z p) :=
  aeval_algHom_apply (IsROrC.conjAe (K := K)) z p

lemma aeval_ofReal (p : ℝ[X]) (x : ℝ) : aeval (IsROrC.ofReal x : K) p = eval x p :=
  aeval_algHom_apply IsROrC.ofRealAm x p

end Polynomial
