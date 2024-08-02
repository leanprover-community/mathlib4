/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Yaël Dillies
-/
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Basic

/-! # Further lemmas about `RCLike` -/

open Function
open scoped ComplexConjugate

variable {G K E : Type*}

namespace AddChar
section AddGroup
variable [AddGroup G]

section NormedField
variable [Finite G] [NormedField K]

@[simp] lemma norm_apply (ψ : AddChar G K) (x : G) : ‖ψ x‖ = 1 :=
  (ψ.toMonoidHom.isOfFinOrder $ isOfFinOrder_of_finite _).norm_eq_one

@[simp] lemma coe_ne_zero (ψ : AddChar G K) : (ψ : G → K) ≠ 0 :=
  ne_iff.2 ⟨0, fun h ↦ by simpa only [h, Pi.zero_apply, zero_ne_one] using map_zero_eq_one ψ⟩

end NormedField

section RCLike
variable [RCLike K]

lemma inv_apply_eq_conj [Finite G] (ψ : AddChar G K) (x : G) : (ψ x)⁻¹ = conj (ψ x) :=
  RCLike.inv_eq_conj $ norm_apply _ _

end RCLike
end AddGroup

section AddCommGroup
variable [AddCommGroup G] [RCLike K] {ψ₁ ψ₂ : AddChar G K}

lemma map_neg_eq_conj [Finite G] (ψ : AddChar G K) (x : G) : ψ (-x) = conj (ψ x) := by
  rw [map_neg_eq_inv, RCLike.inv_eq_conj $ norm_apply _ _]

end AddCommGroup
end AddChar

variable [RCLike K]

namespace Polynomial

open Polynomial

theorem ofReal_eval (p : ℝ[X]) (x : ℝ) : (↑(p.eval x) : K) = aeval (↑x) p :=
  (@aeval_algebraMap_apply_eq_algebraMap_eval ℝ K _ _ _ x p).symm

end Polynomial

namespace FiniteDimensional

open scoped Classical

open RCLike

library_note "RCLike instance"/--
This instance generates a type-class problem with a metavariable `?m` that should satisfy
`RCLike ?m`. Since this can only be satisfied by `ℝ` or `ℂ`, this does not cause problems. -/

/-- An `RCLike` field is finite-dimensional over `ℝ`, since it is spanned by `{1, I}`. -/
-- Porting note(#12094): removed nolint; dangerous_instance linter not ported yet
-- @[nolint dangerous_instance]
instance rclike_to_real : FiniteDimensional ℝ K :=
  ⟨{1, I}, by
    suffices ∀ x : K, ∃ a b : ℝ, a • 1 + b • I = x by
      simpa [Submodule.eq_top_iff', Submodule.mem_span_pair]
    exact fun x ↦ ⟨re x, im x, by simp [real_smul_eq_coe_mul]⟩⟩

variable (K E)
variable [NormedAddCommGroup E] [NormedSpace K E]

/-- A finite dimensional vector space over an `RCLike` is a proper metric space.

This is not an instance because it would cause a search for `FiniteDimensional ?x E` before
`RCLike ?x`. -/
theorem proper_rclike [FiniteDimensional K E] : ProperSpace E := by
  letI : NormedSpace ℝ E := RestrictScalars.normedSpace ℝ K E
  letI : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ K E
  infer_instance

variable {E}

instance RCLike.properSpace_submodule (S : Submodule K E) [FiniteDimensional K S] :
    ProperSpace S :=
  proper_rclike K S

end FiniteDimensional

namespace RCLike

@[simp, rclike_simps]
theorem reCLM_norm : ‖(reCLM : K →L[ℝ] ℝ)‖ = 1 := by
  apply le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _)
  convert ContinuousLinearMap.ratio_le_opNorm (reCLM : K →L[ℝ] ℝ) (1 : K)
  simp

@[simp, rclike_simps]
theorem conjCLE_norm : ‖(@conjCLE K _ : K →L[ℝ] K)‖ = 1 :=
  (@conjLIE K _).toLinearIsometry.norm_toContinuousLinearMap

@[simp, rclike_simps]
theorem ofRealCLM_norm : ‖(ofRealCLM : ℝ →L[ℝ] K)‖ = 1 :=
  -- Porting note: the following timed out
  -- LinearIsometry.norm_toContinuousLinearMap ofRealLI
  LinearIsometry.norm_toContinuousLinearMap _

end RCLike

namespace Polynomial

open ComplexConjugate in
lemma aeval_conj (p : ℝ[X]) (z : K) : aeval (conj z) p = conj (aeval z p) :=
  aeval_algHom_apply (RCLike.conjAe (K := K)) z p

lemma aeval_ofReal (p : ℝ[X]) (x : ℝ) : aeval (RCLike.ofReal x : K) p = eval x p :=
  aeval_algHom_apply RCLike.ofRealAm x p

end Polynomial
