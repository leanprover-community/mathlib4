/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.DerivNotation
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Derivatives of Schwartz functions

In this file we define the various notions of derivatives of Schwartz functions.

## Main definitions

* `SchwartzMap.fderivCLM`: The differential as a continuous linear map
  `𝓢(E, F) →L[𝕜] 𝓢(E, E →L[ℝ] F)`
* `SchwartzMap.derivCLM`: The one-dimensional derivative as a continuous linear map
  `𝓢(ℝ, F) →L[𝕜] 𝓢(ℝ, F)`
* `SchwartzMap.instLineDeriv`: The directional derivative with notation `∂_{m} f`

## Main statements

* `SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv`: the iterated directional derivative is given
  by the applied Fréchet derivative of a Schwartz function.
* `SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left`: Integration by parts using the
  directional derivative `∂_{m}`

-/

@[expose] public noncomputable section

variable {ι 𝕜 𝕜' D E F G H V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SchwartzMap

section Derivatives

/-! ### Derivatives of Schwartz functions -/

variable (𝕜)
variable [RCLike 𝕜] [NormedSpace 𝕜 F]

variable (F) in
/-- The 1-dimensional derivative on Schwartz space as a continuous `𝕜`-linear map. -/
def derivCLM : 𝓢(ℝ, F) →L[𝕜] 𝓢(ℝ, F) :=
  mkCLM (deriv ·) (fun f g _ => deriv_add f.differentiableAt g.differentiableAt)
    (fun a f _ => deriv_const_smul a f.differentiableAt)
    (fun f => (contDiff_succ_iff_deriv.mp (f.smooth ⊤)).2.2) fun ⟨k, n⟩ =>
    ⟨{⟨k, n + 1⟩}, 1, zero_le_one, fun f x => by
      simpa only [Real.norm_eq_abs, Finset.sup_singleton, schwartzSeminormFamily_apply, one_mul,
        norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← iteratedDeriv_succ'] using
        f.le_seminorm' 𝕜 k (n + 1) x⟩

@[simp]
theorem derivCLM_apply (f : 𝓢(ℝ, F)) (x : ℝ) : derivCLM 𝕜 F f x = deriv f x :=
  rfl

theorem hasDerivAt (f : 𝓢(ℝ, F)) (x : ℝ) : HasDerivAt f (deriv f x) x :=
  f.differentiableAt.hasDerivAt

variable [SMulCommClass ℝ 𝕜 F]

open LineDeriv

variable (E F) in
/-- The Fréchet derivative on Schwartz space as a continuous `𝕜`-linear map. -/
def fderivCLM : 𝓢(E, F) →L[𝕜] 𝓢(E, E →L[ℝ] F) :=
  mkCLM (fderiv ℝ ·) (fun f g _ => fderiv_add f.differentiableAt g.differentiableAt)
    (fun a f _ => fderiv_const_smul f.differentiableAt a)
    (fun f => (contDiff_succ_iff_fderiv.mp (f.smooth ⊤)).2.2) fun ⟨k, n⟩ =>
    ⟨{⟨k, n + 1⟩}, 1, zero_le_one, fun f x => by
      simpa only [schwartzSeminormFamily_apply, Seminorm.comp_apply, Finset.sup_singleton,
        one_smul, norm_iteratedFDeriv_fderiv, one_mul] using f.le_seminorm 𝕜 k (n + 1) x⟩

@[simp]
theorem fderivCLM_apply (f : 𝓢(E, F)) (x : E) : fderivCLM 𝕜 E F f x = fderiv ℝ f x :=
  rfl

theorem hasFDerivAt (f : 𝓢(E, F)) (x : E) : HasFDerivAt f (fderiv ℝ f x) x :=
  f.differentiableAt.hasFDerivAt

/-- The partial derivative (or directional derivative) in the direction `m : E` as a
continuous linear map on Schwartz space. -/
instance instLineDeriv : LineDeriv E 𝓢(E, F) 𝓢(E, F) where
  lineDerivOp m f := (SchwartzMap.evalCLM ℝ E F m ∘L fderivCLM ℝ E F) f

instance instLineDerivAdd : LineDerivAdd E 𝓢(E, F) 𝓢(E, F) where
  lineDerivOp_add m := (SchwartzMap.evalCLM ℝ E F m ∘L fderivCLM ℝ E F).map_add

instance instLineDerivSMul : LineDerivSMul 𝕜 E 𝓢(E, F) 𝓢(E, F) where
  lineDerivOp_smul m := (SchwartzMap.evalCLM 𝕜 E F m ∘L fderivCLM 𝕜 E F).map_smul

instance instContinuousLineDeriv : ContinuousLineDeriv E 𝓢(E, F) 𝓢(E, F) where
  continuous_lineDerivOp m := (SchwartzMap.evalCLM ℝ E F m ∘L fderivCLM ℝ E F).continuous

open LineDeriv

theorem lineDerivOpCLM_eq (m : E) :
    lineDerivOpCLM 𝕜 𝓢(E, F) m = SchwartzMap.evalCLM 𝕜 E F m ∘L fderivCLM 𝕜 E F := rfl

@[deprecated (since := "2025-11-25")]
alias pderivCLM := lineDerivOpCLM

@[deprecated (since := "2025-11-25")]
alias pderivCLM_apply := LineDeriv.lineDerivOpCLM_apply

theorem lineDerivOp_apply (m : E) (f : 𝓢(E, F)) (x : E) : ∂_{m} f x = lineDeriv ℝ f x m :=
  f.differentiableAt.lineDeriv_eq_fderiv.symm

theorem lineDerivOp_apply_eq_fderiv (m : E) (f : 𝓢(E, F)) (x : E) :
    ∂_{m} f x = fderiv ℝ f x m := rfl

variable [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem lineDerivOp_compCLMOfContinuousLinearEquiv (m : D) (g : D ≃L[ℝ] E) (f : 𝓢(E, F)) :
    ∂_{m} (compCLMOfContinuousLinearEquiv 𝕜 g f) =
    compCLMOfContinuousLinearEquiv 𝕜 g (∂_{g m} f) := by
  ext x
  simp [lineDerivOp_apply_eq_fderiv, ContinuousLinearEquiv.comp_right_fderiv]

@[deprecated (since := "2025-11-25")]
alias iteratedPDeriv := LineDeriv.iteratedLineDerivOpCLM

@[deprecated (since := "2025-11-25")]
alias iteratedPDeriv_zero := LineDeriv.iteratedLineDerivOp_zero

@[deprecated (since := "2025-11-25")]
alias iteratedPDeriv_one := LineDeriv.iteratedLineDerivOp_one

@[deprecated (since := "2025-11-25")]
alias iteratedPDeriv_succ_left := LineDeriv.iteratedLineDerivOp_succ_left

@[deprecated (since := "2025-11-25")]
alias iteratedPDeriv_succ_right := LineDeriv.iteratedLineDerivOp_succ_right

theorem iteratedLineDerivOp_eq_iteratedFDeriv {n : ℕ} {m : Fin n → E} {f : 𝓢(E, F)} {x : E} :
    ∂^{m} f x = iteratedFDeriv ℝ n f x m := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left, iteratedFDeriv_succ_apply_left,
      ← fderiv_continuousMultilinear_apply_const_apply]
    · simp only [lineDerivOp_apply_eq_fderiv, ← ih]
    · exact (f.smooth ⊤).differentiable_iteratedFDeriv (mod_cast ENat.coe_lt_top n) x

@[deprecated (since := "2025-11-25")]
alias iteratedPDeriv_eq_iteratedFDeriv := iteratedLineDerivOp_eq_iteratedFDeriv

end Derivatives

section integration_by_parts

open ENNReal MeasureTheory

section one_dim

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Integration by parts of Schwartz functions for the 1-dimensional derivative.

Version for a general bilinear map. -/
theorem integral_bilinear_deriv_right_eq_neg_left (f : 𝓢(ℝ, E)) (g : 𝓢(ℝ, F))
    (L : E →L[ℝ] F →L[ℝ] V) :
    ∫ (x : ℝ), L (f x) (deriv g x) = -∫ (x : ℝ), L (deriv f x) (g x) :=
  MeasureTheory.integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    f.hasDerivAt g.hasDerivAt (pairing L f (derivCLM ℝ F g)).integrable
    (pairing L (derivCLM ℝ E f) g).integrable (pairing L f g).integrable

variable [NormedRing 𝕜] [NormedSpace ℝ 𝕜] [IsScalarTower ℝ 𝕜 𝕜] [SMulCommClass ℝ 𝕜 𝕜] in
/-- Integration by parts of Schwartz functions for the 1-dimensional derivative.

Version for multiplication of scalar-valued Schwartz functions. -/
theorem integral_mul_deriv_eq_neg_deriv_mul (f : 𝓢(ℝ, 𝕜)) (g : 𝓢(ℝ, 𝕜)) :
    ∫ (x : ℝ), f x * (deriv g x) = -∫ (x : ℝ), deriv f x * (g x) :=
  integral_bilinear_deriv_right_eq_neg_left f g (ContinuousLinearMap.mul ℝ 𝕜)

variable [RCLike 𝕜] [NormedSpace 𝕜 F] [NormedSpace 𝕜 V]

/-- Integration by parts of Schwartz functions for the 1-dimensional derivative.

Version for a Schwartz function with values in continuous linear maps. -/
theorem integral_smul_deriv_right_eq_neg_left (f : 𝓢(ℝ, 𝕜)) (g : 𝓢(ℝ, F)) :
    ∫ (x : ℝ), f x • deriv g x = -∫ (x : ℝ), deriv f x • g x :=
  integral_bilinear_deriv_right_eq_neg_left f g (ContinuousLinearMap.lsmul ℝ 𝕜)

/-- Integration by parts of Schwartz functions for the 1-dimensional derivative.

Version for a Schwartz function with values in continuous linear maps. -/
theorem integral_clm_comp_deriv_right_eq_neg_left (f : 𝓢(ℝ, F →L[𝕜] V)) (g : 𝓢(ℝ, F)) :
    ∫ (x : ℝ), f x (deriv g x) = -∫ (x : ℝ), deriv f x (g x) :=
  integral_bilinear_deriv_right_eq_neg_left f g
    ((ContinuousLinearMap.id 𝕜 (F →L[𝕜] V)).bilinearRestrictScalars ℝ)

end one_dim

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [MeasurableSpace D] {μ : Measure D} [BorelSpace D] [FiniteDimensional ℝ D] [μ.IsAddHaarMeasure]

open scoped LineDeriv

/-- Integration by parts of Schwartz functions for directional derivatives.

Version for a general bilinear map. -/
theorem integral_bilinear_lineDerivOp_right_eq_neg_left (f : 𝓢(D, E)) (g : 𝓢(D, F))
    (L : E →L[ℝ] F →L[ℝ] V) (v : D) :
    ∫ (x : D), L (f x) (∂_{v} g x) ∂μ = -∫ (x : D), L (∂_{v} f x) (g x) ∂μ := by
  apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (v := v)
    (bilinLeftCLM L g.hasTemperateGrowth _).integrable
    (bilinLeftCLM L (∂_{v} g).hasTemperateGrowth _).integrable
    (bilinLeftCLM L g.hasTemperateGrowth _).integrable
  all_goals
  intro x
  exact (hasFDerivAt _ x).hasLineDerivAt v

variable [NormedRing 𝕜] [NormedSpace ℝ 𝕜] [IsScalarTower ℝ 𝕜 𝕜] [SMulCommClass ℝ 𝕜 𝕜] in
/-- Integration by parts of Schwartz functions for directional derivatives.

Version for multiplication of scalar-valued Schwartz functions. -/
theorem integral_mul_lineDerivOp_right_eq_neg_left (f : 𝓢(D, 𝕜)) (g : 𝓢(D, 𝕜)) (v : D) :
    ∫ (x : D), f x * ∂_{v} g x ∂μ = -∫ (x : D), ∂_{v} f x * g x ∂μ :=
  integral_bilinear_lineDerivOp_right_eq_neg_left f g (ContinuousLinearMap.mul ℝ 𝕜) v

variable [RCLike 𝕜] [NormedSpace 𝕜 F] [NormedSpace 𝕜 V]

/-- Integration by parts of Schwartz functions for directional derivatives.

Version for scalar multiplication. -/
theorem integral_smul_lineDerivOp_right_eq_neg_left (f : 𝓢(D, 𝕜)) (g : 𝓢(D, F)) (v : D) :
    ∫ (x : D), f x • ∂_{v} g x ∂μ = -∫ (x : D), ∂_{v} f x • g x ∂μ :=
  integral_bilinear_lineDerivOp_right_eq_neg_left f g (ContinuousLinearMap.lsmul ℝ 𝕜) v

/-- Integration by parts of Schwartz functions for directional derivatives.

Version for a Schwartz function with values in continuous linear maps. -/
theorem integral_clm_comp_lineDerivOp_right_eq_neg_left (f : 𝓢(D, F →L[𝕜] V)) (g : 𝓢(D, F))
    (v : D) : ∫ (x : D), f x (∂_{v} g x) ∂μ = -∫ (x : D), ∂_{v} f x (g x) ∂μ :=
  integral_bilinear_lineDerivOp_right_eq_neg_left f g
    ((ContinuousLinearMap.id 𝕜 (F →L[𝕜] V)).bilinearRestrictScalars ℝ) v

end integration_by_parts

end SchwartzMap
