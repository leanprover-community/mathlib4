/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel

! This file was ported from Lean 3 source module analysis.calculus.deriv
! leanprover-community/mathlib commit e3fb84046afd187b710170887195d50bada934ee
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.Data.Polynomial.Derivative
import Mathlib.LinearAlgebra.AffineSpace.Slope

/-!

# One-dimensional derivatives

This file defines the derivative of a function `f : 𝕜 → F` where `𝕜` is a
normed field and `F` is a normed space over this field. The derivative of
such a function `f` at a point `x` is given by an element `f' : F`.

The theory is developed analogously to the [Fréchet
derivatives](./fderiv.html). We first introduce predicates defined in terms
of the corresponding predicates for Fréchet derivatives:

 - `HasDerivAtFilter f f' x L` states that the function `f` has the
    derivative `f'` at the point `x` as `x` goes along the filter `L`.

 - `HasDerivWithinAt f f' s x` states that the function `f` has the
    derivative `f'` at the point `x` within the subset `s`.

 - `HasDerivAt f f' x` states that the function `f` has the derivative `f'`
    at the point `x`.

 - `HasStrictDerivAt f f' x` states that the function `f` has the derivative `f'`
    at the point `x` in the sense of strict differentiability, i.e.,
   `f y - f z = (y - z) • f' + o (y - z)` as `y, z → x`.

For the last two notions we also define a functional version:

  - `derivWithin f s x` is a derivative of `f` at `x` within `s`. If the
    derivative does not exist, then `derivWithin f s x` equals zero.

  - `deriv f x` is a derivative of `f` at `x`. If the derivative does not
    exist, then `deriv f x` equals zero.

The theorems `fderivWithin_derivWithin` and `fderiv_deriv` show that the
one-dimensional derivatives coincide with the general Fréchet derivatives.

We also show the existence and compute the derivatives of:
  - constants
  - the identity function
  - linear maps
  - addition
  - sum of finitely many functions
  - negation
  - subtraction
  - multiplication
  - star
  - inverse `x → x⁻¹`
  - multiplication of two functions in `𝕜 → 𝕜`
  - multiplication of a function in `𝕜 → 𝕜` and of a function in `𝕜 → E`
  - composition of a function in `𝕜 → F` with a function in `𝕜 → 𝕜`
  - composition of a function in `F → E` with a function in `𝕜 → F`
  - inverse function (assuming that it exists; the inverse function theorem is in `inverse.lean`)
  - division
  - polynomials

For most binary operations we also define `const_op` and `op_const` theorems for the cases when
the first or second argument is a constant. This makes writing chains of `HasDerivAt`'s easier,
and they more frequently lead to the desired result.

We set up the simplifier so that it can compute the derivative of simple functions. For instance,
```lean
example (x : ℝ) : deriv (λ x, cos (sin x) * exp x) x = (cos(sin(x))-sin(sin(x))*cos(x))*exp(x) :=
by { simp, ring }
```

## Implementation notes

Most of the theorems are direct restatements of the corresponding theorems
for Fréchet derivatives.

The strategy to construct simp lemmas that give the simplifier the possibility to compute
derivatives is the same as the one for differentiability statements, as explained in `fderiv.lean`.
See the explanations there.
-/


universe u v w

noncomputable section

open scoped Classical Topology BigOperators Filter ENNReal Polynomial

open Filter Asymptotics Set

open ContinuousLinearMap (smulRight smulRight_one_eq_iff)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

section

variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- `f` has the derivative `f'` at the point `x` as `x` goes along the filter `L`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges along the filter `L`.
-/
def HasDerivAtFilter (f : 𝕜 → F) (f' : F) (x : 𝕜) (L : Filter 𝕜) :=
  HasFDerivAtFilter f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') x L
#align has_deriv_at_filter HasDerivAtFilter

/-- `f` has the derivative `f'` at the point `x` within the subset `s`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
def HasDerivWithinAt (f : 𝕜 → F) (f' : F) (s : Set 𝕜) (x : 𝕜) :=
  HasDerivAtFilter f f' x (𝓝[s] x)
#align has_deriv_within_at HasDerivWithinAt

/-- `f` has the derivative `f'` at the point `x`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x`.
-/
def HasDerivAt (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
  HasDerivAtFilter f f' x (𝓝 x)
#align has_deriv_at HasDerivAt

/-- `f` has the derivative `f'` at the point `x` in the sense of strict differentiability.

That is, `f y - f z = (y - z) • f' + o(y - z)` as `y, z → x`. -/
def HasStrictDerivAt (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
  HasStrictFDerivAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') x
#align has_strict_deriv_at HasStrictDerivAt

/-- Derivative of `f` at the point `x` within the set `s`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', HasDerivWithinAt f f' s x`), then
`f x' = f x + (x' - x) • derivWithin f s x + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
def derivWithin (f : 𝕜 → F) (s : Set 𝕜) (x : 𝕜) :=
  fderivWithin 𝕜 f s x 1
#align deriv_within derivWithin

/-- Derivative of `f` at the point `x`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', HasDerivAt f f' x`), then
`f x' = f x + (x' - x) • deriv f x + o(x' - x)` where `x'` converges to `x`.
-/
def deriv (f : 𝕜 → F) (x : 𝕜) :=
  fderiv 𝕜 f x 1
#align deriv deriv

variable {f f₀ f₁ g : 𝕜 → F}

variable {f' f₀' f₁' g' : F}

variable {x : 𝕜}

variable {s t : Set 𝕜}

variable {L L₁ L₂ : Filter 𝕜}

/-- Expressing `HasFDerivAtFilter f f' x L` in terms of `HasDerivAtFilter` -/
theorem hasFDerivAtFilter_iff_hasDerivAtFilter {f' : 𝕜 →L[𝕜] F} :
    HasFDerivAtFilter f f' x L ↔ HasDerivAtFilter f (f' 1) x L := by simp [HasDerivAtFilter]
#align has_fderiv_at_filter_iff_has_deriv_at_filter hasFDerivAtFilter_iff_hasDerivAtFilter

theorem HasFDerivAtFilter.hasDerivAtFilter {f' : 𝕜 →L[𝕜] F} :
    HasFDerivAtFilter f f' x L → HasDerivAtFilter f (f' 1) x L :=
  hasFDerivAtFilter_iff_hasDerivAtFilter.mp
#align has_fderiv_at_filter.has_deriv_at_filter HasFDerivAtFilter.hasDerivAtFilter

/-- Expressing `HasFDerivWithinAt f f' s x` in terms of `HasDerivWithinAt` -/
theorem hasFDerivWithinAt_iff_hasDerivWithinAt {f' : 𝕜 →L[𝕜] F} :
    HasFDerivWithinAt f f' s x ↔ HasDerivWithinAt f (f' 1) s x :=
  hasFDerivAtFilter_iff_hasDerivAtFilter
#align has_fderiv_within_at_iff_has_deriv_within_at hasFDerivWithinAt_iff_hasDerivWithinAt

/-- Expressing `HasDerivWithinAt f f' s x` in terms of `HasFDerivWithinAt` -/
theorem hasDerivWithinAt_iff_hasFDerivWithinAt {f' : F} :
    HasDerivWithinAt f f' s x ↔ HasFDerivWithinAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') s x :=
  Iff.rfl
#align has_deriv_within_at_iff_has_fderiv_within_at hasDerivWithinAt_iff_hasFDerivWithinAt

theorem HasFDerivWithinAt.hasDerivWithinAt {f' : 𝕜 →L[𝕜] F} :
    HasFDerivWithinAt f f' s x → HasDerivWithinAt f (f' 1) s x :=
  hasFDerivWithinAt_iff_hasDerivWithinAt.mp
#align has_fderiv_within_at.has_deriv_within_at HasFDerivWithinAt.hasDerivWithinAt

theorem HasDerivWithinAt.hasFDerivWithinAt {f' : F} :
    HasDerivWithinAt f f' s x → HasFDerivWithinAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') s x :=
  hasDerivWithinAt_iff_hasFDerivWithinAt.mp
#align has_deriv_within_at.has_fderiv_within_at HasDerivWithinAt.hasFDerivWithinAt

/-- Expressing `HasFDerivAt f f' x` in terms of `HasDerivAt` -/
theorem hasFDerivAt_iff_hasDerivAt {f' : 𝕜 →L[𝕜] F} : HasFDerivAt f f' x ↔ HasDerivAt f (f' 1) x :=
  hasFDerivAtFilter_iff_hasDerivAtFilter
#align has_fderiv_at_iff_has_deriv_at hasFDerivAt_iff_hasDerivAt

theorem HasFDerivAt.hasDerivAt {f' : 𝕜 →L[𝕜] F} : HasFDerivAt f f' x → HasDerivAt f (f' 1) x :=
  hasFDerivAt_iff_hasDerivAt.mp
#align has_fderiv_at.has_deriv_at HasFDerivAt.hasDerivAt

theorem hasStrictFDerivAt_iff_hasStrictDerivAt {f' : 𝕜 →L[𝕜] F} :
    HasStrictFDerivAt f f' x ↔ HasStrictDerivAt f (f' 1) x := by
  simp [HasStrictDerivAt, HasStrictFDerivAt]
#align has_strict_fderiv_at_iff_has_strict_deriv_at hasStrictFDerivAt_iff_hasStrictDerivAt

protected theorem HasStrictFDerivAt.hasStrictDerivAt {f' : 𝕜 →L[𝕜] F} :
    HasStrictFDerivAt f f' x → HasStrictDerivAt f (f' 1) x :=
  hasStrictFDerivAt_iff_hasStrictDerivAt.mp
#align has_strict_fderiv_at.has_strict_deriv_at HasStrictFDerivAt.hasStrictDerivAt

theorem hasStrictDerivAt_iff_hasStrictFDerivAt :
    HasStrictDerivAt f f' x ↔ HasStrictFDerivAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') x :=
  Iff.rfl
#align has_strict_deriv_at_iff_has_strict_fderiv_at hasStrictDerivAt_iff_hasStrictFDerivAt

alias hasStrictDerivAt_iff_hasStrictFDerivAt ↔ HasStrictDerivAt.hasStrictFDerivAt _
#align has_strict_deriv_at.has_strict_fderiv_at HasStrictDerivAt.hasStrictFDerivAt

/-- Expressing `HasDerivAt f f' x` in terms of `HasFDerivAt` -/
theorem hasDerivAt_iff_hasFDerivAt {f' : F} :
    HasDerivAt f f' x ↔ HasFDerivAt f (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') x :=
  Iff.rfl
#align has_deriv_at_iff_has_fderiv_at hasDerivAt_iff_hasFDerivAt

alias hasDerivAt_iff_hasFDerivAt ↔ HasDerivAt.hasFDerivAt _
#align has_deriv_at.has_fderiv_at HasDerivAt.hasFDerivAt

theorem derivWithin_zero_of_not_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) :
    derivWithin f s x = 0 := by
  unfold derivWithin
  rw [fderivWithin_zero_of_not_differentiableWithinAt]
  simp
  assumption
#align deriv_within_zero_of_not_differentiable_within_at derivWithin_zero_of_not_differentiableWithinAt

theorem differentiableWithinAt_of_derivWithin_ne_zero (h : derivWithin f s x ≠ 0) :
    DifferentiableWithinAt 𝕜 f s x :=
  not_imp_comm.1 derivWithin_zero_of_not_differentiableWithinAt h
#align differentiable_within_at_of_deriv_within_ne_zero differentiableWithinAt_of_derivWithin_ne_zero

theorem deriv_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0 := by
  unfold deriv
  rw [fderiv_zero_of_not_differentiableAt]
  simp
  assumption
#align deriv_zero_of_not_differentiable_at deriv_zero_of_not_differentiableAt

theorem differentiableAt_of_deriv_ne_zero (h : deriv f x ≠ 0) : DifferentiableAt 𝕜 f x :=
  not_imp_comm.1 deriv_zero_of_not_differentiableAt h
#align differentiable_at_of_deriv_ne_zero differentiableAt_of_deriv_ne_zero

theorem UniqueDiffWithinAt.eq_deriv (s : Set 𝕜) (H : UniqueDiffWithinAt 𝕜 s x)
    (h : HasDerivWithinAt f f' s x) (h₁ : HasDerivWithinAt f f₁' s x) : f' = f₁' :=
  smulRight_one_eq_iff.mp <| UniqueDiffWithinAt.eq H h h₁
#align unique_diff_within_at.eq_deriv UniqueDiffWithinAt.eq_deriv

theorem hasDerivAtFilter_iff_isLittleO :
    HasDerivAtFilter f f' x L ↔ (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[L] fun x' => x' - x :=
  Iff.rfl
#align has_deriv_at_filter_iff_is_o hasDerivAtFilter_iff_isLittleO

theorem hasDerivAtFilter_iff_tendsto :
    HasDerivAtFilter f f' x L ↔
      Tendsto (fun x' : 𝕜 => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) L (𝓝 0) :=
  hasFDerivAtFilter_iff_tendsto
#align has_deriv_at_filter_iff_tendsto hasDerivAtFilter_iff_tendsto

theorem hasDerivWithinAt_iff_isLittleO :
    HasDerivWithinAt f f' s x ↔
      (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[𝓝[s] x] fun x' => x' - x :=
  Iff.rfl
#align has_deriv_within_at_iff_is_o hasDerivWithinAt_iff_isLittleO

theorem hasDerivWithinAt_iff_tendsto :
    HasDerivWithinAt f f' s x ↔
      Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) (𝓝[s] x) (𝓝 0) :=
  hasFDerivAtFilter_iff_tendsto
#align has_deriv_within_at_iff_tendsto hasDerivWithinAt_iff_tendsto

theorem hasDerivAt_iff_isLittleO :
    HasDerivAt f f' x ↔ (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[𝓝 x] fun x' => x' - x :=
  Iff.rfl
#align has_deriv_at_iff_is_o hasDerivAt_iff_isLittleO

theorem hasDerivAt_iff_tendsto :
    HasDerivAt f f' x ↔ Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) (𝓝 x) (𝓝 0) :=
  hasFDerivAtFilter_iff_tendsto
#align has_deriv_at_iff_tendsto hasDerivAt_iff_tendsto

theorem HasStrictDerivAt.hasDerivAt (h : HasStrictDerivAt f f' x) : HasDerivAt f f' x :=
  h.hasFDerivAt
#align has_strict_deriv_at.has_deriv_at HasStrictDerivAt.hasDerivAt

/-- If the domain has dimension one, then Fréchet derivative is equivalent to the classical
definition with a limit. In this version we have to take the limit along the subset `-{x}`,
because for `y=x` the slope equals zero due to the convention `0⁻¹=0`. -/
theorem hasDerivAtFilter_iff_tendsto_slope {x : 𝕜} {L : Filter 𝕜} :
    HasDerivAtFilter f f' x L ↔ Tendsto (slope f x) (L ⊓ 𝓟 ({x}ᶜ)) (𝓝 f') := by
  conv_lhs =>
    simp only [hasDerivAtFilter_iff_tendsto, (norm_inv _).symm, (norm_smul _ _).symm,
      tendsto_zero_iff_norm_tendsto_zero.symm]
  conv_rhs => rw [← nhds_translation_sub f', tendsto_comap_iff]
  refine' (tendsto_inf_principal_nhds_iff_of_forall_eq <| by simp).symm.trans (tendsto_congr' _)
  refine' (eventually_principal.2 fun z hz => _).filter_mono inf_le_right
  simp only [(· ∘ ·)]
  rw [smul_sub, ← mul_smul, inv_mul_cancel (sub_ne_zero.2 hz), one_smul, slope_def_module]
#align has_deriv_at_filter_iff_tendsto_slope hasDerivAtFilter_iff_tendsto_slope

theorem hasDerivWithinAt_iff_tendsto_slope :
    HasDerivWithinAt f f' s x ↔ Tendsto (slope f x) (𝓝[s \ {x}] x) (𝓝 f') := by
  simp only [HasDerivWithinAt, nhdsWithin, diff_eq, inf_assoc.symm, inf_principal.symm]
  exact hasDerivAtFilter_iff_tendsto_slope
#align has_deriv_within_at_iff_tendsto_slope hasDerivWithinAt_iff_tendsto_slope

theorem hasDerivWithinAt_iff_tendsto_slope' (hs : x ∉ s) :
    HasDerivWithinAt f f' s x ↔ Tendsto (slope f x) (𝓝[s] x) (𝓝 f') := by
  rw [hasDerivWithinAt_iff_tendsto_slope, diff_singleton_eq_self hs]
#align has_deriv_within_at_iff_tendsto_slope' hasDerivWithinAt_iff_tendsto_slope'

theorem hasDerivAt_iff_tendsto_slope : HasDerivAt f f' x ↔ Tendsto (slope f x) (𝓝[≠] x) (𝓝 f') :=
  hasDerivAtFilter_iff_tendsto_slope
#align has_deriv_at_iff_tendsto_slope hasDerivAt_iff_tendsto_slope

theorem hasDerivWithinAt_congr_set {s t u : Set 𝕜} (hu : u ∈ 𝓝 x) (h : s ∩ u = t ∩ u) :
    HasDerivWithinAt f f' s x ↔ HasDerivWithinAt f f' t x := by
  simp_rw [HasDerivWithinAt, nhdsWithin_eq_nhds_within' hu h]
#align has_deriv_within_at_congr_set hasDerivWithinAt_congr_set

alias hasDerivWithinAt_congr_set ↔ HasDerivWithinAt.congr_set _
#align has_deriv_within_at.congr_set HasDerivWithinAt.congr_set

@[simp]
theorem hasDerivWithinAt_diff_singleton :
    HasDerivWithinAt f f' (s \ {x}) x ↔ HasDerivWithinAt f f' s x := by
  simp only [hasDerivWithinAt_iff_tendsto_slope, sdiff_idem]
#align has_deriv_within_at_diff_singleton hasDerivWithinAt_diff_singleton

@[simp]
theorem hasDerivWithinAt_Ioi_iff_Ici [PartialOrder 𝕜] :
    HasDerivWithinAt f f' (Ioi x) x ↔ HasDerivWithinAt f f' (Ici x) x := by
  rw [← Ici_diff_left, hasDerivWithinAt_diff_singleton]
#align has_deriv_within_at_Ioi_iff_Ici hasDerivWithinAt_Ioi_iff_Ici

alias hasDerivWithinAt_Ioi_iff_Ici ↔ HasDerivWithinAt.Ici_of_Ioi HasDerivWithinAt.Ioi_of_Ici
#align has_deriv_within_at.Ici_of_Ioi HasDerivWithinAt.Ici_of_Ioi
#align has_deriv_within_at.Ioi_of_Ici HasDerivWithinAt.Ioi_of_Ici

@[simp]
theorem hasDerivWithinAt_Iio_iff_Iic [PartialOrder 𝕜] :
    HasDerivWithinAt f f' (Iio x) x ↔ HasDerivWithinAt f f' (Iic x) x := by
  rw [← Iic_diff_right, hasDerivWithinAt_diff_singleton]
#align has_deriv_within_at_Iio_iff_Iic hasDerivWithinAt_Iio_iff_Iic

alias hasDerivWithinAt_Iio_iff_Iic ↔ HasDerivWithinAt.Iic_of_Iio HasDerivWithinAt.Iio_of_Iic
#align has_deriv_within_at.Iic_of_Iio HasDerivWithinAt.Iic_of_Iio
#align has_deriv_within_at.Iio_of_Iic HasDerivWithinAt.Iio_of_Iic

theorem HasDerivWithinAt.Ioi_iff_Ioo [LinearOrder 𝕜] [OrderClosedTopology 𝕜] {x y : 𝕜} (h : x < y) :
    HasDerivWithinAt f f' (Ioo x y) x ↔ HasDerivWithinAt f f' (Ioi x) x :=
  hasDerivWithinAt_congr_set (isOpen_Iio.mem_nhds h) <| by
    rw [Ioi_inter_Iio, inter_eq_left_iff_subset]
    exact Ioo_subset_Iio_self
#align has_deriv_within_at.Ioi_iff_Ioo HasDerivWithinAt.Ioi_iff_Ioo

alias HasDerivWithinAt.Ioi_iff_Ioo ↔ HasDerivWithinAt.Ioi_of_Ioo HasDerivWithinAt.Ioo_of_Ioi
#align has_deriv_within_at.Ioi_of_Ioo HasDerivWithinAt.Ioi_of_Ioo
#align has_deriv_within_at.Ioo_of_Ioi HasDerivWithinAt.Ioo_of_Ioi

theorem hasDerivAt_iff_isLittleO_nhds_zero :
    HasDerivAt f f' x ↔ (fun h => f (x + h) - f x - h • f') =o[𝓝 0] fun h => h :=
  hasFDerivAt_iff_isLittleO_nhds_zero
#align has_deriv_at_iff_is_o_nhds_zero hasDerivAt_iff_isLittleO_nhds_zero

theorem HasDerivAtFilter.mono (h : HasDerivAtFilter f f' x L₂) (hst : L₁ ≤ L₂) :
    HasDerivAtFilter f f' x L₁ :=
  HasFDerivAtFilter.mono h hst
#align has_deriv_at_filter.mono HasDerivAtFilter.mono

theorem HasDerivWithinAt.mono (h : HasDerivWithinAt f f' t x) (hst : s ⊆ t) :
    HasDerivWithinAt f f' s x :=
  HasFDerivWithinAt.mono h hst
#align has_deriv_within_at.mono HasDerivWithinAt.mono

theorem HasDerivAt.hasDerivAtFilter (h : HasDerivAt f f' x) (hL : L ≤ 𝓝 x) :
    HasDerivAtFilter f f' x L :=
  HasFDerivAt.hasFDerivAtFilter h hL
#align has_deriv_at.has_deriv_at_filter HasDerivAt.hasDerivAtFilter

theorem HasDerivAt.hasDerivWithinAt (h : HasDerivAt f f' x) : HasDerivWithinAt f f' s x :=
  HasFDerivAt.hasFDerivWithinAt h
#align has_deriv_at.has_deriv_within_at HasDerivAt.hasDerivWithinAt

theorem HasDerivWithinAt.differentiableWithinAt (h : HasDerivWithinAt f f' s x) :
    DifferentiableWithinAt 𝕜 f s x :=
  HasFDerivWithinAt.differentiableWithinAt h
#align has_deriv_within_at.differentiable_within_at HasDerivWithinAt.differentiableWithinAt

theorem HasDerivAt.differentiableAt (h : HasDerivAt f f' x) : DifferentiableAt 𝕜 f x :=
  HasFDerivAt.differentiableAt h
#align has_deriv_at.differentiable_at HasDerivAt.differentiableAt

@[simp]
theorem hasDerivWithinAt_univ : HasDerivWithinAt f f' univ x ↔ HasDerivAt f f' x :=
  hasFDerivWithinAt_univ
#align has_deriv_within_at_univ hasDerivWithinAt_univ

theorem HasDerivAt.unique (h₀ : HasDerivAt f f₀' x) (h₁ : HasDerivAt f f₁' x) : f₀' = f₁' :=
  smulRight_one_eq_iff.mp <| h₀.hasFDerivAt.unique h₁
#align has_deriv_at.unique HasDerivAt.unique

theorem hasDerivWithinAt_inter' (h : t ∈ 𝓝[s] x) :
    HasDerivWithinAt f f' (s ∩ t) x ↔ HasDerivWithinAt f f' s x :=
  hasFDerivWithinAt_inter' h
#align has_deriv_within_at_inter' hasDerivWithinAt_inter'

theorem hasDerivWithinAt_inter (h : t ∈ 𝓝 x) :
    HasDerivWithinAt f f' (s ∩ t) x ↔ HasDerivWithinAt f f' s x :=
  hasFDerivWithinAt_inter h
#align has_deriv_within_at_inter hasDerivWithinAt_inter

theorem HasDerivWithinAt.union (hs : HasDerivWithinAt f f' s x) (ht : HasDerivWithinAt f f' t x) :
    HasDerivWithinAt f f' (s ∪ t) x :=
  hs.hasFDerivWithinAt.union ht.hasFDerivWithinAt
#align has_deriv_within_at.union HasDerivWithinAt.union

theorem HasDerivWithinAt.nhdsWithin (h : HasDerivWithinAt f f' s x) (ht : s ∈ 𝓝[t] x) :
    HasDerivWithinAt f f' t x :=
  (hasDerivWithinAt_inter' ht).1 (h.mono (inter_subset_right _ _))
#align has_deriv_within_at.nhds_within HasDerivWithinAt.nhdsWithin

theorem HasDerivWithinAt.hasDerivAt (h : HasDerivWithinAt f f' s x) (hs : s ∈ 𝓝 x) :
    HasDerivAt f f' x :=
  HasFDerivWithinAt.hasFDerivAt h hs
#align has_deriv_within_at.has_deriv_at HasDerivWithinAt.hasDerivAt

theorem DifferentiableWithinAt.hasDerivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) :
    HasDerivWithinAt f (derivWithin f s x) s x :=
  h.hasFDerivWithinAt.hasDerivWithinAt
#align differentiable_within_at.has_deriv_within_at DifferentiableWithinAt.hasDerivWithinAt

theorem DifferentiableAt.hasDerivAt (h : DifferentiableAt 𝕜 f x) : HasDerivAt f (deriv f x) x :=
  h.hasFDerivAt.hasDerivAt
#align differentiable_at.has_deriv_at DifferentiableAt.hasDerivAt

@[simp]
theorem hasDerivAt_deriv_iff : HasDerivAt f (deriv f x) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => h.differentiableAt, fun h => h.hasDerivAt⟩
#align has_deriv_at_deriv_iff hasDerivAt_deriv_iff

@[simp]
theorem hasDerivWithinAt_derivWithin_iff :
    HasDerivWithinAt f (derivWithin f s x) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => h.differentiableWithinAt, fun h => h.hasDerivWithinAt⟩
#align has_deriv_within_at_deriv_within_iff hasDerivWithinAt_derivWithin_iff

theorem DifferentiableOn.hasDerivAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    HasDerivAt f (deriv f x) x :=
  (h.hasFDerivAt hs).hasDerivAt
#align differentiable_on.has_deriv_at DifferentiableOn.hasDerivAt

theorem HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x = f' :=
  h.differentiableAt.hasDerivAt.unique h
#align has_deriv_at.deriv HasDerivAt.deriv

theorem deriv_eq {f' : 𝕜 → F} (h : ∀ x, HasDerivAt f (f' x) x) : deriv f = f' :=
  funext fun x => (h x).deriv
#align deriv_eq deriv_eq

theorem HasDerivWithinAt.derivWithin (h : HasDerivWithinAt f f' s x)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f' :=
  hxs.eq_deriv _ h.differentiableWithinAt.hasDerivWithinAt h
#align has_deriv_within_at.deriv_within HasDerivWithinAt.derivWithin

theorem fderivWithin_derivWithin : (fderivWithin 𝕜 f s x : 𝕜 → F) 1 = derivWithin f s x :=
  rfl
#align fderiv_within_deriv_within fderivWithin_derivWithin

theorem derivWithin_fderivWithin :
    smulRight (1 : 𝕜 →L[𝕜] 𝕜) (derivWithin f s x) = fderivWithin 𝕜 f s x := by simp [derivWithin]
#align deriv_within_fderiv_within derivWithin_fderivWithin

theorem fderiv_deriv : (fderiv 𝕜 f x : 𝕜 → F) 1 = deriv f x :=
  rfl
#align fderiv_deriv fderiv_deriv

theorem deriv_fderiv : smulRight (1 : 𝕜 →L[𝕜] 𝕜) (deriv f x) = fderiv 𝕜 f x := by simp [deriv]
#align deriv_fderiv deriv_fderiv

theorem DifferentiableAt.derivWithin (h : DifferentiableAt 𝕜 f x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f s x = deriv f x := by
  unfold derivWithin deriv
  rw [h.fderivWithin hxs]
#align differentiable_at.deriv_within DifferentiableAt.derivWithin

theorem HasDerivWithinAt.deriv_eq_zero (hd : HasDerivWithinAt f 0 s x)
    (H : UniqueDiffWithinAt 𝕜 s x) : deriv f x = 0 :=
  (em' (DifferentiableAt 𝕜 f x)).elim deriv_zero_of_not_differentiableAt fun h =>
    H.eq_deriv _ h.hasDerivAt.hasDerivWithinAt hd
#align has_deriv_within_at.deriv_eq_zero HasDerivWithinAt.deriv_eq_zero

theorem derivWithin_subset (st : s ⊆ t) (ht : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f t x) : derivWithin f s x = derivWithin f t x :=
  ((DifferentiableWithinAt.hasDerivWithinAt h).mono st).derivWithin ht
#align deriv_within_subset derivWithin_subset

@[simp]
theorem derivWithin_univ : derivWithin f univ = deriv f := by
  ext
  unfold derivWithin deriv
  rw [fderivWithin_univ]
#align deriv_within_univ derivWithin_univ

theorem derivWithin_inter (ht : t ∈ 𝓝 x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f (s ∩ t) x = derivWithin f s x := by
  unfold derivWithin
  rw [fderivWithin_inter ht hs]
#align deriv_within_inter derivWithin_inter

theorem derivWithin_of_open (hs : IsOpen s) (hx : x ∈ s) : derivWithin f s x = deriv f x := by
  unfold derivWithin
  rw [fderivWithin_of_open hs hx]
  rfl
#align deriv_within_of_open derivWithin_of_open

theorem deriv_mem_iff {f : 𝕜 → F} {s : Set F} {x : 𝕜} :
    deriv f x ∈ s ↔
      DifferentiableAt 𝕜 f x ∧ deriv f x ∈ s ∨ ¬DifferentiableAt 𝕜 f x ∧ (0 : F) ∈ s :=
  by by_cases hx : DifferentiableAt 𝕜 f x <;> simp [deriv_zero_of_not_differentiableAt, *]
#align deriv_mem_iff deriv_mem_iff

theorem derivWithin_mem_iff {f : 𝕜 → F} {t : Set 𝕜} {s : Set F} {x : 𝕜} :
    derivWithin f t x ∈ s ↔
      DifferentiableWithinAt 𝕜 f t x ∧ derivWithin f t x ∈ s ∨
        ¬DifferentiableWithinAt 𝕜 f t x ∧ (0 : F) ∈ s := by
  by_cases hx : DifferentiableWithinAt 𝕜 f t x <;>
    simp [derivWithin_zero_of_not_differentiableWithinAt, *]
#align deriv_within_mem_iff derivWithin_mem_iff

theorem differentiableWithinAt_Ioi_iff_Ici [PartialOrder 𝕜] :
    DifferentiableWithinAt 𝕜 f (Ioi x) x ↔ DifferentiableWithinAt 𝕜 f (Ici x) x :=
  ⟨fun h => h.hasDerivWithinAt.Ici_of_Ioi.differentiableWithinAt, fun h =>
    h.hasDerivWithinAt.Ioi_of_Ici.differentiableWithinAt⟩
#align differentiable_within_at_Ioi_iff_Ici differentiableWithinAt_Ioi_iff_Ici

theorem derivWithin_Ioi_eq_Ici {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E)
    (x : ℝ) : derivWithin f (Ioi x) x = derivWithin f (Ici x) x := by
  by_cases H : DifferentiableWithinAt ℝ f (Ioi x) x
  · have A := H.hasDerivWithinAt.Ici_of_Ioi
    have B := (differentiableWithinAt_Ioi_iff_Ici.1 H).hasDerivWithinAt
    simpa using (uniqueDiffOn_Ici x).eq left_mem_Ici A B
  · rw [derivWithin_zero_of_not_differentiableWithinAt H,
      derivWithin_zero_of_not_differentiableWithinAt]
    rwa [differentiableWithinAt_Ioi_iff_Ici] at H
#align deriv_within_Ioi_eq_Ici derivWithin_Ioi_eq_Ici

section congr

/-! ### Congruence properties of derivatives -/

theorem Filter.EventuallyEq.hasDerivAtFilter_iff (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x)
    (h₁ : f₀' = f₁') : HasDerivAtFilter f₀ f₀' x L ↔ HasDerivAtFilter f₁ f₁' x L :=
  h₀.hasFDerivAtFilter_iff hx (by simp [h₁])
#align filter.eventually_eq.has_deriv_at_filter_iff Filter.EventuallyEq.hasDerivAtFilter_iff

theorem HasDerivAtFilter.congr_of_eventuallyEq (h : HasDerivAtFilter f f' x L) (hL : f₁ =ᶠ[L] f)
    (hx : f₁ x = f x) : HasDerivAtFilter f₁ f' x L := by rwa [hL.hasDerivAtFilter_iff hx rfl]
#align has_deriv_at_filter.congr_of_eventually_eq HasDerivAtFilter.congr_of_eventuallyEq

theorem HasDerivWithinAt.congr_mono (h : HasDerivWithinAt f f' s x) (ht : ∀ x ∈ t, f₁ x = f x)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasDerivWithinAt f₁ f' t x :=
  HasFDerivWithinAt.congr_mono h ht hx h₁
#align has_deriv_within_at.congr_mono HasDerivWithinAt.congr_mono

theorem HasDerivWithinAt.congr (h : HasDerivWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : HasDerivWithinAt f₁ f' s x :=
  h.congr_mono hs hx (Subset.refl _)
#align has_deriv_within_at.congr HasDerivWithinAt.congr

theorem HasDerivWithinAt.congr_of_mem (h : HasDerivWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : x ∈ s) : HasDerivWithinAt f₁ f' s x :=
  h.congr hs (hs _ hx)
#align has_deriv_within_at.congr_of_mem HasDerivWithinAt.congr_of_mem

theorem HasDerivWithinAt.congr_of_eventuallyEq (h : HasDerivWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasDerivWithinAt f₁ f' s x :=
  HasDerivAtFilter.congr_of_eventuallyEq h h₁ hx
#align has_deriv_within_at.congr_of_eventually_eq HasDerivWithinAt.congr_of_eventuallyEq

theorem HasDerivWithinAt.congr_of_eventuallyEq_of_mem (h : HasDerivWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : HasDerivWithinAt f₁ f' s x :=
  h.congr_of_eventuallyEq h₁ (h₁.eq_of_nhdsWithin hx)
#align has_deriv_within_at.congr_of_eventually_eq_of_mem HasDerivWithinAt.congr_of_eventuallyEq_of_mem

theorem HasDerivAt.congr_of_eventuallyEq (h : HasDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasDerivAt f₁ f' x :=
  HasDerivAtFilter.congr_of_eventuallyEq h h₁ (mem_of_mem_nhds h₁ : _)
#align has_deriv_at.congr_of_eventually_eq HasDerivAt.congr_of_eventuallyEq

theorem Filter.EventuallyEq.derivWithin_eq (hs : UniqueDiffWithinAt 𝕜 s x) (hL : f₁ =ᶠ[𝓝[s] x] f)
    (hx : f₁ x = f x) : derivWithin f₁ s x = derivWithin f s x := by
  unfold derivWithin
  rw [hL.fderivWithin_eq hs hx]
#align filter.eventually_eq.deriv_within_eq Filter.EventuallyEq.derivWithin_eq

theorem derivWithin_congr (hs : UniqueDiffWithinAt 𝕜 s x) (hL : ∀ y ∈ s, f₁ y = f y)
    (hx : f₁ x = f x) : derivWithin f₁ s x = derivWithin f s x := by
  unfold derivWithin
  rw [fderivWithin_congr hs hL hx]
#align deriv_within_congr derivWithin_congr

theorem Filter.EventuallyEq.deriv_eq (hL : f₁ =ᶠ[𝓝 x] f) : deriv f₁ x = deriv f x := by
  unfold deriv
  rwa [Filter.EventuallyEq.fderiv_eq]
#align filter.eventually_eq.deriv_eq Filter.EventuallyEq.deriv_eq

protected theorem Filter.EventuallyEq.deriv (h : f₁ =ᶠ[𝓝 x] f) : deriv f₁ =ᶠ[𝓝 x] deriv f :=
  h.eventuallyEq_nhds.mono fun _ h => h.deriv_eq
#align filter.eventually_eq.deriv Filter.EventuallyEq.deriv

end congr

section id

/-! ### Derivative of the identity -/

variable (s x L)

theorem hasDerivAtFilter_id : HasDerivAtFilter id 1 x L :=
  (hasFDerivAtFilter_id x L).hasDerivAtFilter
#align has_deriv_at_filter_id hasDerivAtFilter_id

theorem hasDerivWithinAt_id : HasDerivWithinAt id 1 s x :=
  hasDerivAtFilter_id _ _
#align has_deriv_within_at_id hasDerivWithinAt_id

theorem hasDerivAt_id : HasDerivAt id 1 x :=
  hasDerivAtFilter_id _ _
#align has_deriv_at_id hasDerivAt_id

theorem hasDerivAt_id' : HasDerivAt (fun x : 𝕜 => x) 1 x :=
  hasDerivAtFilter_id _ _
#align has_deriv_at_id' hasDerivAt_id'

theorem hasStrictDerivAt_id : HasStrictDerivAt id 1 x :=
  (hasStrictFDerivAt_id x).hasStrictDerivAt
#align has_strict_deriv_at_id hasStrictDerivAt_id

theorem deriv_id : deriv id x = 1 :=
  HasDerivAt.deriv (hasDerivAt_id x)
#align deriv_id deriv_id

@[simp]
theorem deriv_id' : deriv (@id 𝕜) = fun _ => 1 :=
  funext deriv_id
#align deriv_id' deriv_id'

@[simp]
theorem deriv_id'' : (deriv fun x : 𝕜 => x) = fun _ => 1 :=
  deriv_id'
#align deriv_id'' deriv_id''

theorem derivWithin_id (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin id s x = 1 :=
  (hasDerivWithinAt_id x s).derivWithin hxs
#align deriv_within_id derivWithin_id

end id

section Const

/-! ### Derivative of constant functions -/

variable (c : F) (s x L)

theorem hasDerivAtFilter_const : HasDerivAtFilter (fun _ => c) 0 x L :=
  (hasFDerivAtFilter_const c x L).hasDerivAtFilter
#align has_deriv_at_filter_const hasDerivAtFilter_const

theorem hasStrictDerivAt_const : HasStrictDerivAt (fun _ => c) 0 x :=
  (hasStrictFDerivAt_const c x).hasStrictDerivAt
#align has_strict_deriv_at_const hasStrictDerivAt_const

theorem hasDerivWithinAt_const : HasDerivWithinAt (fun _ => c) 0 s x :=
  hasDerivAtFilter_const _ _ _
#align has_deriv_within_at_const hasDerivWithinAt_const

theorem hasDerivAt_const : HasDerivAt (fun _ => c) 0 x :=
  hasDerivAtFilter_const _ _ _
#align has_deriv_at_const hasDerivAt_const

theorem deriv_const : deriv (fun _ => c) x = 0 :=
  HasDerivAt.deriv (hasDerivAt_const x c)
#align deriv_const deriv_const

@[simp]
theorem deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0 :=
  funext fun x => deriv_const x c
#align deriv_const' deriv_const'

theorem derivWithin_const (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin (fun _ => c) s x = 0 :=
  (hasDerivWithinAt_const _ _ _).derivWithin hxs
#align deriv_within_const derivWithin_const

end Const

section ContinuousLinearMap

/-! ### Derivative of continuous linear maps -/

variable (e : 𝕜 →L[𝕜] F)

protected theorem ContinuousLinearMap.hasDerivAtFilter : HasDerivAtFilter e (e 1) x L :=
  e.hasFDerivAtFilter.hasDerivAtFilter
#align continuous_linear_map.has_deriv_at_filter ContinuousLinearMap.hasDerivAtFilter

protected theorem ContinuousLinearMap.hasStrictDerivAt : HasStrictDerivAt e (e 1) x :=
  e.hasStrictFDerivAt.hasStrictDerivAt
#align continuous_linear_map.has_strict_deriv_at ContinuousLinearMap.hasStrictDerivAt

protected theorem ContinuousLinearMap.hasDerivAt : HasDerivAt e (e 1) x :=
  e.hasDerivAtFilter
#align continuous_linear_map.has_deriv_at ContinuousLinearMap.hasDerivAt

protected theorem ContinuousLinearMap.hasDerivWithinAt : HasDerivWithinAt e (e 1) s x :=
  e.hasDerivAtFilter
#align continuous_linear_map.has_deriv_within_at ContinuousLinearMap.hasDerivWithinAt

@[simp]
protected theorem ContinuousLinearMap.deriv : deriv e x = e 1 :=
  e.hasDerivAt.deriv
#align continuous_linear_map.deriv ContinuousLinearMap.deriv

protected theorem ContinuousLinearMap.derivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin e s x = e 1 :=
  e.hasDerivWithinAt.derivWithin hxs
#align continuous_linear_map.deriv_within ContinuousLinearMap.derivWithin

end ContinuousLinearMap

section LinearMap

/-! ### Derivative of bundled linear maps -/

variable (e : 𝕜 →ₗ[𝕜] F)

protected theorem LinearMap.hasDerivAtFilter : HasDerivAtFilter e (e 1) x L :=
  e.toContinuousLinearMap₁.hasDerivAtFilter
#align linear_map.has_deriv_at_filter LinearMap.hasDerivAtFilter

protected theorem LinearMap.hasStrictDerivAt : HasStrictDerivAt e (e 1) x :=
  e.toContinuousLinearMap₁.hasStrictDerivAt
#align linear_map.has_strict_deriv_at LinearMap.hasStrictDerivAt

protected theorem LinearMap.hasDerivAt : HasDerivAt e (e 1) x :=
  e.hasDerivAtFilter
#align linear_map.has_deriv_at LinearMap.hasDerivAt

protected theorem LinearMap.hasDerivWithinAt : HasDerivWithinAt e (e 1) s x :=
  e.hasDerivAtFilter
#align linear_map.has_deriv_within_at LinearMap.hasDerivWithinAt

@[simp]
protected theorem LinearMap.deriv : deriv e x = e 1 :=
  e.hasDerivAt.deriv
#align linear_map.deriv LinearMap.deriv

protected theorem LinearMap.derivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin e s x = e 1 :=
  e.hasDerivWithinAt.derivWithin hxs
#align linear_map.deriv_within LinearMap.derivWithin

end LinearMap

section Add

/-! ### Derivative of the sum of two functions -/


nonrec theorem HasDerivAtFilter.add (hf : HasDerivAtFilter f f' x L)
    (hg : HasDerivAtFilter g g' x L) : HasDerivAtFilter (fun y => f y + g y) (f' + g') x L := by
  simpa using (hf.add hg).hasDerivAtFilter
#align has_deriv_at_filter.add HasDerivAtFilter.add

nonrec theorem HasStrictDerivAt.add (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x) :
    HasStrictDerivAt (fun y => f y + g y) (f' + g') x := by simpa using (hf.add hg).hasStrictDerivAt
#align has_strict_deriv_at.add HasStrictDerivAt.add

nonrec theorem HasDerivWithinAt.add (hf : HasDerivWithinAt f f' s x)
    (hg : HasDerivWithinAt g g' s x) : HasDerivWithinAt (fun y => f y + g y) (f' + g') s x :=
  hf.add hg
#align has_deriv_within_at.add HasDerivWithinAt.add

nonrec theorem HasDerivAt.add (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun x => f x + g x) (f' + g') x :=
  hf.add hg
#align has_deriv_at.add HasDerivAt.add

theorem derivWithin_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin (fun y => f y + g y) s x = derivWithin f s x + derivWithin g s x :=
  (hf.hasDerivWithinAt.add hg.hasDerivWithinAt).derivWithin hxs
#align deriv_within_add derivWithin_add

@[simp]
theorem deriv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv (fun y => f y + g y) x = deriv f x + deriv g x :=
  (hf.hasDerivAt.add hg.hasDerivAt).deriv
#align deriv_add deriv_add

theorem HasDerivAtFilter.add_const (hf : HasDerivAtFilter f f' x L) (c : F) :
    HasDerivAtFilter (fun y => f y + c) f' x L :=
  add_zero f' ▸ hf.add (hasDerivAtFilter_const x L c)
#align has_deriv_at_filter.add_const HasDerivAtFilter.add_const

nonrec theorem HasDerivWithinAt.add_const (hf : HasDerivWithinAt f f' s x) (c : F) :
    HasDerivWithinAt (fun y => f y + c) f' s x :=
  hf.add_const c
#align has_deriv_within_at.add_const HasDerivWithinAt.add_const

nonrec theorem HasDerivAt.add_const (hf : HasDerivAt f f' x) (c : F) :
    HasDerivAt (fun x => f x + c) f' x :=
  hf.add_const c
#align has_deriv_at.add_const HasDerivAt.add_const

theorem derivWithin_add_const (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    derivWithin (fun y => f y + c) s x = derivWithin f s x := by
  simp only [derivWithin, fderivWithin_add_const hxs]
#align deriv_within_add_const derivWithin_add_const

theorem deriv_add_const (c : F) : deriv (fun y => f y + c) x = deriv f x := by
  simp only [deriv, fderiv_add_const]
#align deriv_add_const deriv_add_const

@[simp]
theorem deriv_add_const' (c : F) : (deriv fun y => f y + c) = deriv f :=
  funext fun _ => deriv_add_const c
#align deriv_add_const' deriv_add_const'

theorem HasDerivAtFilter.const_add (c : F) (hf : HasDerivAtFilter f f' x L) :
    HasDerivAtFilter (fun y => c + f y) f' x L :=
  zero_add f' ▸ (hasDerivAtFilter_const x L c).add hf
#align has_deriv_at_filter.const_add HasDerivAtFilter.const_add

nonrec theorem HasDerivWithinAt.const_add (c : F) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun y => c + f y) f' s x :=
  hf.const_add c
#align has_deriv_within_at.const_add HasDerivWithinAt.const_add

nonrec theorem HasDerivAt.const_add (c : F) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => c + f x) f' x :=
  hf.const_add c
#align has_deriv_at.const_add HasDerivAt.const_add

theorem derivWithin_const_add (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    derivWithin (fun y => c + f y) s x = derivWithin f s x := by
  simp only [derivWithin, fderivWithin_const_add hxs]
#align deriv_within_const_add derivWithin_const_add

theorem deriv_const_add (c : F) : deriv (fun y => c + f y) x = deriv f x := by
  simp only [deriv, fderiv_const_add]
#align deriv_const_add deriv_const_add

@[simp]
theorem deriv_const_add' (c : F) : (deriv fun y => c + f y) = deriv f :=
  funext fun _ => deriv_const_add c
#align deriv_const_add' deriv_const_add'

end Add

section Sum

/-! ### Derivative of a finite sum of functions -/


open BigOperators

variable {ι : Type _} {u : Finset ι} {A : ι → 𝕜 → F} {A' : ι → F}

theorem HasDerivAtFilter.sum (h : ∀ i ∈ u, HasDerivAtFilter (A i) (A' i) x L) :
    HasDerivAtFilter (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x L := by
  simpa [ContinuousLinearMap.sum_apply] using (HasFDerivAtFilter.sum h).hasDerivAtFilter
#align has_deriv_at_filter.sum HasDerivAtFilter.sum

theorem HasStrictDerivAt.sum (h : ∀ i ∈ u, HasStrictDerivAt (A i) (A' i) x) :
    HasStrictDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x := by
  simpa [ContinuousLinearMap.sum_apply] using (HasStrictFDerivAt.sum h).hasStrictDerivAt
#align has_strict_deriv_at.sum HasStrictDerivAt.sum

theorem HasDerivWithinAt.sum (h : ∀ i ∈ u, HasDerivWithinAt (A i) (A' i) s x) :
    HasDerivWithinAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) s x :=
  HasDerivAtFilter.sum h
#align has_deriv_within_at.sum HasDerivWithinAt.sum

theorem HasDerivAt.sum (h : ∀ i ∈ u, HasDerivAt (A i) (A' i) x) :
    HasDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x :=
  HasDerivAtFilter.sum h
#align has_deriv_at.sum HasDerivAt.sum

theorem derivWithin_sum (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    derivWithin (fun y => ∑ i in u, A i y) s x = ∑ i in u, derivWithin (A i) s x :=
  (HasDerivWithinAt.sum fun i hi => (h i hi).hasDerivWithinAt).derivWithin hxs
#align deriv_within_sum derivWithin_sum

@[simp]
theorem deriv_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    deriv (fun y => ∑ i in u, A i y) x = ∑ i in u, deriv (A i) x :=
  (HasDerivAt.sum fun i hi => (h i hi).hasDerivAt).deriv
#align deriv_sum deriv_sum

end Sum

section Pi

/-! ### Derivatives of functions `f : 𝕜 → Π i, E i` -/


variable {ι : Type _} [Fintype ι] {E' : ι → Type _} [∀ i, NormedAddCommGroup (E' i)]
  [∀ i, NormedSpace 𝕜 (E' i)] {φ : 𝕜 → ∀ i, E' i} {φ' : ∀ i, E' i}

@[simp]
theorem hasStrictDerivAt_pi :
    HasStrictDerivAt φ φ' x ↔ ∀ i, HasStrictDerivAt (fun x => φ x i) (φ' i) x :=
  hasStrictFDerivAt_pi'
#align has_strict_deriv_at_pi hasStrictDerivAt_pi

@[simp]
theorem hasDerivAtFilter_pi :
    HasDerivAtFilter φ φ' x L ↔ ∀ i, HasDerivAtFilter (fun x => φ x i) (φ' i) x L :=
  hasFDerivAtFilter_pi'
#align has_deriv_at_filter_pi hasDerivAtFilter_pi

theorem hasDerivAt_pi : HasDerivAt φ φ' x ↔ ∀ i, HasDerivAt (fun x => φ x i) (φ' i) x :=
  hasDerivAtFilter_pi
#align has_deriv_at_pi hasDerivAt_pi

theorem hasDerivWithinAt_pi :
    HasDerivWithinAt φ φ' s x ↔ ∀ i, HasDerivWithinAt (fun x => φ x i) (φ' i) s x :=
  hasDerivAtFilter_pi
#align has_deriv_within_at_pi hasDerivWithinAt_pi

theorem derivWithin_pi (h : ∀ i, DifferentiableWithinAt 𝕜 (fun x => φ x i) s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin φ s x = fun i => derivWithin (fun x => φ x i) s x :=
  (hasDerivWithinAt_pi.2 fun i => (h i).hasDerivWithinAt).derivWithin hs
#align deriv_within_pi derivWithin_pi

theorem deriv_pi (h : ∀ i, DifferentiableAt 𝕜 (fun x => φ x i) x) :
    deriv φ x = fun i => deriv (fun x => φ x i) x :=
  (hasDerivAt_pi.2 fun i => (h i).hasDerivAt).deriv
#align deriv_pi deriv_pi

end Pi

section Smul

/-! ### Derivative of the multiplication of a scalar function and a vector function -/


variable {𝕜' : Type _} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {c : 𝕜 → 𝕜'} {c' : 𝕜'}

theorem HasDerivWithinAt.smul (hc : HasDerivWithinAt c c' s x) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun y => c y • f y) (c x • f' + c' • f x) s x := by
  simpa using (HasFDerivWithinAt.smul hc hf).hasDerivWithinAt
#align has_deriv_within_at.smul HasDerivWithinAt.smul

theorem HasDerivAt.smul (hc : HasDerivAt c c' x) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => c y • f y) (c x • f' + c' • f x) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.smul hf
#align has_deriv_at.smul HasDerivAt.smul

nonrec theorem HasStrictDerivAt.smul (hc : HasStrictDerivAt c c' x) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun y => c y • f y) (c x • f' + c' • f x) x := by
  simpa using (hc.smul hf).hasStrictDerivAt
#align has_strict_deriv_at.smul HasStrictDerivAt.smul

theorem derivWithin_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    derivWithin (fun y => c y • f y) s x = c x • derivWithin f s x + derivWithin c s x • f x :=
  (hc.hasDerivWithinAt.smul hf.hasDerivWithinAt).derivWithin hxs
#align deriv_within_smul derivWithin_smul

theorem deriv_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    deriv (fun y => c y • f y) x = c x • deriv f x + deriv c x • f x :=
  (hc.hasDerivAt.smul hf.hasDerivAt).deriv
#align deriv_smul deriv_smul

theorem HasStrictDerivAt.smul_const (hc : HasStrictDerivAt c c' x) (f : F) :
    HasStrictDerivAt (fun y => c y • f) (c' • f) x := by
  have := hc.smul (hasStrictDerivAt_const x f)
  rwa [smul_zero, zero_add] at this
#align has_strict_deriv_at.smul_const HasStrictDerivAt.smul_const

theorem HasDerivWithinAt.smul_const (hc : HasDerivWithinAt c c' s x) (f : F) :
    HasDerivWithinAt (fun y => c y • f) (c' • f) s x := by
  have := hc.smul (hasDerivWithinAt_const x s f)
  rwa [smul_zero, zero_add] at this
#align has_deriv_within_at.smul_const HasDerivWithinAt.smul_const

theorem HasDerivAt.smul_const (hc : HasDerivAt c c' x) (f : F) :
    HasDerivAt (fun y => c y • f) (c' • f) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.smul_const f
#align has_deriv_at.smul_const HasDerivAt.smul_const

theorem derivWithin_smul_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    derivWithin (fun y => c y • f) s x = derivWithin c s x • f :=
  (hc.hasDerivWithinAt.smul_const f).derivWithin hxs
#align deriv_within_smul_const derivWithin_smul_const

theorem deriv_smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
    deriv (fun y => c y • f) x = deriv c x • f :=
  (hc.hasDerivAt.smul_const f).deriv
#align deriv_smul_const deriv_smul_const

end Smul

section ConstSmul

variable {R : Type _} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]

nonrec theorem HasStrictDerivAt.const_smul (c : R) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun y => c • f y) (c • f') x := by
  simpa using (hf.const_smul c).hasStrictDerivAt
#align has_strict_deriv_at.const_smul HasStrictDerivAt.const_smul

nonrec theorem HasDerivAtFilter.const_smul (c : R) (hf : HasDerivAtFilter f f' x L) :
    HasDerivAtFilter (fun y => c • f y) (c • f') x L := by
  simpa using (hf.const_smul c).hasDerivAtFilter
#align has_deriv_at_filter.const_smul HasDerivAtFilter.const_smul

nonrec theorem HasDerivWithinAt.const_smul (c : R) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun y => c • f y) (c • f') s x :=
  hf.const_smul c
#align has_deriv_within_at.const_smul HasDerivWithinAt.const_smul

nonrec theorem HasDerivAt.const_smul (c : R) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => c • f y) (c • f') x :=
  hf.const_smul c
#align has_deriv_at.const_smul HasDerivAt.const_smul

theorem derivWithin_const_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (c : R)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    derivWithin (fun y => c • f y) s x = c • derivWithin f s x :=
  (hf.hasDerivWithinAt.const_smul c).derivWithin hxs
#align deriv_within_const_smul derivWithin_const_smul

theorem deriv_const_smul (c : R) (hf : DifferentiableAt 𝕜 f x) :
    deriv (fun y => c • f y) x = c • deriv f x :=
  (hf.hasDerivAt.const_smul c).deriv
#align deriv_const_smul deriv_const_smul

end ConstSmul

section Neg

/-! ### Derivative of the negative of a function -/

nonrec theorem HasDerivAtFilter.neg (h : HasDerivAtFilter f f' x L) :
    HasDerivAtFilter (fun x => -f x) (-f') x L := by simpa using h.neg.hasDerivAtFilter
#align has_deriv_at_filter.neg HasDerivAtFilter.neg

nonrec theorem HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => -f x) (-f') s x :=
  h.neg
#align has_deriv_within_at.neg HasDerivWithinAt.neg

nonrec theorem HasDerivAt.neg (h : HasDerivAt f f' x) : HasDerivAt (fun x => -f x) (-f') x :=
  h.neg
#align has_deriv_at.neg HasDerivAt.neg

nonrec theorem HasStrictDerivAt.neg (h : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => -f x) (-f') x := by simpa using h.neg.hasStrictDerivAt
#align has_strict_deriv_at.neg HasStrictDerivAt.neg

theorem derivWithin.neg (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun y => -f y) s x = -derivWithin f s x := by
  simp only [derivWithin, fderivWithin_neg hxs, ContinuousLinearMap.neg_apply]
#align deriv_within.neg derivWithin.neg

theorem deriv.neg : deriv (fun y => -f y) x = -deriv f x := by
  simp only [deriv, fderiv_neg, ContinuousLinearMap.neg_apply]
#align deriv.neg deriv.neg

@[simp]
theorem deriv.neg' : (deriv fun y => -f y) = fun x => -deriv f x :=
  funext fun _ => deriv.neg
#align deriv.neg' deriv.neg'

end Neg

section Neg2

/-! ### Derivative of the negation function (i.e `has_neg.neg`) -/

variable (s x L)

theorem hasDerivAtFilter_neg : HasDerivAtFilter Neg.neg (-1) x L :=
  HasDerivAtFilter.neg <| hasDerivAtFilter_id _ _
#align has_deriv_at_filter_neg hasDerivAtFilter_neg

theorem hasDerivWithinAt_neg : HasDerivWithinAt Neg.neg (-1) s x :=
  hasDerivAtFilter_neg _ _
#align has_deriv_within_at_neg hasDerivWithinAt_neg

theorem hasDerivAt_neg : HasDerivAt Neg.neg (-1) x :=
  hasDerivAtFilter_neg _ _
#align has_deriv_at_neg hasDerivAt_neg

theorem hasDerivAt_neg' : HasDerivAt (fun x => -x) (-1) x :=
  hasDerivAtFilter_neg _ _
#align has_deriv_at_neg' hasDerivAt_neg'

theorem hasStrictDerivAt_neg : HasStrictDerivAt Neg.neg (-1) x :=
  HasStrictDerivAt.neg <| hasStrictDerivAt_id _
#align has_strict_deriv_at_neg hasStrictDerivAt_neg

theorem deriv_neg : deriv Neg.neg x = -1 :=
  HasDerivAt.deriv (hasDerivAt_neg x)
#align deriv_neg deriv_neg

@[simp]
theorem deriv_neg' : deriv (Neg.neg : 𝕜 → 𝕜) = fun _ => -1 :=
  funext deriv_neg
#align deriv_neg' deriv_neg'

@[simp]
theorem deriv_neg'' : deriv (fun x : 𝕜 => -x) x = -1 :=
  deriv_neg x
#align deriv_neg'' deriv_neg''

theorem derivWithin_neg (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin Neg.neg s x = -1 :=
  (hasDerivWithinAt_neg x s).derivWithin hxs
#align deriv_within_neg derivWithin_neg

theorem differentiable_neg : Differentiable 𝕜 (Neg.neg : 𝕜 → 𝕜) :=
  Differentiable.neg differentiable_id
#align differentiable_neg differentiable_neg

theorem differentiableOn_neg : DifferentiableOn 𝕜 (Neg.neg : 𝕜 → 𝕜) s :=
  DifferentiableOn.neg differentiableOn_id
#align differentiable_on_neg differentiableOn_neg

end Neg2

section Sub

/-! ### Derivative of the difference of two functions -/

theorem HasDerivAtFilter.sub (hf : HasDerivAtFilter f f' x L) (hg : HasDerivAtFilter g g' x L) :
    HasDerivAtFilter (fun x => f x - g x) (f' - g') x L := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
#align has_deriv_at_filter.sub HasDerivAtFilter.sub

nonrec theorem HasDerivWithinAt.sub (hf : HasDerivWithinAt f f' s x)
    (hg : HasDerivWithinAt g g' s x) : HasDerivWithinAt (fun x => f x - g x) (f' - g') s x :=
  hf.sub hg
#align has_deriv_within_at.sub HasDerivWithinAt.sub

nonrec theorem HasDerivAt.sub (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun x => f x - g x) (f' - g') x :=
  hf.sub hg
#align has_deriv_at.sub HasDerivAt.sub

theorem HasStrictDerivAt.sub (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x) :
    HasStrictDerivAt (fun x => f x - g x) (f' - g') x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
#align has_strict_deriv_at.sub HasStrictDerivAt.sub

theorem derivWithin_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin (fun y => f y - g y) s x = derivWithin f s x - derivWithin g s x :=
  (hf.hasDerivWithinAt.sub hg.hasDerivWithinAt).derivWithin hxs
#align deriv_within_sub derivWithin_sub

@[simp]
theorem deriv_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv (fun y => f y - g y) x = deriv f x - deriv g x :=
  (hf.hasDerivAt.sub hg.hasDerivAt).deriv
#align deriv_sub deriv_sub

theorem HasDerivAtFilter.isBigO_sub (h : HasDerivAtFilter f f' x L) :
    (fun x' => f x' - f x) =O[L] fun x' => x' - x :=
  HasFDerivAtFilter.isBigO_sub h
set_option linter.uppercaseLean3 false in
#align has_deriv_at_filter.is_O_sub HasDerivAtFilter.isBigO_sub

nonrec theorem HasDerivAtFilter.isBigO_sub_rev (hf : HasDerivAtFilter f f' x L) (hf' : f' ≠ 0) :
    (fun x' => x' - x) =O[L] fun x' => f x' - f x :=
  suffices AntilipschitzWith ‖f'‖₊⁻¹ (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') from hf.isBigO_sub_rev this
  AddMonoidHomClass.antilipschitz_of_bound (smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') fun x => by
    simp [norm_smul, ← div_eq_inv_mul, mul_div_cancel _ (mt norm_eq_zero.1 hf')]
set_option linter.uppercaseLean3 false in
#align has_deriv_at_filter.is_O_sub_rev HasDerivAtFilter.isBigO_sub_rev

theorem HasDerivAtFilter.sub_const (hf : HasDerivAtFilter f f' x L) (c : F) :
    HasDerivAtFilter (fun x => f x - c) f' x L := by
  simpa only [sub_eq_add_neg] using hf.add_const (-c)
#align has_deriv_at_filter.sub_const HasDerivAtFilter.sub_const

nonrec theorem HasDerivWithinAt.sub_const (hf : HasDerivWithinAt f f' s x) (c : F) :
    HasDerivWithinAt (fun x => f x - c) f' s x :=
  hf.sub_const c
#align has_deriv_within_at.sub_const HasDerivWithinAt.sub_const

nonrec theorem HasDerivAt.sub_const (hf : HasDerivAt f f' x) (c : F) :
    HasDerivAt (fun x => f x - c) f' x :=
  hf.sub_const c
#align has_deriv_at.sub_const HasDerivAt.sub_const

theorem derivWithin_sub_const (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    derivWithin (fun y => f y - c) s x = derivWithin f s x := by
  simp only [derivWithin, fderivWithin_sub_const hxs]
#align deriv_within_sub_const derivWithin_sub_const

theorem deriv_sub_const (c : F) : deriv (fun y => f y - c) x = deriv f x := by
  simp only [deriv, fderiv_sub_const]
#align deriv_sub_const deriv_sub_const

theorem HasDerivAtFilter.const_sub (c : F) (hf : HasDerivAtFilter f f' x L) :
    HasDerivAtFilter (fun x => c - f x) (-f') x L := by
  simpa only [sub_eq_add_neg] using hf.neg.const_add c
#align has_deriv_at_filter.const_sub HasDerivAtFilter.const_sub

nonrec theorem HasDerivWithinAt.const_sub (c : F) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => c - f x) (-f') s x :=
  hf.const_sub c
#align has_deriv_within_at.const_sub HasDerivWithinAt.const_sub

theorem HasStrictDerivAt.const_sub (c : F) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => c - f x) (-f') x := by
  simpa only [sub_eq_add_neg] using hf.neg.const_add c
#align has_strict_deriv_at.const_sub HasStrictDerivAt.const_sub

nonrec theorem HasDerivAt.const_sub (c : F) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => c - f x) (-f') x :=
  hf.const_sub c
#align has_deriv_at.const_sub HasDerivAt.const_sub

theorem derivWithin_const_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    derivWithin (fun y => c - f y) s x = -derivWithin f s x := by
  simp [derivWithin, fderivWithin_const_sub hxs]
#align deriv_within_const_sub derivWithin_const_sub

theorem deriv_const_sub (c : F) : deriv (fun y => c - f y) x = -deriv f x := by
  simp only [← derivWithin_univ,
    derivWithin_const_sub (uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 _ _)]
#align deriv_const_sub deriv_const_sub

end Sub

section Continuous

/-! ### Continuity of a function admitting a derivative -/

nonrec theorem HasDerivAtFilter.tendsto_nhds (hL : L ≤ 𝓝 x) (h : HasDerivAtFilter f f' x L) :
    Tendsto f L (𝓝 (f x)) :=
  h.tendsto_nhds hL
#align has_deriv_at_filter.tendsto_nhds HasDerivAtFilter.tendsto_nhds

theorem HasDerivWithinAt.continuousWithinAt (h : HasDerivWithinAt f f' s x) :
    ContinuousWithinAt f s x :=
  HasDerivAtFilter.tendsto_nhds inf_le_left h
#align has_deriv_within_at.continuous_within_at HasDerivWithinAt.continuousWithinAt

theorem HasDerivAt.continuousAt (h : HasDerivAt f f' x) : ContinuousAt f x :=
  HasDerivAtFilter.tendsto_nhds le_rfl h
#align has_deriv_at.continuous_at HasDerivAt.continuousAt

protected theorem HasDerivAt.continuousOn {f f' : 𝕜 → F} (hderiv : ∀ x ∈ s, HasDerivAt f (f' x) x) :
    ContinuousOn f s := fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
#align has_deriv_at.continuous_on HasDerivAt.continuousOn

end Continuous

section CartesianProduct

/-! ### Derivative of the cartesian product of two functions -/


variable {G : Type w} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable {f₂ : 𝕜 → G} {f₂' : G}

nonrec theorem HasDerivAtFilter.prod (hf₁ : HasDerivAtFilter f₁ f₁' x L)
    (hf₂ : HasDerivAtFilter f₂ f₂' x L) : HasDerivAtFilter (fun x => (f₁ x, f₂ x)) (f₁', f₂') x L :=
  hf₁.prod hf₂
#align has_deriv_at_filter.prod HasDerivAtFilter.prod

nonrec theorem HasDerivWithinAt.prod (hf₁ : HasDerivWithinAt f₁ f₁' s x)
    (hf₂ : HasDerivWithinAt f₂ f₂' s x) : HasDerivWithinAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') s x :=
  hf₁.prod hf₂
#align has_deriv_within_at.prod HasDerivWithinAt.prod

nonrec theorem HasDerivAt.prod (hf₁ : HasDerivAt f₁ f₁' x) (hf₂ : HasDerivAt f₂ f₂' x) :
    HasDerivAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') x :=
  hf₁.prod hf₂
#align has_deriv_at.prod HasDerivAt.prod

nonrec theorem HasStrictDerivAt.prod (hf₁ : HasStrictDerivAt f₁ f₁' x)
    (hf₂ : HasStrictDerivAt f₂ f₂' x) : HasStrictDerivAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') x :=
  hf₁.prod hf₂
#align has_strict_deriv_at.prod HasStrictDerivAt.prod

end CartesianProduct

section Composition

/-!
### Derivative of the composition of a vector function and a scalar function

We use `scomp` in lemmas on composition of vector valued and scalar valued functions, and `comp`
in lemmas on composition of scalar valued functions, in analogy for `smul` and `mul` (and also
because the `comp` version with the shorter name will show up much more often in applications).
The formula for the derivative involves `smul` in `scomp` lemmas, which can be reduced to
usual multiplication in `comp` lemmas.
-/


/- For composition lemmas, we put x explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition -/
variable {𝕜' : Type _} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {s' t' : Set 𝕜'} {h : 𝕜 → 𝕜'} {h₁ : 𝕜 → 𝕜} {h₂ : 𝕜' → 𝕜'} {h' h₂' : 𝕜'}
  {h₁' : 𝕜} {g₁ : 𝕜' → F} {g₁' : F} {L' : Filter 𝕜'} (x)

theorem HasDerivAtFilter.scomp (hg : HasDerivAtFilter g₁ g₁' (h x) L')
    (hh : HasDerivAtFilter h h' x L) (hL : Tendsto h L L') :
    HasDerivAtFilter (g₁ ∘ h) (h' • g₁') x L := by
  simpa using ((hg.restrictScalars 𝕜).comp x hh hL).hasDerivAtFilter
#align has_deriv_at_filter.scomp HasDerivAtFilter.scomp

theorem HasDerivWithinAt.scomp_hasDerivAt (hg : HasDerivWithinAt g₁ g₁' s' (h x))
    (hh : HasDerivAt h h' x) (hs : ∀ x, h x ∈ s') : HasDerivAt (g₁ ∘ h) (h' • g₁') x :=
  hg.scomp x hh <| tendsto_inf.2 ⟨hh.continuousAt, tendsto_principal.2 <| eventually_of_forall hs⟩
#align has_deriv_within_at.scomp_has_deriv_at HasDerivWithinAt.scomp_hasDerivAt

nonrec theorem HasDerivWithinAt.scomp (hg : HasDerivWithinAt g₁ g₁' t' (h x))
    (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s t') :
    HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x :=
  hg.scomp x hh <| hh.continuousWithinAt.tendsto_nhdsWithin hst
#align has_deriv_within_at.scomp HasDerivWithinAt.scomp

/-- The chain rule. -/
nonrec theorem HasDerivAt.scomp (hg : HasDerivAt g₁ g₁' (h x)) (hh : HasDerivAt h h' x) :
    HasDerivAt (g₁ ∘ h) (h' • g₁') x :=
  hg.scomp x hh hh.continuousAt
#align has_deriv_at.scomp HasDerivAt.scomp

theorem HasStrictDerivAt.scomp (hg : HasStrictDerivAt g₁ g₁' (h x)) (hh : HasStrictDerivAt h h' x) :
    HasStrictDerivAt (g₁ ∘ h) (h' • g₁') x := by
  simpa using ((hg.restrictScalars 𝕜).comp x hh).hasStrictDerivAt
#align has_strict_deriv_at.scomp HasStrictDerivAt.scomp

theorem HasDerivAt.scomp_hasDerivWithinAt (hg : HasDerivAt g₁ g₁' (h x))
    (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x :=
  HasDerivWithinAt.scomp x hg.hasDerivWithinAt hh (mapsTo_univ _ _)
#align has_deriv_at.scomp_has_deriv_within_at HasDerivAt.scomp_hasDerivWithinAt

theorem derivWithin.scomp (hg : DifferentiableWithinAt 𝕜' g₁ t' (h x))
    (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s t') (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (g₁ ∘ h) s x = derivWithin h s x • derivWithin g₁ t' (h x) :=
  (HasDerivWithinAt.scomp x hg.hasDerivWithinAt hh.hasDerivWithinAt hs).derivWithin hxs
#align deriv_within.scomp derivWithin.scomp

theorem deriv.scomp (hg : DifferentiableAt 𝕜' g₁ (h x)) (hh : DifferentiableAt 𝕜 h x) :
    deriv (g₁ ∘ h) x = deriv h x • deriv g₁ (h x) :=
  (HasDerivAt.scomp x hg.hasDerivAt hh.hasDerivAt).deriv
#align deriv.scomp deriv.scomp

/-! ### Derivative of the composition of a scalar and vector functions -/


theorem HasDerivAtFilter.comp_hasFDerivAtFilter {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x) {L'' : Filter E}
    (hh₂ : HasDerivAtFilter h₂ h₂' (f x) L') (hf : HasFDerivAtFilter f f' x L'')
    (hL : Tendsto f L'' L') : HasFDerivAtFilter (h₂ ∘ f) (h₂' • f') x L'' := by
  convert (hh₂.restrictScalars 𝕜).comp x hf hL
  ext x
  simp [mul_comm]
#align has_deriv_at_filter.comp_has_fderiv_at_filter HasDerivAtFilter.comp_hasFDerivAtFilter

theorem HasStrictDerivAt.comp_hasStrictFDerivAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
    (hh : HasStrictDerivAt h₂ h₂' (f x)) (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (h₂ ∘ f) (h₂' • f') x := by
  rw [HasStrictDerivAt] at hh
  convert (hh.restrictScalars 𝕜).comp x hf
  ext x
  simp [mul_comm]
#align has_strict_deriv_at.comp_has_strict_fderiv_at HasStrictDerivAt.comp_hasStrictFDerivAt

theorem HasDerivAt.comp_hasFDerivAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
    (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (h₂ ∘ f) (h₂' • f') x :=
  hh.comp_hasFDerivAtFilter x hf hf.continuousAt
#align has_deriv_at.comp_has_fderiv_at HasDerivAt.comp_hasFDerivAt

theorem HasDerivAt.comp_hasFDerivWithinAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s} (x)
    (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (h₂ ∘ f) (h₂' • f') s x :=
  hh.comp_hasFDerivAtFilter x hf hf.continuousWithinAt
#align has_deriv_at.comp_has_fderiv_within_at HasDerivAt.comp_hasFDerivWithinAt

theorem HasDerivWithinAt.comp_hasFDerivWithinAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s t} (x)
    (hh : HasDerivWithinAt h₂ h₂' t (f x)) (hf : HasFDerivWithinAt f f' s x) (hst : MapsTo f s t) :
    HasFDerivWithinAt (h₂ ∘ f) (h₂' • f') s x :=
  hh.comp_hasFDerivAtFilter x hf <| hf.continuousWithinAt.tendsto_nhdsWithin hst
#align has_deriv_within_at.comp_has_fderiv_within_at HasDerivWithinAt.comp_hasFDerivWithinAt

/-! ### Derivative of the composition of two scalar functions -/

theorem HasDerivAtFilter.comp (hh₂ : HasDerivAtFilter h₂ h₂' (h x) L')
    (hh : HasDerivAtFilter h h' x L) (hL : Tendsto h L L') :
    HasDerivAtFilter (h₂ ∘ h) (h₂' * h') x L := by
  rw [mul_comm]
  exact hh₂.scomp x hh hL
#align has_deriv_at_filter.comp HasDerivAtFilter.comp

theorem HasDerivWithinAt.comp (hh₂ : HasDerivWithinAt h₂ h₂' s' (h x))
    (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s s') :
    HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x := by
  rw [mul_comm]
  exact hh₂.scomp x hh hst
#align has_deriv_within_at.comp HasDerivWithinAt.comp

/-- The chain rule. -/
nonrec theorem HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : HasDerivAt h h' x) :
    HasDerivAt (h₂ ∘ h) (h₂' * h') x :=
  hh₂.comp x hh hh.continuousAt
#align has_deriv_at.comp HasDerivAt.comp

theorem HasStrictDerivAt.comp (hh₂ : HasStrictDerivAt h₂ h₂' (h x)) (hh : HasStrictDerivAt h h' x) :
    HasStrictDerivAt (h₂ ∘ h) (h₂' * h') x := by
  rw [mul_comm]
  exact hh₂.scomp x hh
#align has_strict_deriv_at.comp HasStrictDerivAt.comp

theorem HasDerivAt.comp_hasDerivWithinAt (hh₂ : HasDerivAt h₂ h₂' (h x))
    (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x :=
  hh₂.hasDerivWithinAt.comp x hh (mapsTo_univ _ _)
#align has_deriv_at.comp_has_deriv_within_at HasDerivAt.comp_hasDerivWithinAt

theorem derivWithin.comp (hh₂ : DifferentiableWithinAt 𝕜' h₂ s' (h x))
    (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s s') (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (h₂ ∘ h) s x = derivWithin h₂ s' (h x) * derivWithin h s x :=
  (hh₂.hasDerivWithinAt.comp x hh.hasDerivWithinAt hs).derivWithin hxs
#align deriv_within.comp derivWithin.comp

theorem deriv.comp (hh₂ : DifferentiableAt 𝕜' h₂ (h x)) (hh : DifferentiableAt 𝕜 h x) :
    deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x :=
  (hh₂.hasDerivAt.comp x hh.hasDerivAt).deriv
#align deriv.comp deriv.comp

protected nonrec theorem HasDerivAtFilter.iterate {f : 𝕜 → 𝕜} {f' : 𝕜}
    (hf : HasDerivAtFilter f f' x L) (hL : Tendsto f L L) (hx : f x = x) (n : ℕ) :
    HasDerivAtFilter (f^[n]) (f' ^ n) x L := by
  have := hf.iterate hL hx n
  rwa [ContinuousLinearMap.smulRight_one_pow] at this
#align has_deriv_at_filter.iterate HasDerivAtFilter.iterate

protected nonrec theorem HasDerivAt.iterate {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : HasDerivAt f f' x)
    (hx : f x = x) (n : ℕ) : HasDerivAt (f^[n]) (f' ^ n) x :=
  hf.iterate _ (have := hf.tendsto_nhds le_rfl; by rwa [hx] at this) hx n
#align has_deriv_at.iterate HasDerivAt.iterate

protected theorem HasDerivWithinAt.iterate {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : HasDerivWithinAt f f' s x)
    (hx : f x = x) (hs : MapsTo f s s) (n : ℕ) : HasDerivWithinAt (f^[n]) (f' ^ n) s x := by
  have := HasFDerivWithinAt.iterate hf hx hs n
  rwa [ContinuousLinearMap.smulRight_one_pow] at this
#align has_deriv_within_at.iterate HasDerivWithinAt.iterate

protected nonrec  theorem HasStrictDerivAt.iterate {f : 𝕜 → 𝕜} {f' : 𝕜}
    (hf : HasStrictDerivAt f f' x) (hx : f x = x) (n : ℕ) :
    HasStrictDerivAt (f^[n]) (f' ^ n) x := by
  have := hf.iterate hx n
  rwa [ContinuousLinearMap.smulRight_one_pow] at this
#align has_strict_deriv_at.iterate HasStrictDerivAt.iterate

end Composition

section CompositionVector

/-! ### Derivative of the composition of a function between vector spaces and a function on `𝕜` -/

open ContinuousLinearMap

variable {l : F → E} {l' : F →L[𝕜] E}

variable (x)

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative within a set
equal to the Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem HasFDerivWithinAt.comp_hasDerivWithinAt {t : Set F} (hl : HasFDerivWithinAt l l' t (f x))
    (hf : HasDerivWithinAt f f' s x) (hst : MapsTo f s t) :
    HasDerivWithinAt (l ∘ f) (l' f') s x := by
  simpa only [one_apply, one_smul, smulRight_apply, coe_comp', (· ∘ ·)] using
    (hl.comp x hf.hasFDerivWithinAt hst).hasDerivWithinAt
#align has_fderiv_within_at.comp_has_deriv_within_at HasFDerivWithinAt.comp_hasDerivWithinAt

theorem HasFDerivAt.comp_hasDerivWithinAt (hl : HasFDerivAt l l' (f x))
    (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt (l ∘ f) (l' f') s x :=
  hl.hasFDerivWithinAt.comp_hasDerivWithinAt x hf (mapsTo_univ _ _)
#align has_fderiv_at.comp_has_deriv_within_at HasFDerivAt.comp_hasDerivWithinAt

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative equal to the
Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem HasFDerivAt.comp_hasDerivAt (hl : HasFDerivAt l l' (f x)) (hf : HasDerivAt f f' x) :
    HasDerivAt (l ∘ f) (l' f') x :=
  hasDerivWithinAt_univ.mp <| hl.comp_hasDerivWithinAt x hf.hasDerivWithinAt
#align has_fderiv_at.comp_has_deriv_at HasFDerivAt.comp_hasDerivAt

theorem HasStrictFDerivAt.comp_hasStrictDerivAt (hl : HasStrictFDerivAt l l' (f x))
    (hf : HasStrictDerivAt f f' x) : HasStrictDerivAt (l ∘ f) (l' f') x := by
  simpa only [one_apply, one_smul, smulRight_apply, coe_comp', (· ∘ ·)] using
    (hl.comp x hf.hasStrictFDerivAt).hasStrictDerivAt
#align has_strict_fderiv_at.comp_has_strict_deriv_at HasStrictFDerivAt.comp_hasStrictDerivAt

theorem fderivWithin.comp_derivWithin {t : Set F} (hl : DifferentiableWithinAt 𝕜 l t (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) (hs : MapsTo f s t) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (l ∘ f) s x = (fderivWithin 𝕜 l t (f x) : F → E) (derivWithin f s x) :=
  (hl.hasFDerivWithinAt.comp_hasDerivWithinAt x hf.hasDerivWithinAt hs).derivWithin hxs
#align fderiv_within.comp_deriv_within fderivWithin.comp_derivWithin

theorem fderiv.comp_deriv (hl : DifferentiableAt 𝕜 l (f x)) (hf : DifferentiableAt 𝕜 f x) :
    deriv (l ∘ f) x = (fderiv 𝕜 l (f x) : F → E) (deriv f x) :=
  (hl.hasFDerivAt.comp_hasDerivAt x hf.hasDerivAt).deriv
#align fderiv.comp_deriv fderiv.comp_deriv

end CompositionVector

section Mul

/-! ### Derivative of the multiplication of two functions -/


variable {𝕜' 𝔸 : Type _} [NormedField 𝕜'] [NormedRing 𝔸] [NormedAlgebra 𝕜 𝕜'] [NormedAlgebra 𝕜 𝔸]
  {c d : 𝕜 → 𝔸} {c' d' : 𝔸} {u v : 𝕜 → 𝕜'}

theorem HasDerivWithinAt.mul (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x) :
    HasDerivWithinAt (fun y => c y * d y) (c' * d x + c x * d') s x := by
  have := (HasFDerivWithinAt.mul' hc hd).hasDerivWithinAt
  rwa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul, one_smul,
    add_comm] at this
#align has_deriv_within_at.mul HasDerivWithinAt.mul

theorem HasDerivAt.mul (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) :
    HasDerivAt (fun y => c y * d y) (c' * d x + c x * d') x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.mul hd
#align has_deriv_at.mul HasDerivAt.mul

theorem HasStrictDerivAt.mul (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (fun y => c y * d y) (c' * d x + c x * d') x := by
  have := (HasStrictFDerivAt.mul' hc hd).hasStrictDerivAt
  rwa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul, one_smul,
    add_comm] at this
#align has_strict_deriv_at.mul HasStrictDerivAt.mul

theorem derivWithin_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    derivWithin (fun y => c y * d y) s x = derivWithin c s x * d x + c x * derivWithin d s x :=
  (hc.hasDerivWithinAt.mul hd.hasDerivWithinAt).derivWithin hxs
#align deriv_within_mul derivWithin_mul

@[simp]
theorem deriv_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    deriv (fun y => c y * d y) x = deriv c x * d x + c x * deriv d x :=
  (hc.hasDerivAt.mul hd.hasDerivAt).deriv
#align deriv_mul deriv_mul

theorem HasDerivWithinAt.mul_const (hc : HasDerivWithinAt c c' s x) (d : 𝔸) :
    HasDerivWithinAt (fun y => c y * d) (c' * d) s x := by
  convert hc.mul (hasDerivWithinAt_const x s d) using 1
  rw [mul_zero, add_zero]
#align has_deriv_within_at.mul_const HasDerivWithinAt.mul_const

theorem HasDerivAt.mul_const (hc : HasDerivAt c c' x) (d : 𝔸) :
    HasDerivAt (fun y => c y * d) (c' * d) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.mul_const d
#align has_deriv_at.mul_const HasDerivAt.mul_const

theorem hasDerivAt_mul_const (c : 𝕜) : HasDerivAt (fun x => x * c) c x := by
  simpa only [one_mul] using (hasDerivAt_id' x).mul_const c
#align has_deriv_at_mul_const hasDerivAt_mul_const

theorem HasStrictDerivAt.mul_const (hc : HasStrictDerivAt c c' x) (d : 𝔸) :
    HasStrictDerivAt (fun y => c y * d) (c' * d) x := by
  convert hc.mul (hasStrictDerivAt_const x d) using 1
  rw [mul_zero, add_zero]
#align has_strict_deriv_at.mul_const HasStrictDerivAt.mul_const

theorem derivWithin_mul_const (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (d : 𝔸) : derivWithin (fun y => c y * d) s x = derivWithin c s x * d :=
  (hc.hasDerivWithinAt.mul_const d).derivWithin hxs
#align deriv_within_mul_const derivWithin_mul_const

theorem deriv_mul_const (hc : DifferentiableAt 𝕜 c x) (d : 𝔸) :
    deriv (fun y => c y * d) x = deriv c x * d :=
  (hc.hasDerivAt.mul_const d).deriv
#align deriv_mul_const deriv_mul_const

theorem deriv_mul_const_field (v : 𝕜') : deriv (fun y => u y * v) x = deriv u x * v := by
  by_cases hu : DifferentiableAt 𝕜 u x
  · exact deriv_mul_const hu v
  · rw [deriv_zero_of_not_differentiableAt hu, MulZeroClass.zero_mul]
    rcases eq_or_ne v 0 with (rfl | hd)
    · simp only [MulZeroClass.mul_zero, deriv_const]
    · refine' deriv_zero_of_not_differentiableAt (mt (fun H => _) hu)
      simpa only [mul_inv_cancel_right₀ hd] using H.mul_const v⁻¹
#align deriv_mul_const_field deriv_mul_const_field

@[simp]
theorem deriv_mul_const_field' (v : 𝕜') : (deriv fun x => u x * v) = fun x => deriv u x * v :=
  funext fun _ => deriv_mul_const_field v
#align deriv_mul_const_field' deriv_mul_const_field'

theorem HasDerivWithinAt.const_mul (c : 𝔸) (hd : HasDerivWithinAt d d' s x) :
    HasDerivWithinAt (fun y => c * d y) (c * d') s x := by
  convert (hasDerivWithinAt_const x s c).mul hd using 1
  rw [zero_mul, zero_add]
#align has_deriv_within_at.const_mul HasDerivWithinAt.const_mul

theorem HasDerivAt.const_mul (c : 𝔸) (hd : HasDerivAt d d' x) :
    HasDerivAt (fun y => c * d y) (c * d') x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hd.const_mul c
#align has_deriv_at.const_mul HasDerivAt.const_mul

theorem HasStrictDerivAt.const_mul (c : 𝔸) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (fun y => c * d y) (c * d') x := by
  convert (hasStrictDerivAt_const _ _).mul hd using 1
  rw [zero_mul, zero_add]
#align has_strict_deriv_at.const_mul HasStrictDerivAt.const_mul

theorem derivWithin_const_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (c : 𝔸)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    derivWithin (fun y => c * d y) s x = c * derivWithin d s x :=
  (hd.hasDerivWithinAt.const_mul c).derivWithin hxs
#align deriv_within_const_mul derivWithin_const_mul

theorem deriv_const_mul (c : 𝔸) (hd : DifferentiableAt 𝕜 d x) :
    deriv (fun y => c * d y) x = c * deriv d x :=
  (hd.hasDerivAt.const_mul c).deriv
#align deriv_const_mul deriv_const_mul

theorem deriv_const_mul_field (u : 𝕜') : deriv (fun y => u * v y) x = u * deriv v x := by
  simp only [mul_comm u, deriv_mul_const_field]
#align deriv_const_mul_field deriv_const_mul_field

@[simp]
theorem deriv_const_mul_field' (u : 𝕜') : (deriv fun x => u * v x) = fun x => u * deriv v x :=
  funext fun _ => deriv_const_mul_field u
#align deriv_const_mul_field' deriv_const_mul_field'

end Mul

section Inverse

/-! ### Derivative of `x ↦ x⁻¹` -/

theorem hasStrictDerivAt_inv (hx : x ≠ 0) : HasStrictDerivAt Inv.inv (-(x ^ 2)⁻¹) x := by
  suffices
    (fun p : 𝕜 × 𝕜 => (p.1 - p.2) * ((x * x)⁻¹ - (p.1 * p.2)⁻¹)) =o[𝓝 (x, x)] fun p =>
      (p.1 - p.2) * 1 by
    refine' this.congr' _ (eventually_of_forall fun _ => mul_one _)
    refine' Eventually.mono ((isOpen_ne.prod isOpen_ne).mem_nhds ⟨hx, hx⟩) _
    rintro ⟨y, z⟩ ⟨hy, hz⟩
    simp only [mem_setOf_eq] at hy hz
    -- hy : y ≠ 0, hz : z ≠ 0
    field_simp [hx, hy, hz]
    ring
  refine' (isBigO_refl (fun p : 𝕜 × 𝕜 => p.1 - p.2) _).mul_isLittleO ((isLittleO_one_iff 𝕜).2 _)
  rw [← sub_self (x * x)⁻¹]
  exact tendsto_const_nhds.sub ((continuous_mul.tendsto (x, x)).inv₀ <| mul_ne_zero hx hx)
#align has_strict_deriv_at_inv hasStrictDerivAt_inv

theorem hasDerivAt_inv (x_ne_zero : x ≠ 0) : HasDerivAt (fun y => y⁻¹) (-(x ^ 2)⁻¹) x :=
  (hasStrictDerivAt_inv x_ne_zero).hasDerivAt
#align has_deriv_at_inv hasDerivAt_inv

theorem hasDerivWithinAt_inv (x_ne_zero : x ≠ 0) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => x⁻¹) (-(x ^ 2)⁻¹) s x :=
  (hasDerivAt_inv x_ne_zero).hasDerivWithinAt
#align has_deriv_within_at_inv hasDerivWithinAt_inv

theorem differentiableAt_inv : DifferentiableAt 𝕜 (fun x => x⁻¹) x ↔ x ≠ 0 :=
  ⟨fun H => NormedField.continuousAt_inv.1 H.continuousAt, fun H =>
    (hasDerivAt_inv H).differentiableAt⟩
#align differentiable_at_inv differentiableAt_inv

theorem differentiableWithinAt_inv (x_ne_zero : x ≠ 0) :
    DifferentiableWithinAt 𝕜 (fun x => x⁻¹) s x :=
  (differentiableAt_inv.2 x_ne_zero).differentiableWithinAt
#align differentiable_within_at_inv differentiableWithinAt_inv

theorem differentiableOn_inv : DifferentiableOn 𝕜 (fun x : 𝕜 => x⁻¹) { x | x ≠ 0 } := fun _x hx =>
  differentiableWithinAt_inv hx
#align differentiable_on_inv differentiableOn_inv

theorem deriv_inv : deriv (fun x => x⁻¹) x = -(x ^ 2)⁻¹ := by
  rcases eq_or_ne x 0 with (rfl | hne)
  · simp [deriv_zero_of_not_differentiableAt (mt differentiableAt_inv.1 (not_not.2 rfl))]
  · exact (hasDerivAt_inv hne).deriv
#align deriv_inv deriv_inv

@[simp]
theorem deriv_inv' : (deriv fun x : 𝕜 => x⁻¹) = fun x => -(x ^ 2)⁻¹ :=
  funext fun _ => deriv_inv
#align deriv_inv' deriv_inv'

theorem derivWithin_inv (x_ne_zero : x ≠ 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => x⁻¹) s x = -(x ^ 2)⁻¹ := by
  rw [DifferentiableAt.derivWithin (differentiableAt_inv.2 x_ne_zero) hxs]
  exact deriv_inv
#align deriv_within_inv derivWithin_inv

theorem hasFDerivAt_inv (x_ne_zero : x ≠ 0) :
    HasFDerivAt (fun x => x⁻¹) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (-(x ^ 2)⁻¹) : 𝕜 →L[𝕜] 𝕜) x :=
  hasDerivAt_inv x_ne_zero
#align has_fderiv_at_inv hasFDerivAt_inv

theorem hasFDerivWithinAt_inv (x_ne_zero : x ≠ 0) :
    HasFDerivWithinAt (fun x => x⁻¹) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (-(x ^ 2)⁻¹) : 𝕜 →L[𝕜] 𝕜) s x :=
  (hasFDerivAt_inv x_ne_zero).hasFDerivWithinAt
#align has_fderiv_within_at_inv hasFDerivWithinAt_inv

theorem fderiv_inv : fderiv 𝕜 (fun x => x⁻¹) x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (-(x ^ 2)⁻¹) := by
  rw [← deriv_fderiv, deriv_inv]
#align fderiv_inv fderiv_inv

theorem fderivWithin_inv (x_ne_zero : x ≠ 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => x⁻¹) s x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (-(x ^ 2)⁻¹) := by
  rw [DifferentiableAt.fderivWithin (differentiableAt_inv.2 x_ne_zero) hxs]
  exact fderiv_inv
#align fderiv_within_inv fderivWithin_inv

variable {c : 𝕜 → 𝕜} {h : E → 𝕜} {c' : 𝕜} {z : E} {S : Set E}

theorem HasDerivWithinAt.inv (hc : HasDerivWithinAt c c' s x) (hx : c x ≠ 0) :
    HasDerivWithinAt (fun y => (c y)⁻¹) (-c' / c x ^ 2) s x := by
  convert (hasDerivAt_inv hx).comp_hasDerivWithinAt x hc using 1
  field_simp
#align has_deriv_within_at.inv HasDerivWithinAt.inv

theorem HasDerivAt.inv (hc : HasDerivAt c c' x) (hx : c x ≠ 0) :
    HasDerivAt (fun y => (c y)⁻¹) (-c' / c x ^ 2) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.inv hx
#align has_deriv_at.inv HasDerivAt.inv

theorem DifferentiableWithinAt.inv (hf : DifferentiableWithinAt 𝕜 h S z) (hz : h z ≠ 0) :
    DifferentiableWithinAt 𝕜 (fun x => (h x)⁻¹) S z :=
  (differentiableAt_inv.mpr hz).comp_differentiableWithinAt z hf
#align differentiable_within_at.inv DifferentiableWithinAt.inv

@[simp]
theorem DifferentiableAt.inv (hf : DifferentiableAt 𝕜 h z) (hz : h z ≠ 0) :
    DifferentiableAt 𝕜 (fun x => (h x)⁻¹) z :=
  (differentiableAt_inv.mpr hz).comp z hf
#align differentiable_at.inv DifferentiableAt.inv

theorem DifferentiableOn.inv (hf : DifferentiableOn 𝕜 h S) (hz : ∀ x ∈ S, h x ≠ 0) :
    DifferentiableOn 𝕜 (fun x => (h x)⁻¹) S := fun x h => (hf x h).inv (hz x h)
#align differentiable_on.inv DifferentiableOn.inv

@[simp]
theorem Differentiable.inv (hf : Differentiable 𝕜 h) (hz : ∀ x, h x ≠ 0) :
    Differentiable 𝕜 fun x => (h x)⁻¹ := fun x => (hf x).inv (hz x)
#align differentiable.inv Differentiable.inv

theorem derivWithin_inv' (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x ≠ 0)
    (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => (c x)⁻¹) s x = -derivWithin c s x / c x ^ 2 :=
  (hc.hasDerivWithinAt.inv hx).derivWithin hxs
#align deriv_within_inv' derivWithin_inv'

@[simp]
theorem deriv_inv'' (hc : DifferentiableAt 𝕜 c x) (hx : c x ≠ 0) :
    deriv (fun x => (c x)⁻¹) x = -deriv c x / c x ^ 2 :=
  (hc.hasDerivAt.inv hx).deriv
#align deriv_inv'' deriv_inv''

end Inverse

section Division

/-! ### Derivative of `x ↦ c x / d x` -/

variable {𝕜' : Type _} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {c d : 𝕜 → 𝕜'} {c' d' : 𝕜'}

theorem HasDerivWithinAt.div (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x)
    (hx : d x ≠ 0) :
    HasDerivWithinAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) s x := by
  convert hc.mul ((hasDerivAt_inv hx).comp_hasDerivWithinAt x hd) using 1
  · simp only [div_eq_mul_inv, (· ∘ ·)]
  · field_simp
    ring
#align has_deriv_within_at.div HasDerivWithinAt.div

theorem HasStrictDerivAt.div (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x)
    (hx : d x ≠ 0) : HasStrictDerivAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) x := by
  convert hc.mul ((hasStrictDerivAt_inv hx).comp x hd) using 1
  · simp only [div_eq_mul_inv, (· ∘ ·)]
  · field_simp
    ring
#align has_strict_deriv_at.div HasStrictDerivAt.div

theorem HasDerivAt.div (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) (hx : d x ≠ 0) :
    HasDerivAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.div hd hx
#align has_deriv_at.div HasDerivAt.div

theorem DifferentiableWithinAt.div (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) (hx : d x ≠ 0) :
    DifferentiableWithinAt 𝕜 (fun x => c x / d x) s x :=
  (hc.hasDerivWithinAt.div hd.hasDerivWithinAt hx).differentiableWithinAt
#align differentiable_within_at.div DifferentiableWithinAt.div

@[simp]
theorem DifferentiableAt.div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
    (hx : d x ≠ 0) : DifferentiableAt 𝕜 (fun x => c x / d x) x :=
  (hc.hasDerivAt.div hd.hasDerivAt hx).differentiableAt
#align differentiable_at.div DifferentiableAt.div

theorem DifferentiableOn.div (hc : DifferentiableOn 𝕜 c s) (hd : DifferentiableOn 𝕜 d s)
    (hx : ∀ x ∈ s, d x ≠ 0) : DifferentiableOn 𝕜 (fun x => c x / d x) s := fun x h =>
  (hc x h).div (hd x h) (hx x h)
#align differentiable_on.div DifferentiableOn.div

@[simp]
theorem Differentiable.div (hc : Differentiable 𝕜 c) (hd : Differentiable 𝕜 d) (hx : ∀ x, d x ≠ 0) :
    Differentiable 𝕜 fun x => c x / d x := fun x => (hc x).div (hd x) (hx x)
#align differentiable.div Differentiable.div

theorem derivWithin_div (hc : DifferentiableWithinAt 𝕜 c s x) (hd : DifferentiableWithinAt 𝕜 d s x)
    (hx : d x ≠ 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => c x / d x) s x =
      (derivWithin c s x * d x - c x * derivWithin d s x) / d x ^ 2 :=
  (hc.hasDerivWithinAt.div hd.hasDerivWithinAt hx).derivWithin hxs
#align deriv_within_div derivWithin_div

@[simp]
theorem deriv_div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) (hx : d x ≠ 0) :
    deriv (fun x => c x / d x) x = (deriv c x * d x - c x * deriv d x) / d x ^ 2 :=
  (hc.hasDerivAt.div hd.hasDerivAt hx).deriv
#align deriv_div deriv_div

theorem HasDerivAt.div_const (hc : HasDerivAt c c' x) (d : 𝕜') :
    HasDerivAt (fun x => c x / d) (c' / d) x := by
  simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹
#align has_deriv_at.div_const HasDerivAt.div_const

theorem HasDerivWithinAt.div_const (hc : HasDerivWithinAt c c' s x) (d : 𝕜') :
    HasDerivWithinAt (fun x => c x / d) (c' / d) s x := by
  simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹
#align has_deriv_within_at.div_const HasDerivWithinAt.div_const

theorem HasStrictDerivAt.div_const (hc : HasStrictDerivAt c c' x) (d : 𝕜') :
    HasStrictDerivAt (fun x => c x / d) (c' / d) x := by
  simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹
#align has_strict_deriv_at.div_const HasStrictDerivAt.div_const

theorem DifferentiableWithinAt.div_const (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝕜') :
    DifferentiableWithinAt 𝕜 (fun x => c x / d) s x :=
  (hc.hasDerivWithinAt.div_const _).differentiableWithinAt
#align differentiable_within_at.div_const DifferentiableWithinAt.div_const

@[simp]
theorem DifferentiableAt.div_const (hc : DifferentiableAt 𝕜 c x) (d : 𝕜') :
    DifferentiableAt 𝕜 (fun x => c x / d) x :=
  (hc.hasDerivAt.div_const _).differentiableAt
#align differentiable_at.div_const DifferentiableAt.div_const

theorem DifferentiableOn.div_const (hc : DifferentiableOn 𝕜 c s) (d : 𝕜') :
    DifferentiableOn 𝕜 (fun x => c x / d) s := fun x hx => (hc x hx).div_const d
#align differentiable_on.div_const DifferentiableOn.div_const

@[simp]
theorem Differentiable.div_const (hc : Differentiable 𝕜 c) (d : 𝕜') :
    Differentiable 𝕜 fun x => c x / d := fun x => (hc x).div_const d
#align differentiable.div_const Differentiable.div_const

theorem derivWithin_div_const (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝕜')
    (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin (fun x => c x / d) s x = derivWithin c s x / d :=
  by simp [div_eq_inv_mul, derivWithin_const_mul, hc, hxs]
#align deriv_within_div_const derivWithin_div_const

@[simp]
theorem deriv_div_const (d : 𝕜') : deriv (fun x => c x / d) x = deriv c x / d := by
  simp only [div_eq_mul_inv, deriv_mul_const_field]
#align deriv_div_const deriv_div_const

end Division

section Star

/-! ### Derivative of `x ↦ star x` -/


variable [StarRing 𝕜] [TrivialStar 𝕜] [StarAddMonoid F] [ContinuousStar F]

variable [StarModule 𝕜 F]

protected nonrec theorem HasDerivAtFilter.star (h : HasDerivAtFilter f f' x L) :
    HasDerivAtFilter (fun x => star (f x)) (star f') x L := by
  simpa using h.star.hasDerivAtFilter
#align has_deriv_at_filter.star HasDerivAtFilter.star

protected nonrec theorem HasDerivWithinAt.star (h : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => star (f x)) (star f') s x :=
  h.star
#align has_deriv_within_at.star HasDerivWithinAt.star

protected nonrec theorem HasDerivAt.star (h : HasDerivAt f f' x) :
    HasDerivAt (fun x => star (f x)) (star f') x :=
  h.star
#align has_deriv_at.star HasDerivAt.star

protected nonrec theorem HasStrictDerivAt.star (h : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => star (f x)) (star f') x := by simpa using h.star.hasStrictDerivAt
#align has_strict_deriv_at.star HasStrictDerivAt.star

protected theorem derivWithin.star (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun y => star (f y)) s x = star (derivWithin f s x) :=
  FunLike.congr_fun (fderivWithin_star hxs) _
#align deriv_within.star derivWithin.star

protected theorem deriv.star : deriv (fun y => star (f y)) x = star (deriv f x) :=
  FunLike.congr_fun fderiv_star _
#align deriv.star deriv.star

@[simp]
protected theorem deriv.star' : (deriv fun y => star (f y)) = fun x => star (deriv f x) :=
  funext fun _ => deriv.star
#align deriv.star' deriv.star'

end Star

section ClmCompApply

/-! ### Derivative of the pointwise composition/application of continuous linear maps -/


open ContinuousLinearMap

variable {G : Type _} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {c : 𝕜 → F →L[𝕜] G} {c' : F →L[𝕜] G}
  {d : 𝕜 → E →L[𝕜] F} {d' : E →L[𝕜] F} {u : 𝕜 → F} {u' : F}

theorem HasStrictDerivAt.clm_comp (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (fun y => (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') x := by
  have := (hc.hasStrictFDerivAt.clm_comp hd.hasStrictFDerivAt).hasStrictDerivAt
  rwa [add_apply, comp_apply, comp_apply, smulRight_apply, smulRight_apply, one_apply, one_smul,
    one_smul, add_comm] at this
#align has_strict_deriv_at.clm_comp HasStrictDerivAt.clm_comp

theorem HasDerivWithinAt.clm_comp (hc : HasDerivWithinAt c c' s x)
    (hd : HasDerivWithinAt d d' s x) :
    HasDerivWithinAt (fun y => (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') s x := by
  have := (hc.hasFDerivWithinAt.clm_comp hd.hasFDerivWithinAt).hasDerivWithinAt
  rwa [add_apply, comp_apply, comp_apply, smulRight_apply, smulRight_apply, one_apply, one_smul,
    one_smul, add_comm] at this
#align has_deriv_within_at.clm_comp HasDerivWithinAt.clm_comp

theorem HasDerivAt.clm_comp (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) :
    HasDerivAt (fun y => (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.clm_comp hd
#align has_deriv_at.clm_comp HasDerivAt.clm_comp

theorem derivWithin_clm_comp (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun y => (c y).comp (d y)) s x =
      (derivWithin c s x).comp (d x) + (c x).comp (derivWithin d s x) :=
  (hc.hasDerivWithinAt.clm_comp hd.hasDerivWithinAt).derivWithin hxs
#align deriv_within_clm_comp derivWithin_clm_comp

theorem deriv_clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    deriv (fun y => (c y).comp (d y)) x = (deriv c x).comp (d x) + (c x).comp (deriv d x) :=
  (hc.hasDerivAt.clm_comp hd.hasDerivAt).deriv
#align deriv_clm_comp deriv_clm_comp

theorem HasStrictDerivAt.clm_apply (hc : HasStrictDerivAt c c' x) (hu : HasStrictDerivAt u u' x) :
    HasStrictDerivAt (fun y => (c y) (u y)) (c' (u x) + c x u') x := by
  have := (hc.hasStrictFDerivAt.clm_apply hu.hasStrictFDerivAt).hasStrictDerivAt
  rwa [add_apply, comp_apply, flip_apply, smulRight_apply, smulRight_apply, one_apply, one_smul,
    one_smul, add_comm] at this
#align has_strict_deriv_at.clm_apply HasStrictDerivAt.clm_apply

theorem HasDerivWithinAt.clm_apply (hc : HasDerivWithinAt c c' s x)
    (hu : HasDerivWithinAt u u' s x) :
    HasDerivWithinAt (fun y => (c y) (u y)) (c' (u x) + c x u') s x := by
  have := (hc.hasFDerivWithinAt.clm_apply hu.hasFDerivWithinAt).hasDerivWithinAt
  rwa [add_apply, comp_apply, flip_apply, smulRight_apply, smulRight_apply, one_apply, one_smul,
    one_smul, add_comm] at this
#align has_deriv_within_at.clm_apply HasDerivWithinAt.clm_apply

theorem HasDerivAt.clm_apply (hc : HasDerivAt c c' x) (hu : HasDerivAt u u' x) :
    HasDerivAt (fun y => (c y) (u y)) (c' (u x) + c x u') x := by
  have := (hc.hasFDerivAt.clm_apply hu.hasFDerivAt).hasDerivAt
  rwa [add_apply, comp_apply, flip_apply, smulRight_apply, smulRight_apply, one_apply, one_smul,
    one_smul, add_comm] at this
#align has_deriv_at.clm_apply HasDerivAt.clm_apply

theorem derivWithin_clm_apply (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hu : DifferentiableWithinAt 𝕜 u s x) :
    derivWithin (fun y => (c y) (u y)) s x = derivWithin c s x (u x) + c x (derivWithin u s x) :=
  (hc.hasDerivWithinAt.clm_apply hu.hasDerivWithinAt).derivWithin hxs
#align deriv_within_clm_apply derivWithin_clm_apply

theorem deriv_clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) :
    deriv (fun y => (c y) (u y)) x = deriv c x (u x) + c x (deriv u x) :=
  (hc.hasDerivAt.clm_apply hu.hasDerivAt).deriv
#align deriv_clm_apply deriv_clm_apply

end ClmCompApply

theorem HasStrictDerivAt.hasStrictFDerivAt_equiv {f : 𝕜 → 𝕜} {f' x : 𝕜}
    (hf : HasStrictDerivAt f f' x) (hf' : f' ≠ 0) :
    HasStrictFDerivAt f (ContinuousLinearEquiv.unitsEquivAut 𝕜 (Units.mk0 f' hf') : 𝕜 →L[𝕜] 𝕜) x :=
  hf
#align has_strict_deriv_at.has_strict_fderiv_at_equiv HasStrictDerivAt.hasStrictFDerivAt_equiv

theorem HasDerivAt.hasFDerivAt_equiv {f : 𝕜 → 𝕜} {f' x : 𝕜} (hf : HasDerivAt f f' x)
    (hf' : f' ≠ 0) :
    HasFDerivAt f (ContinuousLinearEquiv.unitsEquivAut 𝕜 (Units.mk0 f' hf') : 𝕜 →L[𝕜] 𝕜) x :=
  hf
#align has_deriv_at.has_fderiv_at_equiv HasDerivAt.hasFDerivAt_equiv

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a` in the strict sense, then `g` has the derivative `f'⁻¹` at `a`
in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
theorem HasStrictDerivAt.of_local_left_inverse {f g : 𝕜 → 𝕜} {f' a : 𝕜} (hg : ContinuousAt g a)
    (hf : HasStrictDerivAt f f' (g a)) (hf' : f' ≠ 0) (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) :
    HasStrictDerivAt g f'⁻¹ a :=
  (hf.hasStrictFDerivAt_equiv hf').of_local_left_inverse hg hfg
#align has_strict_deriv_at.of_local_left_inverse HasStrictDerivAt.of_local_left_inverse

/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has a
nonzero derivative `f'` at `f.symm a` in the strict sense, then `f.symm` has the derivative `f'⁻¹`
at `a` in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem LocalHomeomorph.hasStrictDerivAt_symm (f : LocalHomeomorph 𝕜 𝕜) {a f' : 𝕜}
    (ha : a ∈ f.target) (hf' : f' ≠ 0) (htff' : HasStrictDerivAt f f' (f.symm a)) :
    HasStrictDerivAt f.symm f'⁻¹ a :=
  htff'.of_local_left_inverse (f.symm.continuousAt ha) hf' (f.eventually_right_inverse ha)
#align local_homeomorph.has_strict_deriv_at_symm LocalHomeomorph.hasStrictDerivAt_symm

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a`, then `g` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem HasDerivAt.of_local_left_inverse {f g : 𝕜 → 𝕜} {f' a : 𝕜} (hg : ContinuousAt g a)
    (hf : HasDerivAt f f' (g a)) (hf' : f' ≠ 0) (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) :
    HasDerivAt g f'⁻¹ a :=
  (hf.hasFDerivAt_equiv hf').of_local_left_inverse hg hfg
#align has_deriv_at.of_local_left_inverse HasDerivAt.of_local_left_inverse

/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
nonzero derivative `f'` at `f.symm a`, then `f.symm` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem LocalHomeomorph.hasDerivAt_symm (f : LocalHomeomorph 𝕜 𝕜) {a f' : 𝕜} (ha : a ∈ f.target)
    (hf' : f' ≠ 0) (htff' : HasDerivAt f f' (f.symm a)) : HasDerivAt f.symm f'⁻¹ a :=
  htff'.of_local_left_inverse (f.symm.continuousAt ha) hf' (f.eventually_right_inverse ha)
#align local_homeomorph.has_deriv_at_symm LocalHomeomorph.hasDerivAt_symm

theorem HasDerivAt.eventually_ne (h : HasDerivAt f f' x) (hf' : f' ≠ 0) :
    ∀ᶠ z in 𝓝[≠] x, f z ≠ f x :=
  (hasDerivAt_iff_hasFDerivAt.1 h).eventually_ne
    ⟨‖f'‖⁻¹, fun z => by field_simp [norm_smul, mt norm_eq_zero.1 hf'] ⟩
#align has_deriv_at.eventually_ne HasDerivAt.eventually_ne

theorem HasDerivAt.tendsto_punctured_nhds (h : HasDerivAt f f' x) (hf' : f' ≠ 0) :
    Tendsto f (𝓝[≠] x) (𝓝[≠] f x) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h.continuousAt.continuousWithinAt
    (h.eventually_ne hf')
#align has_deriv_at.tendsto_punctured_nhds HasDerivAt.tendsto_punctured_nhds

theorem not_differentiableWithinAt_of_local_left_inverse_hasDerivWithinAt_zero {f g : 𝕜 → 𝕜} {a : 𝕜}
    {s t : Set 𝕜} (ha : a ∈ s) (hsu : UniqueDiffWithinAt 𝕜 s a) (hf : HasDerivWithinAt f 0 t (g a))
    (hst : MapsTo g s t) (hfg : f ∘ g =ᶠ[𝓝[s] a] id) : ¬DifferentiableWithinAt 𝕜 g s a := by
  intro hg
  have := (hf.comp a hg.hasDerivWithinAt hst).congr_of_eventuallyEq_of_mem hfg.symm ha
  simpa using hsu.eq_deriv _ this (hasDerivWithinAt_id _ _)
#align not_differentiable_within_at_of_local_left_inverse_has_deriv_within_at_zero not_differentiableWithinAt_of_local_left_inverse_hasDerivWithinAt_zero

theorem not_differentiableAt_of_local_left_inverse_hasDerivAt_zero {f g : 𝕜 → 𝕜} {a : 𝕜}
    (hf : HasDerivAt f 0 (g a)) (hfg : f ∘ g =ᶠ[𝓝 a] id) : ¬DifferentiableAt 𝕜 g a := by
  intro hg
  have := (hf.comp a hg.hasDerivAt).congr_of_eventuallyEq hfg.symm
  simpa using this.unique (hasDerivAt_id a)
#align not_differentiable_at_of_local_left_inverse_has_deriv_at_zero not_differentiableAt_of_local_left_inverse_hasDerivAt_zero

end

namespace Polynomial

/-! ### Derivative of a polynomial -/

variable {R : Type _} [CommSemiring R] [Algebra R 𝕜]

variable (p : 𝕜[X]) (q : R[X]) {x : 𝕜} {s : Set 𝕜}

/-- The derivative (in the analysis sense) of a polynomial `p` is given by `p.derivative`. -/
protected theorem hasStrictDerivAt (x : 𝕜) :
    HasStrictDerivAt (fun x => p.eval x) (p.derivative.eval x) x := by
  induction p using Polynomial.induction_on with
  | h_C a => simp [hasStrictDerivAt_const]
  | h_add p q hp hq => simpa using hp.add hq
  | h_monomial n a h =>
    convert h.mul (hasStrictDerivAt_id x) using 1
    · simp [pow_succ', mul_assoc]
    · simp only [pow_add, pow_one, derivative_mul, derivative_C, zero_mul, derivative_X_pow,
        derivative_X, mul_one, zero_add, eval_mul, eval_C, eval_add, eval_nat_cast, eval_pow,
        eval_X, id.def]
      ring
#align polynomial.has_strict_deriv_at Polynomial.hasStrictDerivAt

protected theorem hasStrictDerivAt_aeval (x : 𝕜) :
    HasStrictDerivAt (fun x => aeval x q) (aeval x (derivative q)) x := by
  simpa only [aeval_def, eval₂_eq_eval_map, derivative_map] using
    (q.map (algebraMap R 𝕜)).hasStrictDerivAt x
#align polynomial.has_strict_deriv_at_aeval Polynomial.hasStrictDerivAt_aeval

/-- The derivative (in the analysis sense) of a polynomial `p` is given by `p.derivative`. -/
protected theorem hasDerivAt (x : 𝕜) : HasDerivAt (fun x => p.eval x) (p.derivative.eval x) x :=
  (p.hasStrictDerivAt x).hasDerivAt
#align polynomial.has_deriv_at Polynomial.hasDerivAt

protected theorem hasDerivAt_aeval (x : 𝕜) :
    HasDerivAt (fun x => aeval x q) (aeval x (derivative q)) x :=
  (q.hasStrictDerivAt_aeval x).hasDerivAt
#align polynomial.has_deriv_at_aeval Polynomial.hasDerivAt_aeval

protected theorem hasDerivWithinAt (x : 𝕜) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => p.eval x) (p.derivative.eval x) s x :=
  (p.hasDerivAt x).hasDerivWithinAt
#align polynomial.has_deriv_within_at Polynomial.hasDerivWithinAt

protected theorem hasDerivWithinAt_aeval (x : 𝕜) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => aeval x q) (aeval x (derivative q)) s x :=
  (q.hasDerivAt_aeval x).hasDerivWithinAt
#align polynomial.has_deriv_within_at_aeval Polynomial.hasDerivWithinAt_aeval

protected theorem differentiableAt : DifferentiableAt 𝕜 (fun x => p.eval x) x :=
  (p.hasDerivAt x).differentiableAt
#align polynomial.differentiable_at Polynomial.differentiableAt

protected theorem differentiableAt_aeval : DifferentiableAt 𝕜 (fun x => aeval x q) x :=
  (q.hasDerivAt_aeval x).differentiableAt
#align polynomial.differentiable_at_aeval Polynomial.differentiableAt_aeval

protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 (fun x => p.eval x) s x :=
  p.differentiableAt.differentiableWithinAt
#align polynomial.differentiable_within_at Polynomial.differentiableWithinAt

protected theorem differentiableWithinAt_aeval :
    DifferentiableWithinAt 𝕜 (fun x => aeval x q) s x :=
  q.differentiableAt_aeval.differentiableWithinAt
#align polynomial.differentiable_within_at_aeval Polynomial.differentiableWithinAt_aeval

protected theorem differentiable : Differentiable 𝕜 fun x => p.eval x := fun _ => p.differentiableAt
#align polynomial.differentiable Polynomial.differentiable

protected theorem differentiable_aeval : Differentiable 𝕜 fun x : 𝕜 => aeval x q := fun _ =>
  q.differentiableAt_aeval
#align polynomial.differentiable_aeval Polynomial.differentiable_aeval

protected theorem differentiableOn : DifferentiableOn 𝕜 (fun x => p.eval x) s :=
  p.differentiable.differentiableOn
#align polynomial.differentiable_on Polynomial.differentiableOn

protected theorem differentiableOn_aeval : DifferentiableOn 𝕜 (fun x => aeval x q) s :=
  q.differentiable_aeval.differentiableOn
#align polynomial.differentiable_on_aeval Polynomial.differentiableOn_aeval

@[simp]
protected theorem deriv : deriv (fun x => p.eval x) x = p.derivative.eval x :=
  (p.hasDerivAt x).deriv
#align polynomial.deriv Polynomial.deriv

@[simp]
protected theorem deriv_aeval : deriv (fun x => aeval x q) x = aeval x (derivative q) :=
  (q.hasDerivAt_aeval x).deriv
#align polynomial.deriv_aeval Polynomial.deriv_aeval

protected theorem derivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => p.eval x) s x = p.derivative.eval x := by
  rw [DifferentiableAt.derivWithin p.differentiableAt hxs]
  exact p.deriv
#align polynomial.deriv_within Polynomial.derivWithin

protected theorem derivWithin_aeval (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => aeval x q) s x = aeval x (derivative q) := by
  simpa only [aeval_def, eval₂_eq_eval_map, derivative_map] using
    (q.map (algebraMap R 𝕜)).derivWithin hxs
#align polynomial.deriv_within_aeval Polynomial.derivWithin_aeval

protected theorem hasFDerivAt (x : 𝕜) :
    HasFDerivAt (fun x => p.eval x) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x)) x :=
  p.hasDerivAt x
#align polynomial.has_fderiv_at Polynomial.hasFDerivAt

protected theorem hasFDerivAt_aeval (x : 𝕜) :
    HasFDerivAt (fun x => aeval x q) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (aeval x (derivative q))) x :=
  q.hasDerivAt_aeval x
#align polynomial.has_fderiv_at_aeval Polynomial.hasFDerivAt_aeval

protected theorem hasFDerivWithinAt (x : 𝕜) :
    HasFDerivWithinAt (fun x => p.eval x) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x)) s x :=
  (p.hasFDerivAt x).hasFDerivWithinAt
#align polynomial.has_fderiv_within_at Polynomial.hasFDerivWithinAt

protected theorem hasFDerivWithinAt_aeval (x : 𝕜) :
    HasFDerivWithinAt (fun x => aeval x q) (smulRight (1 : 𝕜 →L[𝕜] 𝕜)
      (aeval x (derivative q))) s x :=
  (q.hasFDerivAt_aeval x).hasFDerivWithinAt
#align polynomial.has_fderiv_within_at_aeval Polynomial.hasFDerivWithinAt_aeval

@[simp]
protected theorem fderiv :
    fderiv 𝕜 (fun x => p.eval x) x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x) :=
  (p.hasFDerivAt x).fderiv
#align polynomial.fderiv Polynomial.fderiv

@[simp]
protected theorem fderiv_aeval :
    fderiv 𝕜 (fun x => aeval x q) x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (aeval x (derivative q)) :=
  (q.hasFDerivAt_aeval x).fderiv
#align polynomial.fderiv_aeval Polynomial.fderiv_aeval

protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => p.eval x) s x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x) :=
  (p.hasFDerivWithinAt x).fderivWithin hxs
#align polynomial.fderiv_within Polynomial.fderivWithin

protected theorem fderivWithin_aeval (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => aeval x q) s x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (aeval x (derivative q)) :=
  (q.hasFDerivWithinAt_aeval x).fderivWithin hxs
#align polynomial.fderiv_within_aeval Polynomial.fderivWithin_aeval

end Polynomial

section Pow

/-! ### Derivative of `x ↦ x^n` for `n : ℕ` -/


variable {x : 𝕜} {s : Set 𝕜} {c : 𝕜 → 𝕜} {c' : 𝕜}

variable (n : ℕ)

theorem hasStrictDerivAt_pow (n : ℕ) (x : 𝕜) :
    HasStrictDerivAt (fun x : 𝕜 => x ^ n) ((n : 𝕜) * x ^ (n - 1)) x := by
  simpa using (Polynomial.X ^ n).hasStrictDerivAt x
#align has_strict_deriv_at_pow hasStrictDerivAt_pow

theorem hasDerivAt_pow (n : ℕ) (x : 𝕜) :
    HasDerivAt (fun x : 𝕜 => x ^ n) ((n : 𝕜) * x ^ (n - 1)) x :=
  (hasStrictDerivAt_pow n x).hasDerivAt
#align has_deriv_at_pow hasDerivAt_pow

theorem hasDerivWithinAt_pow (n : ℕ) (x : 𝕜) (s : Set 𝕜) :
    HasDerivWithinAt (fun x : 𝕜 => x ^ n) ((n : 𝕜) * x ^ (n - 1)) s x :=
  (hasDerivAt_pow n x).hasDerivWithinAt
#align has_deriv_within_at_pow hasDerivWithinAt_pow

theorem differentiableAt_pow : DifferentiableAt 𝕜 (fun x : 𝕜 => x ^ n) x :=
  (hasDerivAt_pow n x).differentiableAt
#align differentiable_at_pow differentiableAt_pow

theorem differentiableWithinAt_pow :
    DifferentiableWithinAt 𝕜 (fun x : 𝕜 => x ^ n) s x :=
  (differentiableAt_pow n).differentiableWithinAt
#align differentiable_within_at_pow differentiableWithinAt_pow

theorem differentiable_pow : Differentiable 𝕜 fun x : 𝕜 => x ^ n := fun _ => differentiableAt_pow n
#align differentiable_pow differentiable_pow

theorem differentiableOn_pow : DifferentiableOn 𝕜 (fun x : 𝕜 => x ^ n) s :=
  (differentiable_pow n).differentiableOn
#align differentiable_on_pow differentiableOn_pow

theorem deriv_pow : deriv (fun x : 𝕜 => x ^ n) x = (n : 𝕜) * x ^ (n - 1) :=
  (hasDerivAt_pow n x).deriv
#align deriv_pow deriv_pow

@[simp]
theorem deriv_pow' : (deriv fun x : 𝕜 => x ^ n) = fun x => (n : 𝕜) * x ^ (n - 1) :=
  funext fun _ => deriv_pow n
#align deriv_pow' deriv_pow'

theorem derivWithin_pow (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x : 𝕜 => x ^ n) s x = (n : 𝕜) * x ^ (n - 1) :=
  (hasDerivWithinAt_pow n x s).derivWithin hxs
#align deriv_within_pow derivWithin_pow

theorem HasDerivWithinAt.pow (hc : HasDerivWithinAt c c' s x) :
    HasDerivWithinAt (fun y => c y ^ n) ((n : 𝕜) * c x ^ (n - 1) * c') s x :=
  (hasDerivAt_pow n (c x)).comp_hasDerivWithinAt x hc
#align has_deriv_within_at.pow HasDerivWithinAt.pow

theorem HasDerivAt.pow (hc : HasDerivAt c c' x) :
    HasDerivAt (fun y => c y ^ n) ((n : 𝕜) * c x ^ (n - 1) * c') x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.pow n
#align has_deriv_at.pow HasDerivAt.pow

theorem derivWithin_pow' (hc : DifferentiableWithinAt 𝕜 c s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => c x ^ n) s x = (n : 𝕜) * c x ^ (n - 1) * derivWithin c s x :=
  (hc.hasDerivWithinAt.pow n).derivWithin hxs
#align deriv_within_pow' derivWithin_pow'

@[simp]
theorem deriv_pow'' (hc : DifferentiableAt 𝕜 c x) :
    deriv (fun x => c x ^ n) x = (n : 𝕜) * c x ^ (n - 1) * deriv c x :=
  (hc.hasDerivAt.pow n).deriv
#align deriv_pow'' deriv_pow''

end Pow

section Zpow

/-! ### Derivative of `x ↦ x^m` for `m : ℤ` -/

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {x : 𝕜} {s : Set 𝕜} {m : ℤ}

theorem hasStrictDerivAt_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) :
    HasStrictDerivAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x := by
  have : ∀ m : ℤ, 0 < m → HasStrictDerivAt (· ^ m) ((m : 𝕜) * x ^ (m - 1)) x := fun m hm ↦ by
    lift m to ℕ using hm.le
    simp only [zpow_ofNat, Int.cast_ofNat]
    convert hasStrictDerivAt_pow m x using 2
    rw [← Int.ofNat_one, ← Int.ofNat_sub, zpow_ofNat]
    norm_cast at hm
  rcases lt_trichotomy m 0 with (hm | hm | hm)
  · have hx : x ≠ 0 := h.resolve_right hm.not_le
    have := (hasStrictDerivAt_inv ?_).scomp _ (this (-m) (neg_pos.2 hm)) <;> [skip,
      exact zpow_ne_zero_of_ne_zero hx _]
    simp only [(· ∘ ·), zpow_neg, one_div, inv_inv, smul_eq_mul] at this
    convert this using 1
    rw [sq, mul_inv, inv_inv, Int.cast_neg, neg_mul, neg_mul_neg, ← zpow_add₀ hx, mul_assoc, ←
      zpow_add₀ hx]
    congr
    abel
  · simp only [hm, zpow_zero, Int.cast_zero, zero_mul, hasStrictDerivAt_const]
  · exact this m hm
#align has_strict_deriv_at_zpow hasStrictDerivAt_zpow

theorem hasDerivAt_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) :
    HasDerivAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x :=
  (hasStrictDerivAt_zpow m x h).hasDerivAt
#align has_deriv_at_zpow hasDerivAt_zpow

theorem hasDerivWithinAt_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) s x :=
  (hasDerivAt_zpow m x h).hasDerivWithinAt
#align has_deriv_within_at_zpow hasDerivWithinAt_zpow

theorem differentiableAt_zpow : DifferentiableAt 𝕜 (fun x => x ^ m) x ↔ x ≠ 0 ∨ 0 ≤ m :=
  ⟨fun H => NormedField.continuousAt_zpow.1 H.continuousAt, fun H =>
    (hasDerivAt_zpow m x H).differentiableAt⟩
#align differentiable_at_zpow differentiableAt_zpow

theorem differentiableWithinAt_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) :
    DifferentiableWithinAt 𝕜 (fun x => x ^ m) s x :=
  (differentiableAt_zpow.mpr h).differentiableWithinAt
#align differentiable_within_at_zpow differentiableWithinAt_zpow

theorem differentiableOn_zpow (m : ℤ) (s : Set 𝕜) (h : (0 : 𝕜) ∉ s ∨ 0 ≤ m) :
    DifferentiableOn 𝕜 (fun x => x ^ m) s := fun x hxs =>
  differentiableWithinAt_zpow m x <| h.imp_left <| ne_of_mem_of_not_mem hxs
#align differentiable_on_zpow differentiableOn_zpow

theorem deriv_zpow (m : ℤ) (x : 𝕜) : deriv (fun x => x ^ m) x = m * x ^ (m - 1) := by
  by_cases H : x ≠ 0 ∨ 0 ≤ m
  · exact (hasDerivAt_zpow m x H).deriv
  · rw [deriv_zero_of_not_differentiableAt (mt differentiableAt_zpow.1 H)]
    push_neg  at H
    rcases H with ⟨rfl, hm⟩
    rw [zero_zpow _ ((sub_one_lt _).trans hm).ne, MulZeroClass.mul_zero]
#align deriv_zpow deriv_zpow

@[simp]
theorem deriv_zpow' (m : ℤ) : (deriv fun x : 𝕜 => x ^ m) = fun x => (m : 𝕜) * x ^ (m - 1) :=
  funext <| deriv_zpow m
#align deriv_zpow' deriv_zpow'

theorem derivWithin_zpow (hxs : UniqueDiffWithinAt 𝕜 s x) (h : x ≠ 0 ∨ 0 ≤ m) :
    derivWithin (fun x => x ^ m) s x = (m : 𝕜) * x ^ (m - 1) :=
  (hasDerivWithinAt_zpow m x h s).derivWithin hxs
#align deriv_within_zpow derivWithin_zpow

@[simp]
theorem iter_deriv_zpow' (m : ℤ) (k : ℕ) :
    ((deriv^[k]) fun x : 𝕜 => x ^ m) =
      fun x => (∏ i in Finset.range k, ((m : 𝕜) - i)) * x ^ (m - k) := by
  induction' k with k ihk
  · simp only [Nat.zero_eq, one_mul, Int.ofNat_zero, id, sub_zero, Finset.prod_range_zero,
      Function.iterate_zero]
  · simp only [Function.iterate_succ_apply', ihk, deriv_const_mul_field', deriv_zpow',
      Finset.prod_range_succ, Int.ofNat_succ, ← sub_sub, Int.cast_sub, Int.cast_ofNat, mul_assoc]
#align iter_deriv_zpow' iter_deriv_zpow'

theorem iter_deriv_zpow (m : ℤ) (x : 𝕜) (k : ℕ) :
    (deriv^[k]) (fun y => y ^ m) x = (∏ i in Finset.range k, ((m : 𝕜) - i)) * x ^ (m - k) :=
  congr_fun (iter_deriv_zpow' m k) x
#align iter_deriv_zpow iter_deriv_zpow

theorem iter_deriv_pow (n : ℕ) (x : 𝕜) (k : ℕ) :
    (deriv^[k]) (fun x : 𝕜 => x ^ n) x = (∏ i in Finset.range k, ((n : 𝕜) - i)) * x ^ (n - k) := by
  simp only [← zpow_ofNat, iter_deriv_zpow, Int.cast_ofNat]
  cases' le_or_lt k n with hkn hnk
  · rw [Int.ofNat_sub hkn]
  · have : (∏ i in Finset.range k, (n - i : 𝕜)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.2 hnk) (sub_self _)
    simp only [this, MulZeroClass.zero_mul]
#align iter_deriv_pow iter_deriv_pow

@[simp]
theorem iter_deriv_pow' (n k : ℕ) :
    ((deriv^[k]) fun x : 𝕜 => x ^ n) =
      fun x => (∏ i in Finset.range k, ((n : 𝕜) - i)) * x ^ (n - k) :=
  funext fun x => iter_deriv_pow n x k
#align iter_deriv_pow' iter_deriv_pow'

theorem iter_deriv_inv (k : ℕ) (x : 𝕜) :
    (deriv^[k]) Inv.inv x = (∏ i in Finset.range k, (-1 - i : 𝕜)) * x ^ (-1 - k : ℤ) := by
  simpa only [zpow_neg_one, Int.cast_neg, Int.cast_one] using iter_deriv_zpow (-1) x k
#align iter_deriv_inv iter_deriv_inv

@[simp]
theorem iter_deriv_inv' (k : ℕ) :
    (deriv^[k]) Inv.inv = fun x : 𝕜 => (∏ i in Finset.range k, (-1 - i : 𝕜)) * x ^ (-1 - k : ℤ) :=
  funext (iter_deriv_inv k)
#align iter_deriv_inv' iter_deriv_inv'

variable {f : E → 𝕜} {t : Set E} {a : E}

theorem DifferentiableWithinAt.zpow (hf : DifferentiableWithinAt 𝕜 f t a) (h : f a ≠ 0 ∨ 0 ≤ m) :
    DifferentiableWithinAt 𝕜 (fun x => f x ^ m) t a :=
  (differentiableAt_zpow.2 h).comp_differentiableWithinAt a hf
#align differentiable_within_at.zpow DifferentiableWithinAt.zpow

theorem DifferentiableAt.zpow (hf : DifferentiableAt 𝕜 f a) (h : f a ≠ 0 ∨ 0 ≤ m) :
    DifferentiableAt 𝕜 (fun x => f x ^ m) a :=
  (differentiableAt_zpow.2 h).comp a hf
#align differentiable_at.zpow DifferentiableAt.zpow

theorem DifferentiableOn.zpow (hf : DifferentiableOn 𝕜 f t) (h : (∀ x ∈ t, f x ≠ 0) ∨ 0 ≤ m) :
    DifferentiableOn 𝕜 (fun x => f x ^ m) t := fun x hx =>
  (hf x hx).zpow <| h.imp_left fun h => h x hx
#align differentiable_on.zpow DifferentiableOn.zpow

theorem Differentiable.zpow (hf : Differentiable 𝕜 f) (h : (∀ x, f x ≠ 0) ∨ 0 ≤ m) :
    Differentiable 𝕜 fun x => f x ^ m := fun x => (hf x).zpow <| h.imp_left fun h => h x
#align differentiable.zpow Differentiable.zpow

end Zpow

/-! ### Support of derivatives -/

section Support

open Function

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F}

theorem support_deriv_subset : support (deriv f) ⊆ tsupport f := by
  intro x
  rw [← not_imp_not]
  intro h2x
  rw [not_mem_tsupport_iff_eventuallyEq] at h2x
  exact nmem_support.mpr (h2x.deriv_eq.trans (deriv_const x 0))
#align support_deriv_subset support_deriv_subset

theorem HasCompactSupport.deriv (hf : HasCompactSupport f) : HasCompactSupport (deriv f) :=
  hf.mono' support_deriv_subset
#align has_compact_support.deriv HasCompactSupport.deriv

end Support

/-! ### Upper estimates on liminf and limsup -/

section Real

variable {f : ℝ → ℝ} {f' : ℝ} {s : Set ℝ} {x : ℝ} {r : ℝ}

theorem HasDerivWithinAt.limsup_slope_le (hf : HasDerivWithinAt f f' s x) (hr : f' < r) :
    ∀ᶠ z in 𝓝[s \ {x}] x, slope f x z < r :=
  hasDerivWithinAt_iff_tendsto_slope.1 hf (IsOpen.mem_nhds isOpen_Iio hr)
#align has_deriv_within_at.limsup_slope_le HasDerivWithinAt.limsup_slope_le

theorem HasDerivWithinAt.limsup_slope_le' (hf : HasDerivWithinAt f f' s x) (hs : x ∉ s)
    (hr : f' < r) : ∀ᶠ z in 𝓝[s] x, slope f x z < r :=
  (hasDerivWithinAt_iff_tendsto_slope' hs).1 hf (IsOpen.mem_nhds isOpen_Iio hr)
#align has_deriv_within_at.limsup_slope_le' HasDerivWithinAt.limsup_slope_le'

theorem HasDerivWithinAt.liminf_right_slope_le (hf : HasDerivWithinAt f f' (Ici x) x)
    (hr : f' < r) : ∃ᶠ z in 𝓝[>] x, slope f x z < r :=
  (hf.Ioi_of_Ici.limsup_slope_le' (lt_irrefl x) hr).frequently
#align has_deriv_within_at.liminf_right_slope_le HasDerivWithinAt.liminf_right_slope_le

end Real

section RealSpace

open Metric

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {f' : E} {s : Set ℝ}
  {x r : ℝ}

/-- If `f` has derivative `f'` within `s` at `x`, then for any `r > ‖f'‖` the ratio
`‖f z - f x‖ / ‖z - x‖` is less than `r` in some neighborhood of `x` within `s`.
In other words, the limit superior of this ratio as `z` tends to `x` along `s`
is less than or equal to `‖f'‖`. -/
theorem HasDerivWithinAt.limsup_norm_slope_le (hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r) :
    ∀ᶠ z in 𝓝[s] x, ‖z - x‖⁻¹ * ‖f z - f x‖ < r := by
  have hr₀ : 0 < r := lt_of_le_of_lt (norm_nonneg f') hr
  have A : ∀ᶠ z in 𝓝[s \ {x}] x, ‖(z - x)⁻¹ • (f z - f x)‖ ∈ Iio r :=
    (hasDerivWithinAt_iff_tendsto_slope.1 hf).norm (IsOpen.mem_nhds isOpen_Iio hr)
  have B : ∀ᶠ z in 𝓝[{x}] x, ‖(z - x)⁻¹ • (f z - f x)‖ ∈ Iio r :=
    mem_of_superset self_mem_nhdsWithin (singleton_subset_iff.2 <| by simp [hr₀])
  have C := mem_sup.2 ⟨A, B⟩
  rw [← nhdsWithin_union, diff_union_self, nhdsWithin_union, mem_sup] at C
  filter_upwards [C.1]
  simp only [norm_smul, mem_Iio, norm_inv]
  exact fun _ => id
#align has_deriv_within_at.limsup_norm_slope_le HasDerivWithinAt.limsup_norm_slope_le

/-- If `f` has derivative `f'` within `s` at `x`, then for any `r > ‖f'‖` the ratio
`(‖f z‖ - ‖f x‖) / ‖z - x‖` is less than `r` in some neighborhood of `x` within `s`.
In other words, the limit superior of this ratio as `z` tends to `x` along `s`
is less than or equal to `‖f'‖`.

This lemma is a weaker version of `HasDerivWithinAt.limsup_norm_slope_le`
where `‖f z‖ - ‖f x‖` is replaced by `‖f z - f x‖`. -/
theorem HasDerivWithinAt.limsup_slope_norm_le (hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r) :
    ∀ᶠ z in 𝓝[s] x, ‖z - x‖⁻¹ * (‖f z‖ - ‖f x‖) < r := by
  apply (hf.limsup_norm_slope_le hr).mono
  intro z hz
  refine' lt_of_le_of_lt (mul_le_mul_of_nonneg_left (norm_sub_norm_le _ _) _) hz
  exact inv_nonneg.2 (norm_nonneg _)
#align has_deriv_within_at.limsup_slope_norm_le HasDerivWithinAt.limsup_slope_norm_le

/-- If `f` has derivative `f'` within `(x, +∞)` at `x`, then for any `r > ‖f'‖` the ratio
`‖f z - f x‖ / ‖z - x‖` is frequently less than `r` as `z → x+0`.
In other words, the limit inferior of this ratio as `z` tends to `x+0`
is less than or equal to `‖f'‖`. See also `HasDerivWithinAt.limsup_norm_slope_le`
for a stronger version using limit superior and any set `s`. -/
theorem HasDerivWithinAt.liminf_right_norm_slope_le (hf : HasDerivWithinAt f f' (Ici x) x)
    (hr : ‖f'‖ < r) : ∃ᶠ z in 𝓝[>] x, ‖z - x‖⁻¹ * ‖f z - f x‖ < r :=
  (hf.Ioi_of_Ici.limsup_norm_slope_le hr).frequently
#align has_deriv_within_at.liminf_right_norm_slope_le HasDerivWithinAt.liminf_right_norm_slope_le

/-- If `f` has derivative `f'` within `(x, +∞)` at `x`, then for any `r > ‖f'‖` the ratio
`(‖f z‖ - ‖f x‖) / (z - x)` is frequently less than `r` as `z → x+0`.
In other words, the limit inferior of this ratio as `z` tends to `x+0`
is less than or equal to `‖f'‖`.

See also

* `HasDerivWithinAt.limsup_norm_slope_le` for a stronger version using
  limit superior and any set `s`;
* `HasDerivWithinAt.liminf_right_norm_slope_le` for a stronger version using
  `‖f z - f xp‖` instead of `‖f z‖ - ‖f x‖`. -/
theorem HasDerivWithinAt.liminf_right_slope_norm_le (hf : HasDerivWithinAt f f' (Ici x) x)
    (hr : ‖f'‖ < r) : ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (‖f z‖ - ‖f x‖) < r := by
  have := (hf.Ioi_of_Ici.limsup_slope_norm_le hr).frequently
  refine this.mp (Eventually.mono self_mem_nhdsWithin fun z hxz hz ↦ ?_)
  rwa [Real.norm_eq_abs, abs_of_pos (sub_pos_of_lt hxz)] at hz
#align has_deriv_within_at.liminf_right_slope_norm_le HasDerivWithinAt.liminf_right_slope_norm_le

end RealSpace
