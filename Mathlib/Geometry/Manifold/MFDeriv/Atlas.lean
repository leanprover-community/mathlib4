/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Differentiable partial homeomorphisms and extended charts

This file shows that extended charts are differentiable and have bijective differential.

Suppose a partial homeomorphism `e` is differentiable. This file shows
* `PartialHomeomorph.MDifferentiable.mfderiv`: its derivative is a continuous linear equivalence
* `PartialHomeomorph.MDifferentiable.mfderiv_bijective`: its derivative is bijective;
  there are also spelling with trivial kernel and full range
* `mdifferentiableOn_extChartAt`: `extChartAt` is differentiable on its source

## Tags
charts, differentiable, bijective
-/

noncomputable section

open scoped Manifold
open Topology Set


/-! ### Differentiable partial homeomorphisms -/

namespace PartialHomeomorph.MDifferentiable

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*}
  [TopologicalSpace M'] [ChartedSpace H' M'] {E'' : Type*} [NormedAddCommGroup E'']
  [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M''] {e : PartialHomeomorph M M'}
  (he : e.MDifferentiable I I') {e' : PartialHomeomorph M' M''}

nonrec theorem symm : e.symm.MDifferentiable I' I := he.symm
#align local_homeomorph.mdifferentiable.symm PartialHomeomorph.MDifferentiable.symm

protected theorem mdifferentiableAt {x : M} (hx : x ∈ e.source) : MDifferentiableAt I I' e x :=
  (he.1 x hx).mdifferentiableAt (IsOpen.mem_nhds e.open_source hx)
#align local_homeomorph.mdifferentiable.mdifferentiable_at PartialHomeomorph.MDifferentiable.mdifferentiableAt

theorem mdifferentiableAt_symm {x : M'} (hx : x ∈ e.target) : MDifferentiableAt I' I e.symm x :=
  (he.2 x hx).mdifferentiableAt (IsOpen.mem_nhds e.open_target hx)
#align local_homeomorph.mdifferentiable.mdifferentiable_at_symm PartialHomeomorph.MDifferentiable.mdifferentiableAt_symm

variable [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners I' M']
  [SmoothManifoldWithCorners I'' M'']

theorem symm_comp_deriv {x : M} (hx : x ∈ e.source) :
    (mfderiv I' I e.symm (e x)).comp (mfderiv I I' e x) =
      ContinuousLinearMap.id 𝕜 (TangentSpace I x) := by
  have : mfderiv I I (e.symm ∘ e) x = (mfderiv I' I e.symm (e x)).comp (mfderiv I I' e x) :=
    mfderiv_comp x (he.mdifferentiableAt_symm (e.map_source hx)) (he.mdifferentiableAt hx)
  rw [← this]
  have : mfderiv I I (_root_.id : M → M) x = ContinuousLinearMap.id _ _ := mfderiv_id I
  rw [← this]
  apply Filter.EventuallyEq.mfderiv_eq
  have : e.source ∈ 𝓝 x := IsOpen.mem_nhds e.open_source hx
  exact Filter.mem_of_superset this (by mfld_set_tac)
#align local_homeomorph.mdifferentiable.symm_comp_deriv PartialHomeomorph.MDifferentiable.symm_comp_deriv

theorem comp_symm_deriv {x : M'} (hx : x ∈ e.target) :
    (mfderiv I I' e (e.symm x)).comp (mfderiv I' I e.symm x) =
      ContinuousLinearMap.id 𝕜 (TangentSpace I' x) :=
  he.symm.symm_comp_deriv hx
#align local_homeomorph.mdifferentiable.comp_symm_deriv PartialHomeomorph.MDifferentiable.comp_symm_deriv

/-- The derivative of a differentiable partial homeomorphism, as a continuous linear equivalence
between the tangent spaces at `x` and `e x`. -/
protected def mfderiv {x : M} (hx : x ∈ e.source) : TangentSpace I x ≃L[𝕜] TangentSpace I' (e x) :=
  { mfderiv I I' e x with
    invFun := mfderiv I' I e.symm (e x)
    continuous_toFun := (mfderiv I I' e x).cont
    continuous_invFun := (mfderiv I' I e.symm (e x)).cont
    left_inv := fun y => by
      have : (ContinuousLinearMap.id _ _ : TangentSpace I x →L[𝕜] TangentSpace I x) y = y := rfl
      conv_rhs => rw [← this, ← he.symm_comp_deriv hx]
    right_inv := fun y => by
      have :
        (ContinuousLinearMap.id 𝕜 _ : TangentSpace I' (e x) →L[𝕜] TangentSpace I' (e x)) y = y :=
        rfl
      conv_rhs => rw [← this, ← he.comp_symm_deriv (e.map_source hx)]
      rw [e.left_inv hx]
      rfl }
#align local_homeomorph.mdifferentiable.mfderiv PartialHomeomorph.MDifferentiable.mfderiv

theorem mfderiv_bijective {x : M} (hx : x ∈ e.source) : Function.Bijective (mfderiv I I' e x) :=
  (he.mfderiv hx).bijective
#align local_homeomorph.mdifferentiable.mfderiv_bijective PartialHomeomorph.MDifferentiable.mfderiv_bijective

theorem mfderiv_injective {x : M} (hx : x ∈ e.source) : Function.Injective (mfderiv I I' e x) :=
  (he.mfderiv hx).injective
#align local_homeomorph.mdifferentiable.mfderiv_injective PartialHomeomorph.MDifferentiable.mfderiv_injective

theorem mfderiv_surjective {x : M} (hx : x ∈ e.source) : Function.Surjective (mfderiv I I' e x) :=
  (he.mfderiv hx).surjective
#align local_homeomorph.mdifferentiable.mfderiv_surjective PartialHomeomorph.MDifferentiable.mfderiv_surjective

theorem ker_mfderiv_eq_bot {x : M} (hx : x ∈ e.source) : LinearMap.ker (mfderiv I I' e x) = ⊥ :=
  (he.mfderiv hx).toLinearEquiv.ker
#align local_homeomorph.mdifferentiable.ker_mfderiv_eq_bot PartialHomeomorph.MDifferentiable.ker_mfderiv_eq_bot

theorem range_mfderiv_eq_top {x : M} (hx : x ∈ e.source) : LinearMap.range (mfderiv I I' e x) = ⊤ :=
  (he.mfderiv hx).toLinearEquiv.range
#align local_homeomorph.mdifferentiable.range_mfderiv_eq_top PartialHomeomorph.MDifferentiable.range_mfderiv_eq_top

theorem range_mfderiv_eq_univ {x : M} (hx : x ∈ e.source) : range (mfderiv I I' e x) = univ :=
  (he.mfderiv_surjective hx).range_eq
#align local_homeomorph.mdifferentiable.range_mfderiv_eq_univ PartialHomeomorph.MDifferentiable.range_mfderiv_eq_univ

theorem trans (he' : e'.MDifferentiable I' I'') : (e.trans e').MDifferentiable I I'' := by
  constructor
  · intro x hx
    simp only [mfld_simps] at hx
    exact
      ((he'.mdifferentiableAt hx.2).comp _ (he.mdifferentiableAt hx.1)).mdifferentiableWithinAt
  · intro x hx
    simp only [mfld_simps] at hx
    exact
      ((he.symm.mdifferentiableAt hx.2).comp _
          (he'.symm.mdifferentiableAt hx.1)).mdifferentiableWithinAt
#align local_homeomorph.mdifferentiable.trans PartialHomeomorph.MDifferentiable.trans

end PartialHomeomorph.MDifferentiable

/-! ### Differentiability of `extChartAt` -/

section extChartAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M] {s : Set M} {x y : M}

theorem hasMFDerivAt_extChartAt (h : y ∈ (chartAt H x).source) :
    HasMFDerivAt I 𝓘(𝕜, E) (extChartAt I x) y (mfderiv I I (chartAt H x) y : _) :=
  I.hasMFDerivAt.comp y ((mdifferentiable_chart I x).mdifferentiableAt h).hasMFDerivAt
#align has_mfderiv_at_ext_chart_at hasMFDerivAt_extChartAt

theorem hasMFDerivWithinAt_extChartAt (h : y ∈ (chartAt H x).source) :
    HasMFDerivWithinAt I 𝓘(𝕜, E) (extChartAt I x) s y (mfderiv I I (chartAt H x) y : _) :=
  (hasMFDerivAt_extChartAt I h).hasMFDerivWithinAt
#align has_mfderiv_within_at_ext_chart_at hasMFDerivWithinAt_extChartAt

theorem mdifferentiableAt_extChartAt (h : y ∈ (chartAt H x).source) :
    MDifferentiableAt I 𝓘(𝕜, E) (extChartAt I x) y :=
  (hasMFDerivAt_extChartAt I h).mdifferentiableAt
#align mdifferentiable_at_ext_chart_at mdifferentiableAt_extChartAt

theorem mdifferentiableOn_extChartAt :
    MDifferentiableOn I 𝓘(𝕜, E) (extChartAt I x) (chartAt H x).source := fun _y hy =>
  (hasMFDerivWithinAt_extChartAt I hy).mdifferentiableWithinAt
#align mdifferentiable_on_ext_chart_at mdifferentiableOn_extChartAt

end extChartAt
