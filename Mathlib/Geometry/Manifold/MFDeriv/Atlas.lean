/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Differentiability of models with corners and (extended) charts

In this file, we analyse the differentiability of charts, models with corners and extended charts.
We show that
* models with corners are differentiable
* charts are differentiable on their source
* `mdifferentiableOn_extChartAt`: `extChartAt` is differentiable on its source

Suppose a partial homeomorphism `e` is differentiable. This file shows
* `PartialHomeomorph.MDifferentiable.mfderiv`: its derivative is a continuous linear equivalence
* `PartialHomeomorph.MDifferentiable.mfderiv_bijective`: its derivative is bijective;
  there are also spelling with trivial kernel and full range

In particular, (extended) charts have bijective differential.

## Tags
charts, differentiable, bijective
-/

noncomputable section

open scoped Manifold ContDiff
open Bundle Set Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']

section ModelWithCorners
namespace ModelWithCorners

/- In general, the model with corner `I` is implicit in most theorems in differential geometry, but
this section is about `I` as a map, not as a parameter. Therefore, we make it explicit. -/
variable (I)

/-! #### Model with corners -/

protected theorem hasMFDerivAt {x} : HasMFDerivAt I 𝓘(𝕜, E) I x (ContinuousLinearMap.id _ _) :=
  ⟨I.continuousAt, (hasFDerivWithinAt_id _ _).congr' I.rightInvOn (mem_range_self _)⟩

protected theorem hasMFDerivWithinAt {s x} :
    HasMFDerivWithinAt I 𝓘(𝕜, E) I s x (ContinuousLinearMap.id _ _) :=
  I.hasMFDerivAt.hasMFDerivWithinAt

protected theorem mdifferentiableWithinAt {s x} : MDifferentiableWithinAt I 𝓘(𝕜, E) I s x :=
  I.hasMFDerivWithinAt.mdifferentiableWithinAt

protected theorem mdifferentiableAt {x} : MDifferentiableAt I 𝓘(𝕜, E) I x :=
  I.hasMFDerivAt.mdifferentiableAt

protected theorem mdifferentiableOn {s} : MDifferentiableOn I 𝓘(𝕜, E) I s := fun _ _ =>
  I.mdifferentiableWithinAt

protected theorem mdifferentiable : MDifferentiable I 𝓘(𝕜, E) I := fun _ => I.mdifferentiableAt

theorem hasMFDerivWithinAt_symm {x} (hx : x ∈ range I) :
    HasMFDerivWithinAt 𝓘(𝕜, E) I I.symm (range I) x (ContinuousLinearMap.id _ _) :=
  ⟨I.continuousWithinAt_symm,
    (hasFDerivWithinAt_id _ _).congr' (fun _y hy => I.rightInvOn hy.1) ⟨hx, mem_range_self _⟩⟩

theorem mdifferentiableOn_symm : MDifferentiableOn 𝓘(𝕜, E) I I.symm (range I) := fun _x hx =>
  (I.hasMFDerivWithinAt_symm hx).mdifferentiableWithinAt

theorem mdifferentiableWithinAt_symm {z : E} (hz : z ∈ range I) :
    MDifferentiableWithinAt 𝓘(𝕜, E) I I.symm (range I) z :=
  I.mdifferentiableOn_symm z hz

end ModelWithCorners

end ModelWithCorners

section Charts

variable [IsManifold I 1 M] [IsManifold I' 1 M']
  [IsManifold I'' 1 M''] {e : PartialHomeomorph M H}

theorem mdifferentiableAt_atlas (h : e ∈ atlas H M) {x : M} (hx : x ∈ e.source) :
    MDifferentiableAt I I e x := by
  rw [mdifferentiableAt_iff]
  refine ⟨(e.continuousOn x hx).continuousAt (e.open_source.mem_nhds hx), ?_⟩
  have mem :
    I ((chartAt H x : M → H) x) ∈ I.symm ⁻¹' ((chartAt H x).symm ≫ₕ e).source ∩ range I := by
    simp only [hx, mfld_simps]
  have : (chartAt H x).symm.trans e ∈ contDiffGroupoid 1 I :=
    HasGroupoid.compatible (chart_mem_atlas H x) h
  have A :
    ContDiffOn 𝕜 1 (I ∘ (chartAt H x).symm.trans e ∘ I.symm)
      (I.symm ⁻¹' ((chartAt H x).symm.trans e).source ∩ range I) :=
    this.1
  have B := A.differentiableOn le_rfl (I ((chartAt H x : M → H) x)) mem
  simp only [mfld_simps] at B
  rw [inter_comm, differentiableWithinAt_inter] at B
  · simpa only [mfld_simps]
  · apply IsOpen.mem_nhds ((PartialHomeomorph.open_source _).preimage I.continuous_symm) mem.1

theorem mdifferentiableOn_atlas (h : e ∈ atlas H M) : MDifferentiableOn I I e e.source :=
  fun _x hx => (mdifferentiableAt_atlas h hx).mdifferentiableWithinAt

theorem mdifferentiableAt_atlas_symm (h : e ∈ atlas H M) {x : H} (hx : x ∈ e.target) :
    MDifferentiableAt I I e.symm x := by
  rw [mdifferentiableAt_iff]
  refine ⟨(e.continuousOn_symm x hx).continuousAt (e.open_target.mem_nhds hx), ?_⟩
  have mem : I x ∈ I.symm ⁻¹' (e.symm ≫ₕ chartAt H (e.symm x)).source ∩ range I := by
    simp only [hx, mfld_simps]
  have : e.symm.trans (chartAt H (e.symm x)) ∈ contDiffGroupoid 1 I :=
    HasGroupoid.compatible h (chart_mem_atlas H _)
  have A :
    ContDiffOn 𝕜 1 (I ∘ e.symm.trans (chartAt H (e.symm x)) ∘ I.symm)
      (I.symm ⁻¹' (e.symm.trans (chartAt H (e.symm x))).source ∩ range I) :=
    this.1
  have B := A.differentiableOn le_rfl (I x) mem
  simp only [mfld_simps] at B
  rw [inter_comm, differentiableWithinAt_inter] at B
  · simpa only [mfld_simps]
  · apply IsOpen.mem_nhds ((PartialHomeomorph.open_source _).preimage I.continuous_symm) mem.1

theorem mdifferentiableOn_atlas_symm (h : e ∈ atlas H M) : MDifferentiableOn I I e.symm e.target :=
  fun _x hx => (mdifferentiableAt_atlas_symm h hx).mdifferentiableWithinAt

theorem mdifferentiable_of_mem_atlas (h : e ∈ atlas H M) : e.MDifferentiable I I :=
  ⟨mdifferentiableOn_atlas h, mdifferentiableOn_atlas_symm h⟩

theorem mdifferentiable_chart (x : M) : (chartAt H x).MDifferentiable I I :=
  mdifferentiable_of_mem_atlas (chart_mem_atlas _ _)

end Charts

/-! ### Differentiable partial homeomorphisms -/

namespace PartialHomeomorph.MDifferentiable
variable {e : PartialHomeomorph M M'} (he : e.MDifferentiable I I') {e' : PartialHomeomorph M' M''}
include he

nonrec theorem symm : e.symm.MDifferentiable I' I := he.symm

protected theorem mdifferentiableAt {x : M} (hx : x ∈ e.source) : MDifferentiableAt I I' e x :=
  (he.1 x hx).mdifferentiableAt (e.open_source.mem_nhds hx)

theorem mdifferentiableAt_symm {x : M'} (hx : x ∈ e.target) : MDifferentiableAt I' I e.symm x :=
  (he.2 x hx).mdifferentiableAt (e.open_target.mem_nhds hx)

theorem symm_comp_deriv {x : M} (hx : x ∈ e.source) :
    (mfderiv I' I e.symm (e x)).comp (mfderiv I I' e x) =
      ContinuousLinearMap.id 𝕜 (TangentSpace I x) := by
  have : mfderiv I I (e.symm ∘ e) x = (mfderiv I' I e.symm (e x)).comp (mfderiv I I' e x) :=
    mfderiv_comp x (he.mdifferentiableAt_symm (e.map_source hx)) (he.mdifferentiableAt hx)
  rw [← this]
  have : mfderiv I I (_root_.id : M → M) x = ContinuousLinearMap.id _ _ := mfderiv_id
  rw [← this]
  apply Filter.EventuallyEq.mfderiv_eq
  have : e.source ∈ 𝓝 x := e.open_source.mem_nhds hx
  exact Filter.mem_of_superset this (by mfld_set_tac)

theorem comp_symm_deriv {x : M'} (hx : x ∈ e.target) :
    (mfderiv I I' e (e.symm x)).comp (mfderiv I' I e.symm x) =
      ContinuousLinearMap.id 𝕜 (TangentSpace I' x) :=
  he.symm.symm_comp_deriv hx

/-- The derivative of a differentiable partial homeomorphism, as a continuous linear equivalence
between the tangent spaces at `x` and `e x`. -/
protected def mfderiv (he : e.MDifferentiable I I') {x : M} (hx : x ∈ e.source) :
    TangentSpace I x ≃L[𝕜] TangentSpace I' (e x) :=
  { mfderiv I I' e x with
    invFun := mfderiv I' I e.symm (e x)
    continuous_toFun := (mfderiv I I' e x).cont
    continuous_invFun := (mfderiv I' I e.symm (e x)).cont
    left_inv := fun y => by
      have : (ContinuousLinearMap.id _ _ : TangentSpace I x →L[𝕜] TangentSpace I x) y = y := rfl
      conv_rhs => rw [← this, ← he.symm_comp_deriv hx]
      rfl
    right_inv := fun y => by
      have :
        (ContinuousLinearMap.id 𝕜 _ : TangentSpace I' (e x) →L[𝕜] TangentSpace I' (e x)) y = y :=
        rfl
      conv_rhs => rw [← this, ← he.comp_symm_deriv (e.map_source hx)]
      rw [e.left_inv hx]
      rfl }

theorem mfderiv_bijective {x : M} (hx : x ∈ e.source) : Function.Bijective (mfderiv I I' e x) :=
  (he.mfderiv hx).bijective

theorem mfderiv_injective {x : M} (hx : x ∈ e.source) : Function.Injective (mfderiv I I' e x) :=
  (he.mfderiv hx).injective

theorem mfderiv_surjective {x : M} (hx : x ∈ e.source) : Function.Surjective (mfderiv I I' e x) :=
  (he.mfderiv hx).surjective

theorem ker_mfderiv_eq_bot {x : M} (hx : x ∈ e.source) : LinearMap.ker (mfderiv I I' e x) = ⊥ :=
  (he.mfderiv hx).toLinearEquiv.ker

theorem range_mfderiv_eq_top {x : M} (hx : x ∈ e.source) : LinearMap.range (mfderiv I I' e x) = ⊤ :=
  (he.mfderiv hx).toLinearEquiv.range

theorem range_mfderiv_eq_univ {x : M} (hx : x ∈ e.source) : range (mfderiv I I' e x) = univ :=
  (he.mfderiv_surjective hx).range_eq

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

end PartialHomeomorph.MDifferentiable

/-! ### Differentiability of `extChartAt` -/

section extChartAt

variable [IsManifold I 1 M] {s : Set M} {x y : M} {z : E}

theorem hasMFDerivAt_extChartAt (h : y ∈ (chartAt H x).source) :
    HasMFDerivAt I 𝓘(𝕜, E) (extChartAt I x) y (mfderiv I I (chartAt H x) y :) :=
  I.hasMFDerivAt.comp y ((mdifferentiable_chart x).mdifferentiableAt h).hasMFDerivAt

theorem hasMFDerivWithinAt_extChartAt (h : y ∈ (chartAt H x).source) :
    HasMFDerivWithinAt I 𝓘(𝕜, E) (extChartAt I x) s y (mfderiv I I (chartAt H x) y :) :=
  (hasMFDerivAt_extChartAt h).hasMFDerivWithinAt

theorem mdifferentiableAt_extChartAt (h : y ∈ (chartAt H x).source) :
    MDifferentiableAt I 𝓘(𝕜, E) (extChartAt I x) y :=
  (hasMFDerivAt_extChartAt h).mdifferentiableAt

theorem mdifferentiableOn_extChartAt :
    MDifferentiableOn I 𝓘(𝕜, E) (extChartAt I x) (chartAt H x).source := fun _y hy =>
  (hasMFDerivWithinAt_extChartAt hy).mdifferentiableWithinAt

theorem mdifferentiableWithinAt_extChartAt_symm (h : z ∈ (extChartAt I x).target) :
    MDifferentiableWithinAt 𝓘(𝕜, E) I (extChartAt I x).symm (range I) z := by
  have Z := I.mdifferentiableWithinAt_symm (extChartAt_target_subset_range x h)
  apply MDifferentiableAt.comp_mdifferentiableWithinAt (I' := I) _ _ Z
  apply mdifferentiableAt_atlas_symm (ChartedSpace.chart_mem_atlas x)
  simp only [extChartAt, PartialHomeomorph.extend, PartialEquiv.trans_target,
    ModelWithCorners.target_eq, ModelWithCorners.toPartialEquiv_coe_symm, mem_inter_iff, mem_range,
    mem_preimage] at h
  exact h.2

theorem mdifferentiableOn_extChartAt_symm :
    MDifferentiableOn 𝓘(𝕜, E) I (extChartAt I x).symm (extChartAt I x).target := by
  intro y hy
  exact (mdifferentiableWithinAt_extChartAt_symm hy).mono (extChartAt_target_subset_range x)

/-- The composition of the derivative of `extChartAt` with the derivative of the inverse of
`extChartAt` gives the identity.
Version where the basepoint belongs to `(extChartAt I x).target`. -/
lemma mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm {x : M}
    {y : E} (hy : y ∈ (extChartAt I x).target) :
    (mfderiv I 𝓘(𝕜, E) (extChartAt I x) ((extChartAt I x).symm y)) ∘L
      (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I) y) = ContinuousLinearMap.id _ _ := by
  have U : UniqueMDiffWithinAt 𝓘(𝕜, E) (range ↑I) y := by
    apply I.uniqueMDiffOn
    exact extChartAt_target_subset_range x hy
  have h'y : (extChartAt I x).symm y ∈ (extChartAt I x).source := (extChartAt I x).map_target hy
  have h''y : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    rwa [← extChartAt_source (I := I)]
  rw [← mfderiv_comp_mfderivWithin]; rotate_left
  · apply mdifferentiableAt_extChartAt h''y
  · exact mdifferentiableWithinAt_extChartAt_symm hy
  · exact U
  rw [← mfderivWithin_id U]
  apply Filter.EventuallyEq.mfderivWithin_eq
  · filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hy] with z hz
    simp only [Function.comp_def, PartialEquiv.right_inv (extChartAt I x) hz, id_eq]
  · simp only [Function.comp_def, PartialEquiv.right_inv (extChartAt I x) hy, id_eq]

/-- The composition of the derivative of `extChartAt` with the derivative of the inverse of
`extChartAt` gives the identity.
Version where the basepoint belongs to `(extChartAt I x).source`. -/
lemma mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' {x : M}
    {y : M} (hy : y ∈ (extChartAt I x).source) :
    (mfderiv I 𝓘(𝕜, E) (extChartAt I x) y) ∘L
      (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I) (extChartAt I x y))
    = ContinuousLinearMap.id _ _ := by
  have : y = (extChartAt I x).symm (extChartAt I x y) := ((extChartAt I x).left_inv hy).symm
  convert mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm ((extChartAt I x).map_source hy)

/-- The composition of the derivative of the inverse of `extChartAt` with the derivative of
`extChartAt` gives the identity.
Version where the basepoint belongs to `(extChartAt I x).target`. -/
lemma mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
    {y : E} (hy : y ∈ (extChartAt I x).target) :
    (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I) y) ∘L
      (mfderiv I 𝓘(𝕜, E) (extChartAt I x) ((extChartAt I x).symm y))
      = ContinuousLinearMap.id _ _ := by
  have h'y : (extChartAt I x).symm y ∈ (extChartAt I x).source := (extChartAt I x).map_target hy
  have h''y : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    rwa [← extChartAt_source (I := I)]
  have U' : UniqueMDiffWithinAt I (extChartAt I x).source ((extChartAt I x).symm y) :=
    (isOpen_extChartAt_source x).uniqueMDiffWithinAt h'y
  have : mfderiv I 𝓘(𝕜, E) (extChartAt I x) ((extChartAt I x).symm y)
      = mfderivWithin I 𝓘(𝕜, E) (extChartAt I x) (extChartAt I x).source
      ((extChartAt I x).symm y) := by
    rw [mfderivWithin_eq_mfderiv U']
    exact mdifferentiableAt_extChartAt h''y
  rw [this, ← mfderivWithin_comp_of_eq]; rotate_left
  · exact mdifferentiableWithinAt_extChartAt_symm hy
  · exact (mdifferentiableAt_extChartAt h''y).mdifferentiableWithinAt
  · intro z hz
    apply extChartAt_target_subset_range x
    exact PartialEquiv.map_source (extChartAt I x) hz
  · exact U'
  · exact PartialEquiv.right_inv (extChartAt I x) hy
  rw [← mfderivWithin_id U']
  apply Filter.EventuallyEq.mfderivWithin_eq
  · filter_upwards [extChartAt_source_mem_nhdsWithin' h'y] with z hz
    simp only [Function.comp_def, PartialEquiv.left_inv (extChartAt I x) hz, id_eq]
  · simp only [Function.comp_def, PartialEquiv.right_inv (extChartAt I x) hy, id_eq]

/-- The composition of the derivative of the inverse of `extChartAt` with the derivative of
`extChartAt` gives the identity.
Version where the basepoint belongs to `(extChartAt I x).source`. -/
lemma mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    {y : M} (hy : y ∈ (extChartAt I x).source) :
    (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I) (extChartAt I x y)) ∘L
      (mfderiv I 𝓘(𝕜, E) (extChartAt I x) y)
      = ContinuousLinearMap.id _ _ := by
  have : y = (extChartAt I x).symm (extChartAt I x y) := ((extChartAt I x).left_inv hy).symm
  convert mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt ((extChartAt I x).map_source hy)

lemma isInvertible_mfderivWithin_extChartAt_symm {y : E} (hy : y ∈ (extChartAt I x).target) :
    (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I) y).IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hy)
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hy)

lemma isInvertible_mfderiv_extChartAt {y : M} (hy : y ∈ (extChartAt I x).source) :
    (mfderiv I 𝓘(𝕜, E) (extChartAt I x) y).IsInvertible := by
  have h'y : extChartAt I x y ∈ (extChartAt I x).target := (extChartAt I x).map_source hy
  have Z := ContinuousLinearMap.IsInvertible.of_inverse
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm h'y)
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt h'y)
  have : (extChartAt I x).symm ((extChartAt I x) y) = y := (extChartAt I x).left_inv hy
  rwa [this] at Z

/-- The trivialization of the tangent bundle at a point is the manifold derivative of the
extended chart.
Use with care as this abuses the defeq `TangentSpace 𝓘(𝕜, E) y = E` for `y : E`. -/
theorem TangentBundle.continuousLinearMapAt_trivializationAt
    {x₀ x : M} (hx : x ∈ (chartAt H x₀).source) :
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x =
      mfderiv I 𝓘(𝕜, E) (extChartAt I x₀) x := by
  have : MDifferentiableAt I 𝓘(𝕜, E) (extChartAt I x₀) x := mdifferentiableAt_extChartAt hx
  simp only [extChartAt, PartialHomeomorph.extend, PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, PartialHomeomorph.toFun_eq_coe] at this
  simp [hx, mfderiv, this]

/-- The inverse trivialization of the tangent bundle at a point is the manifold derivative of the
inverse of the extended chart.
Use with care as this abuses the defeq `TangentSpace 𝓘(𝕜, E) y = E` for `y : E`. -/
theorem TangentBundle.symmL_trivializationAt
    {x₀ x : M} (hx : x ∈ (chartAt H x₀).source) :
    (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x =
      mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (range I) (extChartAt I x₀ x) := by
  have : MDifferentiableWithinAt 𝓘(𝕜, E) I ((chartAt H x₀).symm ∘ I.symm) (range I)
      (I (chartAt H x₀ x)) := by
    simpa using mdifferentiableWithinAt_extChartAt_symm (by simp [hx])
  simp [hx, mfderivWithin, this]

end extChartAt
