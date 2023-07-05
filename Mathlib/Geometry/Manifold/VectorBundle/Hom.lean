/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module geometry.manifold.vector_bundle.hom
! leanprover-community/mathlib commit e473c3198bb41f68560cab68a0529c854b618833
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.Hom

/-! # Homs of smooth vector bundles over the same base space

Here we show that `bundle.continuous_linear_map` is a smooth vector bundle.

Note that we only do this for bundles of linear maps, not for bundles of arbitrary semilinear maps.
To do it for semilinear maps, we would need to generalize `continuous_linear_map.cont_mdiff`
(and `continuous_linear_map.cont_diff`) to semilinear maps.
-/


noncomputable section

open Bundle Set LocalHomeomorph ContinuousLinearMap Pretrivialization

open scoped Manifold Bundle

variable {𝕜 B F F₁ F₂ M M₁ M₂ : Type _} {E : B → Type _} {E₁ : B → Type _} {E₂ : B → Type _}
  [NontriviallyNormedField 𝕜] [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [_i₁ : ∀ x, TopologicalAddGroup (E₂ x)] [_i₂ : ∀ x, ContinuousSMul 𝕜 (E₂ x)] {EB : Type _}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type _} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB) [TopologicalSpace B] [ChartedSpace HB B] {EM : Type _}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type _} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [Is : SmoothManifoldWithCorners IM M] {n : ℕ∞} [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] {e₁ e₁' : Trivialization F₁ (π F₁ E₁)}
  {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}

local notation "LE₁E₂" => TotalSpace (F₁ →L[𝕜] F₂) (Bundle.ContinuousLinearMap (RingHom.id 𝕜) E₁ E₂)

-- This proof is slow, especially the `simp only` and the elaboration of `h₂`.
theorem smoothOn_continuousLinearMapCoordChange [SmoothManifoldWithCorners IB B]
    [SmoothVectorBundle F₁ E₁ IB] [SmoothVectorBundle F₂ E₂ IB] [MemTrivializationAtlas e₁]
    [MemTrivializationAtlas e₁'] [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    SmoothOn IB 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] F₁ →L[𝕜] F₂)
      (continuousLinearMapCoordChange (RingHom.id 𝕜) e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  let L₁ := compL 𝕜 F₁ F₂ F₂
  have h₁ : Smooth _ _ _ := L₁.cont_mdiff
  have h₂ : Smooth _ _ _ := (ContinuousLinearMap.flip (compL 𝕜 F₁ F₁ F₂)).ContMDiff
  have h₃ : SmoothOn IB _ _ _ := smooth_on_coord_change e₁' e₁
  have h₄ : SmoothOn IB _ _ _ := smooth_on_coord_change e₂ e₂'
  refine' ((h₁.comp_smooth_on (h₄.mono _)).clm_comp (h₂.comp_smooth_on (h₃.mono _))).congr _
  · mfld_set_tac
  · mfld_set_tac
  · intro b hb; ext L v
    simp only [continuous_linear_map_coord_change, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.arrowCongrSL_apply, comp_apply, Function.comp, compL_apply, flip_apply,
      ContinuousLinearEquiv.symm_symm, LinearEquiv.toFun_eq_coe,
      ContinuousLinearEquiv.arrowCongrₛₗ_apply, ContinuousLinearMap.coe_comp']
#align smooth_on_continuous_linear_map_coord_change smoothOn_continuousLinearMapCoordChange

theorem hom_chart (y₀ y : LE₁E₂) :
    chartAt (ModelProd HB (F₁ →L[𝕜] F₂)) y₀ y =
      (chartAt HB y₀.1 y.1, inCoordinates F₁ E₁ F₂ E₂ y₀.1 y.1 y₀.1 y.1 y.2) := by
  simp_rw [FiberBundle.chartedSpace_chartAt, trans_apply, LocalHomeomorph.prod_apply,
    Trivialization.coe_coe, LocalHomeomorph.refl_apply, Function.id_def, hom_trivializationAt_apply]
#align hom_chart hom_chart

variable {IB}

theorem contMDiffAt_hom_bundle (f : M → LE₁E₂) {x₀ : M} {n : ℕ∞} :
    ContMDiffAt IM (IB.Prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n f x₀ ↔
      ContMDiffAt IM IB n (fun x => (f x).1) x₀ ∧
        ContMDiffAt IM 𝓘(𝕜, F₁ →L[𝕜] F₂) n
          (fun x => inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  by apply cont_mdiff_at_total_space
#align cont_mdiff_at_hom_bundle contMDiffAt_hom_bundle

theorem smoothAt_hom_bundle (f : M → LE₁E₂) {x₀ : M} :
    SmoothAt IM (IB.Prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) f x₀ ↔
      SmoothAt IM IB (fun x => (f x).1) x₀ ∧
        SmoothAt IM 𝓘(𝕜, F₁ →L[𝕜] F₂)
          (fun x => inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  contMDiffAt_hom_bundle f
#align smooth_at_hom_bundle smoothAt_hom_bundle

variable [SmoothManifoldWithCorners IB B] [SmoothVectorBundle F₁ E₁ IB]
  [SmoothVectorBundle F₂ E₂ IB]

instance Bundle.ContinuousLinearMap.vectorPrebundle.isSmooth :
    (Bundle.ContinuousLinearMap.vectorPrebundle (RingHom.id 𝕜) F₁ E₁ F₂ E₂).IsSmooth IB
    where exists_smooth_coord_change := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    skip
    refine'
      ⟨continuous_linear_map_coord_change (RingHom.id 𝕜) e₁ e₁' e₂ e₂',
        smoothOn_continuousLinearMapCoordChange IB,
        continuous_linear_map_coord_change_apply (RingHom.id 𝕜) e₁ e₁' e₂ e₂'⟩
#align bundle.continuous_linear_map.vector_prebundle.is_smooth Bundle.ContinuousLinearMap.vectorPrebundle.isSmooth

instance SmoothVectorBundle.continuousLinearMap :
    SmoothVectorBundle (F₁ →L[𝕜] F₂) (Bundle.ContinuousLinearMap (RingHom.id 𝕜) E₁ E₂) IB :=
  (Bundle.ContinuousLinearMap.vectorPrebundle (RingHom.id 𝕜) F₁ E₁ F₂ E₂).SmoothVectorBundle IB
#align smooth_vector_bundle.continuous_linear_map SmoothVectorBundle.continuousLinearMap

