/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.Hom

#align_import geometry.manifold.vector_bundle.hom from "leanprover-community/mathlib"@"8905e5ed90859939681a725b00f6063e65096d95"

/-! # Homs of smooth vector bundles over the same base space

Here we show that `Bundle.ContinuousLinearMap` is a smooth vector bundle.

Note that we only do this for bundles of linear maps, not for bundles of arbitrary semilinear maps.
To do it for semilinear maps, we would need to generalize `ContinuousLinearMap.contMDiff`
(and `ContinuousLinearMap.contDiff`) to semilinear maps.
-/


noncomputable section

open Bundle Set PartialHomeomorph ContinuousLinearMap Pretrivialization

open scoped Manifold Bundle

variable {𝕜 B F₁ F₂ M : Type*} {E₁ : B → Type*} {E₂ : B → Type*} [NontriviallyNormedField 𝕜]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, TopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)] {EB : Type*}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB) [TopologicalSpace B] [ChartedSpace HB B] {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [SmoothManifoldWithCorners IM M] {n : ℕ∞} [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] {e₁ e₁' : Trivialization F₁ (π F₁ E₁)}
  {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}

local notation "LE₁E₂" => TotalSpace (F₁ →L[𝕜] F₂) (Bundle.ContinuousLinearMap (RingHom.id 𝕜) E₁ E₂)

-- Porting note (#11083): moved slow parts to separate lemmas
theorem smoothOn_continuousLinearMapCoordChange
    [SmoothVectorBundle F₁ E₁ IB] [SmoothVectorBundle F₂ E₂ IB] [MemTrivializationAtlas e₁]
    [MemTrivializationAtlas e₁'] [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    SmoothOn IB 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] F₁ →L[𝕜] F₂)
      (continuousLinearMapCoordChange (RingHom.id 𝕜) e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  have h₁ := smoothOn_coordChangeL IB e₁' e₁
  have h₂ := smoothOn_coordChangeL IB e₂ e₂'
  refine (h₁.mono ?_).cle_arrowCongr (h₂.mono ?_) <;> mfld_set_tac
#align smooth_on_continuous_linear_map_coord_change smoothOn_continuousLinearMapCoordChange

theorem hom_chart (y₀ y : LE₁E₂) :
    chartAt (ModelProd HB (F₁ →L[𝕜] F₂)) y₀ y =
      (chartAt HB y₀.1 y.1, inCoordinates F₁ E₁ F₂ E₂ y₀.1 y.1 y₀.1 y.1 y.2) := by
  rw [FiberBundle.chartedSpace_chartAt, trans_apply, PartialHomeomorph.prod_apply,
    Trivialization.coe_coe, PartialHomeomorph.refl_apply, Function.id_def,
    hom_trivializationAt_apply]
#align hom_chart hom_chart

variable {IB}

theorem contMDiffAt_hom_bundle (f : M → LE₁E₂) {x₀ : M} {n : ℕ∞} :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n f x₀ ↔
      ContMDiffAt IM IB n (fun x => (f x).1) x₀ ∧
        ContMDiffAt IM 𝓘(𝕜, F₁ →L[𝕜] F₂) n
          (fun x => inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  contMDiffAt_totalSpace ..
#align cont_mdiff_at_hom_bundle contMDiffAt_hom_bundle

theorem smoothAt_hom_bundle (f : M → LE₁E₂) {x₀ : M} :
    SmoothAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) f x₀ ↔
      SmoothAt IM IB (fun x => (f x).1) x₀ ∧
        SmoothAt IM 𝓘(𝕜, F₁ →L[𝕜] F₂)
          (fun x => inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  contMDiffAt_hom_bundle f
#align smooth_at_hom_bundle smoothAt_hom_bundle

variable [SmoothVectorBundle F₁ E₁ IB] [SmoothVectorBundle F₂ E₂ IB]

instance Bundle.ContinuousLinearMap.vectorPrebundle.isSmooth :
    (Bundle.ContinuousLinearMap.vectorPrebundle (RingHom.id 𝕜) F₁ E₁ F₂ E₂).IsSmooth IB where
  exists_smoothCoordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousLinearMapCoordChange (RingHom.id 𝕜) e₁ e₁' e₂ e₂',
      smoothOn_continuousLinearMapCoordChange IB,
      continuousLinearMapCoordChange_apply (RingHom.id 𝕜) e₁ e₁' e₂ e₂'⟩
#align bundle.continuous_linear_map.vector_prebundle.is_smooth Bundle.ContinuousLinearMap.vectorPrebundle.isSmooth

instance SmoothVectorBundle.continuousLinearMap :
    SmoothVectorBundle (F₁ →L[𝕜] F₂) (Bundle.ContinuousLinearMap (RingHom.id 𝕜) E₁ E₂) IB :=
  (Bundle.ContinuousLinearMap.vectorPrebundle (RingHom.id 𝕜) F₁ E₁ F₂ E₂).smoothVectorBundle IB
#align smooth_vector_bundle.continuous_linear_map SmoothVectorBundle.continuousLinearMap
