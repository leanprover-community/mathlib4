/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Riemannian metrics -/

noncomputable section
open Manifold BigOperators
open Bundle--open scoped Bundle --open_locale Manifold big_operators
--open Bundle

universe u -- FIXME

variable
  (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type u) [_i : TopologicalSpace M] [ChartedSpace E M]
  [SmoothManifoldWithCorners 𝓘(ℝ, E) M]

-- move this
instance (x : M) : ContinuousAdd (Bundle.Trivial M ℝ x) :=
id (inferInstance : ContinuousAdd ℝ)

-- move this
instance (x : M) : TopologicalAddGroup (Bundle.Trivial M ℝ x) :=
  id (inferInstance : TopologicalAddGroup ℝ)

-- move this
instance (x : M) : ContinuousSMul ℝ (Bundle.Trivial M ℝ x) :=
  (inferInstance : ContinuousSMul ℝ ℝ)

instance (x : M) : ContinuousSMul ℝ (TangentSpace 𝓘(ℝ, E) x) := sorry


/-- The cotangent space at a point `x` in a smooth manifold `M`. -/
--@[derive inhabited, TopologicalSpace, add_comm_group, module ℝ]
def CotangentSpace (x : M) : Type u := Bundle.ContinuousLinearMap
  (RingHom.id ℝ) /-E-/ (TangentSpace 𝓘(ℝ, E)) /-ℝ-/ (Trivial M ℝ) x

-- TODO: add these instances; they were previously derived
instance (x : M) : TopologicalSpace (CotangentSpace E M x) := sorry

instance (x : M) : Inhabited (CotangentSpace E M x) := sorry

instance (x : M): AddCommGroup (CotangentSpace E M x) := sorry

instance (x : M) : SMul ℝ (CotangentSpace E M x) := sorry

instance (x : M) : Module ℝ (CotangentSpace E M x) := sorry

namespace CotangentSpace

/- instance : TopologicalSpace (TotalSpace (CotangentSpace E M)) :=
  ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E (TangentSpace 𝓘(ℝ, E)) ℝ (Trivial M ℝ)

instance : FiberBundle (E →L[ℝ] ℝ) (CotangentSpace E M) :=
  ContinuousLinearMap.fiberBundle _ _ _ _ _

instance : VectorBundle ℝ (E →L[ℝ] ℝ) (CotangentSpace E M) :=
  ContinuousLinearMap.vectorBundle (RingHom.id ℝ) E (TangentSpace 𝓘(ℝ, E)) ℝ (Trivial M ℝ)

instance : SmoothVectorBundle (E →L[ℝ] ℝ) (CotangentSpace E M) 𝓘(ℝ, E) :=
  SmoothVectorBundle.continuousLinearMap -/

instance (x : M) : LinearMapClass (CotangentSpace E M x) ℝ (TangentSpace 𝓘(ℝ, E) x) ℝ :=
  sorry -- ContinuousSemilinearMapClass (RingHom.id ℝ) _ _ _ _ _

instance (x : M) : TopologicalAddGroup (CotangentSpace E M x) :=
  sorry --ContinuousLinearMap.topologicalAddGroup

instance (x : M) : ContinuousSMul ℝ (CotangentSpace E M x) :=
  sorry --ContinuousLinearMap.continuousSMul

instance (x : M) : TopologicalAddGroup (TangentSpace 𝓘(ℝ, E) x →L[ℝ] Trivial M ℝ x) :=
  ContinuousLinearMap.topologicalAddGroup

instance (x : M) : ContinuousSMul ℝ (TangentSpace 𝓘(ℝ, E) x →L[ℝ] Trivial M ℝ x) :=
  ContinuousLinearMap.continuousSMul

end CotangentSpace

/-- The "bicotangent space" at a point `x` in a smooth manifold `M`; that is, the space of bilinear
maps from `TangentSpace 𝓘(ℝ, E) x` to `ℝ`. -/
--@[derive [inhabited, TopologicalSpace, add_comm_group, module ℝ]]
def biCotangentSpace (x : M) : Type u := Bundle.ContinuousLinearMap
  (RingHom.id ℝ) (TangentSpace 𝓘(ℝ, E)) /-(E →L[ℝ] ℝ)-/ (CotangentSpace E M) x

-- TODO: fill in these instances/derive them
instance (x : M) : Inhabited (biCotangentSpace E M x) := sorry

instance (x : M) : TopologicalSpace (biCotangentSpace E M x) := sorry

instance (x : M) : AddCommGroup (biCotangentSpace E M x) := sorry

instance (x : M) : Module ℝ (biCotangentSpace E M x) := sorry

namespace biCotangentSpace

/- instance : TopologicalSpace (TotalSpace (biCotangentSpace E M)) :=
ContinuousLinearMap.topologicalSpaceTotalSpace
  (RingHom.id ℝ) E (TangentSpace 𝓘(ℝ, E)) (E →L[ℝ] ℝ) (CotangentSpace E M)

instance : FiberBundle (E →L[ℝ] E →L[ℝ] ℝ) (biCotangentSpace E M) :=
  ContinuousLinearMap.fiberBundle _ _ _ _ _

instance : VectorBundle ℝ (E →L[ℝ] E →L[ℝ] ℝ) (biCotangentSpace E M) :=
  ContinuousLinearMap.vectorBundle _ _ _ _ _

instance : SmoothVectorBundle (E →L[ℝ] E →L[ℝ] ℝ) (biCotangentSpace E M) 𝓘(ℝ, E) :=
  SmoothVectorBundle.continuousLinearMap -/

instance (x : M) : LinearMapClass (biCotangentSpace E M x) ℝ (TangentSpace 𝓘(ℝ, E) x)
    (CotangentSpace E M x) :=
  sorry -- ContinuousSemilinearMapClass (RingHom.id ℝ) _ _ _ _ _

instance (x : M) : TopologicalAddGroup (biCotangentSpace E M x) :=
  sorry -- ContinuousLinearMap.topologicalAddGroup

instance (x : M) : ContinuousSMul ℝ (biCotangentSpace E M x) :=
  sorry -- ContinuousLinearMap.continuousSMul

end biCotangentSpace

variable {E M}

/-- A Riemannian metric on `M` is a smooth, symmetric, positive-definite section of the Bundle of
continuous bilinear maps from the tangent Bundle of `M` to `ℝ`. -/
structure RiemannianMetric (g : SmoothSection 𝓘(ℝ, E) (E →L[ℝ] E →L[ℝ] ℝ) (biCotangentSpace E M)) : Prop :=
  (symm : ∀ x : M, ∀ v w : TangentSpace 𝓘(ℝ, E) x, g x v w = g x w v)
  (posdef : ∀ x : M, ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < g x v v)

/-- The sum of two Riemannian metrics is a Riemannian metric. -/
lemma RiemannianMetric.add
  {g₁ g₂ : SmoothSection 𝓘(ℝ, E) (E →L[ℝ] E →L[ℝ] ℝ) (biCotangentSpace E M)}
  (hg₁ : RiemannianMetric g₁) (hg₂ : RiemannianMetric g₂) :
  RiemannianMetric (g₁ + g₂) where--:= {
  symm := fun x v w ↦ by
    simp only [pi.add_apply, cont_mdiff_section.coe_add, ContinuousLinearMap.add_apply,
      hg₁.symm x v w, hg₂.symm x v w]
  posdef := fun x v hv ↦ by
    have h₁ : 0 < g₁ x v v := hg₁.posdef x v hv
    have h₂ : 0 < g₂ x v v := hg₂.posdef x v hv
    simpa only [pi.add_apply, cont_mdiff_section.coe_add, ContinuousLinearMap.add_apply]
      using add_pos h₁ h₂

/-- The scaling of a Riemannian metric by a positive real number is a Riemannian metric. -/
lemma RiemannianMetric.smul
    {g : SmoothSection 𝓘(ℝ, E) (E →L[ℝ] E →L[ℝ] ℝ) (biCotangentSpace E M)}
    (hg : RiemannianMetric g) {c : ℝ} (hc : 0 < c) :
  RiemannianMetric (c • g) where
  symm := fun x v w ↦by
    simp only [pi.smul_apply, cont_mdiff_section.coe_smul, ContinuousLinearMap.smul_apply,
      hg.symm x v w]
  posdef := fun x v hv ↦ by
    have h : 0 < g x v v := hg.posdef x v hv
    simpa only [pi.smul_apply, cont_mdiff_section.coe_smul, ContinuousLinearMap.smul_apply]
      using smul_pos hc h

variable (M E)

/-- Riemannian metrics form a convex cone in the space of sections. -/
noncomputable def RiemannianMetric_cone :
  ConvexCone ℝ (SmoothSection 𝓘(ℝ, E) (E →L[ℝ] E →L[ℝ] ℝ) (biCotangentSpace E M)) where
    carrier := {g | RiemannianMetric g}
    smul_mem' := fun c hc g hg ↦ hg.smul hc
    add_mem' := fun g₁ hg₁ g₂ hg₂ ↦ hg₁.add hg₂

variable
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [ChartedSpace F M]
  [SmoothManifoldWithCorners 𝓘(ℝ, F) M]
  [FiniteDimensional ℝ F] [SigmaCompactSpace M] [T2Space M]

-- move this
def charts_PartitionOfUnity : SmoothPartitionOfUnity M 𝓘(ℝ, F) M := by
  let U : M → Set M := fun x ↦ (chartAt F x).source
  have hU : ∀ i, IsOpen (U i) := fun x ↦ (chartAt F x).open_source
  have hUM : Set.univ ⊆ ⋃ i, U i := by
    intros x _
    rw [Set.mem_iUnion]
    use x
    exact mem_chart_source _ x
  sorry -- exact (SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, F) isClosed_univ U hU hUM).some

-- move this
lemma charts_PartitionOfUnity_isSubordinate :
  (charts_PartitionOfUnity M F).IsSubordinate (fun x ↦ (chartAt F x).source) := by

  let U : M → Set M := fun x ↦ (chartAt F x).source
  have hU : ∀ i, IsOpen (U i) := fun x ↦ (chartAt F x).open_source
  have hUM : Set.univ ⊆ ⋃ i, U i := by
    intros x _
    rw [Set.mem_iUnion]
    use x
    exact mem_chart_source _ x
  sorry -- exact (SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, F) isClosed_univ U hU hUM).some_spec
end

def patch (x : M) : TangentSpace 𝓘(ℝ, F) x →L[ℝ] TangentSpace 𝓘(ℝ, F) x →L[ℝ] ℝ := by
  let s : SmoothPartitionOfUnity M 𝓘(ℝ, F) M := charts_PartitionOfUnity M F
  let g₀ : F →L[ℝ] F →L[ℝ] ℝ := innerSL ℝ
  let e : Π y : M, TangentSpace 𝓘(ℝ, F) x →L[ℝ] F :=
    fun y ↦ (trivialization_at F (TangentSpace 𝓘(ℝ, F)) y).ContinuousLinearMap_at ℝ x
  let G : Π y : M, TangentSpace 𝓘(ℝ, F) x →L[ℝ] TangentSpace 𝓘(ℝ, F) x →L[ℝ] ℝ :=
    fun y, (g₀ ∘L (e y)).flip ∘L (e y)
  exact ∑ᶠ y : M, s y x • G y

/- A (σ-compact, Hausdorff, finite-dimensional) manifold admits a Riemannian metric. -/
lemma exists_RiemannianMetric :
    ∃ g : SmoothSection 𝓘(ℝ, F) (F →L[ℝ] F →L[ℝ] ℝ) (biCotangentSpace F M),
  RiemannianMetric g := by
  refine ⟨⟨patch M F, ?_⟩, ?_⟩
  · sorry
  · sorry
