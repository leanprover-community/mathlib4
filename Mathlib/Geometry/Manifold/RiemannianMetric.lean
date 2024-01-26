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

variable
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type*) [_i : TopologicalSpace M] [ChartedSpace E M]
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
--@[derive [inhabited, TopologicalSpace, add_comm_group, module ℝ]]
def CotangentSpace (x : M) : Type* := Bundle.ContinuousLinearMap
  (RingHom.id ℝ) E /-(TangentSpace 𝓘(ℝ, E))-/ ℝ /-(trivial M ℝ)-/ x
#exit
namespace CotangentSpace

instance : TopologicalSpace (TotalSpace (CotangentSpace E M)) :=
ContinuousLinearMap.topologicalSpaceTotalSpace
  (RingHom.id ℝ) E (TangentSpace 𝓘(ℝ, E)) ℝ (Trivial M ℝ)

instance : FiberBundle (E →L[ℝ] ℝ) (CotangentSpace E M) :=
  ContinuousLinearMap.FiberBundle _ _ _ _ _

instance : VectorBundle ℝ (E →L[ℝ] ℝ) (CotangentSpace E M) :=
ContinuousLinearMap.VectorBundle (RingHom.id ℝ) E (TangentSpace 𝓘(ℝ, E)) ℝ (trivial M ℝ)

instance : SmoothVectorBundle (E →L[ℝ] ℝ) (CotangentSpace E M) 𝓘(ℝ, E) :=
SmoothVectorBundle.ContinuousLinearMap

instance (x : M) : linear_map_class (CotangentSpace E M x) ℝ (TangentSpace 𝓘(ℝ, E) x) ℝ :=
ContinuousLinearMap.semilinear_map_class (RingHom.id ℝ) _ _ _ _ _

instance (x : M) : TopologicalAddGroup (CotangentSpace E M x) :=
ContinuousLinearMap.TopologicalAddGroup

instance (x : M) : ContinuousSMul ℝ (CotangentSpace E M x) :=
ContinuousLinearMap.ContinuousSMul

instance (x : M) : TopologicalAddGroup (TangentSpace 𝓘(ℝ, E) x →L[ℝ] trivial M ℝ x) :=
ContinuousLinearMap.TopologicalAddGroup

instance (x : M) : ContinuousSMul ℝ (TangentSpace 𝓘(ℝ, E) x →L[ℝ] trivial M ℝ x) :=
ContinuousLinearMap.ContinuousSMul

end CotangentSpace
-/

/-- The "bicotangent space" at a point `x` in a smooth manifold `M`; that is, the space of bilinear
maps from `TangentSpace 𝓘(ℝ, E) x` to `ℝ`. -/
--@[derive [inhabited, TopologicalSpace, add_comm_group, module ℝ]]
def biCotangentSpace (x : M) : Type* :=
Bundle.ContinuousLinearMap
  (RingHom.id ℝ) E (TangentSpace 𝓘(ℝ, E)) (E →L[ℝ] ℝ) (CotangentSpace E M) x

namespace biCotangentSpace

instance : TopologicalSpace (TotalSpace (biCotangentSpace E M)) :=
ContinuousLinearMap.topologicalSpaceTotalSpace
  (RingHom.id ℝ) E (TangentSpace 𝓘(ℝ, E)) (E →L[ℝ] ℝ) (CotangentSpace E M)

instance : FiberBundle (E →L[ℝ] E →L[ℝ] ℝ) (biCotangentSpace E M) :=
ContinuousLinearMap.FiberBundle _ _ _ _ _

instance : VectorBundle ℝ (E →L[ℝ] E →L[ℝ] ℝ) (biCotangentSpace E M) :=
  ContinuousLinearMap.VectorBundle _ _ _ _ _

instance : SmoothVectorBundle (E →L[ℝ] E →L[ℝ] ℝ) (biCotangentSpace E M) 𝓘(ℝ, E) :=
  SmoothVectorBundle.ContinuousLinearMap

instance (x : M) : linear_map_class (biCotangentSpace E M x) ℝ (TangentSpace 𝓘(ℝ, E) x)
    (CotangentSpace E M x) :=
ContinuousLinearMap.semilinear_map_class (RingHom.id ℝ) _ _ _ _ _

instance (x : M) : TopologicalAddGroup (biCotangentSpace E M x) :=
  ContinuousLinearMap.TopologicalAddGroup

instance (x : M) : ContinuousSMul ℝ (biCotangentSpace E M x) :=
  ContinuousLinearMap.ContinuousSMul

end biCotangentSpace

#exit

variables {E M}

/-- A Riemannian metric on `M` is a smooth, symmetric, positive-definite section of the Bundle of
continuous bilinear maps from the tangent Bundle of `M` to `ℝ`. -/
structure RiemannianMetric (g : SmoothSection 𝓘(ℝ, E) (E →L[ℝ] E →L[ℝ] ℝ) (biCotangentSpace E M)) : Prop :=
  (symm : ∀ x : M, ∀ v w : TangentSpace 𝓘(ℝ, E) x, g x v w = g x w v)
  (posdef : ∀ x : M, ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < g x v v)

/-- The sum of two Riemannian metrics is a Riemannian metric. -/
lemma RiemannianMetric.add
  {g₁ g₂ : SmoothSection 𝓘(ℝ, E) (E →L[ℝ] E →L[ℝ] ℝ) (biCotangentSpace E M)}
  (hg₁ : RiemannianMetric g₁) (hg₂ : RiemannianMetric g₂) :
  RiemannianMetric (g₁ + g₂) := {
  symm := λ x v w,
  begin
    simp only [pi.add_apply, cont_mdiff_section.coe_add, ContinuousLinearMap.add_apply,
      hg₁.symm x v w, hg₂.symm x v w],
  end,
  posdef := λ x v hv,
  begin
    have h₁ : 0 < g₁ x v v := hg₁.posdef x v hv,
    have h₂ : 0 < g₂ x v v := hg₂.posdef x v hv,
    simpa only [pi.add_apply, cont_mdiff_section.coe_add, ContinuousLinearMap.add_apply]
      using add_pos h₁ h₂,
  end }

/-- The scaling of a Riemannian metric by a positive real number is a Riemannian metric. -/
lemma RiemannianMetric.smul
  {g : SmoothSection 𝓘(ℝ, E) (E →L[ℝ] E →L[ℝ] ℝ) (biCotangentSpace E M)}
  (hg : RiemannianMetric g) {c : ℝ} (hc : 0 < c) :
  RiemannianMetric (c • g) :=
{ symm := λ x v w,
  begin
    simp only [pi.smul_apply, cont_mdiff_section.coe_smul, ContinuousLinearMap.smul_apply,
      hg.symm x v w],
  end,
  posdef := λ x v hv,
  begin
    have h : 0 < g x v v := hg.posdef x v hv,
    simpa only [pi.smul_apply, cont_mdiff_section.coe_smul, ContinuousLinearMap.smul_apply]
      using smul_pos hc h,
  end }

variables (M E)

/-- Riemannian metrics form a convex cone in the space of sections. -/
noncomputable! def RiemannianMetric_cone :
  convex_cone ℝ (SmoothSection 𝓘(ℝ, E) (E →L[ℝ] E →L[ℝ] ℝ) (biCotangentSpace E M)) :=
{ carrier := {g | RiemannianMetric g},
  smul_mem' := λ c hc g hg, hg.smul hc,
  add_mem' := λ g₁ hg₁ g₂ hg₂, hg₁.add hg₂ }

variables
  (F : Type*) [NormedAddCommGroup F] [inner_product_space ℝ F] [ChartedSpace F M]
  [SmoothManifoldWithCorners 𝓘(ℝ, F) M]
  [finite_dimensional ℝ F] [sigma_compact_space M] [t2_space M]

-- move this
def charts_PartitionOfUnity : SmoothPartitionOfUnity M 𝓘(ℝ, F) M :=
begin
  let U : M → set M := λ x, (chart_at F x).source,
  have hU : ∀ i, is_open (U i) := λ x, (chart_at F x).open_source,
  have hUM : set.univ ⊆ ⋃ i, U i,
  { intros x _,
    rw [set.mem_Union],
    use x,
    exact mem_chart_source _ x, },
  exact (SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, F) is_closed_univ U hU hUM).some,
end

-- move this
lemma charts_PartitionOfUnity_isSubordinate :
  (charts_PartitionOfUnity M F).IsSubordinate (λ x, (chart_at F x).source) :=
begin
  let U : M → set M := λ x, (chart_at F x).source,
  have hU : ∀ i, is_open (U i) := λ x, (chart_at F x).open_source,
  have hUM : set.univ ⊆ ⋃ i, U i,
  { intros x _,
    rw [set.mem_Union],
    use x,
    exact mem_chart_source _ x, },
  exact (SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, F) is_closed_univ U hU hUM).some_spec,
end

def patch (x : M) : TangentSpace 𝓘(ℝ, F) x →L[ℝ] TangentSpace 𝓘(ℝ, F) x →L[ℝ] ℝ :=
begin
  let s : SmoothPartitionOfUnity M 𝓘(ℝ, F) M := charts_PartitionOfUnity M F,
  let g₀ : F →L[ℝ] F →L[ℝ] ℝ := innerSL ℝ,
  let e : Π y : M, TangentSpace 𝓘(ℝ, F) x →L[ℝ] F :=
    λ y, (trivialization_at F (TangentSpace 𝓘(ℝ, F)) y).ContinuousLinearMap_at ℝ x,
  let G : Π y : M, TangentSpace 𝓘(ℝ, F) x →L[ℝ] TangentSpace 𝓘(ℝ, F) x →L[ℝ] ℝ :=
    λ y, (g₀ ∘L (e y)).flip ∘L (e y),
  exact ∑ᶠ y : M, s y x • G y,
end

/- A (σ-compact, Hausdorff, finite-dimensional) manifold admits a Riemannian metric. -/
lemma exists_RiemannianMetric :
  ∃ g : SmoothSection 𝓘(ℝ, F) (F →L[ℝ] F →L[ℝ] ℝ) (biCotangentSpace F M),
  RiemannianMetric g :=
begin
  refine ⟨⟨patch M F, _⟩, _⟩,
  { sorry },
  { sorry },
end
