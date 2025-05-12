/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth (ported by Michael Lee)
-/
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Riemannian metrics -/

universe uι uE uH uM uF

open Bundle Function Filter Module Set
open scoped Topology Manifold ContDiff

noncomputable section

variable (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type uM) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

-- These instances should exist in Mathlib4 if the topology on the fibers
-- of the trivial bundle is correctly set up.
-- The fiber (Bundle.Trivial M ℝ x) is ℝ. ℝ has these instances.
-- instance (x : M) : HasContinuousAdd (Bundle.Trivial M ℝ x) := by infer_instance
-- instance (x : M) : TopologicalAddGroup (Bundle.Trivial M ℝ x) := by infer_instance
-- instance (x : M) : HasContinuousSMul ℝ (Bundle.Trivial M ℝ x) := by infer_instance

-- This instance is fundamental for the tangent bundle.
-- Each tangent space `TangentSpace I x` is a normed space, and `ContinuousSMul`
-- is part of the `NormedSpace` structure.
instance (x : M) : ContinuousSMul ℝ (TangentSpace I x) := inferInstance

-- These instances are needed for ContinuousLinearMap operations on tangent spaces
instance (x : M) : SeminormedAddCommGroup (TangentSpace I x) :=
  inferInstanceAs (SeminormedAddCommGroup E)
instance (x : M) : NormedSpace ℝ (TangentSpace I x) := inferInstanceAs (NormedSpace ℝ E)

/-- The cotangent space at a point `x` in a smooth manifold `M`.
This is the space of continuous linear maps from the tangent space at `x` to `ℝ`. -/
def CotangentSpace (x : M) := (TangentSpace I x) →L[ℝ] ℝ

-- Note: In Mathlib4, CotangentBundle is
-- `Bundle.ContinuousLinearMap (RingHom.id ℝ) (TangentBundle I M) (Bundle.Trivial M ℝ)`
-- and `CotangentSpace I x` would be the fiber of this bundle.
-- The definition above is directly the fiber type.

namespace CotangentSpace

instance (x : M) : Inhabited (CotangentSpace E I M x) := ContinuousLinearMap.inhabited
instance (x : M) : TopologicalSpace (CotangentSpace E I M x) :=
  ContinuousLinearMap.topologicalSpace
instance (x : M) : AddCommGroup (CotangentSpace E I M x) := ContinuousLinearMap.addCommGroup
instance (x : M) : Module ℝ (CotangentSpace E I M x) := ContinuousLinearMap.module
instance (x : M) : IsTopologicalAddGroup (CotangentSpace E I M x) :=
  ContinuousLinearMap.topologicalAddGroup
instance (x : M) : ContinuousSMul ℝ (CotangentSpace E I M x) := ContinuousLinearMap.continuousSMul

-- We need to define the CotangentBundle as a type to have sections of it.
-- Let F_cotangent be the model fiber E →L[ℝ] ℝ
def CotangentBundleModelFiber := E →L[ℝ] ℝ
instance : SeminormedAddCommGroup (CotangentBundleModelFiber E) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
instance : NormedAddCommGroup (CotangentBundleModelFiber E) :=
  NormedAddCommGroup.ofSeparation fun (f : CotangentBundleModelFiber E) =>
  (ContinuousLinearMap.opNorm_zero_iff f).mp
instance : NormedSpace ℝ (CotangentBundleModelFiber E) := ContinuousLinearMap.toNormedSpace

-- The cotangent bundle can be defined as follows:
abbrev CotangentBundle :=
  Bundle.ContinuousLinearMap (RingHom.id ℝ) (TangentSpace I) (Trivial M ℝ)

-- Check: Fiber of CotangentBundle I M at x is (TangentSpace I x) →L[ℝ] (Bundle.Trivial M ℝ x)
-- Since (Bundle.Trivial M ℝ x) is ℝ, this matches `CotangentSpace I M x`.

instance : TopologicalSpace (TotalSpace (CotangentBundleModelFiber E) (CotangentBundle E I M)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E (TangentSpace I) ℝ (Trivial M ℝ)
instance : FiberBundle (CotangentBundleModelFiber E) (CotangentBundle E I M) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ) E (TangentSpace I) ℝ (Trivial M ℝ)
instance : VectorBundle ℝ (CotangentBundleModelFiber E) (CotangentBundle E I M) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ) E (TangentSpace I) ℝ (Trivial M ℝ)
instance : ContMDiffVectorBundle ∞ (CotangentBundleModelFiber E) (CotangentBundle E I M) I :=
  ContMDiffVectorBundle.continuousLinearMap

instance (x : M) : LinearMapClass (CotangentBundle E I M x) ℝ (TangentSpace I x) ℝ := inferInstance
instance (x : M) : IsTopologicalAddGroup (CotangentBundle E I M x) := inferInstance
instance (x : M) : ContinuousSMul ℝ (CotangentBundle E I M x) := inferInstance

end CotangentSpace

/-- The "bicotangent space" at a point `x` in a smooth manifold `M`; that is, the space of bilinear
maps from `TangentSpace I x` to `ℝ`.
This is `TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)`,
i.e., `TangentSpace I x →L[ℝ] CotangentSpace I x`. -/
def BicotangentSpace (x : M) := (TangentSpace I x) →L[ℝ] (CotangentSpace E I M x)

namespace BicotangentSpace

instance (x : M) : Inhabited (BicotangentSpace E I M x) := ContinuousLinearMap.inhabited
instance (x : M) : TopologicalSpace (BicotangentSpace E I M x)
  := ContinuousLinearMap.topologicalSpace
instance (x : M) : AddCommGroup (BicotangentSpace E I M x) := ContinuousLinearMap.addCommGroup
instance (x : M) : Module ℝ (BicotangentSpace E I M x) := ContinuousLinearMap.module
instance (x : M) : IsTopologicalAddGroup (BicotangentSpace E I M x) :=
  ContinuousLinearMap.topologicalAddGroup
instance (x : M) : ContinuousSMul ℝ (BicotangentSpace E I M x) :=
  ContinuousLinearMap.continuousSMul

def BicotangentBundleModelFiber := E →L[ℝ] (E →L[ℝ] ℝ)
instance : SeminormedAddCommGroup (BicotangentBundleModelFiber E) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
instance : NormedAddCommGroup (BicotangentBundleModelFiber E) :=
  NormedAddCommGroup.ofSeparation fun (f : BicotangentBundleModelFiber E) =>
  (ContinuousLinearMap.opNorm_zero_iff f).mp
instance : NormedSpace ℝ (BicotangentBundleModelFiber E) := ContinuousLinearMap.toNormedSpace

-- The bicotangent bundle is Hom(TM, T*M)
abbrev BicotangentBundle :=
  Bundle.ContinuousLinearMap (RingHom.id ℝ) (TangentSpace I) (CotangentSpace.CotangentBundle E I M)

instance : TopologicalSpace
    (TotalSpace (BicotangentBundleModelFiber E) (BicotangentBundle E I M)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) E (TangentSpace I)
    (CotangentSpace.CotangentBundleModelFiber E) (CotangentSpace.CotangentBundle E I M)
instance : FiberBundle (BicotangentBundleModelFiber E) (BicotangentBundle E I M) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ) E (TangentSpace I)
    (CotangentSpace.CotangentBundleModelFiber E) (CotangentSpace.CotangentBundle E I M)
instance : VectorBundle ℝ (BicotangentBundleModelFiber E) (BicotangentBundle E I M) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ) E (TangentSpace I)
    (CotangentSpace.CotangentBundleModelFiber E) (CotangentSpace.CotangentBundle E I M)
instance : ContMDiffVectorBundle ∞ (BicotangentBundleModelFiber E) (BicotangentBundle E I M) I :=
  ContMDiffVectorBundle.continuousLinearMap

instance (x : M) : LinearMapClass (BicotangentBundle E I M x) ℝ
  (TangentSpace I x) (CotangentSpace E I M x) := inferInstance
instance (x : M) : IsTopologicalAddGroup (BicotangentBundle E I M x) := inferInstance
instance (x : M) : ContinuousSMul ℝ (BicotangentBundle E I M x) := inferInstance

end BicotangentSpace

variable {E M I}

/-- A Riemannian metric on `M` is a smooth, symmetric, positive-definite section of the bundle of
continuous bilinear maps from the tangent bundle of `M` to `ℝ`.
The bundle is `BicotangentBundle E M I`. A section `g` has `g x : BicotangentSpace E I M x`.
So `g x v w` is `(g x v) w`. -/
structure RiemannianMetric
    (g : ContMDiffSection I (BicotangentSpace.BicotangentBundleModelFiber E) ∞
      (BicotangentSpace.BicotangentBundle E I M)) : Prop where
  (symm : ∀ x : M, ∀ v w : TangentSpace I x, g x v w = g x w v)
  (posdef : ∀ x : M, ∀ v : TangentSpace I x, v ≠ 0 → 0 < g x v v)

/-- The sum of two Riemannian metrics is a Riemannian metric. -/
lemma RiemannianMetric.add
    {g₁ g₂ : ContMDiffSection I (BicotangentSpace.BicotangentBundleModelFiber E) ∞
      (BicotangentSpace.BicotangentBundle E I M)}
    (hg₁ : RiemannianMetric g₁) (hg₂ : RiemannianMetric g₂) :
    RiemannianMetric (g₁ + g₂) :=
  { symm := fun x v w => by
      simp only [ContMDiffSection.coe_add, Pi.add_apply, ContinuousLinearMap.add_apply,
        hg₁.symm x v w, hg₂.symm x v w],
    posdef := fun x v hv => by
      have h₁ : 0 < g₁ x v v := hg₁.posdef x v hv
      have h₂ : 0 < g₂ x v v := hg₂.posdef x v hv
      simp only [ContMDiffSection.coe_add, ContinuousLinearMap.add_apply]
      exact add_pos h₁ h₂ }

/-- The scaling of a Riemannian metric by a positive real number is a Riemannian metric. -/
lemma RiemannianMetric.smul
    {g : ContMDiffSection I (BicotangentSpace.BicotangentBundleModelFiber E) ∞
      (BicotangentSpace.BicotangentBundle E I M)}
    (hg : RiemannianMetric g) {c : ℝ} (hc : 0 < c) :
    RiemannianMetric (c • g) :=
  { symm := fun x v w => by
      simp only [ContMDiffSection.coe_smul, Pi.smul_apply, ContinuousLinearMap.smul_apply,
        hg.symm x v w, smul_eq_mul],
    posdef := fun x v hv => by
      have h : 0 < g x v v := hg.posdef x v hv
      simp only [ContMDiffSection.coe_smul, ContinuousLinearMap.smul_apply]
      exact mul_pos hc h }

variable (E M I)

/-- Riemannian metrics form a convex cone in the space of sections. -/
noncomputable def riemannianMetricCone :
    ConvexCone ℝ (ContMDiffSection I (BicotangentSpace.BicotangentBundleModelFiber E) ∞
      (BicotangentSpace.BicotangentBundle E I M)) :=
  { carrier := {g | RiemannianMetric g},
    smul_mem' := fun _ hc _ hg => hg.smul hc,
    add_mem' := fun _ hg₁ _ hg₂ => hg₁.add hg₂ }

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]

-- chartsPartitionOfUnity needs M (manifold), IF (its model with corners),
-- and F (the model space for the charts).
def chartsPartitionOfUnity : SmoothPartitionOfUnity M I M :=
  let U : M → Set M := fun x => (chartAt H x).source
  have hU_isOpen : ∀ i, IsOpen (U i) := fun x => (chartAt H x).open_source
  have hU_covers : univ ⊆ ⋃ i, U i := by
    intro x _
    simp only [mem_iUnion, mem_univ]
    exact ⟨x, mem_chart_source H x⟩
  (SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ U hU_isOpen hU_covers).choose

lemma chartsPartitionOfUnity_isSubordinate :
    (chartsPartitionOfUnity E I M).IsSubordinate (fun x => (chartAt H x).source) :=
  let U : M → Set M := fun x => (chartAt H x).source
  have hU_isOpen : ∀ i, IsOpen (U i) := fun x => (chartAt H x).open_source
  have hU_covers : univ ⊆ ⋃ i, U i := by
    intro x _
    simp only [mem_iUnion, mem_univ]
    exact ⟨x, mem_chart_source H x⟩
  (SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ U hU_isOpen hU_covers).choose_spec

variable (F : Type uF) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (I : ModelWithCorners ℝ F H) [IsManifold I ∞ M]

-- The patch function constructs a BicotangentSpace F I M x element (a bilinear form on
-- TangentSpace I x). It depends on the manifold M, its model H, and its smooth structure I.
def patch (x : M) : BicotangentSpace F I M x :=
  let s : SmoothPartitionOfUnity M I M := chartsPartitionOfUnity F I M
  -- g₀ is the model inner product on F, as a continuous bilinear map.
  -- set_option diagnostics true in
  let g₀ : F →L[ℝ] (F →L[ℝ] ℝ) := @innerSL ℝ F _ _ _
  -- For each point y_center in M (potential center of a chart),
  -- `e y_center` maps vectors in `TangentSpace I x` to the model vector space `F`.
  -- This is achieved by taking the derivative of the extended chart map I ∘ φ_{y_center} at x.
  -- `extChartAt I y_center` maps `M → F`.
  -- `mfderiv I (𝓘(ℝ, E)) (extChartAt I y_center) x` maps
  -- `TangentSpace I x` (which is F) to `TangentSpace (𝓘(ℝ, F)) ((extChartAt I y_center) x)`
  -- (which is F).
  let e (y_center : M) : TangentSpace I x →L[ℝ] F :=
    mfderiv I (modelWithCornersSelf ℝ F) (extChartAt I y_center) x
  -- G y_center is a bilinear form on TangentSpace I x, defined by pulling back g₀ by e y_center.
  -- (v, w) ↦ g₀ ((e y_center) v) ((e y_center) w)
  let G (y_center : M) : BicotangentSpace F I M x :=
    ContinuousLinearMap.comp (ContinuousLinearMap.flip (ContinuousLinearMap.comp g₀ (e y_center)))
      (e y_center)
  -- This is a finite sum because `s` is a partition of unity, so for a given `x`,
  -- `(s y_idx x)` is non-zero for only finitely many `y_idx`.
  ∑ᶠ (y_idx : M), ((s y_idx) x) • (G y_idx)

/- A (sigma-compact, Hausdorff, finite-dimensional) manifold admits a Riemannian metric. -/
lemma exists_riemannian_metric :
    ∃ g : ContMDiffSection I (BicotangentSpace.BicotangentBundleModelFiber F) ∞
      (BicotangentSpace.BicotangentBundle F I M), RiemannianMetric g := by
  -- Define the section `g_val` by `g_val x = patch x`.
  let g_val (x : M) : BicotangentSpace F I M x := patch M F I x
  -- We need to show this section is smooth. This is the hard part.
  have hs_g_val : ContMDiffSection I (BicotangentSpace.BicotangentBundleModelFiber F) ∞
      (BicotangentSpace.BicotangentBundle F I M) :=
    ⟨g_val, by sorry⟩ -- Proof of smoothness for `x ↦ patch x`
  exists hs_g_val
  constructor
  · -- Prove symmetry: `g_val x v w = g_val x w v`
    -- This follows from the symmetry of `g₀` (innerSL) and the construction of `G`.
    -- `(G y) v w = g₀ (e y v) (e y w)`
    -- `(G y) w v = g₀ (e y w) (e y v)`
    -- `g₀` is symmetric, so these are equal. The sum inherits symmetry.
    sorry
  · -- Prove positive definiteness: `v ≠ 0 → 0 < g_val x v v`
    -- `g_val x v v = ∑ᶠ y ∈ s.support, (s.funMap y x) • (G y v v)`
    -- where `G y v v = g₀ (e y v) (e y v) = ∥e y v∥² ≥ 0`.
    -- Since `s.funMap y x ≥ 0` and `∑ y, s.funMap y x = 1`
    -- (for `x` in the manifold, assuming `s.locallyFinite` and `s.sum_eq_one`).
    -- If `v ≠ 0`, then for some chart `chartAt F x` centered at `x`, `e x`
    -- (which is `mfderiv ... (chartAt F x) x`)
    -- is a linear isomorphism, so `e x v ≠ 0`. Thus `G x v v > 0`.
    -- If `s.funMap x x > 0` (i.e., `x` is in the support of `s x`), this term is positive.
    -- Need to argue that the sum is positive.
    sorry
