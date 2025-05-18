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

-- These instances should exist in Mathlib if the topology on the fibers
-- of the trivial bundle is correctly set up.
-- The fiber `Bundle.Trivial M ℝ x` is `ℝ`. `ℝ` has these instances.
-- instance (x : M) : HasContinuousAdd (Bundle.Trivial M ℝ x) := by infer_instance
-- instance (x : M) : TopologicalAddGroup (Bundle.Trivial M ℝ x) := by infer_instance
-- instance (x : M) : HasContinuousSMul ℝ (Bundle.Trivial M ℝ x) := by infer_instance

-- This instance is fundamental for the tangent bundle.
-- Each tangent space `TangentSpace I x` is a normed space, and `ContinuousSMul`
-- is part of the `NormedSpace` structure.
instance (x : M) : ContinuousSMul ℝ (TangentSpace I x) := inferInstance

-- These instances are needed for `ContinuousLinearMap` operations on tangent spaces.
instance (x : M) : SeminormedAddCommGroup (TangentSpace I x) :=
  inferInstanceAs (SeminormedAddCommGroup E)
instance (x : M) : NormedSpace ℝ (TangentSpace I x) := inferInstanceAs (NormedSpace ℝ E)

/-- The cotangent space at a point `x` in a smooth manifold `M`.
This is the space of continuous linear maps from the tangent space at `x` to `ℝ`. -/
def CotangentSpace (x : M) := (TangentSpace I x) →L[ℝ] ℝ

-- Note: In Mathlib, `CotangentBundle` is
-- `Bundle.ContinuousLinearMap (RingHom.id ℝ) (TangentBundle I M) (Bundle.Trivial M ℝ)`
-- and `CotangentSpace I x` would be the fiber of this bundle.
-- The definition of `CotangentSpace` above is directly the fiber type.

namespace CotangentSpace

instance (x : M) : Inhabited (CotangentSpace E I M x) := ContinuousLinearMap.inhabited
instance (x : M) : TopologicalSpace (CotangentSpace E I M x) :=
  ContinuousLinearMap.topologicalSpace
instance (x : M) : AddCommGroup (CotangentSpace E I M x) := ContinuousLinearMap.addCommGroup
instance (x : M) : Module ℝ (CotangentSpace E I M x) := ContinuousLinearMap.module
instance (x : M) : IsTopologicalAddGroup (CotangentSpace E I M x) :=
  ContinuousLinearMap.topologicalAddGroup
instance (x : M) : ContinuousSMul ℝ (CotangentSpace E I M x) := ContinuousLinearMap.continuousSMul

/-- The model fiber for the cotangent bundle, which is `E →L[ℝ] ℝ`.
This is used to type `ContMDiffSection`s of the cotangent bundle. -/
def CotangentBundleModelFiber := E →L[ℝ] ℝ
instance : SeminormedAddCommGroup (CotangentBundleModelFiber E) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
instance : NormedAddCommGroup (CotangentBundleModelFiber E) :=
  NormedAddCommGroup.ofSeparation fun (f : CotangentBundleModelFiber E) =>
  (ContinuousLinearMap.opNorm_zero_iff f).mp
instance : NormedSpace ℝ (CotangentBundleModelFiber E) := ContinuousLinearMap.toNormedSpace

/-- The cotangent bundle, defined as the bundle of continuous linear maps from the tangent bundle
to the trivial real line bundle. This is `Hom(TM, M × ℝ)`.
The fiber at `x` is `CotangentSpace I M x`. -/
abbrev CotangentBundle :=
  Bundle.ContinuousLinearMap (RingHom.id ℝ) (TangentSpace I) (Trivial M ℝ)

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
maps from `TangentSpace I x × TangentSpace I x` to `ℝ`.
This is isomorphic to `TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)`,
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

/-- The model fiber for the bicotangent bundle, `E →L[ℝ] (E →L[ℝ] ℝ)`. -/
def BicotangentBundleModelFiber := E →L[ℝ] (E →L[ℝ] ℝ)
instance : SeminormedAddCommGroup (BicotangentBundleModelFiber E) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
instance : NormedAddCommGroup (BicotangentBundleModelFiber E) :=
  NormedAddCommGroup.ofSeparation fun (f : BicotangentBundleModelFiber E) =>
  (ContinuousLinearMap.opNorm_zero_iff f).mp
instance : NormedSpace ℝ (BicotangentBundleModelFiber E) := ContinuousLinearMap.toNormedSpace

/-- The bicotangent bundle, defined as the bundle of continuous linear maps from the tangent bundle
to the cotangent bundle. This is `Hom(TM, T*M)`.
The fiber at `x` is `BicotangentSpace E I M x`. -/
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

/-- A pseudo-Riemannian metric on `M` is a smooth, symmetric, non-degenerate section of the
bundle of continuous bilinear maps from the tangent bundle of `M` to `ℝ`.
The bundle is `BicotangentBundle E I M`. A section `g` has `g x : BicotangentSpace E I M x`.
So `g x v w` is `((g x) v) w`. -/
structure PseudoRiemannianMetric
    (g : ContMDiffSection I (BicotangentSpace.BicotangentBundleModelFiber E) ∞
      (BicotangentSpace.BicotangentBundle E I M)) : Prop where
  (symm : ∀ x : M, ∀ v w : TangentSpace I x, g x v w = g x w v)
  (nondegenerate : ∀ x : M, ∀ v : TangentSpace I x, (∀ w : TangentSpace I x, g x v w = 0) → v = 0)

/-- A Riemannian metric on `M` is a pseudo-Riemannian metric that is also positive-definite. -/
structure RiemannianMetric
    (g : ContMDiffSection I (BicotangentSpace.BicotangentBundleModelFiber E) ∞
      (BicotangentSpace.BicotangentBundle E I M)) : Prop where
  (toPseudoRiemannianMetric : PseudoRiemannianMetric g)
  (posdef : ∀ x : M, ∀ v : TangentSpace I x, v ≠ 0 → 0 < g x v v)

lemma RiemannianMetric.symm
    {g : ContMDiffSection I (BicotangentSpace.BicotangentBundleModelFiber E) ∞
      (BicotangentSpace.BicotangentBundle E I M)}
    (hg : RiemannianMetric g) (x : M) (v w : TangentSpace I x) : g x v w = g x w v :=
  hg.toPseudoRiemannianMetric.symm x v w

lemma RiemannianMetric.nondegenerate
    {g : ContMDiffSection I (BicotangentSpace.BicotangentBundleModelFiber E) ∞
      (BicotangentSpace.BicotangentBundle E I M)}
    (hg : RiemannianMetric g) (x : M) (v : TangentSpace I x)
    (h_all_zero : ∀ w : TangentSpace I x, g x v w = 0) : v = 0 :=
  hg.toPseudoRiemannianMetric.nondegenerate x v h_all_zero

/-- A symmetric, positive-definite section `g` automatically satisfies the non-degeneracy condition
and is therefore a pseudo-Riemannian metric. This lemma shows that for a symmetric bilinear form,
positive-definiteness implies non-degeneracy. -/
lemma PseudoRiemannianMetric.of_symm_posdef
    {g : ContMDiffSection I (BicotangentSpace.BicotangentBundleModelFiber E) ∞
      (BicotangentSpace.BicotangentBundle E I M)}
    (hsymm : ∀ x : M, ∀ v w : TangentSpace I x, g x v w = g x w v)
    (hposdef : ∀ x : M, ∀ v : TangentSpace I x, v ≠ 0 → 0 < g x v v) :
    PseudoRiemannianMetric g := {
  symm := hsymm,
  nondegenerate := by
    intro x v h_all_zero_w
    specialize h_all_zero_w v
    by_cases hv_zero : v = 0
    · exact hv_zero
    · exact (lt_irrefl 0 (h_all_zero_w ▸ (hposdef x v hv_zero))).elim
    }

/-- A symmetric, positive-definite section `g` is a Riemannian metric. -/
lemma RiemannianMetric.of_symm_posdef
    {g : ContMDiffSection I (BicotangentSpace.BicotangentBundleModelFiber E) ∞
      (BicotangentSpace.BicotangentBundle E I M)}
    (hsymm : ∀ x : M, ∀ v w : TangentSpace I x, g x v w = g x w v)
    (hposdef : ∀ x : M, ∀ v : TangentSpace I x, v ≠ 0 → 0 < g x v v) :
    RiemannianMetric g := {
  toPseudoRiemannianMetric := PseudoRiemannianMetric.of_symm_posdef hsymm hposdef,
  posdef := hposdef
    }

/-- The scaling of a pseudo-Riemannian metrics by a nonzero real number is a pseudo-Riemannian
metric. -/
lemma PseudoRiemannianMetric.smul
    {g : ContMDiffSection I (BicotangentSpace.BicotangentBundleModelFiber E) ∞
      (BicotangentSpace.BicotangentBundle E I M)}
    (hg : PseudoRiemannianMetric g) {c : ℝ} (hc : c ≠ 0) : PseudoRiemannianMetric (c • g) :=
  let g_smul := c • g
  have symm_smul : ∀ x v w, g_smul x v w = g_smul x w v := by
    intro x v w
    simp only [ContMDiffSection.coe_smul, Pi.smul_apply, ContinuousLinearMap.smul_apply,
      hg.symm x v w, smul_eq_mul, g_smul]
  have nondegenerate_smul : ∀ x v, (∀ w : TangentSpace I x, g_smul x v w = 0) → v = 0 := by
      intro x v h_all_zero_w
      have h_g_zero : ∀ w, g x v w = 0 := by
        intro w
        have h_smul_zero : g_smul x v w = 0 := h_all_zero_w w
        simp only [g_smul] at h_smul_zero
        exact (mul_eq_zero.mp h_smul_zero).resolve_left hc
      exact hg.nondegenerate x v h_g_zero
  { symm := symm_smul,
    nondegenerate := nondegenerate_smul }

/-- The sum of two Riemannian metrics is a Riemannian metric. -/
lemma RiemannianMetric.add
    {g₁ g₂ : ContMDiffSection I (BicotangentSpace.BicotangentBundleModelFiber E) ∞
      (BicotangentSpace.BicotangentBundle E I M)}
    (hg₁ : RiemannianMetric g₁) (hg₂ : RiemannianMetric g₂) : RiemannianMetric (g₁ + g₂) := by
  let g_sum := g₁ + g₂
  have symm_sum : ∀ x v w, g_sum x v w = g_sum x w v := by
    intro x v w
    simp only [ContMDiffSection.coe_add, Pi.add_apply, ContinuousLinearMap.add_apply,
      hg₁.toPseudoRiemannianMetric.symm x v w, hg₂.toPseudoRiemannianMetric.symm x v w, g_sum]
  have posdef_sum : ∀ x v, v ≠ 0 → 0 < g_sum x v v := by
    intro x v hv_ne_zero
    simp only [ContMDiffSection.coe_add, Pi.add_apply, ContinuousLinearMap.add_apply]
    exact add_pos (hg₁.posdef x v hv_ne_zero) (hg₂.posdef x v hv_ne_zero)
  exact RiemannianMetric.of_symm_posdef symm_sum posdef_sum

/-- The scaling of a Riemannian metric by a positive real number is a Riemannian metric. -/
lemma RiemannianMetric.smul
    {g : ContMDiffSection I (BicotangentSpace.BicotangentBundleModelFiber E) ∞
      (BicotangentSpace.BicotangentBundle E I M)}
    (hg : RiemannianMetric g) {c : ℝ} (hc : 0 < c) : RiemannianMetric (c • g) := by
  let g_smul := c • g
  have symm_smul : ∀ x v w, g_smul x v w = g_smul x w v :=
    (PseudoRiemannianMetric.smul hg.toPseudoRiemannianMetric (ne_of_gt hc)).symm
  have posdef_smul : ∀ x v, v ≠ 0 → 0 < g_smul x v v := by
    intro x v hv_ne_zero
    simp only [ContMDiffSection.coe_smul, Pi.smul_apply, ContinuousLinearMap.smul_apply]
    exact mul_pos hc (hg.posdef x v hv_ne_zero)
  exact RiemannianMetric.of_symm_posdef symm_smul posdef_smul

variable (E M I)

/-- Riemannian metrics form a convex cone in the space of sections. -/
noncomputable def riemannianMetricCone :
    ConvexCone ℝ (ContMDiffSection I (BicotangentSpace.BicotangentBundleModelFiber E) ∞
      (BicotangentSpace.BicotangentBundle E I M)) :=
  { carrier := {g | RiemannianMetric g},
    smul_mem' := fun _ hc _ hg => hg.smul hc,
    add_mem' := fun _ hg₁ _ hg₂ => hg₁.add hg₂ }

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]

/-- A smooth partition of unity on `M` subordinate to the domains of the charts.
This partition is indexed by `M` itself (each point `x : M` corresponds to the chart `chartAt H x`).
The manifold `M` is charted on `H`, and its model with corners `I` is over `E`. -/
def chartsPartitionOfUnity : SmoothPartitionOfUnity M I M :=
  let U : M → Set M := fun x => (chartAt H x).source
  have hU_isOpen : ∀ i, IsOpen (U i) := fun x => (chartAt H x).open_source
  have hU_covers : univ ⊆ ⋃ i, U i := by
    intro x _
    simp only [mem_iUnion, mem_univ]
    exact ⟨x, mem_chart_source H x⟩
  (SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ U hU_isOpen hU_covers).choose

/-- `chartsPartitionOfUnity` is subordinate to the collection of chart domains. -/
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

/-- Construct a local positive-definite symmetric bilinear form (a `BicotangentSpace` element)
at point `x` on a manifold `M`.
This is done by taking a convex combination of inner products pulled back from the model space `F`
using chart derivatives. The coefficients of the combination are given by a partition of unity.
This "patch" is a key component in constructing a global Riemannian metric.

The manifold `M` is charted on `H`. The model with corners `I` is over `F`.
The tangent space `TangentSpace I x` is identified with `F`. -/
def patch (x : M) : BicotangentSpace F I M x :=
  let s : SmoothPartitionOfUnity M I M := chartsPartitionOfUnity F I M
  -- `g₀` is the model inner product on `F`, as a continuous bilinear map.
  let g₀ : F →L[ℝ] (F →L[ℝ] ℝ) := innerSL ℝ
  -- For each point `y_center` in `M` (which indexes a chart in `chartsPartitionOfUnity`),
  -- `e y_center` is the derivative of the extended chart map `extChartAt I y_center` at `x`.
  -- It maps vectors in `TangentSpace I x` (i.e., `F`) to the model vector space `F`.
  -- `extChartAt I y_center : M → F`.
  -- `mfderiv I (modelWithCornersSelf ℝ F) (extChartAt I y_center) x : TangentSpace I x →L[ℝ] F`.
  let e (y_center : M) : TangentSpace I x →L[ℝ] F :=
    mfderiv I (modelWithCornersSelf ℝ F) (extChartAt I y_center) x
  -- `G y_center` is a bilinear form on `TangentSpace I x`
  -- defined by pulling back `g₀` by `e y_center`.
  -- `(v, w) ↦ g₀ ((e y_center) v) ((e y_center) w)`.
  let G (y_center : M) : BicotangentSpace F I M x := (g₀.comp (e y_center)).flip.comp (e y_center)
  -- This is a finite sum because `s` is a partition of unity. For a given `x`,
  -- `(s y_idx x)` is non-zero for only finitely many `y_idx` in the support of the partition.
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
    -- `(G y_center v w) = g₀ ((e y_center) v) ((e y_center) w)`
    -- `(G y_center w v) = g₀ ((e y_center) w) ((e y_center) v)`
    -- `g₀` is symmetric, so these are equal. The sum inherits symmetry.
    sorry
  · -- Prove positive definiteness: `v ≠ 0 → 0 < g_val x v v`
    -- `g_val x v v = ∑ᶠ y_idx, (s y_idx x) • (G y_idx v v)`
    -- where `G y_idx v v = g₀ ((e y_idx) v) ((e y_idx) v) = ∥(e y_idx) v∥² ≥ 0`.
    -- Since `s y_idx x ≥ 0` and `∑ y_idx, s y_idx x = 1` (for `x` in the manifold,
    -- due to properties of partition of unity `s`).
    -- If `v ≠ 0`, then for some chart (e.g., indexed by `x_chart_idx`) covering `x`,
    -- `e x_chart_idx` (which is `mfderiv ... (extChartAt I x_chart_idx) x`)
    -- is a linear isomorphism if `x` is in the interior of the chart, or injective.
    -- Thus, `(e x_chart_idx) v ≠ 0`, which implies `G x_chart_idx v v > 0`.
    -- If `s x_chart_idx x > 0` (i.e., `x` is in the support
    -- of the partition function `s x_chart_idx`), this term in the sum is positive.
    -- Need to argue that at least one such term is positive and the sum remains positive.
    -- Since `∑ (s y_idx x) = 1` and `s y_idx x ≥ 0`, at least one `s y_idx x` must be positive.
    -- For that `y_idx`, if `(e y_idx v) ≠ 0`, then `G y_idx v v > 0`.
    -- We need to ensure that for `v ≠ 0`, there's some `y_idx`
    -- such that `s y_idx x > 0` AND `(e y_idx v) ≠ 0`.
    -- This typically relies on `v` being expressible in local chart coordinates and the derivative
    -- of the chart map being an isomorphism.
    sorry
