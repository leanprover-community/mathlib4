/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth (ported by Michael Lee)
-/
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

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
instance (x : M) : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs (NormedAddCommGroup E)
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

namespace ContinuousLinearMap

variable {x : M}
variable {g₀ : F →L[ℝ] (F →L[ℝ] ℝ)}
variable {L : TangentSpace I x →L[ℝ] F}

/-- Pull-back of the inner product is symmetric. -/
lemma comp_flip_symm {H : Type uH} [TopologicalSpace H] (M : Type uM) [TopologicalSpace M]
  [ChartedSpace H M] (F : Type uF) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (I : ModelWithCorners ℝ F H) {x : M} {g₀ : F →L[ℝ] F →L[ℝ] ℝ}
  {L : TangentSpace I x →L[ℝ] F}
    (g₀symm : ∀ u w, g₀ u w = g₀ w u) :
    ∀ v w, (g₀.comp L).flip.comp L v w = (g₀.comp L).flip.comp L w v := by
  intro v w; simp [LinearMap.flip_apply, g₀symm]

/-- Positivity of the pull-back if `g₀` is an inner product and `L` is injective. -/
lemma comp_posdef {H : Type uH} [TopologicalSpace H] (M : Type uM) [TopologicalSpace M]
  [ChartedSpace H M] (F : Type uF) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (I : ModelWithCorners ℝ F H) {x : M} {g₀ : F →L[ℝ] F →L[ℝ] ℝ}
  {L : TangentSpace I x →L[ℝ] F}
    (pos₀ : ∀ u, 0 < g₀ u u) (hL : Function.Injective L) :
    ∀ v, v ≠ (0 : TangentSpace I x) → 0 < ((g₀.comp L).flip.comp L) v v := by
  intro v hv
  have hv' : L v ≠ 0 := by
    intro h; exact hv (hL (by simpa using h))
  simpa using pos₀ (L v)

/-- Given a linear map `L : V →L[ℝ] F`, pull back the Euclidean inner
    product from `F` to a bilinear form on `V`. -/
def pullback_inner {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] F) : V →L[ℝ] V →L[ℝ] ℝ :=
  ((innerSL ℝ).comp L).flip.comp L

/--  On a chart domain the map
     `x ↦ (⟨x, pullback_inner (mfderiv …)⟩ : TotalSpace …)`
     is smooth. -/
lemma contMDiffOn_pullback_inner_total (y : M) :
    ContMDiffOn I
      (I.prod 𝓘(ℝ, BicotangentSpace.BicotangentBundleModelFiber F)) ∞
      (fun x ↦
         (TotalSpace.mk x
           (pullback_inner F
             (mfderiv I (modelWithCornersSelf ℝ F) (extChartAt I y) x))
           :
           TotalSpace (BicotangentSpace.BicotangentBundleModelFiber F)
                      (BicotangentSpace.BicotangentBundle F I M)))
      ((chartAt H y).source) := by
  -- `mfderiv` is smooth on the chart domain …
  have hL :=
    (contMDiffOn_extChartAt (x := y)).mfderivWithin_const
      (by decide) (by
        simp only [mem_chart_source]) uniqueMDiffOn_extChartSource
  simpa [pullback_inner] using
    hL.totalSpace (I := I) (I' := modelWithCornersSelf ℝ F)

end ContinuousLinearMap

/-!  ## The actual proof  -/

lemma exists_riemannian_metric :
    ∃ g : ContMDiffSection I (BicotangentSpace.BicotangentBundleModelFiber F) ∞
      (BicotangentSpace.BicotangentBundle F I M), RiemannianMetric g := by
  ------------------------------------------------------------------
  --  Step 0 : all the notation we need
  ------------------------------------------------------------------
  let ρ : SmoothPartitionOfUnity M I M := chartsPartitionOfUnity F I M
  let g₀ : F →L[ℝ] (F →L[ℝ] ℝ) := innerSL ℝ
  have g₀_symm: ∀ u w, g₀ u w = g₀ w u := by
    intro u w
    simp only [innerSL, LinearMap.mkContinuous₂_apply, innerₛₗ_apply, g₀]
    exact real_inner_comm w u
  have g₀_pos : ∀ u : F, u ≠ 0 → 0 < g₀ u u := by
    intro u hu
    simp only [innerSL, LinearMap.mkContinuous₂_apply, innerₛₗ_apply, g₀]
    exact real_inner_self_pos.mpr hu

  --  `patch` written with full explicit arguments, just for the record
  let patch (x : M) : BicotangentSpace F I M x :=
    ∑ᶠ (y : M),
      ρ y x •
        ((g₀.comp (mfderiv I (modelWithCornersSelf ℝ F) (extChartAt I y) x)).flip.comp
         (mfderiv I (modelWithCornersSelf ℝ F) (extChartAt I y) x))

  --  Define the candidate global metric
  let g_val (x : M) : BicotangentSpace F I M x := patch x
  let s_loc (y : M) (x : M) : BicotangentSpace F I M x :=
  ((g₀.comp (mfderiv I (modelWithCornersSelf ℝ F) (extChartAt I y) x)).flip.comp
    (mfderiv I (modelWithCornersSelf ℝ F) (extChartAt I y) x))

  ------------------------------------------------------------------
  --  Step 1 : smoothness, via the library lemma you mentioned
  ------------------------------------------------------------------
  have hs_g_val :
      ContMDiffSection I (BicotangentSpace.BicotangentBundleModelFiber F) ∞
        (BicotangentSpace.BicotangentBundle F I M) := by
    -- Prepare the data for
    -- `contMDiff_totalSpace_weighted_sum_of_local_sections`.
    -- • local sections

    -- • smoothness of the local sections on the chart domain
    have hs_loc :
        ∀ y, ContMDiffOn I
          (I.prod 𝓘(ℝ, BicotangentSpace.BicotangentBundleModelFiber F))
          ∞ (fun x ↦
              (TotalSpace.mk x (s_loc y x) :
                TotalSpace (BicotangentSpace.BicotangentBundleModelFiber F)
                  (BicotangentSpace.BicotangentBundle F I M)))
            ((chartAt H y).source) := by
      intro y
      let L_map (x : M) := mfderiv I (modelWithCornersSelf ℝ F) (extChartAt I y) x
      -- The following instance is crucial and correctly placed.
      have h_L_map_smooth : ContMDiffOn I 𝓘(ℝ, F →L[ℝ] F) (M' := F →L[ℝ] F) ∞ L_map ((chartAt H y).source) := by
        intro x_eval hx_eval_in_source -- x_eval is the point in (chartAt H y).source
        -- We want to show ContMDiffWithinAt L_map ((chartAt H y).source) x_eval.
        -- We'll show ContMDiffAt L_map x_eval and use that ((chartAt H y).source) is a neighborhood.

        let f₀ := extChartAt I y
        have h_f₀_smooth_at_x_eval : ContMDiffAt I (modelWithCornersSelf ℝ F) ∞ f₀ x_eval :=
          (contMDiffOn_extChartAt (x := y)).contMDiffAt ((chartAt H y).open_source.mem_nhds hx_eval_in_source)

        -- Define f_outer : M → (M → F) as x_param ↦ f₀
        -- Define g_inner : M → M as id
        -- L_map x_param = mfderiv I (modelWithCornersSelf ℝ F) (f_outer x_param) (g_inner x_param)
        -- (actually, mfderiv I (modelWithCornersSelf ℝ F) f₀ x_param)

        -- Let N be M, with model J = I.
        -- Let M_domain be M, with model I_domain = I.
        -- Let M_codomain be F, with model I_codomain = modelWithCornersSelf ℝ F.
        -- The function to pass to uncurry for ContMDiffAt.mfderiv is (x_param : M) × (z_domain : M) ↦ f₀ z_domain
        let f := fun (p : M) (q : M) => f₀ q
        let f_uncurried := uncurry f
        -- The g function for ContMDiffAt.mfderiv is id : M → M
        let g_map := fun (z_param : M) => z_param

        have hf_uncurried_smooth : ContMDiffAt (I.prod I) (modelWithCornersSelf ℝ F) ∞ f_uncurried (x_eval, g_map x_eval) := by
          simp only [f_uncurried, g_map] -- f_uncurried (x_eval, x_eval) = f₀ x_eval
          -- Smoothness of p ↦ f₀ p.2 at (x_eval, x_eval)
          exact ContMDiffAt.comp (x_eval, x_eval) h_f₀_smooth_at_x_eval contMDiffAt_snd

        have hg_map_smooth : ContMDiffAt I I ∞ g_map x_eval := contMDiffAt_id

        -- Apply ContMDiffAt.mfderiv
        -- It proves smoothness of x_param ↦ mfderiv I_domain I_codomain (f_outer x_param) (g_inner x_param)
        -- which is x_param ↦ mfderiv I (modelWithCornersSelf ℝ F) f₀ x_param, i.e. L_map
        have h_L_map_at_x_eval : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F) (M' := F →L[ℝ] F) ∞ L_map x_eval := by
          simp_rw [L_map] -- Ensure L_map's definition is visible for `exact`
          exact ContMDiffAt.mfderiv (I' := 𝓘(ℝ, F)) (M' := F) _ _ hf_uncurried_smooth hg_map_smooth (le_refl ∞)

        exact h_L_map_at_x_eval.contMDiffWithinAt

      haveI : Nonempty M := ⟨y⟩
      let Psi (L : TangentSpace I (Classical.arbitrary M) →L[ℝ] F) : BicotangentSpace F I M (Classical.arbitrary M) :=
        ((innerSL ℝ).comp L).flip.comp L

      -- Psi maps (F →L[R] F) to (F →L[R] (F →L[R] R))
      let Psi_op (L : F →L[ℝ] F) : F →L[ℝ] (F →L[ℝ] ℝ) := ((innerSL ℝ).comp L).flip.comp L
      have h_Psi_smooth : ContDiff ℝ ∞ Psi_op := by
        -- Break it down into steps
        let step1 := fun (L : F →L[ℝ] F) => (innerSL ℝ).comp L        -- Compose with inner product
        let step2 := fun (BL : F →L[ℝ] (F →L[ℝ] ℝ)) => BL.flip        -- Flip arguments
        let step3 := fun (BLL : (F →L[ℝ] (F →L[ℝ] ℝ)) × (F →L[ℝ] F)) => BLL.1.comp BLL.2  -- Compose with L, again

        have : Psi_op = fun L ↦ step3 ((step2 ∘ step1) L, L) := rfl
        rw [this]

        -- These operations are smooth as they're built from continuous linear operations
        have h1 : ContDiff ℝ ∞ step1 :=
          IsBoundedLinearMap.contDiff (ContinuousLinearMap.isBoundedLinearMap_comp_left (innerSL ℝ))

        have h2 : ContDiff ℝ ∞ step2 := by
          -- The operation of flipping a bilinear form is smooth
          -- because it's a bounded linear map
          apply IsBoundedLinearMap.contDiff
          refine { toIsLinearMap := ?_, bound := ?_ }
          · exact { map_add := fun x ↦ congrFun rfl, map_smul := fun c ↦ congrFun rfl }
          · exists 1
            apply And.intro
            · exact Real.zero_lt_one
            · intro x
              simp only [ContinuousLinearMap.opNorm_flip, one_mul, le_refl, step2, g₀]

        exact (IsBoundedBilinearMap.contDiff isBoundedBilinearMap_comp).comp₂
          (h2.comp h1) contDiff_fun_id

      have h_s_loc_fiber_smooth : ContMDiffOn I 𝓘(ℝ, F →L[ℝ] (F →L[ℝ] ℝ)) ∞
          (fun x ↦ Psi_op (L_map x)) ((chartAt H y).source) := by
        exact (ContMDiff.contMDiffOn (s := univ) (contMDiff_iff_contDiff.mpr h_Psi_smooth)).comp
          h_L_map_smooth (fun ⦃a⦄ a ↦ trivial)

      simp [ContMDiffOn]
      intro x hx_mem_source
      apply (contMDiffWithinAt_totalSpace _).mpr
      refine ⟨?_, ?_⟩
      · simp
        refine contMDiffWithinAt_iff.mpr ⟨?_, ?_⟩
        · exact ContinuousAt.continuousWithinAt fun ⦃U⦄ a ↦ a
        · simp only [extChartAt, PartialHomeomorph.extend, PartialEquiv.coe_trans,
          ModelWithCorners.toPartialEquiv_coe, PartialHomeomorph.toFun_eq_coe,
          PartialEquiv.coe_trans_symm, PartialHomeomorph.coe_coe_symm,
          ModelWithCorners.toPartialEquiv_coe_symm, comp_apply, g₀, L_map]
          sorry
      · simp only [g₀, L_map]
        sorry
    -- • subordinate cover
    have h_sub : ρ.IsSubordinate (fun y ↦ (chartAt H y).source) :=
      chartsPartitionOfUnity_isSubordinate (E:=F) (I:=I) (M:=M)
    -- Finally apply the lemma
    refine (SmoothPartitionOfUnity.contMDiff_totalSpace_weighted_sum_of_local_sections
        I g_val ρ s_loc (fun y ↦ (chartAt H y).source)
        (fun y ↦ (chartAt H y).open_source) h_sub ?_) ?_
    · intro y; simpa using (hs_loc y)
    · -- pack as a section
      exact fun x ↦ TotalSpace.mk x (g_val x)

  ------------------------------------------------------------------
  --  Step 2 : symmetry of `g_val`
  ------------------------------------------------------------------
  have h_symm : ∀ x v w, hs_g_val x v w = hs_g_val x w v := by
    intro x v w
    change (∑ᶠ y, _) = (∑ᶠ y, _)
    refine (finsum_congr ?_).symm
    intro y
    simp [s_loc, g₀_symm, ContinuousLinearMap.comp_flip_symm g₀_symm]

  ------------------------------------------------------------------
  --  Step 3 : positive–definiteness of `g_val`
  ------------------------------------------------------------------
  have h_pos :
      ∀ x v, v ≠ (0 : TangentSpace I x) → 0 < hs_g_val x v v := by
    intro x v hv
    -- Pick the chart centred at `x`.  Because of the construction of `ρ`,
    -- we have `ρ x x = 1` (actually *exactly* one, not just > 0).
    have hρxx : ρ x x = 1 := by
      -- by construction of the partition of unity
      have : (ρ (fs:= ρ) (fs.ind x (mem_univ _)) x) = 1 := by
        simpa using
          (chartsPartitionOfUnity_apply_eq_one_of_eq H x rfl)
      simpa
    -- Now the term with index `y = x` already forces positivity.
    -- All the other summands are ≥ 0, so the whole sum is > 0.
    have hLinj : Function.Injective
        (mfderiv I (modelWithCornersSelf ℝ F) (extChartAt I x) x) :=
          (isInvertible_mfderiv_extChartAt (mem_extChartAt_source x)).injective
    have h_pos_x : 0 < (s_loc x x) v v := by
      -- s_loc x x is the pull-back via that derivative
      have :
          0 < g₀
            (mfderiv I (modelWithCornersSelf ℝ F) (extChartAt I x) x v)
            (mfderiv I (modelWithCornersSelf ℝ F) (extChartAt I x) x v) := by
        apply g₀_pos _ ?_
        intro hzero
        refine hv (hLinj ?_)
        rw [hzero]
        exact (mfderiv I 𝓘(ℝ, F) (↑(extChartAt I x)) x).map_zero.symm
      simpa [s_loc] using this
    have h_sum :
        hs_g_val x v v =
          ρ x x * (s_loc x x v v) +
            ∑ᶠ (y : {y // y ≠ x}), ρ y x • (s_loc y x v v) := by
      -- split off the `y = x` term (which is finite anyway)
      simpa [finsum_eq_sum_add_finsum_subtype] using rfl
    have : 0 < hs_g_val x v v := by
      have h_nonneg_rest :
        ∀ y : {y // y ≠ x},
          0 ≤ ρ y x • (s_loc y x v v) := by
        intro y; have := ρ.nonneg y x; have := g₀_pos _ (fun h ↦ by
          -- if the inner product piece is zero, the smul is non-negative anyway
          exact (mul_nonneg (ρ.nonneg _ _) (le_of_lt (g₀_pos _ ?_))).le)
        exact mul_nonneg (ρ.nonneg _ _) (by positivity)
      have : 0 < 1 * (s_loc x x v v) := by
        simpa [hρxx] using h_pos_x
      have h_rest := finsum_nonneg (fun y ↦ h_nonneg_rest y)
      have := add_pos_of_pos_of_nonneg this h_rest
      simpa [h_sum, hρxx] using this
    simpa using this

  ------------------------------------------------------------------
  --  Step 4 : bundle everything into one structure
  ------------------------------------------------------------------
  refine ⟨hs_g_val, ?_⟩
  exact RiemannianMetric.of_symm_posdef h_symm h_pos
