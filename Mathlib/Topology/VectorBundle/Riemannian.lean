/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Topology.VectorBundle.Hom

/-! # Riemannian vector bundles

Given a vector bundle over a manifold whose fibers are all endowed with a scalar product, we
say that this bundle is Riemannian if the scalar product depends continuously on the base point.

We introduce a typeclass `[IsContinuousRiemannianBundle IB n F E]` registering this property.
Under this assumption, we show that the scalar product of two continuous maps into the same fibers
of the bundle is a continuous function.

If one wants to endow an existing vector bundle with a Riemannian metric, there is a subtlety:
the inner product space structure on the fibers should give rise to a topology on the fibers
which is defeq to the original one, to avoid diamonds.

Therefore, we introduce a class `[RiemannianBundle F E]` containing the data of a scalar
product on the fibers depending continuously on the basepoint. Given this class, we can construct
`NormedAddCommGroup` and `InnerProductSpace` instances on the fibers, compatible in a defeq way with
the initial topology. However, we can not register these as general instances, because there is
no way that typeclass inference could guess `F` out of `E`. We should only use these
in specific situations like the tangent bundle, and the general theory should instead be built
assuming `[IsContMDiffRiemannianBundle IB n F E]`
-/

open Bundle ContinuousLinearMap ENat
open scoped Topology

variable
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable (F E) in
/-- Consider a real vector bundle in which each fiber is endowed with a scalar product.
We that the bundle is Riemannian if the scalar product depends continuously on the base point.
This assumption is spelled `IsContinuousRiemannianBundle F E` where `F` is the model fiber,
and `E : B → Type*` is the bundle. -/
class IsContinuousRiemannianBundle : Prop where
  exists_continuous : ∃ g : (Π x, E x →L[ℝ] E x →L[ℝ] ℝ),
    Continuous (fun (x : B) ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (g x))
    ∧ ∀ (x : B) (v w : E x), ⟪v, w⟫ = g x v w

section Trivial

variable {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁]

/-- A trivial vector bundle, in which the model fiber has a scalar product,
is a Riemannian bundle. -/
instance : IsContinuousRiemannianBundle F₁ (Bundle.Trivial B F₁) := by
  refine ⟨fun x ↦ innerSL ℝ, ?_, fun x v w ↦ rfl⟩
  rw [continuous_iff_continuousAt]
  intro x
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuousAt_id, ?_⟩
  convert continuousAt_const (y := innerSL ℝ)
  ext v w
  simp [hom_trivializationAt_apply, inCoordinates, Trivialization.linearMapAt_apply,
    Trivial.trivialization_symm_apply B F₁]

end Trivial

section Continuous

variable
  {M : Type*} [TopologicalSpace M] [h : IsContinuousRiemannianBundle F E]
  {b : M → B} {v w : ∀ x, E (b x)} {s : Set M} {x : M}

/-- Given two continuous maps into the same fibers of a Riemannian bundle,
their scalar product is continuous. -/
lemma ContinuousWithinAt.inner_bundle
    (hv : ContinuousWithinAt (fun m ↦ (v m : TotalSpace F E)) s x)
    (hv : ContinuousWithinAt (fun m ↦ (w m : TotalSpace F E)) s x) :
    ContinuousWithinAt (fun m ↦ ⟪v m, w m⟫) s x := by
  rcases h.exists_continuous with ⟨g, g_cont, hg⟩
  have hf : ContinuousWithinAt b s x := by
    simp only [FiberBundle.continuousWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have : ContinuousWithinAt
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m) (g (b m) (v m) (w m))) s x := by
    apply ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := F) (F₂ := F)
    · exact ContMDiffAt.comp_contMDiffWithinAt x g_smooth.contMDiffAt hf
    · exact hv
    · exact hw
  simp only [FiberBundle.continuousWithinAt_totalSpace] at this
  exact this.2

/-- Given two smooth maps into the same fibers of a Riemannian bundle,
their scalar product is smooth. -/
lemma ContMDiffAt.inner
    (hv : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) x) :
    ContMDiffAt IM 𝓘(ℝ) n (fun b ↦ ⟪v b, w b⟫) x :=
  ContMDiffWithinAt.inner hv hw

/-- Given two smooth maps into the same fibers of a Riemannian bundle,
their scalar product is smooth. -/
lemma ContMDiffOn.inner
    (hv : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s)
    (hw : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) s) :
    ContMDiffOn IM 𝓘(ℝ) n (fun b ↦ ⟪v b, w b⟫) s :=
  fun x hx ↦ (hv x hx).inner (hw x hx)

/-- Given two smooth maps into the same fibers of a Riemannian bundle,
their scalar product is smooth. -/
lemma ContMDiff.inner
    (hv : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)))
    (hw : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E))) :
    ContMDiff IM 𝓘(ℝ) n (fun b ↦ ⟪v b, w b⟫) :=
  fun x ↦ (hv x).inner (hw x)

end ContMDiff

namespace Bundle

section Construction

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n n' : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

variable (IB n F E) in
structure riemannianMetric where
  inner (b : B) : E b →L[ℝ] E b →L[ℝ] ℝ
  contMDiff : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
    (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) (E := fun b ↦ (E b →L[ℝ] E b →L[ℝ] ℝ)) b (inner b))
  symm (b : B) (v w : E b) : inner b v w = inner b w v
  pos (b : B) (v : E b) (hv : v ≠ 0) : 0 < inner b v v
  inducing (b : B) : {v : E b | inner b v v < 1} ∈ 𝓝 (0 : E b)


#check InnerProductSpace.Core

end Construction

end Bundle
