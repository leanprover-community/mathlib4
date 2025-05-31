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

We introduce a typeclass `[IsContinuousRiemannianBundle F E]` registering this property.
Under this assumption, we show that the scalar product of two continuous maps into the same fibers
of the bundle is a continuous function.

If one wants to endow an existing vector bundle with a Riemannian metric, there is a subtlety:
the inner product space structure on the fibers should give rise to a topology on the fibers
which is defeq to the original one, to avoid diamonds.

Therefore, we introduce a class `[RiemannianBundle E]` containing the data of a scalar
product on the fibers defining the same topology as the original one. Given this class, we can
construct `NormedAddCommGroup` and `InnerProductSpace` instances on the fibers, compatible in a
defeq way with the initial topology. If the data used to register the instance `RiemannianBundle E`
depends continuously on the base point, we register automatically an instance of
`[IsContinuousRiemannianBundle F E]` (and similarly if the data is smooth).

The general theory should be built assuming `[IsContinuousRiemannianBundle IB n F E]`, while the
`[RiemannianBundle E]` mechanism is only to build data in specific situations.
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

/-- Given two continuous maps into the same fibers of a continuous Riemannian bundle,
their scalar product is continuous. -/
lemma ContinuousWithinAt.inner_bundle
    (hv : ContinuousWithinAt (fun m ↦ (v m : TotalSpace F E)) s x)
    (hw : ContinuousWithinAt (fun m ↦ (w m : TotalSpace F E)) s x) :
    ContinuousWithinAt (fun m ↦ ⟪v m, w m⟫) s x := by
  rcases h.exists_continuous with ⟨g, g_cont, hg⟩
  have hf : ContinuousWithinAt b s x := by
    simp only [FiberBundle.continuousWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have : ContinuousWithinAt
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m) (g (b m) (v m) (w m))) s x := by
    apply ContinuousWithinAt.clm_bundle_apply₂ (F₁ := F) (F₂ := F)
    · exact ContinuousAt.comp_continuousWithinAt g_cont.continuousAt hf
    · exact hv
    · exact hw
  simp only [FiberBundle.continuousWithinAt_totalSpace] at this
  exact this.2

/-- Given two continuous maps into the same fibers of a continuous Riemannian bundle,
their scalar product is continuous. -/
lemma ContinuousAt.inner_bundle
    (hv : ContinuousAt (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : ContinuousAt (fun m ↦ (w m : TotalSpace F E)) x) :
    ContinuousAt (fun b ↦ ⟪v b, w b⟫) x := by
  simp only [← continuousWithinAt_univ] at hv hw ⊢
  exact ContinuousWithinAt.inner_bundle hv hw

/-- Given two continuous maps into the same fibers of a continuous Riemannian bundle,
their scalar product is continuous. -/
lemma ContinuousOn.inner_bundle
    (hv : ContinuousOn (fun m ↦ (v m : TotalSpace F E)) s)
    (hw : ContinuousOn (fun m ↦ (w m : TotalSpace F E)) s) :
    ContinuousOn (fun b ↦ ⟪v b, w b⟫) s :=
  fun x hx ↦ (hv x hx).inner_bundle (hw x hx)

/-- Given two continuous maps into the same fibers of a continuous Riemannian bundle,
their scalar product is continuous. -/
lemma Continuous.inner_bundle
    (hv : Continuous (fun m ↦ (v m : TotalSpace F E)))
    (hw : Continuous (fun m ↦ (w m : TotalSpace F E))) :
    Continuous (fun b ↦ ⟪v b, w b⟫) := by
  simp only [continuous_iff_continuousAt] at hv hw ⊢
  exact fun x ↦ (hv x).inner_bundle (hw x)

end Continuous

namespace Bundle

section Construction

variable
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

open Bornology

variable (E) in
structure RiemannianMetric where
  inner (b : B) : E b →L[ℝ] E b →L[ℝ] ℝ
  symm (b : B) (v w : E b) : inner b v w = inner b w v
  pos (b : B) (v : E b) (hv : v ≠ 0) : 0 < inner b v v
  continuousAt (b : B) : ContinuousAt (fun (v : E b) ↦ inner b v v) 0
  isVonNBounded (b : B) : IsVonNBounded ℝ {v : E b | inner b v v < 1}

noncomputable def RiemannianMetric.toCore  (g : RiemannianMetric E) (b : B) :
    InnerProductSpace.Core ℝ (E b) where
  inner v w := g.inner b v w
  conj_inner_symm v w := g.symm b w v
  re_inner_nonneg v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · simpa using (g.pos b v hv).le
  add_left v w x := by simp
  smul_left c v := by simp
  definite v h := by contrapose! h; exact (g.pos b v h).ne'

variable (E) in
class RiemannianBundle where
  out : RiemannianMetric E

noncomputable instance [h : RiemannianBundle E] (b : B) : NormedAddCommGroup (E b) :=
  (h.out.toCore b).toNormedAddCommGroupOfTopology (h.out.continuousAt b) (h.out.isVonNBounded b)

#check MetricSpace.ext

noncomputable instance [h : RiemannianBundle E] (b : B) : NormedSpace ℝ (E b) := by
  convert (h.out.toCore b).toNormedSpace



--  (h.out.toCore b).toNormedAddCommGroupOfTopology (h.out.continuousAt b) (h.out.isVonNBounded b)



#exit



def riemannianMetric.toNormedAddCommGroup (g : riemannianMetric E) :
    ∀ x, NormedAddCommGroup (E x) := fun

variable (F E) in
structure continuousRiemannianMetric extends riemannianMetric E where
  continuous : Continuous (fun (b : B) ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (inner b))


#check InnerProductSpace.Core

end Construction

end Bundle
