/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Topology.VectorBundle.Hom

/-! # Riemannian vector bundles

Given a real vector bundle over a topological space whose fibers are all endowed with an inner
product, we say that this bundle is Riemannian if the inner product depends continuously on the
base point.

We introduce a typeclass `[IsContinuousRiemannianBundle F E]` registering this property.
Under this assumption, we show that the inner product of two continuous maps into the same fibers
of the bundle is a continuous function.

If one wants to endow an existing vector bundle with a Riemannian metric, there is a subtlety:
the inner product space structure on the fibers should give rise to a topology on the fibers
which is defeq to the original one, to avoid diamonds. To do this, we introduce a
class `[RiemannianBundle E]` containing the data of an inner
product on the fibers defining the same topology as the original one. Given this class, we can
construct `NormedAddCommGroup` and `InnerProductSpace` instances on the fibers, compatible in a
defeq way with the initial topology. If the data used to register the instance `RiemannianBundle E`
depends continuously on the base point, we register automatically an instance of
`[IsContinuousRiemannianBundle F E]` (and similarly if the data is smooth).

The general theory should be built assuming `[IsContinuousRiemannianBundle F E]`, while the
`[RiemannianBundle E]` mechanism is only to build data in specific situations.

## Keywords
Vector bundle, Riemannian metric
-/

open Bundle ContinuousLinearMap
open scoped Topology

variable
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable (F E) in
/-- Consider a real vector bundle in which each fiber is endowed with an inner product.
We say that the bundle is *Riemannian* if the inner product depends continuously on the base point.
This assumption is spelled `IsContinuousRiemannianBundle F E` where `F` is the model fiber,
and `E : B → Type*` is the bundle. -/
class IsContinuousRiemannianBundle : Prop where
  exists_continuous : ∃ g : (Π x, E x →L[ℝ] E x →L[ℝ] ℝ),
    Continuous (fun (x : B) ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (g x))
    ∧ ∀ (x : B) (v w : E x), ⟪v, w⟫ = g x v w

section Trivial

variable {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁]

/-- A trivial vector bundle, in which the model fiber has a inner product,
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
their inner product is continuous. Version with `ContinuousWithinAt`. -/
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
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m) (g (b m) (v m) (w m))) s x :=
    (g_cont.continuousAt.comp_continuousWithinAt hf).clm_bundle_apply₂ (F₁ := F) (F₂ := F) hv hw
  simp only [FiberBundle.continuousWithinAt_totalSpace] at this
  exact this.2

/-- Given two continuous maps into the same fibers of a continuous Riemannian bundle,
their inner product is continuous. Version with `ContinuousAt`. -/
lemma ContinuousAt.inner_bundle
    (hv : ContinuousAt (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : ContinuousAt (fun m ↦ (w m : TotalSpace F E)) x) :
    ContinuousAt (fun b ↦ ⟪v b, w b⟫) x := by
  simp only [← continuousWithinAt_univ] at hv hw ⊢
  exact ContinuousWithinAt.inner_bundle hv hw

/-- Given two continuous maps into the same fibers of a continuous Riemannian bundle,
their inner product is continuous. Version with `ContinuousOn`. -/
lemma ContinuousOn.inner_bundle
    (hv : ContinuousOn (fun m ↦ (v m : TotalSpace F E)) s)
    (hw : ContinuousOn (fun m ↦ (w m : TotalSpace F E)) s) :
    ContinuousOn (fun b ↦ ⟪v b, w b⟫) s :=
  fun x hx ↦ (hv x hx).inner_bundle (hw x hx)

/-- Given two continuous maps into the same fibers of a continuous Riemannian bundle,
their inner product is continuous. -/
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
/-- A family of inner product space structures on the fibers of a fiber bundle, defining the same
topology as the already existing one. This family is not assumed to be continuous or smooth: to
guarantee continuity, resp. smoothness, of the inner product as a function of the base point,
use `ContinuousRiemannianMetric` or `ContMDiffRiemannianMetric`.

This structure is used through `RiemannianBundle` for typeclass inference, to register the inner
product space structure on the fibers without creating diamonds. -/
structure RiemannianMetric where
  /-- The inner product along the fibers of the bundle. -/
  inner (b : B) : E b →L[ℝ] E b →L[ℝ] ℝ
  symm (b : B) (v w : E b) : inner b v w = inner b w v
  pos (b : B) (v : E b) (hv : v ≠ 0) : 0 < inner b v v
  /-- The continuity at `0` is automatic when `E b` is isomorphic to a normed space, but since
  we are not making this assumption here we have to include it. -/
  continuousAt (b : B) : ContinuousAt (fun (v : E b) ↦ inner b v v) 0
  isVonNBounded (b : B) : IsVonNBounded ℝ {v : E b | inner b v v < 1}

/-- `Core structure associated to a family of inner products on the fibers of a fiber bundle. This
is an auxiliary construction to endow the fibers with an inner product space structure without
creating diamonds.

Warning: Do not use this `Core` structure if the space you are interested in already has a norm
instance defined on it, otherwise this will create a second non-defeq norm instance! -/
@[reducible] noncomputable def RiemannianMetric.toCore (g : RiemannianMetric E) (b : B) :
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
/-- Class used to create an inner product structure space on the fibers of a fiber bundle, without
creating diamonds. Use as follows:
* `instance : RiemannianBundle E := ⟨g⟩` where `g : RiemannianMetric E` registers the inner product
space on the fibers;
* `instance : RiemannianBundle E := ⟨g.toRiemannianMetric⟩` where
`g : ContinuousRiemannianMetric F E` registers the inner product space on the fibers, and the fact
that it varies continuously (i.e., a `[IsContinuousRiemannianBundle]` instance).
* `instance : RiemannianBundle E := ⟨g.toRiemannianMetric⟩` where
`g : ContMDiffRiemannianMetric IB n F E` registers the inner product space on the fibers, and the
fact that it varies smoothly (and continuously), i.e., `[IsContMDiffRiemannianBundle]` and
`[IsContinuousRiemannianBundle]` instances.
-/
class RiemannianBundle where
  /-- The family of inner products on the fibers -/
  g : RiemannianMetric E

/- The normal priority for an instance which always applies like this one should be 100.
We use 80 as this is rather specialized, so we want other paths to be tried first typically. -/
noncomputable instance (priority := 80) [h : RiemannianBundle E] (b : B) :
    NormedAddCommGroup (E b) :=
  (h.g.toCore b).toNormedAddCommGroupOfTopology (h.g.continuousAt b) (h.g.isVonNBounded b)

/- The normal priority for an instance which always applies like this one should be 100.
We use 80 as this is rather specialized, so we want other paths to be tried first typically. -/
noncomputable instance (priority := 80) [h : RiemannianBundle E] (b : B) :
    InnerProductSpace ℝ (E b) :=
  .ofCoreOfTopology (h.g.toCore b) (h.g.continuousAt b) (h.g.isVonNBounded b)

variable (F E) in
/-- A family of inner product space structures on the fibers of a fiber bundle, defining the same
topology as the already existing one, and varying continuously with the base point. See also
`ContMDiffRiemannianMetric` for a smooth version.

This structure is used through `RiemannianBundle` for typeclass inference, to register the inner
product space structure on the fibers without creating diamonds. -/
structure ContinuousRiemannianMetric where
  /-- The inner product along the fibers of the bundle. -/
  inner (b : B) : E b →L[ℝ] E b →L[ℝ] ℝ
  symm (b : B) (v w : E b) : inner b v w = inner b w v
  pos (b : B) (v : E b) (hv : v ≠ 0) : 0 < inner b v v
  isVonNBounded (b : B) : IsVonNBounded ℝ {v : E b | inner b v v < 1}
  continuous : Continuous (fun (b : B) ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (inner b))

/-- A continuous Riemannian metric is in particular a Riemannian metric. -/
def ContinuousRiemannianMetric.toRiemannianMetric (g : ContinuousRiemannianMetric F E) :
    RiemannianMetric E where
  inner := g.inner
  symm := g.symm
  pos := g.pos
  isVonNBounded := g.isVonNBounded
  continuousAt b := by
    -- Continuity of bilinear maps is only true on normed spaces. As `F` is a normed space by
    -- assumption, we transfer everything to `F` and argue there.
    let e : E b ≃L[ℝ] F := Trivialization.continuousLinearEquivAt ℝ (trivializationAt F E b) _
      (FiberBundle.mem_baseSet_trivializationAt' b)
    let m : (E b →L[ℝ] E b →L[ℝ] ℝ) ≃L[ℝ] (F →L[ℝ] F →L[ℝ] ℝ) :=
      e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ ))
    have A (v : E b) : g.inner b v v = ((fun w ↦ m (g.inner b) w w) ∘ e) v := by simp [m]
    simp only [A]
    fun_prop

/-- If a Riemannian bundle structure is defined using `g.toRiemannianMetric` where `g` is
a `ContinuousRiemannianMetric`, then we make sure typeclass inference can infer automatically
that the the bundle is a continuous Riemannian bundle. -/
instance (g : ContinuousRiemannianMetric F E) :
    letI : RiemannianBundle E := ⟨g.toRiemannianMetric⟩;
    IsContinuousRiemannianBundle F E := by
  letI : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
  exact ⟨⟨g.inner, g.continuous, fun b v w ↦ rfl⟩⟩

end Construction

end Bundle
