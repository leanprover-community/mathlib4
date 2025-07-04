/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Riemannian

/-! # Riemannian vector bundles

Given a vector bundle over a manifold whose fibers are all endowed with a scalar product, we
say that this bundle is Riemannian if the scalar product depends smoothly on the base point.

We introduce a typeclass `[IsContMDiffRiemannianBundle IB n F E]` registering this property.
Under this assumption, we show that the scalar product of two smooth maps into the same fibers of
the bundle is a smooth function.

If the fibers of a bundle `E` have a preexisting topology (like the tangent bundle), one can not
assume additionally `[∀ b, InnerProductSpace ℝ (E b)]` as this would create diamonds. Instead,
use `[RiemannianBundle E]`, which endows the fibers with a scalar product while ensuring that
there is no diamond. We provide a constructor for `[RiemannianBundle E]` from a smooth family
of metrics, which registers automatically `[IsContMDiffRiemannianBundle IB n F E]`.

The following code block is the standard way to say "Let `E` be a smooth vector bundle equipped with
a `C^n` Riemannian structure over a `C^n` manifold `B`":
```
variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsManifold IB n B] [ContMDiffVectorBundle n F E IB]
  [IsContMDiffRiemannianBundle IB n F E]
```
-/

open Manifold Bundle ContinuousLinearMap ENat Bornology
open scoped ContDiff Topology

section

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n n' : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable (IB n F E) in
/-- Consider a real vector bundle in which each fiber is endowed with a scalar product.
We that the bundle is Riemannian if the scalar product depends smoothly on the base point.
This assumption is spelled `IsContMDiffRiemannianBundle IB n F E` where `IB` is the model space of
the base, `n` is the smoothness, `F` is the model fiber, and `E : B → Type*` is the bundle. -/
class IsContMDiffRiemannianBundle : Prop where
  exists_contMDiff : ∃ g : Π (x : B), E x →L[ℝ] E x →L[ℝ] ℝ,
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (g b))
    ∧ ∀ (x : B) (v w : E x), ⟪v, w⟫ = g x v w

lemma IsContMDiffRiemannianBundle.of_le [h : IsContMDiffRiemannianBundle IB n F E] (h' : n' ≤ n) :
    IsContMDiffRiemannianBundle IB n' F E := by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  exact ⟨g, g_smooth.of_le h', hg⟩

instance {a : WithTop ℕ∞} [IsContMDiffRiemannianBundle IB ∞ F E] [h : LEInfty a] :
    IsContMDiffRiemannianBundle IB a F E :=
  IsContMDiffRiemannianBundle.of_le h.out

instance {a : WithTop ℕ∞} [IsContMDiffRiemannianBundle IB ω F E] :
    IsContMDiffRiemannianBundle IB a F E :=
  IsContMDiffRiemannianBundle.of_le le_top

instance [IsContMDiffRiemannianBundle IB 1 F E] : IsContMDiffRiemannianBundle IB 0 F E :=
  IsContMDiffRiemannianBundle.of_le zero_le_one

instance [IsContMDiffRiemannianBundle IB 2 F E] : IsContMDiffRiemannianBundle IB 1 F E :=
  IsContMDiffRiemannianBundle.of_le one_le_two

instance [IsContMDiffRiemannianBundle IB 3 F E] : IsContMDiffRiemannianBundle IB 2 F E :=
  IsContMDiffRiemannianBundle.of_le (n := 3) (by norm_cast)

section Trivial

variable {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁]

/-- A trivial vector bundle, in which the model fiber has a scalar product,
is a Riemannian bundle. -/
instance : IsContMDiffRiemannianBundle IB n F₁ (Bundle.Trivial B F₁) := by
  refine ⟨fun x ↦ innerSL ℝ, fun x ↦ ?_, fun x v w ↦ rfl⟩
  simp only [contMDiffAt_section]
  convert contMDiffAt_const (c := innerSL ℝ)
  ext v w
  simp [hom_trivializationAt_apply, inCoordinates, Trivialization.linearMapAt_apply]

end Trivial

section ContMDiff

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [h : IsContMDiffRiemannianBundle IB n F E]
  {b : M → B} {v w : ∀ x, E (b x)} {s : Set M} {x : M}

/-- Given two smooth maps into the same fibers of a Riemannian bundle,
their scalar product is smooth. -/
lemma ContMDiffWithinAt.inner_bundle
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) s x) :
    ContMDiffWithinAt IM 𝓘(ℝ) n (fun m ↦ ⟪v m, w m⟫) s x := by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  have hb : ContMDiffWithinAt IM IB n b s x := by
    simp only [contMDiffWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ)) n
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m) (g (b m) (v m) (w m))) s x := by
    apply ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := F) (F₂ := F)
    · exact ContMDiffAt.comp_contMDiffWithinAt x g_smooth.contMDiffAt hb
    · exact hv
    · exact hw
  simp only [contMDiffWithinAt_totalSpace] at this
  exact this.2

/-- Given two smooth maps into the same fibers of a Riemannian bundle,
their scalar product is smooth. -/
lemma ContMDiffAt.inner_bundle
    (hv : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) x) :
    ContMDiffAt IM 𝓘(ℝ) n (fun b ↦ ⟪v b, w b⟫) x :=
  ContMDiffWithinAt.inner_bundle hv hw

/-- Given two smooth maps into the same fibers of a Riemannian bundle,
their scalar product is smooth. -/
lemma ContMDiffOn.inner_bundle
    (hv : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s)
    (hw : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) s) :
    ContMDiffOn IM 𝓘(ℝ) n (fun b ↦ ⟪v b, w b⟫) s :=
  fun x hx ↦ (hv x hx).inner_bundle (hw x hx)

/-- Given two smooth maps into the same fibers of a Riemannian bundle,
their scalar product is smooth. -/
lemma ContMDiff.inner_bundle
    (hv : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)))
    (hw : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E))) :
    ContMDiff IM 𝓘(ℝ) n (fun b ↦ ⟪v b, w b⟫) :=
  fun x ↦ (hv x).inner_bundle (hw x)

end ContMDiff

end

namespace Bundle

section Construction

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n n' : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

variable (IB n F E) in
/-- A family of inner product space structures on the fibers of a fiber bundle, defining the same
topology as the already existing one, and varying continuously with the base point. See also
`ContinuousRiemannianMetric` for a continuous version.

This structure is used through `RiemannianBundle` for typeclass inference, to register the inner
product space structure on the fibers without creating diamonds. -/
structure ContMDiffRiemannianMetric where
  /-- The scalar product along the fibers of the bundle. -/
  inner (b : B) : E b →L[ℝ] E b →L[ℝ] ℝ
  symm (b : B) (v w : E b) : inner b v w = inner b w v
  pos (b : B) (v : E b) (hv : v ≠ 0) : 0 < inner b v v
  isVonNBounded (b : B) : IsVonNBounded ℝ {v : E b | inner b v v < 1}
  contMDiff : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
    (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (inner b))

/-- A smooth Riemannian metric defines in particular a continuous Riemannian metric. -/
def ContMDiffRiemannianMetric.toContinuousRiemannianMetric
    (g : ContMDiffRiemannianMetric IB n F E) : ContinuousRiemannianMetric F E :=
  { g with continuous := g.contMDiff.continuous }

/-- A smooth Riemannian metric defines in particular a Riemannian metric. -/
def ContMDiffRiemannianMetric.toRiemannianMetric
    (g : ContMDiffRiemannianMetric IB n F E) : RiemannianMetric E :=
  g.toContinuousRiemannianMetric.toRiemannianMetric

instance (g : ContMDiffRiemannianMetric IB n F E) :
    letI : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
    IsContMDiffRiemannianBundle IB n F E :=
  letI : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
  ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩

end Construction

end Bundle
