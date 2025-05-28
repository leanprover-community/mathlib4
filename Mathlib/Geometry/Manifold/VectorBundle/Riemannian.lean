/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-! # Riemannian vector bundles

Given a vector bundle over a manifold whose fibers are all endowed with a scalar product, we
say that this bundle is Riemannian if the scalar product depends smoothly on the base point.

We introduce a typeclass `[IsRiemannianBundle IB n F E]` registering this property. Under this
assumption, we show that the scalar product of two smooth maps into the same fibers of the bundle
is a smooth function.
-/

open Manifold Bundle ContinuousLinearMap ENat
open scoped ContDiff

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
This assumption is spelled `IsRiemannianBundle IB n F E` where `IB` is the model space of the base,
`n` is the smoothness, `F` is the model fiber, and `E : B → Type*` is the bundle. -/
class IsRiemannianBundle : Prop where
  exists_contMDiff : ∃ g : Cₛ^n⟮IB; F →L[ℝ] F →L[ℝ] ℝ, fun (x : B) ↦ E x →L[ℝ] E x →L[ℝ] ℝ⟯,
    ∀ (x : B) (v w : E x), ⟪v, w⟫ = g x v w

lemma IsRiemannianBundle.of_le [h : IsRiemannianBundle IB n F E] (h' : n' ≤ n) :
    IsRiemannianBundle IB n' F E := by
  rcases h.exists_contMDiff with ⟨⟨g, g_smooth⟩, hg⟩
  exact ⟨⟨g, g_smooth.of_le h'⟩, hg⟩

instance {a : WithTop ℕ∞} [IsRiemannianBundle IB ∞ F E] [h : LEInfty a] :
    IsRiemannianBundle IB a F E :=
  IsRiemannianBundle.of_le h.out

instance {a : WithTop ℕ∞} [IsRiemannianBundle IB ω F E] :
    IsRiemannianBundle IB a F E :=
  IsRiemannianBundle.of_le le_top

instance [IsRiemannianBundle IB 1 F E] : IsRiemannianBundle IB 0 F E :=
  IsRiemannianBundle.of_le zero_le_one

instance [IsRiemannianBundle IB 2 F E] : IsRiemannianBundle IB 1 F E :=
  IsRiemannianBundle.of_le one_le_two

instance [IsRiemannianBundle IB 3 F E] : IsRiemannianBundle IB 2 F E :=
  IsRiemannianBundle.of_le (n := 3) (by norm_cast)

section Trivial

variable {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁]

/-- A trivial vector bundle, in which the model fiber has a scalar product,
is a Riemannian bundle. -/
instance : IsRiemannianBundle IB n F₁ (Bundle.Trivial B F₁) := by
  refine ⟨⟨fun x ↦ innerSL ℝ, fun x ↦ ?_⟩, fun x v w ↦ rfl⟩
  simp only [contMDiffAt_section]
  convert contMDiffAt_const (c := innerSL ℝ)
  ext v w
  simp [hom_trivializationAt_apply, inCoordinates, Trivialization.linearMapAt_apply,
    Trivial.trivialization_symm_apply B F₁]

end Trivial

section ContMDiff

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [h : IsRiemannianBundle IB n F E]
  {b : M → B} {v w : ∀ x, E (b x)} {s : Set M} {x : M}

/-- Given two smooth maps into the same fibers of a Riemannian bundle,
their scalar product is smooth. -/
lemma ContMDiffWithinAt.inner
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) s x) :
    ContMDiffWithinAt IM 𝓘(ℝ) n (fun m ↦ ⟪v m, w m⟫) s x := by
  rcases h.exists_contMDiff with ⟨⟨g, g_smooth⟩, hg⟩
  have hf : ContMDiffWithinAt IM IB n b s x := by
    simp only [contMDiffWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ)) n
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m) (g (b m) (v m) (w m))) s x := by
    apply ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := F) (F₂ := F)
    · exact ContMDiffAt.comp_contMDiffWithinAt x g_smooth.contMDiffAt hf
    · exact hv
    · exact hw
  simp only [contMDiffWithinAt_totalSpace] at this
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
