/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-! # Riemannian and Hermitian vector bundles
-/

open Manifold Bundle ContinuousLinearMap

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
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

lemma ContMDiffWithinAt.inner [h : IsRiemannianBundle IB n F E]
    {f : M → B} {v w : ∀ x, E (f x)} {s : Set M} {x : M}
    (hf : ContMDiffWithinAt IM IB n f s x)
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F (f b) (v b)) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun b ↦ TotalSpace.mk' F (f b) (v b)) s x) :
    ContMDiffWithinAt IM 𝓘(ℝ) n (fun b ↦ ⟪v b, w b⟫) s x := by
  rcases h.exists_contMDiff with ⟨g, hg⟩
  simp only [hg]
  apply ContMDiffWithinAt.clm_apply_of_inCoordinates



end ContMDiff
