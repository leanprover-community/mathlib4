/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! ## Equivalence of manifold differentiability with the basic definition for functions between
vector spaces

The API in this file is mostly copied from `Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean`,
providing the same statements for higher smoothness. In this file, we do the same for
differentiability.

-/

open Set ChartedSpace IsManifold
open scoped Topology Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  -- declare a charted space `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- declare a `C^n` manifold `M'` over the pair `(E', H')`.
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' n M']
  -- declare a `C^n` manifold `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J n N]
  -- declare a `C^n` manifold `N'` over the pair `(F', G')`.
  {F' : Type*}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  [IsManifold J' n N']
  -- F₁, F₂, F₃, F₄ are normed spaces
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {F₂ : Type*} [NormedAddCommGroup F₂]
  [NormedSpace 𝕜 F₂] {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] {F₄ : Type*}
  [NormedAddCommGroup F₄] [NormedSpace 𝕜 F₄]
  -- declare functions, sets, points and smoothness indices
  {f f₁ : M → M'} {s t : Set M} {x : M} {m n : ℕ∞}

section Module

theorem DifferentiableWithinAt.comp_mdifferentiableWithinAt
    {g : F → F'} {f : M → F} {s : Set M} {t : Set F}
    {x : M} (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : MDifferentiableWithinAt I 𝓘(𝕜, F) f s x)
    (h : MapsTo f s t) : MDifferentiableWithinAt I 𝓘(𝕜, F') (g ∘ f) s x :=
  hg.mdifferentiableWithinAt.comp x hf h

theorem DifferentiableAt.comp_mdifferentiableWithinAt {g : F → F'} {f : M → F} {s : Set M}
    {x : M} (hg : DifferentiableAt 𝕜 g (f x)) (hf : MDifferentiableWithinAt I 𝓘(𝕜, F) f s x) :
    MDifferentiableWithinAt I 𝓘(𝕜, F') (g ∘ f) s x :=
  hg.mdifferentiableAt.comp_mdifferentiableWithinAt x hf

theorem DifferentiableAt.comp_mdifferentiableAt
    {g : F → F'} {f : M → F} {x : M} (hg : DifferentiableAt 𝕜 g (f x))
    (hf : MDifferentiableAt I 𝓘(𝕜, F) f x) : MDifferentiableAt I 𝓘(𝕜, F') (g ∘ f) x :=
  hg.comp_mdifferentiableWithinAt hf

theorem Differentiable.comp_mdifferentiableWithinAt {g : F → F'} {f : M → F} {s : Set M} {x : M}
    (hg : Differentiable 𝕜 g) (hf : MDifferentiableWithinAt I 𝓘(𝕜, F) f s x) :
    MDifferentiableWithinAt I 𝓘(𝕜, F') (g ∘ f) s x :=
  hg.differentiableAt.comp_mdifferentiableWithinAt hf

theorem Differentiable.comp_mdifferentiableAt
    {g : F → F'} {f : M → F} {x : M} (hg : Differentiable 𝕜 g)
    (hf : MDifferentiableAt I 𝓘(𝕜, F) f x) : MDifferentiableAt I 𝓘(𝕜, F') (g ∘ f) x :=
  hg.comp_mdifferentiableWithinAt hf

theorem Differentiable.comp_mdifferentiable {g : F → F'} {f : M → F} (hg : Differentiable 𝕜 g)
    (hf : MDifferentiable I 𝓘(𝕜, F) f) : MDifferentiable I 𝓘(𝕜, F') (g ∘ f) := fun x =>
  hg.differentiableAt.comp_mdifferentiableAt (hf x)

end Module

/-! ### Linear maps between normed spaces are differentiable -/

theorem MDifferentiableWithinAt.clm_precomp {f : M → F₁ →L[𝕜] F₂} {s : Set M} {x : M}
    (hf : MDifferentiableWithinAt I 𝓘(𝕜, F₁ →L[𝕜] F₂) f s x) :
    MDifferentiableWithinAt I 𝓘(𝕜, (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃))
      (fun y ↦ (f y).precomp F₃ : M → (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) s x :=
  Differentiable.comp_mdifferentiableWithinAt
    (ContinuousLinearMap.differentiable
      (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃).flip) hf

nonrec theorem MDifferentiableAt.clm_precomp {f : M → F₁ →L[𝕜] F₂} {x : M}
    (hf : MDifferentiableAt I 𝓘(𝕜, F₁ →L[𝕜] F₂) f x) :
    MDifferentiableAt I 𝓘(𝕜, (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃))
      (fun y ↦ (f y).precomp F₃ : M → (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) x :=
  Differentiable.comp_mdifferentiableAt
    (ContinuousLinearMap.differentiable
      (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃).flip) hf

theorem MDifferentiableOn.clm_precomp {f : M → F₁ →L[𝕜] F₂} {s : Set M}
    (hf : MDifferentiableOn I 𝓘(𝕜, F₁ →L[𝕜] F₂) f s) :
    MDifferentiableOn I 𝓘(𝕜, (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃))
      (fun y ↦ (f y).precomp F₃ : M → (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) s := fun x hx ↦
  (hf x hx).clm_precomp

theorem MDifferentiable.clm_precomp
    {f : M → F₁ →L[𝕜] F₂} (hf : MDifferentiable I 𝓘(𝕜, F₁ →L[𝕜] F₂) f) :
    MDifferentiable I 𝓘(𝕜, (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃))
      (fun y ↦ (f y).precomp F₃ : M → (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) := fun x ↦
  (hf x).clm_precomp

theorem MDifferentiableWithinAt.clm_postcomp {f : M → F₂ →L[𝕜] F₃} {s : Set M} {x : M}
    (hf : MDifferentiableWithinAt I 𝓘(𝕜, F₂ →L[𝕜] F₃) f s x) :
    MDifferentiableWithinAt I 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃))
      (fun y ↦ (f y).postcomp F₁ : M → (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) s x :=
  Differentiable.comp_mdifferentiableWithinAt
    (ContinuousLinearMap.differentiable
      (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃)) hf

theorem MDifferentiableAt.clm_postcomp {f : M → F₂ →L[𝕜] F₃} {x : M}
    (hf : MDifferentiableAt I 𝓘(𝕜, F₂ →L[𝕜] F₃) f x) :
    MDifferentiableAt I 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃))
      (fun y ↦ (f y).postcomp F₁ : M → (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) x :=
  Differentiable.comp_mdifferentiableAt
    (ContinuousLinearMap.differentiable
      (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃)) hf

nonrec theorem MDifferentiableOn.clm_postcomp {f : M → F₂ →L[𝕜] F₃} {s : Set M}
    (hf : MDifferentiableOn I 𝓘(𝕜, F₂ →L[𝕜] F₃) f s) :
    MDifferentiableOn I 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃))
      (fun y ↦ (f y).postcomp F₁ : M → (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) s := fun x hx ↦
  (hf x hx).clm_postcomp

theorem MDifferentiable.clm_postcomp
    {f : M → F₂ →L[𝕜] F₃} (hf : MDifferentiable I 𝓘(𝕜, F₂ →L[𝕜] F₃) f) :
    MDifferentiable I 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃))
      (fun y ↦ (f y).postcomp F₁ : M → (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) := fun x ↦
  (hf x).clm_postcomp

theorem MDifferentiableWithinAt.clm_comp
    {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁} {s : Set M} {x : M}
    (hg : MDifferentiableWithinAt I 𝓘(𝕜, F₁ →L[𝕜] F₃) g s x)
    (hf : MDifferentiableWithinAt I 𝓘(𝕜, F₂ →L[𝕜] F₁) f s x) :
    MDifferentiableWithinAt I 𝓘(𝕜, F₂ →L[𝕜] F₃) (fun x => (g x).comp (f x)) s x :=
  Differentiable.comp_mdifferentiableWithinAt
    (g := fun x : (F₁ →L[𝕜] F₃) × (F₂ →L[𝕜] F₁) => x.1.comp x.2)
    (f := fun x => (g x, f x)) (differentiable_fst.clm_comp differentiable_snd)
    (hg.prodMk_space hf)

theorem MDifferentiableAt.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁} {x : M}
    (hg : MDifferentiableAt I 𝓘(𝕜, F₁ →L[𝕜] F₃) g x)
    (hf : MDifferentiableAt I 𝓘(𝕜, F₂ →L[𝕜] F₁) f x) :
    MDifferentiableAt I 𝓘(𝕜, F₂ →L[𝕜] F₃) (fun x => (g x).comp (f x)) x :=
  (hg.mdifferentiableWithinAt.clm_comp hf.mdifferentiableWithinAt).mdifferentiableAt Filter.univ_mem

theorem MDifferentiableOn.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁} {s : Set M}
    (hg : MDifferentiableOn I 𝓘(𝕜, F₁ →L[𝕜] F₃) g s)
    (hf : MDifferentiableOn I 𝓘(𝕜, F₂ →L[𝕜] F₁) f s) :
    MDifferentiableOn I 𝓘(𝕜, F₂ →L[𝕜] F₃) (fun x => (g x).comp (f x)) s := fun x hx =>
  (hg x hx).clm_comp (hf x hx)

theorem MDifferentiable.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁}
    (hg : MDifferentiable I 𝓘(𝕜, F₁ →L[𝕜] F₃) g) (hf : MDifferentiable I 𝓘(𝕜, F₂ →L[𝕜] F₁) f) :
    MDifferentiable I 𝓘(𝕜, F₂ →L[𝕜] F₃) fun x => (g x).comp (f x) := fun x => (hg x).clm_comp (hf x)

/-- Applying a linear map to a vector is differentiable within a set. Version in vector spaces. For
a version in nontrivial vector bundles, see `MDifferentiableWithinAt.clm_apply_of_inCoordinates`. -/
theorem MDifferentiableWithinAt.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {s : Set M} {x : M}
    (hg : MDifferentiableWithinAt I 𝓘(𝕜, F₁ →L[𝕜] F₂) g s x)
    (hf : MDifferentiableWithinAt I 𝓘(𝕜, F₁) f s x) :
    MDifferentiableWithinAt I 𝓘(𝕜, F₂) (fun x => g x (f x)) s x :=
  DifferentiableWithinAt.comp_mdifferentiableWithinAt (t := univ)
    (g := fun x : (F₁ →L[𝕜] F₂) × F₁ => x.1 x.2)
    (by apply (Differentiable.differentiableAt _).differentiableWithinAt
        exact differentiable_fst.clm_apply differentiable_snd) (hg.prodMk_space hf)
    (by simp_rw [mapsTo_univ])

/-- Applying a linear map to a vector is differentiable. Version in vector spaces. For a
version in nontrivial vector bundles, see `MDifferentiableAt.clm_apply_of_inCoordinates`. -/
theorem MDifferentiableAt.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {x : M}
    (hg : MDifferentiableAt I 𝓘(𝕜, F₁ →L[𝕜] F₂) g x) (hf : MDifferentiableAt I 𝓘(𝕜, F₁) f x) :
    MDifferentiableAt I 𝓘(𝕜, F₂) (fun x => g x (f x)) x :=
  DifferentiableWithinAt.comp_mdifferentiableWithinAt (t := univ)
    (g := fun x : (F₁ →L[𝕜] F₂) × F₁ => x.1 x.2)
    (by apply (Differentiable.differentiableAt _).differentiableWithinAt
        exact differentiable_fst.clm_apply differentiable_snd) (hg.prodMk_space hf)
    (by simp_rw [mapsTo_univ])

theorem MDifferentiableOn.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {s : Set M}
    (hg : MDifferentiableOn I 𝓘(𝕜, F₁ →L[𝕜] F₂) g s) (hf : MDifferentiableOn I 𝓘(𝕜, F₁) f s) :
    MDifferentiableOn I 𝓘(𝕜, F₂) (fun x => g x (f x)) s := fun x hx => (hg x hx).clm_apply (hf x hx)

theorem MDifferentiable.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁}
    (hg : MDifferentiable I 𝓘(𝕜, F₁ →L[𝕜] F₂) g) (hf : MDifferentiable I 𝓘(𝕜, F₁) f) :
    MDifferentiable I 𝓘(𝕜, F₂) fun x => g x (f x) := fun x => (hg x).clm_apply (hf x)

theorem MDifferentiableWithinAt.cle_arrowCongr {f : M → F₁ ≃L[𝕜] F₂} {g : M → F₃ ≃L[𝕜] F₄}
    {s : Set M} {x : M}
    (hf : MDifferentiableWithinAt I 𝓘(𝕜, F₂ →L[𝕜] F₁) (fun x ↦ ((f x).symm : F₂ →L[𝕜] F₁)) s x)
    (hg : MDifferentiableWithinAt I 𝓘(𝕜, F₃ →L[𝕜] F₄) (fun x ↦ (g x : F₃ →L[𝕜] F₄)) s x) :
    MDifferentiableWithinAt I 𝓘(𝕜, (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄))
      (fun y ↦ (f y).arrowCongr (g y) : M → (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) s x :=
  show MDifferentiableWithinAt I 𝓘(𝕜, (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄))
    (fun y ↦ (((f y).symm : F₂ →L[𝕜] F₁).precomp F₄).comp ((g y : F₃ →L[𝕜] F₄).postcomp F₁)) s x
  from hf.clm_precomp (F₃ := F₄) |>.clm_comp <| hg.clm_postcomp (F₁ := F₁)

theorem MDifferentiableAt.cle_arrowCongr {f : M → F₁ ≃L[𝕜] F₂} {g : M → F₃ ≃L[𝕜] F₄} {x : M}
    (hf : MDifferentiableAt I 𝓘(𝕜, F₂ →L[𝕜] F₁) (fun x ↦ ((f x).symm : F₂ →L[𝕜] F₁)) x)
    (hg : MDifferentiableAt I 𝓘(𝕜, F₃ →L[𝕜] F₄) (fun x ↦ (g x : F₃ →L[𝕜] F₄)) x) :
    MDifferentiableAt I 𝓘(𝕜, (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄))
      (fun y ↦ (f y).arrowCongr (g y) : M → (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) x :=
  show MDifferentiableAt I 𝓘(𝕜, (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄))
    (fun y ↦ (((f y).symm : F₂ →L[𝕜] F₁).precomp F₄).comp ((g y : F₃ →L[𝕜] F₄).postcomp F₁)) x
  from hf.clm_precomp (F₃ := F₄) |>.clm_comp <| hg.clm_postcomp (F₁ := F₁)

theorem MDifferentiableOn.cle_arrowCongr {f : M → F₁ ≃L[𝕜] F₂} {g : M → F₃ ≃L[𝕜] F₄} {s : Set M}
    (hf : MDifferentiableOn I 𝓘(𝕜, F₂ →L[𝕜] F₁) (fun x ↦ ((f x).symm : F₂ →L[𝕜] F₁)) s)
    (hg : MDifferentiableOn I 𝓘(𝕜, F₃ →L[𝕜] F₄) (fun x ↦ (g x : F₃ →L[𝕜] F₄)) s) :
    MDifferentiableOn I 𝓘(𝕜, (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄))
      (fun y ↦ (f y).arrowCongr (g y) : M → (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) s := fun x hx ↦
  (hf x hx).cle_arrowCongr (hg x hx)

theorem MDifferentiable.cle_arrowCongr {f : M → F₁ ≃L[𝕜] F₂} {g : M → F₃ ≃L[𝕜] F₄}
    (hf : MDifferentiable I 𝓘(𝕜, F₂ →L[𝕜] F₁) (fun x ↦ ((f x).symm : F₂ →L[𝕜] F₁)))
    (hg : MDifferentiable I 𝓘(𝕜, F₃ →L[𝕜] F₄) (fun x ↦ (g x : F₃ →L[𝕜] F₄))) :
    MDifferentiable I 𝓘(𝕜, (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄))
      (fun y ↦ (f y).arrowCongr (g y) : M → (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) := fun x ↦
  (hf x).cle_arrowCongr (hg x)

theorem MDifferentiableWithinAt.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄} {s : Set M}
    {x : M} (hg : MDifferentiableWithinAt I 𝓘(𝕜, F₁ →L[𝕜] F₃) g s x)
    (hf : MDifferentiableWithinAt I 𝓘(𝕜, F₂ →L[𝕜] F₄) f s x) :
    MDifferentiableWithinAt I 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₃ × F₄) (fun x => (g x).prodMap (f x)) s x :=
  Differentiable.comp_mdifferentiableWithinAt
    (g := fun x : (F₁ →L[𝕜] F₃) × (F₂ →L[𝕜] F₄) => x.1.prodMap x.2)
    (f := fun x => (g x, f x)) (ContinuousLinearMap.prodMapL 𝕜 F₁ F₃ F₂ F₄).differentiable
    (hg.prodMk_space hf)

nonrec theorem MDifferentiableAt.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄} {x : M}
    (hg : MDifferentiableAt I 𝓘(𝕜, F₁ →L[𝕜] F₃) g x)
    (hf : MDifferentiableAt I 𝓘(𝕜, F₂ →L[𝕜] F₄) f x) :
    MDifferentiableAt I 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₃ × F₄) (fun x => (g x).prodMap (f x)) x :=
  Differentiable.comp_mdifferentiableWithinAt
    (g := fun x : (F₁ →L[𝕜] F₃) × (F₂ →L[𝕜] F₄) => x.1.prodMap x.2)
    (f := fun x => (g x, f x)) (ContinuousLinearMap.prodMapL 𝕜 F₁ F₃ F₂ F₄).differentiable
    (hg.prodMk_space hf)

theorem MDifferentiableOn.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄} {s : Set M}
    (hg : MDifferentiableOn I 𝓘(𝕜, F₁ →L[𝕜] F₃) g s)
    (hf : MDifferentiableOn I 𝓘(𝕜, F₂ →L[𝕜] F₄) f s) :
    MDifferentiableOn I 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₃ × F₄) (fun x => (g x).prodMap (f x)) s := fun x hx =>
  (hg x hx).clm_prodMap (hf x hx)

theorem MDifferentiable.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄}
    (hg : MDifferentiable I 𝓘(𝕜, F₁ →L[𝕜] F₃) g) (hf : MDifferentiable I 𝓘(𝕜, F₂ →L[𝕜] F₄) f) :
    MDifferentiable I 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₃ × F₄) fun x => (g x).prodMap (f x) := fun x =>
  (hg x).clm_prodMap (hf x)

/-! ### Differentiability of scalar multiplication -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

theorem MDifferentiableWithinAt.smul {f : M → 𝕜} {g : M → V}
    (hf : MDifferentiableWithinAt I 𝓘(𝕜) f s x) (hg : MDifferentiableWithinAt I 𝓘(𝕜, V) g s x) :
    MDifferentiableWithinAt I 𝓘(𝕜, V) (fun p => f p • g p) s x :=
  ((contMDiff_smul.of_le le_top).mdifferentiable le_rfl _).comp_mdifferentiableWithinAt x
    (hf.prodMk hg)

theorem MDifferentiableAt.smul {f : M → 𝕜} {g : M → V} (hf : MDifferentiableAt I 𝓘(𝕜) f x)
    (hg : MDifferentiableAt I 𝓘(𝕜, V) g x) : MDifferentiableAt I 𝓘(𝕜, V) (fun p => f p • g p) x :=
  ((contMDiff_smul.of_le le_top).mdifferentiable le_rfl _).comp x (hf.prodMk hg)

theorem MDifferentiableOn.smul {f : M → 𝕜} {g : M → V} (hf : MDifferentiableOn I 𝓘(𝕜) f s)
    (hg : MDifferentiableOn I 𝓘(𝕜, V) g s) : MDifferentiableOn I 𝓘(𝕜, V) (fun p => f p • g p) s :=
  fun x hx => (hf x hx).smul (hg x hx)

theorem MDifferentiable.smul {f : M → 𝕜} {g : M → V} (hf : MDifferentiable I 𝓘(𝕜) f)
    (hg : MDifferentiable I 𝓘(𝕜, V) g) : MDifferentiable I 𝓘(𝕜, V) fun p => f p • g p := fun x =>
  (hf x).smul (hg x)
