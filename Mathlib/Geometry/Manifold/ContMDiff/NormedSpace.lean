/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Geometry.Manifold.ContMDiff.Product
import Mathlib.Analysis.NormedSpace.OperatorNorm.Prod

/-! ## Equivalence of smoothness with the basic definition for functions between vector spaces

* `contMDiff_iff_contDiff`: for functions between vector spaces,
  manifold-smoothness is equivalent to usual smoothness.
* `ContinuousLinearMap.contMDiff`: continuous linear maps between normed spaces are smooth
* `smooth_smul`: multiplication by scalars is a smooth operation

-/

open Set ChartedSpace SmoothManifoldWithCorners
open scoped Topology Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]
  -- declare a smooth manifold `M'` over the pair `(E', H')`.
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [SmoothManifoldWithCorners I' M']
  -- declare a smooth manifold `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [SmoothManifoldWithCorners J N]
  -- declare a smooth manifold `N'` over the pair `(F', G')`.
  {F' : Type*}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  [SmoothManifoldWithCorners J' N']
  -- F₁, F₂, F₃, F₄ are normed spaces
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {F₂ : Type*} [NormedAddCommGroup F₂]
  [NormedSpace 𝕜 F₂] {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] {F₄ : Type*}
  [NormedAddCommGroup F₄] [NormedSpace 𝕜 F₄]
  -- declare functions, sets, points and smoothness indices
  {f f₁ : M → M'} {s t : Set M} {x : M} {m n : ℕ∞}

section Module

theorem contMDiffWithinAt_iff_contDiffWithinAt {f : E → E'} {s : Set E} {x : E} :
    ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') n f s x ↔ ContDiffWithinAt 𝕜 n f s x := by
  simp (config := { contextual := true }) only [ContMDiffWithinAt, liftPropWithinAt_iff',
    ContDiffWithinAtProp, iff_def, mfld_simps]
  exact ContDiffWithinAt.continuousWithinAt
#align cont_mdiff_within_at_iff_cont_diff_within_at contMDiffWithinAt_iff_contDiffWithinAt

alias ⟨ContMDiffWithinAt.contDiffWithinAt, ContDiffWithinAt.contMDiffWithinAt⟩ :=
  contMDiffWithinAt_iff_contDiffWithinAt
#align cont_mdiff_within_at.cont_diff_within_at ContMDiffWithinAt.contDiffWithinAt
#align cont_diff_within_at.cont_mdiff_within_at ContDiffWithinAt.contMDiffWithinAt

theorem contMDiffAt_iff_contDiffAt {f : E → E'} {x : E} :
    ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E') n f x ↔ ContDiffAt 𝕜 n f x := by
  rw [← contMDiffWithinAt_univ, contMDiffWithinAt_iff_contDiffWithinAt, contDiffWithinAt_univ]
#align cont_mdiff_at_iff_cont_diff_at contMDiffAt_iff_contDiffAt

alias ⟨ContMDiffAt.contDiffAt, ContDiffAt.contMDiffAt⟩ := contMDiffAt_iff_contDiffAt
#align cont_mdiff_at.cont_diff_at ContMDiffAt.contDiffAt
#align cont_diff_at.cont_mdiff_at ContDiffAt.contMDiffAt

theorem contMDiffOn_iff_contDiffOn {f : E → E'} {s : Set E} :
    ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E') n f s ↔ ContDiffOn 𝕜 n f s :=
  forall_congr' <| by simp [contMDiffWithinAt_iff_contDiffWithinAt]
#align cont_mdiff_on_iff_cont_diff_on contMDiffOn_iff_contDiffOn

alias ⟨ContMDiffOn.contDiffOn, ContDiffOn.contMDiffOn⟩ := contMDiffOn_iff_contDiffOn
#align cont_mdiff_on.cont_diff_on ContMDiffOn.contDiffOn
#align cont_diff_on.cont_mdiff_on ContDiffOn.contMDiffOn

theorem contMDiff_iff_contDiff {f : E → E'} : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E') n f ↔ ContDiff 𝕜 n f := by
  rw [← contDiffOn_univ, ← contMDiffOn_univ, contMDiffOn_iff_contDiffOn]
#align cont_mdiff_iff_cont_diff contMDiff_iff_contDiff

alias ⟨ContMDiff.contDiff, ContDiff.contMDiff⟩ := contMDiff_iff_contDiff
#align cont_mdiff.cont_diff ContMDiff.contDiff
#align cont_diff.cont_mdiff ContDiff.contMDiff

theorem ContDiffWithinAt.comp_contMDiffWithinAt {g : F → F'} {f : M → F} {s : Set M} {t : Set F}
    {x : M} (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContMDiffWithinAt I 𝓘(𝕜, F) n f s x)
    (h : s ⊆ f ⁻¹' t) : ContMDiffWithinAt I 𝓘(𝕜, F') n (g ∘ f) s x :=
  hg.contMDiffWithinAt.comp x hf h
#align cont_diff_within_at.comp_cont_mdiff_within_at ContDiffWithinAt.comp_contMDiffWithinAt

theorem ContDiffAt.comp_contMDiffWithinAt {g : F → F'} {f : M → F} {s : Set M}
    {x : M} (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContMDiffWithinAt I 𝓘(𝕜, F) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, F') n (g ∘ f) s x :=
  hg.contMDiffAt.comp_contMDiffWithinAt x hf

theorem ContDiffAt.comp_contMDiffAt {g : F → F'} {f : M → F} {x : M} (hg : ContDiffAt 𝕜 n g (f x))
    (hf : ContMDiffAt I 𝓘(𝕜, F) n f x) : ContMDiffAt I 𝓘(𝕜, F') n (g ∘ f) x :=
  hg.comp_contMDiffWithinAt hf
#align cont_diff_at.comp_cont_mdiff_at ContDiffAt.comp_contMDiffAt

theorem ContDiff.comp_contMDiffWithinAt {g : F → F'} {f : M → F} {s : Set M} {x : M}
    (hg : ContDiff 𝕜 n g) (hf : ContMDiffWithinAt I 𝓘(𝕜, F) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, F') n (g ∘ f) s x :=
  hg.contDiffAt.comp_contMDiffWithinAt hf

theorem ContDiff.comp_contMDiffAt {g : F → F'} {f : M → F} {x : M} (hg : ContDiff 𝕜 n g)
    (hf : ContMDiffAt I 𝓘(𝕜, F) n f x) : ContMDiffAt I 𝓘(𝕜, F') n (g ∘ f) x :=
  hg.comp_contMDiffWithinAt hf

theorem ContDiff.comp_contMDiff {g : F → F'} {f : M → F} (hg : ContDiff 𝕜 n g)
    (hf : ContMDiff I 𝓘(𝕜, F) n f) : ContMDiff I 𝓘(𝕜, F') n (g ∘ f) := fun x =>
  hg.contDiffAt.comp_contMDiffAt (hf x)
#align cont_diff.comp_cont_mdiff ContDiff.comp_contMDiff

end Module

/-! ### Linear maps between normed spaces are smooth -/

theorem ContinuousLinearMap.contMDiff (L : E →L[𝕜] F) : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) n L :=
  L.contDiff.contMDiff
#align continuous_linear_map.cont_mdiff ContinuousLinearMap.contMDiff

theorem ContinuousLinearMap.contMDiffAt (L : E →L[𝕜] F) {x} : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, F) n L x :=
  L.contMDiff _

theorem ContinuousLinearMap.contMDiffWithinAt (L : E →L[𝕜] F) {s x} :
    ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, F) n L s x :=
  L.contMDiffAt.contMDiffWithinAt

theorem ContinuousLinearMap.contMDiffOn (L : E →L[𝕜] F) {s} : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, F) n L s :=
  L.contMDiff.contMDiffOn

theorem ContinuousLinearMap.smooth (L : E →L[𝕜] F) : Smooth 𝓘(𝕜, E) 𝓘(𝕜, F) L := L.contMDiff

theorem ContMDiffWithinAt.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁} {s : Set M} {x : M}
    (hg : ContMDiffWithinAt I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g s x)
    (hf : ContMDiffWithinAt I 𝓘(𝕜, F₂ →L[𝕜] F₁) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, F₂ →L[𝕜] F₃) n (fun x => (g x).comp (f x)) s x :=
  ContDiff.comp_contMDiffWithinAt (g := fun x : (F₁ →L[𝕜] F₃) × (F₂ →L[𝕜] F₁) => x.1.comp x.2)
    (f := fun x => (g x, f x)) (contDiff_fst.clm_comp contDiff_snd) (hg.prod_mk_space hf)
#align cont_mdiff_within_at.clm_comp ContMDiffWithinAt.clm_comp

theorem ContMDiffAt.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁} {x : M}
    (hg : ContMDiffAt I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g x) (hf : ContMDiffAt I 𝓘(𝕜, F₂ →L[𝕜] F₁) n f x) :
    ContMDiffAt I 𝓘(𝕜, F₂ →L[𝕜] F₃) n (fun x => (g x).comp (f x)) x :=
  (hg.contMDiffWithinAt.clm_comp hf.contMDiffWithinAt).contMDiffAt Filter.univ_mem
#align cont_mdiff_at.clm_comp ContMDiffAt.clm_comp

theorem ContMDiffOn.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁} {s : Set M}
    (hg : ContMDiffOn I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g s) (hf : ContMDiffOn I 𝓘(𝕜, F₂ →L[𝕜] F₁) n f s) :
    ContMDiffOn I 𝓘(𝕜, F₂ →L[𝕜] F₃) n (fun x => (g x).comp (f x)) s := fun x hx =>
  (hg x hx).clm_comp (hf x hx)
#align cont_mdiff_on.clm_comp ContMDiffOn.clm_comp

theorem ContMDiff.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁}
    (hg : ContMDiff I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g) (hf : ContMDiff I 𝓘(𝕜, F₂ →L[𝕜] F₁) n f) :
    ContMDiff I 𝓘(𝕜, F₂ →L[𝕜] F₃) n fun x => (g x).comp (f x) := fun x => (hg x).clm_comp (hf x)
#align cont_mdiff.clm_comp ContMDiff.clm_comp

theorem ContMDiffWithinAt.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {s : Set M} {x : M}
    (hg : ContMDiffWithinAt I 𝓘(𝕜, F₁ →L[𝕜] F₂) n g s x)
    (hf : ContMDiffWithinAt I 𝓘(𝕜, F₁) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, F₂) n (fun x => g x (f x)) s x :=
  @ContDiffWithinAt.comp_contMDiffWithinAt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun x : (F₁ →L[𝕜] F₂) × F₁ => x.1 x.2) (fun x => (g x, f x)) s _ x
    (by apply ContDiff.contDiffAt; exact contDiff_fst.clm_apply contDiff_snd) (hg.prod_mk_space hf)
    (by simp_rw [preimage_univ, subset_univ])
#align cont_mdiff_within_at.clm_apply ContMDiffWithinAt.clm_apply

nonrec theorem ContMDiffAt.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {x : M}
    (hg : ContMDiffAt I 𝓘(𝕜, F₁ →L[𝕜] F₂) n g x) (hf : ContMDiffAt I 𝓘(𝕜, F₁) n f x) :
    ContMDiffAt I 𝓘(𝕜, F₂) n (fun x => g x (f x)) x :=
  hg.clm_apply hf
#align cont_mdiff_at.clm_apply ContMDiffAt.clm_apply

theorem ContMDiffOn.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {s : Set M}
    (hg : ContMDiffOn I 𝓘(𝕜, F₁ →L[𝕜] F₂) n g s) (hf : ContMDiffOn I 𝓘(𝕜, F₁) n f s) :
    ContMDiffOn I 𝓘(𝕜, F₂) n (fun x => g x (f x)) s := fun x hx => (hg x hx).clm_apply (hf x hx)
#align cont_mdiff_on.clm_apply ContMDiffOn.clm_apply

theorem ContMDiff.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁}
    (hg : ContMDiff I 𝓘(𝕜, F₁ →L[𝕜] F₂) n g) (hf : ContMDiff I 𝓘(𝕜, F₁) n f) :
    ContMDiff I 𝓘(𝕜, F₂) n fun x => g x (f x) := fun x => (hg x).clm_apply (hf x)
#align cont_mdiff.clm_apply ContMDiff.clm_apply

theorem ContMDiffWithinAt.clm_precomp {f : M → F₁ →L[𝕜] F₂} {s : Set M} {x : M}
    (hf : ContMDiffWithinAt I 𝓘(𝕜, F₁ →L[𝕜] F₂) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) n
      (fun y ↦ (f y).precomp F₃ : M → (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) s x :=
  ContDiff.comp_contMDiffWithinAt (g := (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃).flip)
    (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃).flip.contDiff hf

nonrec theorem ContMDiffAt.clm_precomp {f : M → F₁ →L[𝕜] F₂} {x : M}
    (hf : ContMDiffAt I 𝓘(𝕜, F₁ →L[𝕜] F₂) n f x) :
    ContMDiffAt I 𝓘(𝕜, (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) n
      (fun y ↦ (f y).precomp F₃ : M → (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) x :=
  hf.clm_precomp

theorem ContMDiffOn.clm_precomp {f : M → F₁ →L[𝕜] F₂} {s : Set M}
    (hf : ContMDiffOn I 𝓘(𝕜, F₁ →L[𝕜] F₂) n f s) :
    ContMDiffOn I 𝓘(𝕜, (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) n
      (fun y ↦ (f y).precomp F₃ : M → (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) s := fun x hx ↦
  (hf x hx).clm_precomp

theorem ContMDiff.clm_precomp {f : M → F₁ →L[𝕜] F₂} (hf : ContMDiff I 𝓘(𝕜, F₁ →L[𝕜] F₂) n f) :
    ContMDiff I 𝓘(𝕜, (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) n
      (fun y ↦ (f y).precomp F₃ : M → (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) := fun x ↦
  (hf x).clm_precomp

theorem ContMDiffWithinAt.clm_postcomp {f : M → F₂ →L[𝕜] F₃} {s : Set M} {x : M}
    (hf : ContMDiffWithinAt I 𝓘(𝕜, F₂ →L[𝕜] F₃) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) n
      (fun y ↦ (f y).postcomp F₁ : M → (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) s x :=
  ContDiff.comp_contMDiffWithinAt (F' := (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃))
    (g := ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃) (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃).contDiff hf

nonrec theorem ContMDiffAt.clm_postcomp {f : M → F₂ →L[𝕜] F₃} {x : M}
    (hf : ContMDiffAt I 𝓘(𝕜, F₂ →L[𝕜] F₃) n f x) :
    ContMDiffAt I 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) n
      (fun y ↦ (f y).postcomp F₁ : M → (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) x :=
  hf.clm_postcomp

nonrec theorem ContMDiffOn.clm_postcomp {f : M → F₂ →L[𝕜] F₃} {s : Set M}
    (hf : ContMDiffOn I 𝓘(𝕜, F₂ →L[𝕜] F₃) n f s) :
    ContMDiffOn I 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) n
      (fun y ↦ (f y).postcomp F₁ : M → (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) s := fun x hx ↦
  (hf x hx).clm_postcomp

theorem ContMDiff.clm_postcomp {f : M → F₂ →L[𝕜] F₃} (hf : ContMDiff I 𝓘(𝕜, F₂ →L[𝕜] F₃) n f) :
    ContMDiff I 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) n
      (fun y ↦ (f y).postcomp F₁ : M → (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) := fun x ↦
  (hf x).clm_postcomp

theorem ContMDiffWithinAt.cle_arrowCongr {f : M → F₁ ≃L[𝕜] F₂} {g : M → F₃ ≃L[𝕜] F₄}
    {s : Set M} {x : M}
    (hf : ContMDiffWithinAt I 𝓘(𝕜, F₂ →L[𝕜] F₁) n (fun x ↦ ((f x).symm : F₂ →L[𝕜] F₁)) s x)
    (hg : ContMDiffWithinAt I 𝓘(𝕜, F₃ →L[𝕜] F₄) n (fun x ↦ (g x : F₃ →L[𝕜] F₄)) s x) :
    ContMDiffWithinAt I 𝓘(𝕜, (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) n
      (fun y ↦ (f y).arrowCongr (g y) : M → (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) s x :=
  show ContMDiffWithinAt I 𝓘(𝕜, (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) n
    (fun y ↦ (((f y).symm : F₂ →L[𝕜] F₁).precomp F₄).comp ((g y : F₃ →L[𝕜] F₄).postcomp F₁)) s x
  from hf.clm_precomp (F₃ := F₄) |>.clm_comp <| hg.clm_postcomp (F₁ := F₁)

nonrec theorem ContMDiffAt.cle_arrowCongr {f : M → F₁ ≃L[𝕜] F₂} {g : M → F₃ ≃L[𝕜] F₄} {x : M}
    (hf : ContMDiffAt I 𝓘(𝕜, F₂ →L[𝕜] F₁) n (fun x ↦ ((f x).symm : F₂ →L[𝕜] F₁)) x)
    (hg : ContMDiffAt I 𝓘(𝕜, F₃ →L[𝕜] F₄) n (fun x ↦ (g x : F₃ →L[𝕜] F₄)) x) :
    ContMDiffAt I 𝓘(𝕜, (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) n
      (fun y ↦ (f y).arrowCongr (g y) : M → (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) x :=
  hf.cle_arrowCongr hg

theorem ContMDiffOn.cle_arrowCongr {f : M → F₁ ≃L[𝕜] F₂} {g : M → F₃ ≃L[𝕜] F₄} {s : Set M}
    (hf : ContMDiffOn I 𝓘(𝕜, F₂ →L[𝕜] F₁) n (fun x ↦ ((f x).symm : F₂ →L[𝕜] F₁)) s)
    (hg : ContMDiffOn I 𝓘(𝕜, F₃ →L[𝕜] F₄) n (fun x ↦ (g x : F₃ →L[𝕜] F₄)) s) :
    ContMDiffOn I 𝓘(𝕜, (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) n
      (fun y ↦ (f y).arrowCongr (g y) : M → (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) s := fun x hx ↦
  (hf x hx).cle_arrowCongr (hg x hx)

theorem ContMDiff.cle_arrowCongr {f : M → F₁ ≃L[𝕜] F₂} {g : M → F₃ ≃L[𝕜] F₄}
    (hf : ContMDiff I 𝓘(𝕜, F₂ →L[𝕜] F₁) n (fun x ↦ ((f x).symm : F₂ →L[𝕜] F₁)))
    (hg : ContMDiff I 𝓘(𝕜, F₃ →L[𝕜] F₄) n (fun x ↦ (g x : F₃ →L[𝕜] F₄))) :
    ContMDiff I 𝓘(𝕜, (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) n
      (fun y ↦ (f y).arrowCongr (g y) : M → (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) := fun x ↦
  (hf x).cle_arrowCongr (hg x)

theorem ContMDiffWithinAt.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄} {s : Set M}
    {x : M} (hg : ContMDiffWithinAt I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g s x)
    (hf : ContMDiffWithinAt I 𝓘(𝕜, F₂ →L[𝕜] F₄) n f s x) :
    ContMDiffWithinAt I 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₃ × F₄) n (fun x => (g x).prodMap (f x)) s x :=
  ContDiff.comp_contMDiffWithinAt (g := fun x : (F₁ →L[𝕜] F₃) × (F₂ →L[𝕜] F₄) => x.1.prodMap x.2)
    (f := fun x => (g x, f x)) (ContinuousLinearMap.prodMapL 𝕜 F₁ F₃ F₂ F₄).contDiff
    (hg.prod_mk_space hf)
#align cont_mdiff_within_at.clm_prod_map ContMDiffWithinAt.clm_prodMap

nonrec theorem ContMDiffAt.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄} {x : M}
    (hg : ContMDiffAt I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g x) (hf : ContMDiffAt I 𝓘(𝕜, F₂ →L[𝕜] F₄) n f x) :
    ContMDiffAt I 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₃ × F₄) n (fun x => (g x).prodMap (f x)) x :=
  hg.clm_prodMap hf
#align cont_mdiff_at.clm_prod_map ContMDiffAt.clm_prodMap

theorem ContMDiffOn.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄} {s : Set M}
    (hg : ContMDiffOn I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g s) (hf : ContMDiffOn I 𝓘(𝕜, F₂ →L[𝕜] F₄) n f s) :
    ContMDiffOn I 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₃ × F₄) n (fun x => (g x).prodMap (f x)) s := fun x hx =>
  (hg x hx).clm_prodMap (hf x hx)
#align cont_mdiff_on.clm_prod_map ContMDiffOn.clm_prodMap

theorem ContMDiff.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄}
    (hg : ContMDiff I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g) (hf : ContMDiff I 𝓘(𝕜, F₂ →L[𝕜] F₄) n f) :
    ContMDiff I 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₃ × F₄) n fun x => (g x).prodMap (f x) := fun x =>
  (hg x).clm_prodMap (hf x)
#align cont_mdiff.clm_prod_map ContMDiff.clm_prodMap

/-! ### Smoothness of scalar multiplication -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- On any vector space, multiplication by a scalar is a smooth operation. -/
theorem smooth_smul : Smooth (𝓘(𝕜).prod 𝓘(𝕜, V)) 𝓘(𝕜, V) fun p : 𝕜 × V => p.1 • p.2 :=
  smooth_iff.2 ⟨continuous_smul, fun _ _ => contDiff_smul.contDiffOn⟩
#align smooth_smul smooth_smul

theorem ContMDiffWithinAt.smul {f : M → 𝕜} {g : M → V} (hf : ContMDiffWithinAt I 𝓘(𝕜) n f s x)
    (hg : ContMDiffWithinAt I 𝓘(𝕜, V) n g s x) :
    ContMDiffWithinAt I 𝓘(𝕜, V) n (fun p => f p • g p) s x :=
  (smooth_smul.of_le le_top).contMDiffAt.comp_contMDiffWithinAt x (hf.prod_mk hg)
#align cont_mdiff_within_at.smul ContMDiffWithinAt.smul

nonrec theorem ContMDiffAt.smul {f : M → 𝕜} {g : M → V} (hf : ContMDiffAt I 𝓘(𝕜) n f x)
    (hg : ContMDiffAt I 𝓘(𝕜, V) n g x) : ContMDiffAt I 𝓘(𝕜, V) n (fun p => f p • g p) x :=
  hf.smul hg
#align cont_mdiff_at.smul ContMDiffAt.smul

theorem ContMDiffOn.smul {f : M → 𝕜} {g : M → V} (hf : ContMDiffOn I 𝓘(𝕜) n f s)
    (hg : ContMDiffOn I 𝓘(𝕜, V) n g s) : ContMDiffOn I 𝓘(𝕜, V) n (fun p => f p • g p) s :=
  fun x hx => (hf x hx).smul (hg x hx)
#align cont_mdiff_on.smul ContMDiffOn.smul

theorem ContMDiff.smul {f : M → 𝕜} {g : M → V} (hf : ContMDiff I 𝓘(𝕜) n f)
    (hg : ContMDiff I 𝓘(𝕜, V) n g) : ContMDiff I 𝓘(𝕜, V) n fun p => f p • g p := fun x =>
  (hf x).smul (hg x)
#align cont_mdiff.smul ContMDiff.smul

nonrec theorem SmoothWithinAt.smul {f : M → 𝕜} {g : M → V} (hf : SmoothWithinAt I 𝓘(𝕜) f s x)
    (hg : SmoothWithinAt I 𝓘(𝕜, V) g s x) : SmoothWithinAt I 𝓘(𝕜, V) (fun p => f p • g p) s x :=
  hf.smul hg
#align smooth_within_at.smul SmoothWithinAt.smul

nonrec theorem SmoothAt.smul {f : M → 𝕜} {g : M → V} (hf : SmoothAt I 𝓘(𝕜) f x)
    (hg : SmoothAt I 𝓘(𝕜, V) g x) : SmoothAt I 𝓘(𝕜, V) (fun p => f p • g p) x :=
  hf.smul hg
#align smooth_at.smul SmoothAt.smul

nonrec theorem SmoothOn.smul {f : M → 𝕜} {g : M → V} (hf : SmoothOn I 𝓘(𝕜) f s)
    (hg : SmoothOn I 𝓘(𝕜, V) g s) : SmoothOn I 𝓘(𝕜, V) (fun p => f p • g p) s :=
  hf.smul hg
#align smooth_on.smul SmoothOn.smul

nonrec theorem Smooth.smul {f : M → 𝕜} {g : M → V} (hf : Smooth I 𝓘(𝕜) f)
    (hg : Smooth I 𝓘(𝕜, V) g) : Smooth I 𝓘(𝕜, V) fun p => f p • g p :=
  hf.smul hg
#align smooth.smul Smooth.smul
