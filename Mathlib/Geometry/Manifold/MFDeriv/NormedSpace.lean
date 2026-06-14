/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! ## Equivalence of manifold differentiability with the basic definition for functions between
vector spaces

The API in this file is mostly copied from `Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean`,
providing the same statements for higher smoothness. In this file, we do the same for
differentiability.

In addition to the above, this file provides
* `mvfderiv`: the exterior derivative of a vector-valued function, as a section of the
  cotangent bundle; adds notation `d% f` for `mvfderiv I f` via a custom elaborator scoped to the
  `Manifold` namespace, with a corresponding delaborator, and
  adds basic lemmas about `mvfderiv` (such as addition, subtraction, multiplication and constants).
* `mvfderivWithin` with notation `d[s]f` for `mvfderivWithin I f s` in the `Manifold` namespace:
  the analogous concept within a set, with analogous API lemmas
* results about the differentiability of scalar multiplication (`mvfderiv_smul` and friends),

-/

public section

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
    {g : F → F'} {f : M → F} {s : Set M} {t : Set F} {x : M}
    (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : MDiffAt[s] f x) (h : MapsTo f s t) :
    MDiffAt[s] (g ∘ f) x :=
  hg.mdifferentiableWithinAt.comp x hf h

theorem DifferentiableAt.comp_mdifferentiableWithinAt {g : F → F'} {f : M → F} {s : Set M} {x : M}
    (hg : DifferentiableAt 𝕜 g (f x)) (hf : MDiffAt[s] f x) : MDiffAt[s] (g ∘ f) x :=
  hg.mdifferentiableAt.comp_mdifferentiableWithinAt x hf

theorem DifferentiableAt.comp_mdifferentiableAt {g : F → F'} {f : M → F} {x : M}
    (hg : DifferentiableAt 𝕜 g (f x)) (hf : MDiffAt f x) : MDiffAt (g ∘ f) x :=
  hg.comp_mdifferentiableWithinAt hf

theorem Differentiable.comp_mdifferentiableWithinAt {g : F → F'} {f : M → F} {s : Set M} {x : M}
    (hg : Differentiable 𝕜 g) (hf : MDiffAt[s] f x) : MDiffAt[s] (g ∘ f) x :=
  hg.differentiableAt.comp_mdifferentiableWithinAt hf

theorem Differentiable.comp_mdifferentiableAt {g : F → F'} {f : M → F} {x : M}
    (hg : Differentiable 𝕜 g) (hf : MDiffAt f x) : MDiffAt (g ∘ f) x :=
  hg.comp_mdifferentiableWithinAt hf

theorem Differentiable.comp_mdifferentiable {g : F → F'} {f : M → F}
    (hg : Differentiable 𝕜 g) (hf : MDiff f) : MDiff (g ∘ f) :=
  fun x ↦ hg.differentiableAt.comp_mdifferentiableAt (hf x)

end Module

section extChartAt

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : M → F}

-- TODO: add pre-composition version also
theorem MDifferentiableWithinAt.differentiableWithinAt_comp_extChartAt_symm (hf : MDiffAt[s] f x) :
    letI φ := extChartAt I x
    DifferentiableWithinAt 𝕜 (f ∘ φ.symm) (φ.symm ⁻¹' s ∩ range I) (φ x) := by
  simpa [extChartAt_self_eq] using (mdifferentiableWithinAt_iff.1 hf).2

-- TODO: the `IsManifold I 1 M` assumption can probably be removed
theorem DifferentiableWithinAt.mdifferentiableWithinAt_of_comp_extChartAt_symm [IsManifold I 1 M]
    (hf : letI φ := extChartAt I x
      DifferentiableWithinAt 𝕜 (f ∘ φ.symm) (φ.symm ⁻¹' s ∩ range I) (φ x)) :
    MDiffAt[s] f x := by
  refine (mdifferentiableWithinAt_iff_source_of_mem_source (mem_chart_source H x)).2 ?_
  simpa [extChartAt_self_eq] using hf.mdifferentiableWithinAt

end extChartAt

/-! ### Linear maps between normed spaces are differentiable -/

theorem MDifferentiableWithinAt.clm_precomp {f : M → F₁ →L[𝕜] F₂} {s : Set M} {x : M}
    (hf : MDiffAt[s] f x) :
    MDiffAt[s] (fun y ↦ (f y).precomp F₃ : M → (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) x :=
  Differentiable.comp_mdifferentiableWithinAt
    (ContinuousLinearMap.differentiable (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃).flip) hf

nonrec theorem MDifferentiableAt.clm_precomp {f : M → F₁ →L[𝕜] F₂} {x : M} (hf : MDiffAt f x) :
    MDiffAt (fun y ↦ (f y).precomp F₃ : M → (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) x :=
  Differentiable.comp_mdifferentiableAt
    (ContinuousLinearMap.differentiable (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃).flip) hf

theorem MDifferentiableOn.clm_precomp {f : M → F₁ →L[𝕜] F₂} {s : Set M} (hf : MDiff[s] f) :
    MDiff[s] (fun y ↦ (f y).precomp F₃ : M → (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) :=
  fun x hx ↦ (hf x hx).clm_precomp

theorem MDifferentiable.clm_precomp {f : M → F₁ →L[𝕜] F₂} (hf : MDiff f) :
    MDiff (fun y ↦ (f y).precomp F₃ : M → (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) :=
  fun x ↦ (hf x).clm_precomp

theorem MDifferentiableWithinAt.clm_postcomp {f : M → F₂ →L[𝕜] F₃} {s : Set M} {x : M}
    (hf : MDiffAt[s] f x) :
    MDiffAt[s] (fun y ↦ (f y).postcomp F₁ : M → (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) x :=
  Differentiable.comp_mdifferentiableWithinAt
    (ContinuousLinearMap.differentiable (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃)) hf

theorem MDifferentiableAt.clm_postcomp {f : M → F₂ →L[𝕜] F₃} {x : M} (hf : MDiffAt f x) :
    MDiffAt (fun y ↦ (f y).postcomp F₁ : M → (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) x :=
  Differentiable.comp_mdifferentiableAt
    (ContinuousLinearMap.differentiable (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃)) hf

nonrec theorem MDifferentiableOn.clm_postcomp {f : M → F₂ →L[𝕜] F₃} {s : Set M} (hf : MDiff[s] f) :
    MDiff[s] (fun y ↦ (f y).postcomp F₁ : M → (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) := fun x hx ↦
  (hf x hx).clm_postcomp

theorem MDifferentiable.clm_postcomp {f : M → F₂ →L[𝕜] F₃} (hf : MDiff f) :
    MDiff (fun y ↦ (f y).postcomp F₁ : M → (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) :=
  fun x ↦ (hf x).clm_postcomp

theorem MDifferentiableWithinAt.clm_comp
    {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁} {s : Set M} {x : M}
    (hg : MDiffAt[s] g x) (hf : MDiffAt[s] f x) :
    MDiffAt[s] (fun x ↦ (g x).comp (f x)) x :=
  Differentiable.comp_mdifferentiableWithinAt
    (g := fun x : (F₁ →L[𝕜] F₃) × (F₂ →L[𝕜] F₁) => x.1.comp x.2)
    (f := fun x => (g x, f x)) (differentiable_fst.clm_comp differentiable_snd)
    (hg.prodMk_space hf)

theorem MDifferentiableAt.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁} {x : M}
    (hg : MDiffAt g x) (hf : MDiffAt f x) :
    MDiffAt (fun x ↦ (g x).comp (f x)) x :=
  (hg.mdifferentiableWithinAt.clm_comp hf.mdifferentiableWithinAt).mdifferentiableAt Filter.univ_mem

theorem MDifferentiableOn.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁} {s : Set M}
    (hg : MDiff[s] g) (hf : MDiff[s] f) : MDiff[s] (fun x ↦ (g x).comp (f x)) :=
  fun x hx ↦ (hg x hx).clm_comp (hf x hx)

theorem MDifferentiable.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁}
    (hg : MDiff g) (hf : MDiff f) : MDiff fun x ↦ (g x).comp (f x) :=
  fun x ↦ (hg x).clm_comp (hf x)

/-- Applying a linear map to a vector is differentiable within a set. Version in vector spaces. For
a version in nontrivial vector bundles, see `MDifferentiableWithinAt.clm_apply_of_inCoordinates`. -/
theorem MDifferentiableWithinAt.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {s : Set M} {x : M}
    (hg : MDiffAt[s] g x) (hf : MDiffAt[s] f x) :
    MDiffAt[s] (fun x ↦ g x (f x)) x :=
  DifferentiableWithinAt.comp_mdifferentiableWithinAt (t := univ)
    (g := fun x : (F₁ →L[𝕜] F₂) × F₁ ↦ x.1 x.2)
    (by apply (Differentiable.differentiableAt _).differentiableWithinAt
        exact differentiable_fst.clm_apply differentiable_snd) (hg.prodMk_space hf)
    (by simp_rw [mapsTo_univ])

/-- Applying a linear map to a vector is differentiable. Version in vector spaces. For a
version in nontrivial vector bundles, see `MDifferentiableAt.clm_apply_of_inCoordinates`. -/
theorem MDifferentiableAt.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {x : M}
    (hg : MDiffAt g x) (hf : MDiffAt f x) : MDiffAt (fun x ↦ g x (f x)) x :=
  DifferentiableWithinAt.comp_mdifferentiableWithinAt (t := univ)
    (g := fun x : (F₁ →L[𝕜] F₂) × F₁ => x.1 x.2)
    (by apply (Differentiable.differentiableAt _).differentiableWithinAt
        exact differentiable_fst.clm_apply differentiable_snd) (hg.prodMk_space hf)
    (by simp_rw [mapsTo_univ])

theorem MDifferentiableOn.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {s : Set M}
    (hg : MDiff[s] g) (hf : MDiff[s] f) : MDiff[s] (fun x ↦ g x (f x)) :=
  fun x hx ↦ (hg x hx).clm_apply (hf x hx)

theorem MDifferentiable.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁}
    (hg : MDiff g) (hf : MDiff f) : MDiff fun x ↦ g x (f x) :=
  fun x ↦ (hg x).clm_apply (hf x)

theorem MDifferentiableWithinAt.cle_arrowCongr
    {f : M → F₁ ≃L[𝕜] F₂} {g : M → F₃ ≃L[𝕜] F₄} {s : Set M} {x : M}
    (hf : MDiffAt[s] (fun x ↦ ((f x).symm : F₂ →L[𝕜] F₁)) x)
    (hg : MDiffAt[s] (fun x ↦ (g x : F₃ →L[𝕜] F₄)) x) :
    MDiffAt[s] (fun y ↦ (f y).arrowCongr (g y) : M → (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) x :=
  show MDifferentiableWithinAt I 𝓘(𝕜, (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄))
    (fun y ↦ (((f y).symm : F₂ →L[𝕜] F₁).precomp F₄).comp ((g y : F₃ →L[𝕜] F₄).postcomp F₁)) s x
  from hf.clm_precomp (F₃ := F₄) |>.clm_comp <| hg.clm_postcomp (F₁ := F₁)

theorem MDifferentiableAt.cle_arrowCongr {f : M → F₁ ≃L[𝕜] F₂} {g : M → F₃ ≃L[𝕜] F₄} {x : M}
    (hf : MDiffAt (fun x ↦ ((f x).symm : F₂ →L[𝕜] F₁)) x)
    (hg : MDiffAt (fun x ↦ (g x : F₃ →L[𝕜] F₄)) x) :
    MDiffAt (fun y ↦ (f y).arrowCongr (g y) : M → (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) x :=
  show MDifferentiableAt I 𝓘(𝕜, (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄))
    (fun y ↦ (((f y).symm : F₂ →L[𝕜] F₁).precomp F₄).comp ((g y : F₃ →L[𝕜] F₄).postcomp F₁)) x
  from hf.clm_precomp (F₃ := F₄) |>.clm_comp <| hg.clm_postcomp (F₁ := F₁)

theorem MDifferentiableOn.cle_arrowCongr {f : M → F₁ ≃L[𝕜] F₂} {g : M → F₃ ≃L[𝕜] F₄} {s : Set M}
    (hf : MDiff[s] (fun x ↦ ((f x).symm : F₂ →L[𝕜] F₁)))
    (hg : MDiff[s] (fun x ↦ (g x : F₃ →L[𝕜] F₄))) :
    MDiff[s] (fun y ↦ (f y).arrowCongr (g y) : M → (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) := fun x hx ↦
  (hf x hx).cle_arrowCongr (hg x hx)

theorem MDifferentiable.cle_arrowCongr {f : M → F₁ ≃L[𝕜] F₂} {g : M → F₃ ≃L[𝕜] F₄}
    (hf : MDiff (fun x ↦ ((f x).symm : F₂ →L[𝕜] F₁)))
    (hg : MDiff (fun x ↦ (g x : F₃ →L[𝕜] F₄))) :
    MDiff (fun y ↦ (f y).arrowCongr (g y) : M → (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) := fun x ↦
  (hf x).cle_arrowCongr (hg x)

theorem MDifferentiableWithinAt.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄} {s : Set M}
    {x : M} (hg : MDiffAt[s] g x) (hf : MDiffAt[s] f x) :
    MDiffAt[s] (fun x ↦ (g x).prodMap (f x)) x :=
  Differentiable.comp_mdifferentiableWithinAt
    (g := fun x : (F₁ →L[𝕜] F₃) × (F₂ →L[𝕜] F₄) => x.1.prodMap x.2)
    (f := fun x => (g x, f x)) (ContinuousLinearMap.prodMapL 𝕜 F₁ F₃ F₂ F₄).differentiable
    (hg.prodMk_space hf)

nonrec theorem MDifferentiableAt.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄} {x : M}
    (hg : MDiffAt g x) (hf : MDiffAt f x) : MDiffAt (fun x ↦ (g x).prodMap (f x)) x :=
  Differentiable.comp_mdifferentiableWithinAt
    (g := fun x : (F₁ →L[𝕜] F₃) × (F₂ →L[𝕜] F₄) => x.1.prodMap x.2)
    (f := fun x => (g x, f x)) (ContinuousLinearMap.prodMapL 𝕜 F₁ F₃ F₂ F₄).differentiable
    (hg.prodMk_space hf)

theorem MDifferentiableOn.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄} {s : Set M}
    (hg : MDiff[s] g) (hf : MDiff[s] f) :
    MDiff[s] (fun x ↦ (g x).prodMap (f x)) :=
  fun x hx ↦ (hg x hx).clm_prodMap (hf x hx)

theorem MDifferentiable.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄}
    (hg : MDiff g) (hf : MDiff f) : MDiff fun x ↦ (g x).prodMap (f x) :=
  fun x ↦ (hg x).clm_prodMap (hf x)

/-! ### Differentiability of scalar multiplication -/

section smul

open NormedSpace ContinuousLinearMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {f : M → 𝕜} {g : M → V}

theorem MDifferentiableWithinAt.smul
    (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x) :
    MDiffAt[s] (fun p ↦ f p • g p) x :=
  ((contMDiff_smul.of_le le_top).mdifferentiable one_ne_zero _).comp_mdifferentiableWithinAt x
    (hf.prodMk hg)

theorem MDifferentiableAt.smul (hf : MDiffAt f x)
    (hg : MDiffAt g x) : MDiffAt (fun p ↦ f p • g p) x :=
  ((contMDiff_smul.of_le le_top).mdifferentiable one_ne_zero _).comp x (hf.prodMk hg)

theorem MDifferentiableOn.smul (hf : MDiff[s] f)
    (hg : MDiff[s] g) : MDiff[s] (fun p ↦ f p • g p) :=
  fun x hx ↦ (hf x hx).smul (hg x hx)

theorem MDifferentiable.smul (hf : MDiff f) (hg : MDiff g) : MDiff fun p ↦ f p • g p :=
  fun x ↦ (hf x).smul (hg x)

end smul

/-! ### Exterior derivative of a vector-valued function -/

variable (I) in
/-- `mvfderiv I J f x` is the exterior derivative of a vector-valued function `g` on `M`,
as a section of the cotangent bundle.

Future: this could be generalised to functions into additive torsors over abelian Lie groups.
-/
@[expose]
noncomputable def mvfderivWithin (g : M → F) (s : Set M) :
    Π x : M, TangentSpace I x →L[𝕜] F :=
  fun x ↦ (NormedSpace.fromTangentSpace <| g x).toContinuousLinearMap ∘L (mfderiv[s] g x)

variable (I) in
/-- The exterior derivative of a vector-valued function on `M`,
as a section of the cotangent bundle.

Future: this could be generalised to functions into additive torsors over abelian Lie groups.
-/
@[expose]
noncomputable def mvfderiv (g : M → F) :
    Π x : M, TangentSpace I x →L[𝕜] F :=
  fun x ↦ (NormedSpace.fromTangentSpace <| g x).toContinuousLinearMap ∘L (mfderiv% g x)
@[deprecated (since := "2026-05-17")] alias extDerivFun := mvfderiv

namespace Manifold
open scoped Bundle Manifold ContDiff

open Lean Meta Elab Tactic

/-- `d[s] f x` (scoped to the `Manifold` namespace) elaborates to `mvfderivWithin I J f s x`,
trying to determine `I` and `J` from the local context. -/
scoped elab:max "d[" s:term "]" ppSpace t:term:arg : term => do
  let es ← Term.elabTerm s none
  let e ← ensureIsFunction <| ← Term.elabTerm t none
  let (srcI, _tgtI) ← findModels e none
  mkAppM ``mvfderivWithin #[srcI, e, es]

/-- `d% f x` (scoped to the `Manifold` namespace) elaborates to `mvfderiv I J f x`,
trying to determine `I` and `J` from the local context. -/
scoped elab:max "d%" ppSpace t:term:arg : term => do
  let e ← ensureIsFunction <| ← Term.elabTerm t none
  let (srcI, _tgtI) ← findModels e none
  mkAppM ``mvfderiv #[srcI, e]

open Bundle PrettyPrinter Delaborator SubExpr

/-- Delaborator for `mvfderivWithin`. -/
-- There is no need to special-case any arguments which could use the `T%` elaborator:
-- the argument to `mvfderivWithin` is a vector-valued function, which a map to a total space
-- can never be.
@[app_delab mvfderivWithin] meta def delabMVFDerivWithin : Delab := do
  whenPPOption getPPNotation do
  withOverApp 16 do
  let ss ← withAppArg delab
  let fs ← withNaryArg 14 <| delab
  `(d[$ss] $fs) >>= annotateGoToSyntaxDef

/-- Delaborator for `mvfderiv`. -/
-- There is no need to special-case any arguments which could use the `T%` elaborator:
-- the argument to `mvfderiv` is a vector-valued function, which a map to a total space
-- can never be.
@[app_delab mvfderiv] meta def delabMVFDeriv : Delab := do
  whenPPOption getPPNotation do
  withOverApp 15 do
  let fs ← withAppArg delab
  `(d% $fs) >>= annotateGoToSyntaxDef

end Manifold

@[simp, mfld_simps] lemma mvfderivWithin_univ {f : M → F} : d[(univ : Set M)] f = d% f := by
  ext X
  simp [mvfderiv, mvfderivWithin]

lemma mvfderivWithin_const (c : F) {x : M} : d[s] (fun _ : M ↦ c) x = 0 := by
  simp [mvfderivWithin, mfderivWithin_const]

@[simp, to_fun mvfderivWithin_fun_add]
lemma mvfderivWithin_add {g g' : M → F} {x : M}
    (hg : MDiffAt[s] g x) (hg' : MDiffAt[s] g' x) (hs : UniqueMDiffWithinAt I s x) :
    d[s](g + g') x = d[s]g x + d[s]g' x := by
  simp [mvfderivWithin, (hg.hasMFDerivWithinAt.add hg'.hasMFDerivWithinAt).mfderivWithin hs]
  rfl

@[simp, to_fun mvfderivWithin_fun_sub]
lemma mvfderivWithin_sub {g g' : M → F} {x : M}
    (hg : MDiffAt[s] g x) (hg' : MDiffAt[s] g' x) (hs : UniqueMDiffWithinAt I s x) :
    d[s](g - g') x = d[s]g x - d[s]g' x := by
  simp [mvfderivWithin, (hg.hasMFDerivWithinAt.sub hg'.hasMFDerivWithinAt).mfderivWithin hs]
  rfl

@[simp, to_fun mvfderivWithin_fun_neg]
lemma mvfderivWithin_neg {g : M → F} {x : M} (hs : UniqueMDiffWithinAt I s x) :
    d[s](-g) x = -d[s]g x := by
  simp only [mvfderivWithin, mfderivWithin]
  by_cases hg : MDiffAt[s] g x
  · exact hg.hasMFDerivWithinAt.neg.mfderivWithin hs
  · rw [if_neg hg]; rw [← mdifferentiableWithinAt_neg] at hg; simp [if_neg hg]

@[simp, to_fun mvfderivWithin_fun_smul]
lemma mvfderivWithin_smul {a : M → 𝕜} (ha : MDiffAt[s] a x) {g : M → F} (hg : MDiffAt[s] g x)
    (hs : UniqueMDiffWithinAt I s x) :
    d[s](a • g) x = a x • d[s] g x + (d[s] a x).smulRight (g x) := by
  refine HasMFDerivWithinAt.mfderivWithin ⟨ha.1.smul hg.1, ?_⟩ hs
  convert! ha.hasMFDerivWithinAt.2.smul hg.hasMFDerivWithinAt.2
  simp
  rfl

@[simp, to_fun mvfderivWithin_fun_mul]
lemma mvfderivWithin_mul {f g : M → 𝕜} {x : M} (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x)
    (hs : UniqueMDiffWithinAt I s x) :
    d[s](f * g) x = f x • d[s]g x + (g x) • (d[s]f x) := by
  convert! mvfderivWithin_smul hf hg hs
  ext v
  simp [mul_comm]

@[simp]
lemma mvfderivWithin_zero {s : Set M} (hs : UniqueMDiffWithinAt I s x) :
    d[s] (0 : M → F) x = 0 := by
  have : d[s] (0 : M → F) x + d[s] (0 : M → F) x = d[s] (0 : M → F) x := by
    rw [← mvfderivWithin_add (by exact mdifferentiableWithinAt_const)
      (by exact mdifferentiableWithinAt_const) hs]
    simp
  simpa using this

lemma mvfderiv_const (c : F) {x : M} : d% (fun _ : M ↦ c) x = 0 := by
  simp [mvfderiv, mfderiv_const]

@[simp, to_fun mvfderiv_fun_add]
lemma mvfderiv_add {g g' : M → F} {x : M} (hg : MDiffAt g x) (hg' : MDiffAt g' x) :
    d% (g + g') x = d% g x + d% g' x := by
  rw [← mdifferentiableWithinAt_univ] at hg hg'
  simp_rw [← mvfderivWithin_univ, mvfderivWithin_add hg hg' (uniqueMDiffWithinAt_univ I)]

@[deprecated (since := "2026-05-17")] alias extDerivFun_add := mvfderiv_add

@[simp, to_fun mvfderiv_fun_sub]
lemma mvfderiv_sub {g g' : M → F} {x : M} (hg : MDiffAt g x) (hg' : MDiffAt g' x) :
    d% (g - g') x = d% g x - d% g' x := by
  rw [← mdifferentiableWithinAt_univ] at hg hg'
  simp_rw [← mvfderivWithin_univ, mvfderivWithin_sub hg hg' (uniqueMDiffWithinAt_univ I)]

@[simp, to_fun mvfderiv_fun_neg]
lemma mvfderiv_neg {g : M → F} {x : M} :
    d% (-g) x = -d% g x := by
  simp_rw [← mvfderivWithin_univ, mvfderivWithin_neg (uniqueMDiffWithinAt_univ I)]

@[simp, to_fun mvfderiv_fun_smul]
lemma mvfderiv_smul {x : M} {a : M → 𝕜} (ha : MDiffAt a x) {g : M → F} (hg : MDiffAt g x) :
    d% (a • g) x = a x • d% g x + (d% a x).smulRight (g x) := by
  rw [← mdifferentiableWithinAt_univ] at ha hg
  simp_rw [← mvfderivWithin_univ, mvfderivWithin_smul ha hg (uniqueMDiffWithinAt_univ I)]

@[simp, to_fun mvfderiv_fun_mul]
lemma mvfderiv_mul {f g : M → 𝕜} {x : M} (hf : MDiffAt f x) (hg : MDiffAt g x) :
    d% (f * g) x = f x • d% g x + (g x) • (d% f x) := by
  rw [← mdifferentiableWithinAt_univ] at hf hg
  simp_rw [← mvfderivWithin_univ, mvfderivWithin_mul hf hg (uniqueMDiffWithinAt_univ I)]

@[simp]
lemma mvfderiv_zero {x : M} : d% (0 : M → F) x = 0 := by
  rw [← mvfderivWithin_univ]
  exact mvfderivWithin_zero (uniqueMDiffWithinAt_univ I)
@[deprecated (since := "2026-05-17")] alias extDerivFun_zero := mvfderiv_zero

section deprecated

variable {f g : M → E'} {z : M}

@[deprecated mvfderiv_add
  "this lemma abuses the identification of E with its tangent space: use mvfderiv instead"
  (since := "2026-05-31")]
theorem mfderiv_add (hf : MDiffAt f z) (hg : MDiffAt g z) :
    (mfderiv% (f + g) z : TangentSpace I z →L[𝕜] E') =
      (by exact mfderiv% f z) + (by exact mfderiv% g z) :=
  (hf.hasMFDerivAt.add hg.hasMFDerivAt).mfderiv

@[deprecated mvfderivWithin_add
  "this lemma abuses the identification of E with its tangent space: use mvfderivWithin instead"
  (since := "2026-05-31")]
theorem mfderivWithin_add (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z)
    (hs : UniqueMDiffWithinAt I s z) :
    (mfderiv[s] (f + g) z : TangentSpace I z →L[𝕜] E') =
      (by exact mfderiv[s] f z) + (by exact mfderiv[s] g z) :=
  (hf.hasMFDerivWithinAt.add hg.hasMFDerivWithinAt).mfderivWithin hs

@[deprecated mvfderivWithin_sub
  "this lemma abuses the identification of E with its tangent space: use mvfderivWithin instead"
  (since := "2026-05-31")]
theorem mfderivWithin_sub (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z)
    (hs : UniqueMDiffWithinAt I s z) :
    (mfderiv[s] (f - g) z : TangentSpace I z →L[𝕜] E') =
      (by exact mfderiv[s] f z) - (by exact mfderiv[s] g z) :=
  (hf.hasMFDerivWithinAt.sub hg.hasMFDerivWithinAt).mfderivWithin hs

@[deprecated mvfderiv_sub
  "this lemma abuses the identification of E with its tangent space: use mvfderivWithin instead"
  (since := "2026-05-31")]
theorem mfderiv_sub (hf : MDiffAt f z) (hg : MDiffAt g z) :
    (mfderiv% (f - g) z : TangentSpace I z →L[𝕜] E') =
      (by exact mfderiv% f z) - (by exact mfderiv% g z) :=
  (hf.hasMFDerivAt.sub hg.hasMFDerivAt).mfderiv

set_option backward.isDefEq.respectTransparency false in
@[deprecated mvfderivWithin_neg
  "this lemma abuses the identification of E with its tangent space: use mvfderivWithin instead"
  (since := "2026-05-31")]
theorem mfderivWithin_neg (hs : UniqueMDiffWithinAt I s x) :
    mfderiv[s] (-f) x = -mfderiv[s] f x := by
  simp_rw [mfderivWithin]
  by_cases hf : MDiffAt[s] f x
  · exact hf.hasMFDerivWithinAt.neg.mfderivWithin hs
  · rw [if_neg hf]; rw [← mdifferentiableWithinAt_neg] at hf; rw [if_neg hf, neg_zero]

@[deprecated mvfderiv_neg
  "this lemma abuses the identification of E with its tangent space: use mvfderivWithin instead"
  (since := "2026-05-31")]
theorem mfderiv_neg : mfderiv% (-f) x = -mfderiv% f x := by
  rw [← mfderivWithin_univ, mfderivWithin_neg (uniqueMDiffWithinAt_univ I), mfderivWithin_univ]

end deprecated
