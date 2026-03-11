/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! ## Equivalence of manifold differentiability with the basic definition for functions between
vector spaces

The API in this file is mostly copied from `Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean`,
providing the same statements for higher smoothness. In this file, we do the same for
differentiability.

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

section ExtChartAt

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

end ExtChartAt

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
variable {f : M → 𝕜} {g : M → V}

/-- Given maps `f`, `g` from a manifold into a field `𝕜` and `𝕜`-vector space `V`, respectively, if
at some point `x`, `f` has differential `f' : TangentSpace I x →L[𝕜] 𝕜` and `g` has differential
`g' : TangentSpace I x →L[𝕜] V` (both phrased using the predicate `HasMFDerivAt`), it follows that
their scalar multiplication `f • g` has differential `f x • g' + toSpanSingleton 𝕜 (g x) ∘L f'`.

In fact, the statement above is not literally true, because, for example, the differential of `g`
really takes values in the tangent space to `V` at `g x`, rather than in `V` itself. Of course, this
tangent space can be canonically identified with `V`.

This lemma phrases the formula using the equiv `NormedSpace.fromTangentSpace`, which provides this
canonical identification. (It would also be possible to phrase the formula without this equiv,
instead using casting and definitional abuse.) -/
lemma HasMFDerivAt.smul
    {f' : TangentSpace I x →L[𝕜] 𝕜}
    (hs : HasMFDerivAt% f x ((fromTangentSpace (f x)).symm.toContinuousLinearMap ∘L f'))
    {g' : TangentSpace I x →L[𝕜] V}
    (hg : HasMFDerivAt% g x ((fromTangentSpace (g x)).symm.toContinuousLinearMap ∘L g')) :
    -- canonically identify `g'` with a linear map into the tangent space at `(f • g) x`
    letI g'_ : TangentSpace I x →L[𝕜] TangentSpace 𝓘(𝕜, V) ((f • g) x) :=
      (fromTangentSpace _).symm.toContinuousLinearMap ∘L g'
    -- canonically identify `g x` with a linear map into a tangent space at `(f • g) x`
    letI gx :  𝕜 →L[𝕜] TangentSpace 𝓘(𝕜, V) ((f • g) x) :=
      toSpanSingleton 𝕜 ((fromTangentSpace _).symm (g x))
    -- now the main statement typechecks
    HasMFDerivAt% (f • g) x (f x • g'_ + gx ∘L f') := by
  constructor
  · exact hs.1.smul hg.1
  · simpa using hs.2.smul hg.2

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

/-- Given maps `f`, `g` from a manifold into a field `𝕜` and `𝕜`-vector space `V`, respectively, the
formula for the `mfderiv` (differential) of their scalar multiplication `f • g`.

Mathematically speaking the formula is `d(f • g) = f • dg + df ⊗ g`, i.e.
`mfderiv% (f • g) x = f x • mfderiv% g x + toSpanSingleton 𝕜 (g x) ∘L mfderiv% f x`,
but this doesn't typecheck because `mfderiv% (f • g) x` and `mfderiv% g x` take values in different
tangent spaces -- respectively the tangent spaces to `V` at `(f • g) x` and `g x`. Of course, both
these tangent spaces can be canonically identified with `V`.

This lemma phrases the formula using the equiv `NormedSpace.fromTangentSpace`, which provides this
canonical identification. (It would also be possible to phrase the formula without this equiv,
instead using casting and definitional abuse.)

It is good practice to use the equiv `NormedSpace.fromTangentSpace` throughout a computation. If
this is done, typically `mfderiv% (f • g) x` will only turn up paired with this equiv (i.e., in an
expression `(fromTangentSpace _) ∘L mfderiv% (f • g) x`), and the more convenient lemma
`fromTangentSpace_mfderiv_smul` (see below) can be used instead. -/
lemma mfderiv_smul (hf : MDiffAt f x) (hg : MDiffAt g x) :
    mfderiv% (f • g) x
    = f x • (fromTangentSpace _).symm.toContinuousLinearMap ∘L
      ((fromTangentSpace (g x)).toContinuousLinearMap ∘L mfderiv% g x)
    + toSpanSingleton 𝕜 ((fromTangentSpace _).symm (g x)) ∘L
      ((fromTangentSpace (f x)).toContinuousLinearMap ∘L mfderiv% f x) :=
  (hf.hasMFDerivAt.smul hg.hasMFDerivAt).mfderiv

/-- Given maps `f`, `g` from a manifold into a field `𝕜` and `𝕜`-vector space `V`, respectively, the
formula for the `mfderiv` (differential) of their scalar multiplication `f • g`.

Mathematically speaking the formula is `d(f • g) = f • dg + df ⊗ g`, i.e.
`mfderiv% (f • g) x = f x • mfderiv% g x + toSpanSingleton 𝕜 (g x) ∘L mfderiv% f x`,
but this doesn't typecheck because `mfderiv% (f • g) x` and `mfderiv% g x` take values in different
tangent spaces -- respectively the tangent spaces to `V` at `(f • g) x` and `g x`. Of course, both
these tangent spaces can be canonically identified with `V`.

This lemma phrases the formula using the equiv `NormedSpace.fromTangentSpace`, which provides this
canonical identification. (It would also be possible to phrase the formula without this equiv,
instead using casting and definitional abuse.) -/
lemma fromTangentSpace_mfderiv_smul (hf : MDiffAt f x) (hg : MDiffAt g x) :
    (fromTangentSpace ((f • g) x)).toContinuousLinearMap ∘L mfderiv% (f • g) x
    = f x • (fromTangentSpace _).toContinuousLinearMap ∘L mfderiv% g x
    + toSpanSingleton 𝕜 (g x) ∘L (fromTangentSpace _).toContinuousLinearMap ∘L mfderiv% f x := by
  rw [mfderiv_smul hf hg]
  rfl

/-- Given maps `f`, `g` from a manifold into a field `𝕜` and `𝕜`-vector space `V`, respectively, the
formula for the `mfderiv` (differential) of their scalar multiplication `f • g`.

Mathematically speaking the formula is `d(f • g) = f • dg + df ⊗ g`, but to get it to typecheck
we need a phrasing involving the canonical identification `NormedSpace.fromTangentSpace` between
the vector space `V` and the tangent space to this vector space at any point. This is because two
different tangent spaces (at `(f • g) x` and `g x`) appear in the equation.

This is a defeq variant of the main lemma `fromTangentSpace_mfderiv_smul`, in which we work in the
tangent space at `f x • g x` (the simp-normal form) rather than at `(f • g) x`. -/
lemma fromTangentSpace_mfderiv_smul' (hf : MDiffAt f x) (hg : MDiffAt g x) :
    (fromTangentSpace (f x • g x)).toContinuousLinearMap ∘L mfderiv% (f • g) x
    = f x • (fromTangentSpace _).toContinuousLinearMap ∘L mfderiv% g x
    + toSpanSingleton 𝕜 (g x) ∘L (fromTangentSpace _).toContinuousLinearMap ∘L mfderiv% f x :=
  fromTangentSpace_mfderiv_smul hf hg

/-- Given maps `f`, `g` from a manifold into a field `𝕜` and `𝕜`-vector space `V`, respectively, the
formula for the `mfderiv` (differential) of their scalar multiplication `f • g` in the direction of
the tangent vector `v`.

Mathematically speaking the formula is `d(f • g)(v) = f • dg(v) + df(v) • g`, but to get it to
typecheck we need a phrasing involving the canonical identification `NormedSpace.fromTangentSpace`
between the vector space `V` and the tangent space to this vector space at any point. This is
because two different tangent spaces (at `(f • g) x` and `g x`) appear in the equation. -/
lemma fromTangentSpace_mfderiv_smul_apply (hf : MDiffAt f x) (hg : MDiffAt g x)
    (v : TangentSpace I x) :
    fromTangentSpace _ (mfderiv% (f • g) x v)
    = f x • fromTangentSpace _ (mfderiv% g x v) + fromTangentSpace _ (mfderiv% f x v) • g x := by
  simpa using congr($(fromTangentSpace_mfderiv_smul hf hg) v)

/-- Given maps `f`, `g` from a manifold into a field `𝕜` and `𝕜`-vector space `V`, respectively, the
formula for the `mfderiv` (differential) of their scalar multiplication `f • g` in the direction of
the tangent vector `v`.

Mathematically speaking the formula is `d(f • g)(v) = f • dg(v) + df(v) • g`, but to get it to
typecheck we need a phrasing involving the canonical identification `NormedSpace.fromTangentSpace`
between the vector space `V` and the tangent space to this vector space at any point. This is
because two different tangent spaces (at `(f • g) x` and `g x`) appear in the equation.

This is a defeq variant of the main lemma `fromTangentSpace_mfderiv_smul_apply`, in which we work in
the tangent space at `f x • g x` (the simp-normal form) rather than at `(f • g) x`. -/
lemma fromTangentSpace_mfderiv_smul_apply' (hf : MDiffAt f x) (hg : MDiffAt g x)
    (v : TangentSpace I x) :
    fromTangentSpace (f x • g x) (mfderiv% (f • g) x v)
    = f x • fromTangentSpace _ (mfderiv% g x v) + fromTangentSpace _ (mfderiv% f x v) • g x :=
  fromTangentSpace_mfderiv_smul_apply hf hg v

end smul
