/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Geometry.Manifold.LocalSourceTargetProperty
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Analysis.Normed.Module.Shrink  -- shake: keep (NormedAddCommGroup (Shrink ...)), cf. lean#13417
public import Mathlib.Topology.Algebra.Module.TransferInstance

/-! # Smooth immersions

In this file, we define `C^n` immersions between `C^n` manifolds.
The correct definition in the infinite-dimensional setting differs from the standard
finite-dimensional definition (concerning the `mfderiv` being injective): future pull requests will
prove that our definition implies the latter, and that both are equivalent for finite-dimensional
manifolds.

This definition can be conveniently formulated in terms of local properties: `f` is an immersion at
`x` iff there exist suitable charts near `x` and `f x` such that `f` has a nice form w.r.t. these
charts. Most results below can be deduced from more abstract results about such local properties.
This shortens the overall argument, as the definition of submersions has the same general form.

## Main definitions

* `IsImmersionAtOfComplement F I J n f x` means a map `f : M → N` between `C^n` manifolds `M` and
  `N` is an immersion at `x : M`: there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`,
  respectively, such that in these charts, `f` looks like `u ↦ (u, 0)`, w.r.t. some equivalence
  `E' ≃L[𝕜] E × F`. We do not demand that `f` be differentiable (this follows from this definition).
* `IsImmersionAt I J n f x` means that `f` is a `C^n` immersion at `x : M` for some choice of a
  complement `F` of the model normed space `E` of `M` in the model normed space `E'` of `N`.
  In most cases, prefer this definition over `IsImmersionAtOfComplement`.
* `IsImmersionOfComplement F I J n f` means `f : M → N` is an immersion at every point `x : M`,
  w.r.t. the chosen complement `F`.
* `IsImmersion I J n f` means `f : M → N` is an immersion at every point `x : M`,
  w.r.t. some global choice of complement.

## Main results

* `IsImmersionAt.congr_of_eventuallyEq`: being an immersion is a local property.
  If `f` and `g` agree near `x` and `f` is an immersion at `x`, so is `g`
* `IsImmersionAtOfComplement.congr_F`, `IsImmersionOfComplement.congr_F`:
  being an immersion (at `x`) w.r.t. `F` is stable under
  replacing the complement `F` by an isomorphic copy.
* `IsOpen.isImmersionAtOfComplement` and `IsOpen.isImmersionAt`:
  the set of points where `IsImmersionAt(OfComplement)` holds is open.
* `IsImmersionAt.prodMap` and `IsImmersion.prodMap`: the product of two immersions (at a point)
  is an immersion (at the product point).
* `IsImmersion.id`: the identity map is an immersion
* `IsImmersion.of_opens`: the inclusion of an open subset `s → M` of a smooth manifold
  is a smooth immersion
* `IsImmersionAt.contMDiffAt`: if f is an immersion at `x`, it is `C^n` at `x`.
* `IsImmersion.contMDiff`: if f is a `C^n` immersion, it is automatically `C^n`
  in the sense of `ContMDiff`.
* `ContMDiffAt.iff_comp_isImmersionAt` and `ContMDiff.iff_comp_isImmersion`: a function `f : M → N`
  between `C^k` manifolds is `C^k` (at `x`) if and only if it is continuous (at `x`)
  and its composition `φ ∘ f` with a `C^k` immersion `φ : N → P` (at `f x`) is `C^k`.

## Implementation notes

* In most applications, there is no need to control the choice of complement in the definition of an
  immersion, so `IsImmersion(At)` is perfectly adequate. Such control will be helpful, however,
  when considering the local characterisation of submanifolds: locally, a submanifold is described
  either as the image of an immersion, or the preimage of a submersion --- w.r.t. the same
  complement. Providing a version of the definition that includes complements enables stating this
  equivalence cleanly.
* To avoid a free universe variable in `IsImmersion(At)`, we ask for a complement in the same
  universe as the model normed space for `N`. We provide convenience constructors which do not
  have this restriction to preserve usability.
  This relies on the observation that the equivalence in the definition of immersions allows
  shrinking the universe of the complement: this is implemented in
  `IsImmersion(At)OfComplement.small` and `IsImmersion(At)OfComplement.smallEquiv`.

## TODO
* The converse to `IsImmersionAtOfComplement.congr_F` also holds: any two complements are
  isomorphic, as they are isomorphic to the cokernel of the differential `mfderiv I J f x`.
* If `f` is an immersion at `x`, its differential splits, hence is injective.
* If `f : M → N` is a map between Banach manifolds, `mfderiv I J f x` splitting implies `f` is an
  immersion at `x`. (This requires the inverse function theorem.)
* `IsImmersionAt.comp`: if `f : M → N` and `g: N → N'` are maps between Banach manifolds such that
  `f` is an immersion at `x : M` and `g` is an immersion at `f x`, then `g ∘ f` is an immersion
  at `x`.
* `IsImmersion.comp`: the composition of immersions (between Banach manifolds) is an immersion
* If `f : M → N` is a map between finite-dimensional manifolds, `mfderiv I J f x` being injective
  implies `f` is an immersion at `x`.
* `IsLocalDiffeomorphAt.isImmersionAt` and `IsLocalDiffeomorph.isImmersion`:
  a local diffeomorphism (at `x`) is an immersion (at `x`)
* `Diffeomorph.isImmersion`: in particular, a diffeomorphism is an immersion

## References

* [Juan Margalef-Roig and Enrique Outerelo Dominguez, *Differential topology*][roigdomingues1992]

-/

open scoped Topology ContDiff
open Function Set

public noncomputable section

namespace Manifold

-- We manually name the universe of `E''` as `IsImmersionAt` will use it.
universe u
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' E''' : Type*} {E'' : Type u} {F F' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : ℕ∞ω}

variable (F I J M N) in
/-- The local property of being an immersion at a point: `f : M → N` is an immersion at `x` if
there exist charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively, such that in these
charts, `f` looks like the inclusion `u ↦ (u, 0)`.

This definition has a fixed parameter `F`, which is a choice of complement of `E` in the model
normed space `E'` of `N`: being an immersion at `x` includes a choice of linear isomorphism
between `E × F` and `E'`. -/
def ImmersionAtProp : (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop :=
  fun f domChart codChart ↦ ∃ equiv : (E × F) ≃L[𝕜] E'',
    EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target

omit [ChartedSpace H M] [ChartedSpace G N] in
/-- Being an immersion at `x` is a local property. -/
lemma isLocalSourceTargetProperty_immersionAtProp :
    IsLocalSourceTargetProperty (ImmersionAtProp F I J M N) where
  mono_source {f φ ψ s} hs := fun ⟨equiv, hf⟩ ↦ ⟨equiv, hf.mono (by simp; grind)⟩
  congr {f g φ ψ} hfg := by
    intro ⟨equiv, hf⟩
    refine ⟨equiv, EqOn.trans (fun x hx ↦ ?_) (hf.mono (by simp))⟩
    have : ((φ.extend I).symm) x ∈ φ.source := by simp_all
    grind

variable (F I J n) in
/-- `f : M → N` is a `C^n` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlases used for `M` and `N`, so asking for `φ` and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficient.

This definition has a fixed parameter `F`, which is a choice of complement of `E` in `E'`:
being an immersion at `x` includes a choice of linear isomorphism between `E × F` and `E'`.
While the particular choice of complement is often not important, choosing a complement is useful
in some settings, such as proving that embedded submanifolds are locally given either by an
immersion or a submersion.
Unless you have a particular reason, prefer to use `IsImmersionAt` instead.
-/
def IsImmersionAtOfComplement (f : M → N) (x : M) : Prop :=
  LiftSourceTargetPropertyAt I J n f x (ImmersionAtProp F I J M N)

-- Lift the universe from `E''`, to avoid a free universe parameter.
variable (I J n) in
/-- `f : M → N` is a `C^n` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlases used for `M` and `N`, so asking for `φ` and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficient.

Implicit in this definition is an abstract choice `F` of a complement of `E` in `E'`: being an
immersion at `x` includes a choice of linear isomorphism between `E × F` and `E'`, which is
where the choice of `F` enters.
If you need stronger control over the complement `F`, use `IsImmersionAtOfComplement` instead.
-/
def IsImmersionAt (f : M → N) (x : M) : Prop :=
  ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
    IsImmersionAtOfComplement F I J n f x

variable {f g : M → N} {x : M}

namespace IsImmersionAtOfComplement

lemma mk_of_charts (equiv : (E × F) ≃L[𝕜] E'') (domChart : OpenPartialHomeomorph M H)
    (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hsource : domChart.source ⊆ f ⁻¹' codChart.source)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAtOfComplement F I J n f x := by
  use domChart, codChart
  use equiv

/-- `f : M → N` is a `C^n` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.
This version does not assume that `f` maps `φ.source` to `ψ.source`,
but that `f` is continuous at `x`. -/
lemma mk_of_continuousAt {f : M → N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'')
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAtOfComplement F I J n f x :=
  LiftSourceTargetPropertyAt.mk_of_continuousAt hf isLocalSourceTargetProperty_immersionAtProp
    _ _ hx hfx hdomChart hcodChart ⟨equiv, hwrittenInExtend⟩

/-- A choice of chart on the domain `M` of an immersion `f` at `x`:
w.r.t. this chart and the data `h.codChart` and `h.equiv`,
`f` will look like an inclusion `u ↦ (u, 0)` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.codChart` and `h.codChart`. -/
def domChart (h : IsImmersionAtOfComplement F I J n f x) : OpenPartialHomeomorph M H :=
  LiftSourceTargetPropertyAt.domChart h

/-- A choice of chart on the co-domain `N` of an immersion `f` at `x`:
w.r.t. this chart and the data `h.domChart` and `h.equiv`,
`f` will look like an inclusion `u ↦ (u, 0)` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.equiv` and `h.domChart`. -/
def codChart (h : IsImmersionAtOfComplement F I J n f x) : OpenPartialHomeomorph N G :=
  LiftSourceTargetPropertyAt.codChart h

lemma mem_domChart_source (h : IsImmersionAtOfComplement F I J n f x) : x ∈ h.domChart.source :=
  LiftSourceTargetPropertyAt.mem_domChart_source h

lemma mem_codChart_source (h : IsImmersionAtOfComplement F I J n f x) : f x ∈ h.codChart.source :=
  LiftSourceTargetPropertyAt.mem_codChart_source h

lemma domChart_mem_maximalAtlas (h : IsImmersionAtOfComplement F I J n f x) :
    h.domChart ∈ IsManifold.maximalAtlas I n M :=
  LiftSourceTargetPropertyAt.domChart_mem_maximalAtlas h

lemma codChart_mem_maximalAtlas (h : IsImmersionAtOfComplement F I J n f x) :
    h.codChart ∈ IsManifold.maximalAtlas J n N :=
  LiftSourceTargetPropertyAt.codChart_mem_maximalAtlas h

lemma source_subset_preimage_source (h : IsImmersionAtOfComplement F I J n f x) :
    h.domChart.source ⊆ f ⁻¹' h.codChart.source :=
  LiftSourceTargetPropertyAt.source_subset_preimage_source h

lemma mapsto_domChart_source_codChart_source (h : IsImmersionAtOfComplement F I J n f x) :
    MapsTo f h.domChart.source h.codChart.source :=
  h.source_subset_preimage_source

/-- A linear equivalence `E × F ≃L[𝕜] E''` which belongs to the data of an immersion `f` at `x`:
the particular equivalence is arbitrary, but this choice matches the witnesses given by
`h.domChart` and `h.codChart`. -/
def equiv (h : IsImmersionAtOfComplement F I J n f x) : (E × F) ≃L[𝕜] E'' :=
  Classical.choose <| LiftSourceTargetPropertyAt.property h

lemma writtenInCharts (h : IsImmersionAtOfComplement F I J n f x) :
    EqOn ((h.codChart.extend J) ∘ f ∘ (h.domChart.extend I).symm) (h.equiv ∘ (·, 0))
      (h.domChart.extend I).target :=
  Classical.choose_spec <| LiftSourceTargetPropertyAt.property h

lemma property (h : IsImmersionAtOfComplement F I J n f x) :
    LiftSourceTargetPropertyAt I J n f x (ImmersionAtProp F I J M N) := h

/--
If `f` is an immersion at `x`, it maps its domain chart's target `(h.domChart.extend I).target`
to its codomain chart's target `(h.domChart.extend J).target`.

Roig and Domingues' [roigdomingues1992] definition of immersions only asks for this inclusion
between the targets of the local charts: using mathlib's formalisation conventions, that condition
is *slightly* weaker than `source_subset_preimage_source`: the latter implies that
`h.codChart.extend J ∘ f` maps `h.domChart.source` to
`(h.codChart.extend J).target = (h.codChart.extend I) '' h.codChart.source`,
but that does *not* imply `f` maps `h.domChart.source` to `h.codChart.source`;
a priori `f` could map some point `f ∘ h.domChart.extend I x ∉ h.codChart.source` into the target.
Note that this difference only occurs because of our design using junk values;
this is not a mathematically meaningful difference.

At the same time, this condition is fairly weak: it is implied, for instance, by `f` being
continuous at `x` (see `mk_of_continuousAt`), which is easy to ascertain in practice.

See `target_subset_preimage_target` for a version stated using preimages instead of images.
-/
lemma map_target_subset_target (h : IsImmersionAtOfComplement F I J n f x) :
    (h.equiv ∘ (·, 0)) '' (h.domChart.extend I).target ⊆ (h.codChart.extend J).target := by
  rw [← h.writtenInCharts.image_eq, Set.image_comp, Set.image_comp,
    PartialEquiv.symm_image_target_eq_source, OpenPartialHomeomorph.extend_source,
    ← PartialEquiv.image_source_eq_target]
  have : f '' h.domChart.source ⊆ h.codChart.source := by
    simp [h.source_subset_preimage_source]
  grw [this, OpenPartialHomeomorph.extend_source]

/-- If `f` is an immersion at `x`, its domain chart's target `(h.domChart.extend I).target`
is mapped to its codomain chart's target `(h.domChart.extend J).target`:
see `map_target_subset_target` for a version stated using images. -/
lemma target_subset_preimage_target (h : IsImmersionAtOfComplement F I J n f x) :
    (h.domChart.extend I).target ⊆ (h.equiv ∘ (·, 0)) ⁻¹' (h.codChart.extend J).target :=
  fun _x hx ↦ h.map_target_subset_target (mem_image_of_mem _ hx)

/-- If `f` is an immersion at `x` and `g = f` on some neighbourhood of `x`,
then `g` is an immersion at `x`. -/
lemma congr_of_eventuallyEq (hf : IsImmersionAtOfComplement F I J n f x) (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAtOfComplement F I J n g x :=
  LiftSourceTargetPropertyAt.congr_of_eventuallyEq
    isLocalSourceTargetProperty_immersionAtProp hf.property hfg

/-- If `f = g` on some neighbourhood of `x`,
then `f` is an immersion at `x` if and only if `g` is an immersion at `x`. -/
lemma congr_iff_of_eventuallyEq (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAtOfComplement F I J n f x ↔ IsImmersionAtOfComplement F I J n g x :=
  LiftSourceTargetPropertyAt.congr_iff_of_eventuallyEq
      isLocalSourceTargetProperty_immersionAtProp hfg

lemma small (hf : IsImmersionAtOfComplement F I J n f x) : Small.{u} F :=
  small_of_injective <| hf.equiv.injective.comp (Prod.mk_right_injective 0)

/-- Given an immersion `f` at `x`, this is a choice of complement which lives in the same universe
as the model space for the co-domain of `f`: this is useful to avoid universe restrictions. -/
def smallComplement (hf : IsImmersionAtOfComplement F I J n f x) : Type u :=
  haveI := hf.small
  Shrink.{u} F

instance (hf : IsImmersionAtOfComplement F I J n f x) : NormedAddCommGroup hf.smallComplement :=
  haveI := hf.small
  inferInstanceAs <| NormedAddCommGroup (Shrink F)

instance (hf : IsImmersionAtOfComplement F I J n f x) : NormedSpace 𝕜 hf.smallComplement :=
  haveI := hf.small
  inferInstanceAs <| NormedSpace 𝕜 (Shrink F)

/-- Given an immersion `f` at `x` w.r.t. a complement `F`, this construction provides
a continuous linear equivalence from `F` to the small complement of `F`:
mathematically, this is just the identity map; however, this is technically useful as it enables
us to always work with `hf.smallComplement`. -/
def smallEquiv (hf : IsImmersionAtOfComplement F I J n f x) : F ≃L[𝕜] hf.smallComplement :=
  haveI := hf.small
  ((equivShrink F).symm.continuousLinearEquiv 𝕜).symm

lemma trans_F (h : IsImmersionAtOfComplement F I J n f x) (e : F ≃L[𝕜] F') :
    IsImmersionAtOfComplement F' I J n f x := by
  refine ⟨h.domChart, h.codChart, h.mem_domChart_source, h.mem_codChart_source,
    h.domChart_mem_maximalAtlas, h.codChart_mem_maximalAtlas, h.source_subset_preimage_source, ?_⟩
  use ((ContinuousLinearEquiv.refl 𝕜 E).prodCongr e.symm).trans h.equiv
  apply Set.EqOn.trans h.writtenInCharts
  intro x hx
  simp

/-- Being an immersion at `x` w.r.t. `F` is stable under replacing `F` by an isomorphic copy. -/
lemma congr_F (e : F ≃L[𝕜] F') :
    IsImmersionAtOfComplement F I J n f x ↔ IsImmersionAtOfComplement F' I J n f x :=
  ⟨fun h ↦ trans_F (e := e) h, fun h ↦ trans_F (e := e.symm) h⟩

/- The set of points where `IsImmersionAtOfComplement` holds is open. -/
lemma _root_.IsOpen.isImmersionAtOfComplement :
    IsOpen {x | IsImmersionAtOfComplement F I J n f x} :=
  IsOpen.liftSourceTargetPropertyAt

set_option backward.isDefEq.respectTransparency false in
/-- If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is an immersion at `(x, x')`. -/
theorem prodMap {f : M → N} {g : M' → N'} {x' : M'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsImmersionAtOfComplement F I J n f x) (hg : IsImmersionAtOfComplement F' I' J' n g x') :
    IsImmersionAtOfComplement (F × F') (I.prod I') (J.prod J') n (Prod.map f g) (x, x') := by
  apply LiftSourceTargetPropertyAt.prodMap hf.property hg.property
  rintro f φ₁ ψ₁ g φ₂ ψ₂ ⟨equiv₁, hfprop⟩ ⟨equiv₂, hgprop⟩
  use (ContinuousLinearEquiv.prodProdProdComm 𝕜 E E' F F').trans (equiv₁.prodCongr equiv₂)
  rw [φ₁.extend_prod φ₂, ψ₁.extend_prod, PartialEquiv.prod_target, eqOn_prod_iff]
  exact ⟨fun x ⟨hx, hx'⟩ ↦ by simpa using hfprop hx, fun x ⟨hx, hx'⟩ ↦ by simpa using hgprop hx'⟩

/-- If `f` is an immersion at `x` w.r.t. some complement `F`, it is an immersion at `x`.

Note that the proof contains a small formalisation-related subtlety: `F` can live in any universe,
while being an immersion at `x` requires the existence of a complement in the same universe as
the model normed space of `N`. This is solved by `smallComplement` and `smallEquiv`.
-/
lemma isImmersionAt (h : IsImmersionAtOfComplement F I J n f x) :
    IsImmersionAt I J n f x := by
  use h.smallComplement, by infer_instance, by infer_instance
  exact (IsImmersionAtOfComplement.congr_F h.smallEquiv).mp h

open IsManifold in
/- The inclusion of an open subset `s` of a smooth manifold `M` is an immersion at every point. -/
lemma of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) (y : s) :
    IsImmersionAtOfComplement PUnit I I n (Subtype.val : s → M) y := by
  apply IsImmersionAtOfComplement.mk_of_continuousAt (by fun_prop) (.prodUnique 𝕜 E _)
    (chartAt H y) (chartAt H y.val) (mem_chart_source H y) (mem_chart_source H y.val)
    (chart_mem_maximalAtlas y) (chart_mem_maximalAtlas y.val)
  intro x hx
  suffices I ((chartAt H ↑y) ((chartAt H y).symm (I.symm x))) = x by simpa +contextual
  simp_all

@[deprecated (since := "2025-12-16")] alias ofOpen := of_opens

/-- Prefer using `IsImmersionAtOfComplement.continuousAt` instead -/
theorem continuousOn (h : IsImmersionAtOfComplement F I J n f x) :
    ContinuousOn f h.domChart.source := by
  rw [← h.domChart.continuousOn_writtenInExtend_iff le_rfl
      h.mapsto_domChart_source_codChart_source (I' := J) (I := I),
    ← h.domChart.extend_target_eq_image_source]
  have : ContinuousOn (h.equiv ∘ fun x ↦ (x, 0)) (h.domChart.extend I).target := by fun_prop
  exact this.congr h.writtenInCharts

/-- A `C^n` immersion at `x` is continuous at `x`. -/
theorem continuousAt (h : IsImmersionAtOfComplement F I J n f x) : ContinuousAt f x :=
  h.continuousOn.continuousAt (h.domChart.open_source.mem_nhds (mem_domChart_source h))

/-- Prefer using `IsImmersionAtOfComplement.contMDiffAt` instead -/
theorem contMDiffOn (h : IsImmersionAtOfComplement F I J n f x) :
    CMDiff[h.domChart.source] n f := by
  rw [← h.domChart.contMDiffOn_writtenInExtend_iff h.domChart_mem_maximalAtlas
    h.codChart_mem_maximalAtlas le_rfl h.mapsto_domChart_source_codChart_source,
    ← h.domChart.extend_target_eq_image_source]
  have : CMDiff n (h.equiv ∘ fun x ↦ (x, 0)) := by
    have : ContMDiff 𝓘(𝕜, E × F) 𝓘(𝕜, E'') n h.equiv := by
      rw [contMDiff_iff_contDiff]
      exact h.equiv.contDiff
    apply this.comp
    rw [contMDiff_iff_contDiff, contDiff_prod_iff]
    exact ⟨contDiff_id, contDiff_const (c := (0 : F))⟩
  exact this.contMDiffOn.congr h.writtenInCharts

/-- A `C^n` immersion at `x` is `C^n` at `x`. -/
theorem contMDiffAt (h : IsImmersionAtOfComplement F I J n f x) : CMDiffAt n f x :=
  h.contMDiffOn.contMDiffAt (h.domChart.open_source.mem_nhds (mem_domChart_source h))

/-- Let `f : M → N` be a function, and suppose `φ : N → P` is a `C^k` immersion at `f x`, such
that `φ ∘ f` is `C^k` at `x`. Let `x ∈ t ⊆ M` be contained in the slice chart at `f x`.
Then `f` seen in the slice chart at `φ (f x)` and any chart `e` in the maximal atlas
is `C^n` at (the image of) `x` within (the image of) `t`. -/
private lemma aux {f : M → N} {φ : N → N'}
    (h : IsImmersionAtOfComplement F J J' n φ (f x)) (h' : CMDiffAt n (φ ∘ f) x)
    {t : Set M} (ht : t ⊆ f ⁻¹' h.domChart.source) (hxt : x ∈ t)
    (e : OpenPartialHomeomorph M H) (hxe : x ∈ e.source) (he : e ∈ IsManifold.maximalAtlas I n M) :
    ContDiffWithinAt 𝕜 n ((h.domChart.extend J) ∘ f ∘ (e.extend I).symm)
      ((e.extend I).symm ⁻¹' t ∩ range I) ((e.extend I) x) := by
  -- Consider the local expressions of `f`, `φ`, `x` and `s'` in the charts we're considering.
  set f' := (h.domChart.extend J) ∘ f ∘ (e.extend I).symm
  set φ' := (h.codChart.extend J') ∘ φ ∘ (h.domChart.extend J).symm
  set x' := (e.extend I) x
  set s := (e.extend I).symm ⁻¹' t ∩ range I
  have hx' : (e.extend I) x ∈ s := ⟨by simp [e.left_inv hxe, hxt], mem_range_self _⟩
  have h'loc : ContDiffWithinAt 𝕜 n ((h.codChart.extend J') ∘ (φ ∘ f) ∘ (e.extend I).symm)
      ((e.extend I).symm ⁻¹' t ∩ range I) (e.extend I x) := by
    replace h' : CMDiffAt[t] n (φ ∘ f) x := h'.contMDiffWithinAt
    rw [contMDiffWithinAt_iff_of_mem_maximalAtlas he h.codChart_mem_maximalAtlas hxe
      h.mem_codChart_source] at h'
    exact h'.2
  -- By hypothesis, `φ ∘ f` (read in our charts) is `C^n` at `x'` within `s`.
  have h'' : ContDiffWithinAt 𝕜 n (φ' ∘ f') s x' := by
    apply h'loc.congr_of_mem (fun y hy ↦ ?_) hx'
    simp only [mfld_simps, φ', f']
    rw [h.domChart.left_inv]
    apply ht hy.1
  -- On the other hand, composing `f'` with the inclusion `u ↦ (u, 0)` is also `C^n`
  -- (as a composition of `C^n` functions); this locally equals `φ ∘ f` in coordinates
  -- (since `f` is an immersion).
  set f'' := (h.equiv ∘ fun x ↦ (x, 0)) ∘ f'
  have h''' : ContDiffWithinAt 𝕜 n f'' s x' := by
    refine h''.congr_of_mem (fun y hy ↦ ?_) hx'
    simp only [f'', φ', f']
    nth_rw 2 [comp_apply]
    rw [Function.comp_apply, h.writtenInCharts]
    rw [h.domChart.extend_target_eq_image_source]
    exact ⟨(f ∘ (e.extend I).symm) y, ht hy.1, by simp⟩
  -- Composing with a suitable projection to cancel the inclusion, we deduce that `f` is `C^n`.
  have h'''' : ContDiffWithinAt 𝕜 n ((Prod.fst ∘ h.equiv.symm) ∘ f'') s x' := by
    refine ContDiffWithinAt.comp x' ?_ h''' (mapsTo_univ _ _)
    rw [contDiffWithinAt_univ]
    exact contDiffAt_fst.comp _ h.equiv.symm.contDiff.contDiffAt
  exact h''''.congr_of_mem (fun y hy ↦ by simp [f'']) hx'

/-- A function `f : M → N` between `C^k` manifolds is `C^k` at `x` if and only if it is continuous
at `x` and its composition `φ ∘ f` with a `C^k` immersion `φ : N → P` at `f x` is `C^k` at `x`. -/
lemma _root_.ContMDiffAt.iff_comp_isImmersionAtOfComplement [IsManifold I n M]
    {f : M → N} {φ : N → N'} (hφ : IsImmersionAtOfComplement F J J' n φ (f x)) :
    -- Note: `φ` need not be inducing, so continuity of `φ ∘ f` at `x`
    -- generally does not imply continuity of `f`
    CMDiffAt n f x ↔ ContinuousAt f x ∧ CMDiffAt n (φ ∘ f) x := by
  refine ⟨fun hf ↦ ⟨hf.continuousAt, hφ.contMDiffAt.comp x hf⟩, fun ⟨hf, h'⟩ ↦ ?_⟩
  -- Since `f` is continuous at `x`, some neighbourhood `t` of `x` is mapped
  -- into `hφ.domChart.source` under `f`. By restriction, we may assume `t` is open,
  -- so it suffices to test smoothness on `t`.
  have : hφ.domChart.source ∈ 𝓝 (f x) := hφ.domChart.open_source.mem_nhds hφ.mem_domChart_source
  obtain ⟨t, ht, htopen, hxt⟩ := mem_nhds_iff.mp (hf this)
  suffices CMDiffAt[t] n f x from this.contMDiffAt <| htopen.mem_nhds hxt
  -- We test smoothness of `f` on `t` in the preferred chart at `x` and `hφ.codChart`.
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
    hφ.domChart_mem_maximalAtlas (mem_chart_source H x) hφ.mem_domChart_source]
  refine ⟨hf.continuousWithinAt, ?_⟩
  exact aux hφ h' ht hxt _ (mem_chart_source H x) (IsManifold.chart_mem_maximalAtlas x)

end IsImmersionAtOfComplement

namespace IsImmersionAt

lemma mk_of_charts (equiv : (E × F) ≃L[𝕜] E'')
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hsource : domChart.source ⊆ f ⁻¹' codChart.source)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAt I J n f x := by
  have aux : IsImmersionAtOfComplement F I J n f x := by
    apply IsImmersionAtOfComplement.mk_of_charts <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsImmersionAtOfComplement.congr_F aux.smallEquiv]

/-- `f : M → N` is a `C^n` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.
This version does not assume that `f` maps `φ.source` to `ψ.source`,
but that `f` is continuous at `x`. -/
lemma mk_of_continuousAt {f : M → N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'')
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAt I J n f x := by
  have aux : IsImmersionAtOfComplement F I J n f x := by
    apply IsImmersionAtOfComplement.mk_of_continuousAt <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsImmersionAtOfComplement.congr_F aux.smallEquiv]

/-- A choice of complement of the model normed space `E` of `M` in the model normed space
`E'` of `N` -/
def complement (h : IsImmersionAt I J n f x) : Type u := Classical.choose h

@[no_expose] instance (h : IsImmersionAt I J n f x) : NormedAddCommGroup h.complement :=
  Classical.choose <| Classical.choose_spec h

@[no_expose] instance (h : IsImmersionAt I J n f x) : NormedSpace 𝕜 h.complement :=
  Classical.choose <| Classical.choose_spec <| Classical.choose_spec h

lemma isImmersionAtOfComplement_complement (h : IsImmersionAt I J n f x) :
    IsImmersionAtOfComplement h.complement I J n f x :=
  Classical.choose_spec <| Classical.choose_spec <| Classical.choose_spec h

/-- A choice of chart on the domain `M` of an immersion `f` at `x`:
w.r.t. this chart and the data `h.codChart` and `h.equiv`,
`f` will look like an inclusion `u ↦ (u, 0)` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.codChart` and `h.codChart`. -/
def domChart (h : IsImmersionAt I J n f x) : OpenPartialHomeomorph M H :=
  h.isImmersionAtOfComplement_complement.domChart

/-- A choice of chart on the co-domain `N` of an immersion `f` at `x`:
w.r.t. this chart and the data `h.domChart` and `h.equiv`,
`f` will look like an inclusion `u ↦ (u, 0)` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.equiv` and `h.domChart`. -/
def codChart (h : IsImmersionAt I J n f x) : OpenPartialHomeomorph N G :=
  h.isImmersionAtOfComplement_complement.codChart

lemma mem_domChart_source (h : IsImmersionAt I J n f x) : x ∈ h.domChart.source :=
  h.isImmersionAtOfComplement_complement.mem_domChart_source

lemma mem_codChart_source (h : IsImmersionAt I J n f x) : f x ∈ h.codChart.source :=
  h.isImmersionAtOfComplement_complement.mem_codChart_source

lemma domChart_mem_maximalAtlas (h : IsImmersionAt I J n f x) :
    h.domChart ∈ IsManifold.maximalAtlas I n M :=
  h.isImmersionAtOfComplement_complement.domChart_mem_maximalAtlas

lemma codChart_mem_maximalAtlas (h : IsImmersionAt I J n f x) :
    h.codChart ∈ IsManifold.maximalAtlas J n N :=
  h.isImmersionAtOfComplement_complement.codChart_mem_maximalAtlas

lemma source_subset_preimage_source (h : IsImmersionAt I J n f x) :
    h.domChart.source ⊆ f ⁻¹' h.codChart.source :=
  h.isImmersionAtOfComplement_complement.source_subset_preimage_source

/-- A linear equivalence `E × F ≃L[𝕜] E''` which belongs to the data of an immersion `f` at `x`:
the particular equivalence is arbitrary, but this choice matches the witnesses given by
`h.domChart` and `h.codChart`. -/
def equiv (h : IsImmersionAt I J n f x) : (E × h.complement) ≃L[𝕜] E'' :=
  h.isImmersionAtOfComplement_complement.equiv

lemma writtenInCharts (h : IsImmersionAt I J n f x) :
    EqOn ((h.codChart.extend J) ∘ f ∘ (h.domChart.extend I).symm) (h.equiv ∘ (·, 0))
      (h.domChart.extend I).target :=
  h.isImmersionAtOfComplement_complement.writtenInCharts

lemma property (h : IsImmersionAt I J n f x) :
    LiftSourceTargetPropertyAt I J n f x (ImmersionAtProp h.complement I J M N) :=
  h.isImmersionAtOfComplement_complement.property

/--
If `f` is an immersion at `x`, it maps its domain chart's target to its codomain chart's target:
`(h.domChart.extend I).target` to `(h.domChart.extend J).target`.

Roig and Domingues' [roigdomingues1992] definition of immersions only asks for this inclusion
between the targets of the local charts: using mathlib's formalisation conventions, that condition
is *slightly* weaker than `source_subset_preimage_source`: the latter implies that
`h.codChart.extend J ∘ f` maps `h.domChart.source` to
`(h.codChart.extend J).target = (h.codChart.extend I) '' h.codChart.source`,
but that does *not* imply `f` maps `h.domChart.source` to `h.codChart.source`;
a priori `f` could map some point `f ∘ h.domChart.extend I x ∉ h.codChart.source` into the target.
Note that this difference only occurs because of our design using junk values;
this is not a mathematically meaningful difference.

At the same time, this condition is fairly weak: it is implied, for instance, by `f` being
continuous at `x` (see `mk_of_continuousAt`), which is easy to ascertain in practice.

See `target_subset_preimage_target` for a version stated using preimages instead of images.
-/
lemma map_target_subset_target (h : IsImmersionAt I J n f x) :
    (h.equiv ∘ (·, 0)) '' (h.domChart.extend I).target ⊆ (h.codChart.extend J).target :=
  h.isImmersionAtOfComplement_complement.map_target_subset_target

/-- If `f` is an immersion at `x`, its domain chart's target `(h.domChart.extend I).target`
is mapped to its codomain chart's target `(h.domChart.extend J).target`:
see `map_target_subset_target` for a version stated using images. -/
lemma target_subset_preimage_target (h : IsImmersionAt I J n f x) :
    (h.domChart.extend I).target ⊆ (h.equiv ∘ (·, 0)) ⁻¹' (h.codChart.extend J).target :=
  fun _x hx ↦ h.map_target_subset_target (mem_image_of_mem _ hx)

/-- If `f` is an immersion at `x` and `g = f` on some neighbourhood of `x`,
then `g` is an immersion at `x`. -/
lemma congr_of_eventuallyEq (hf : IsImmersionAt I J n f x) (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAt I J n g x := by
  use hf.complement, by infer_instance, by infer_instance
  exact hf.isImmersionAtOfComplement_complement.congr_of_eventuallyEq hfg

/-- If `f = g` on some neighbourhood of `x`,
then `f` is an immersion at `x` if and only if `g` is an immersion at `x`. -/
lemma congr_iff (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAt I J n f x ↔ IsImmersionAt I J n g x :=
  ⟨fun h ↦ h.congr_of_eventuallyEq hfg, fun h ↦ h.congr_of_eventuallyEq hfg.symm⟩

/- The set of points where `IsImmersionAt` holds is open. -/
lemma _root_.IsOpen.isImmersionAt :
    IsOpen {x | IsImmersionAt I J n f x} := by
  rw [isOpen_iff_forall_mem_open]
  exact fun x hx ↦ ⟨{x | IsImmersionAtOfComplement hx.complement I J n f x },
    fun y hy ↦ hy.isImmersionAt, .isImmersionAtOfComplement,
    by simp [hx.isImmersionAtOfComplement_complement]⟩

/-- If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is an immersion at `(x, x')`. -/
theorem prodMap {f : M → N} {g : M' → N'} {x' : M'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsImmersionAt I J n f x) (hg : IsImmersionAt I' J' n g x') :
    IsImmersionAt (I.prod I') (J.prod J') n (Prod.map f g) (x, x') :=
  hf.isImmersionAtOfComplement_complement.prodMap hg.isImmersionAtOfComplement_complement
    |>.isImmersionAt

/- The inclusion of an open subset `s` of a smooth manifold `M` is an immersion at every point. -/
lemma of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) (hx : x ∈ s) :
    IsImmersionAt I I n (Subtype.val : s → M) ⟨x, hx⟩ := by
  use PUnit, by infer_instance, by infer_instance
  apply Manifold.IsImmersionAtOfComplement.of_opens

@[deprecated (since := "2025-12-16")] alias ofOpen := of_opens

/-- Prefer using `IsImmersionAt.continuousAt` instead -/
theorem continuousOn (h : IsImmersionAt I J n f x) : ContinuousOn f h.domChart.source :=
  h.isImmersionAtOfComplement_complement.continuousOn

/-- A `C^n` immersion at `x` is continuous at `x`. -/
theorem continuousAt (h : IsImmersionAt I J n f x) : ContinuousAt f x :=
  h.isImmersionAtOfComplement_complement.continuousAt

/-- Prefer using `IsImmersionAt.contMDiffAt` instead -/
theorem contMDiffOn (h : IsImmersionAt I J n f x) : CMDiff[h.domChart.source] n f :=
  h.isImmersionAtOfComplement_complement.contMDiffOn

/-- A `C^n` immersion at `x` is `C^n` at `x`. -/
theorem contMDiffAt (h : IsImmersionAt I J n f x) : CMDiffAt n f x :=
  h.isImmersionAtOfComplement_complement.contMDiffAt

/-- A function `f : M → N` between `C^k` manifolds is `C^k` at `x` if and only if it is continuous
at `x` and its composition `φ ∘ f` with a `C^k` immersion `φ : N → P` at `f x` is `C^k` at `x`. -/
lemma _root_.ContMDiffAt.iff_comp_isImmersionAt [IsManifold I n M] {f : M → N} {φ : N → N'}
    (hφ : IsImmersionAt J J' n φ (f x)) :
    -- Note: `φ` need not be inducing, so continuity of `φ ∘ f` at `x`
    -- generally does not imply continuity of `f`
    CMDiffAt n f x ↔ ContinuousAt f x ∧ CMDiffAt n (φ ∘ f) x := by
  rw [← ContMDiffAt.iff_comp_isImmersionAtOfComplement hφ.isImmersionAtOfComplement_complement]

end IsImmersionAt

variable (F I J n) in
/-- `f : M → N` is a `C^n` immersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `u ↦ (u, 0)`.

In other words, `f` is an immersion at each `x ∈ M`.

This definition has a fixed parameter `F`, which is a choice of complement of `E` in `E'`:
being an immersion at `x` includes a choice of linear isomorphism between `E × F` and `E'`.
-/
def IsImmersionOfComplement (f : M → N) : Prop := ∀ x, IsImmersionAtOfComplement F I J n f x

variable (I J n) in
/-- `f : M → N` is a `C^n` immersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `u ↦ (u, 0)`.

Implicit in this definition is an abstract choice `F` of a complement of `E` in `E'`:
being an immersion includes a choice of linear isomorphism between `E × F` and `E'`, which is where
the choice of `F` enters. If you need stronger control over the complement `F`,
use `IsImmersionOfComplement` instead.

Note that our global choice of complement is a bit stronger than asking `f` to be an immersion at
each `x ∈ M` w.r.t. potentially varying complements: see `isImmersionAt` for details.
-/
def IsImmersion (f : M → N) : Prop :=
  ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F), IsImmersionOfComplement F I J n f

namespace IsImmersionOfComplement

variable {f g : M → N}

/-- If `f` is an immersion, it is an immersion at each point. -/
lemma isImmersionAt (h : IsImmersionOfComplement F I J n f) (x : M) :
    IsImmersionAtOfComplement F I J n f x := h x

/-- If `f = g` and `f` is an immersion, so is `g`. -/
theorem congr (h : IsImmersionOfComplement F I J n f) (heq : f = g) :
    IsImmersionOfComplement F I J n g :=
  heq ▸ h

lemma trans_F (h : IsImmersionOfComplement F I J n f) (e : F ≃L[𝕜] F') :
    IsImmersionOfComplement F' I J n f :=
  fun x ↦ (h x).trans_F e

/-- Being an immersion w.r.t. `F` is stable under replacing `F` by an isomorphic copy. -/
lemma congr_F (e : F ≃L[𝕜] F') :
    IsImmersionOfComplement F I J n f ↔ IsImmersionOfComplement F' I J n f :=
  ⟨fun h ↦ trans_F (e := e) h, fun h ↦ trans_F (e := e.symm) h⟩

/-- If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'` (w.r.t. `F` and `F'`),
respectively, then `f × g: M × N → M' × N'` is an immersion at `(x, x')` w.r.t. `F × F'`. -/
theorem prodMap {f : M → N} {g : M' → N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (h : IsImmersionOfComplement F I J n f) (h' : IsImmersionOfComplement F' I' J' n g) :
    IsImmersionOfComplement (F × F') (I.prod I') (J.prod J') n (Prod.map f g) :=
  fun ⟨x, x'⟩ ↦ (h x).prodMap (h' x')

/-- If `f` is an immersion w.r.t. some complement `F`, it is an immersion.

Note that the proof contains a small formalisation-related subtlety: `F` can live in any universe,
while being an immersion requires the existence of a complement in the same universe as
the model normed space of `N`. This is solved by `smallComplement` and `smallEquiv`.
-/
lemma isImmersion (h : IsImmersionOfComplement F I J n f) : IsImmersion I J n f := by
  by_cases! hM : IsEmpty M
  · rw [IsImmersion]
    use PUnit, by infer_instance, by infer_instance
    exact fun x ↦ (IsEmpty.false x).elim
  inhabit M
  let x : M := Inhabited.default
  use (h x).smallComplement, by infer_instance, by infer_instance
  exact (IsImmersionOfComplement.congr_F (h x).smallEquiv).mp h

open IsManifold in
/-- The identity map is an immersion with complement `PUnit`. -/
protected lemma id [IsManifold I n M] : IsImmersionOfComplement PUnit I I n (@id M) := by
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt (continuousAt_id) (.prodUnique 𝕜 E _)
    (chartAt H x) (chartAt H x) (mem_chart_source H x) (mem_chart_source H x)
    (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas x)
  intro y hy
  have : I ((chartAt H x) ((chartAt H x).symm (I.symm y))) = y := by
    rw [(chartAt H x).right_inv (by simp_all), I.right_inv (by simp_all)]
  simpa

/- The inclusion of an open subset `s` of a smooth manifold `M` is an immersion. -/
lemma of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) :
    IsImmersionOfComplement PUnit I I n (Subtype.val : s → M) :=
  fun y ↦ IsImmersionAtOfComplement.of_opens s y

@[deprecated (since := "2025-12-16")] alias ofOpen := of_opens

/-- A `C^n` immersion is `C^n`. -/
theorem contMDiff (h : IsImmersionOfComplement F I J n f) : CMDiff n f :=
  fun x ↦ (h x).contMDiffAt

/-- A function `f : M → N` between `C^k` manifolds is `C^k` if and only if it is continuous
and its composition `φ ∘ f` with a `C^k` immersion `φ : N → P` is `C^k`. -/
lemma _root_.ContMDiff.iff_comp_isImmersionOfComplement [IsManifold I n M] {f : M → N} {φ : N → N'}
    (hφ : IsImmersionOfComplement F J J' n φ) :
    CMDiff n f ↔ Continuous f ∧ CMDiff n (φ ∘ f) := by
  refine ⟨fun h ↦ ⟨h.continuous, hφ.contMDiff.comp h⟩, fun ⟨h, h'⟩ x ↦ ?_⟩
  rw [ContMDiffAt.iff_comp_isImmersionAtOfComplement (hφ (f x))]
  exact ⟨h.continuousAt, h' x⟩

end IsImmersionOfComplement

namespace IsImmersion

variable {f g : M → N}

/-- A choice of complement of the model normed space `E` of `M` in the model normed space
`E'` of `N` -/
def complement (h : IsImmersion I J n f) : Type u := Classical.choose h

@[no_expose] instance (h : IsImmersion I J n f) : NormedAddCommGroup h.complement :=
  Classical.choose <| Classical.choose_spec h

@[no_expose] instance (h : IsImmersion I J n f) : NormedSpace 𝕜 h.complement :=
  Classical.choose <| Classical.choose_spec <| Classical.choose_spec h

lemma isImmersionOfComplement_complement (h : IsImmersion I J n f) :
    IsImmersionOfComplement h.complement I J n f :=
  Classical.choose_spec <| Classical.choose_spec <| Classical.choose_spec h

/-- If `f` is an immersion, it is an immersion at each point.

Note that the converse statement is false in general:
if `f` is an immersion at each `x`, but with the choice of complement possibly depending on `x`,
there need not be a global choice of complement for which `f` is an immersion at each point.
The complement of `f` at `x` is isomorphic to the cokernel of `mfderiv I J f x`, but the `mfderiv`
of `f` at (even nearby) points `x` and `x'` are not directly related. They have the same rank
(the dimension of `E`, as will follow from injectivity), but if `E''` is infinite-dimensional this
is not conclusive. If `E''` is infinite-dimensional, this dimension can indeed change between
different connected components of `M`.
-/
lemma isImmersionAt (h : IsImmersion I J n f) (x : M) : IsImmersionAt I J n f x := by
  rw [IsImmersionAt]
  use h.complement, by infer_instance, by infer_instance
  exact h.isImmersionOfComplement_complement x

/-- If `f = g` and `f` is an immersion, so is `g`. -/
theorem congr (h : IsImmersion I J n f) (heq : f = g) : IsImmersion I J n g :=
  heq ▸ h

/-- If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is an immersion at `(x, x')`. -/
theorem prodMap {f : M → N} {g : M' → N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsImmersion I J n f) (hg : IsImmersion I' J' n g) :
    IsImmersion (I.prod I') (J.prod J') n (Prod.map f g) :=
  (hf.isImmersionOfComplement_complement.prodMap hg.isImmersionOfComplement_complement).isImmersion

open IsManifold in
/-- The identity map is an immersion. -/
protected lemma id [IsManifold I n M] : IsImmersion I I n (@id M) := by
  use PUnit, by infer_instance, by infer_instance
  exact IsImmersionOfComplement.id

/- The inclusion of an open subset `s` of a smooth manifold `M` is an immersion. -/
lemma of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) :
    IsImmersion I I n (Subtype.val : s → M) := by
  use PUnit, by infer_instance, by infer_instance
  exact IsImmersionOfComplement.of_opens s

@[deprecated (since := "2025-12-16")] alias ofOpen := of_opens

/-- A `C^n` immersion is `C^n`. -/
theorem contMDiff
    (h : IsImmersion I J n f) : CMDiff n f :=
  h.isImmersionOfComplement_complement.contMDiff

/-- A function `f : M → N` between `C^k` manifolds is `C^k` if and only if it is continuous
and its composition `φ ∘ f` with a `C^k` immersion `φ : N → P` is `C^k`. -/
lemma _root_.ContMDiff.iff_comp_isImmersion [IsManifold I n M] {f : M → N} {φ : N → N'}
    (hφ : IsImmersion J J' n φ) :
    CMDiff n f ↔ Continuous f ∧ CMDiff n (φ ∘ f) := by
  rw [ContMDiff.iff_comp_isImmersionOfComplement hφ.isImmersionOfComplement_complement]

end IsImmersion

end Manifold
