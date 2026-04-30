/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Samantha Naranjo Guevara
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Geometry.Manifold.LocalSourceTargetProperty
public import Mathlib.Analysis.Normed.Module.Shrink
public import Mathlib.Topology.Algebra.Module.TransferInstance

/-! # Smooth submersions

In this file, we define `C^n` submersions between `C^n` manifolds.
As in the case of immersions, the correct definition in the infinite-dimensional setting differs
from the classical finite-dimensional one (which is usually phrased in terms of surjectivity of the
`mfderiv`). Future work will prove that our definition implies the latter, and that both are
equivalent for finite-dimensional manifolds.

Our definition is formulated in terms of local normal forms; i.e., a map `f` is a submersion at `x`
if there exist charts near `x` and `f x` in which `f` looks like the standard projection
`(u, v) ↦ u`. The results in this file follow from abstract results about such local properties.

## Main definitions

* `IsSubmersionAtOfComplement F I J n f x` means a map `f : M → N` between `C^n` manifolds `M` and
  `N` is a submersion at `x : M`: there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`,
  respectively, such that in these charts, `f` looks like `(u, v) ↦ u`, w.r.t. some equivalence
  `E ≃L[𝕜] (E'' × F)`. Differentiability of `f` is not assumed as it follows from this definition.
* `IsSubmersionAt I J n f x` means that `f` is a `C^n` submersion at `x : M` for some choice of a
  complement `F` of the model normed space `E` of `M` in the model normed space `E''` of `N`.
* `IsSubmersionOfComplement F I J n f` means `f : M → N` is a submersion at every point `x : M`,
  w.r.t. the chosen complement `F`.
* `IsSubmersion I J n f` means `f : M → N` is a submersion at every point `x : M`,
  w.r.t. some global choice of complement.

## Main results

* `IsSubmersionAt.congr_of_eventuallyEq`: being a submersion is a local property.
  If `f` and `g` agree near `x` and `f` is a submersion at `x`, then so is `g`.
* `IsSubmersionAtOfComplement.congr_F`, `IsSubmersionOfComplement.congr_F`:
  being a submersion at `x` w.r.t. `F` is stable under
  replacing the complement `F` by an isomorphic copy.
* `isOpen_isSubmersionAtOfComplement` and `isOpen_isSubmersionAt`:
  the set of points where `IsSubmersionAt(OfComplement)` holds is open.
* `IsSubmersionAt.prodMap` and `IsSubmersion.prodMap`: the product of two submersions (at a point)
  is an submersion (at the product point).

## Implementation notes

* In most applications, there is no need to control the choice of complement in the definition of a
  submersion, so `IsSubmersion(At)` is perfectly adequate. Nevertheless, explicit control over
  complements is useful when studying the local characterisation of submanifolds: locally,
  a submanifold is described either as the image of an immersion, or the preimage of a submersion
  --- w.r.t. the same complement. Providing a version of the definition that includes complements
  enables stating this equivalence cleanly.
* To avoid a free universe variable in `IsSubmersion(At)`, we ask for a complement in the same
  universe as the model normed space for `N`. We provide convenience constructors which do not
  have this restriction to preserve usability.
  This relies on the observation that the equivalence in the definition of submersions allows
  reducing the universe of the complement; this is implemented in
  `IsSubmersion(At)OfComplement.small` and  `IsSubmersion(At)OfComplement.smallEquiv`.

## TODO
* The converse to `IsSubmersionAtOfComplement.congr_F` also holds: any two complements are
  isomorphic, as they are isomorphic to the kernel of the differential `mfderiv I J f x`.
* `IsSubmersionAt.contMDiffAt`: if f is a submersion at `x`, it is `C^n` at `x`.
* `IsSubmersion.contMDiff`: if f is a submersion, it is `C^n`.
* If `f` is a submersion at `x`, its differential `mfderiv I J f x` admits a continuous right
  inverse, in particular is surjective.
* If `f : M → N` is a map between Banach manifolds, `mfderiv I J f x` having a continuous right
  inverse implies `f` is a submersion at `x`. (This requires the inverse function theorem.)
* `IsSubmersionAt.comp`: if `f : M → N` and `g: N → N'` are maps between Banach manifolds such that
  `f` is a submersion at `x : M` and `g` is a submersion at `f x`, then `g ∘ f` is a submersion
  at `x`.
* `IsSubmersion.comp`: the composition of submersions is a submersion
* If `f : M → N` is a map between finite-dimensional manifolds, `mfderiv I J f x` being surjective
  implies `f` is a submersion at `x`.
* `IsLocalDiffeomorphAt.isSubmersionAt` and `IsLocalDiffeomorph.isSubmersion`:
  a local diffeomorphism (at `x`) is a submersion (at `x`)
* `Diffeomorph.isSubmersion`: in particular, a diffeomorphism is a submersion

**Please do not work** on this file without prior discussion with Michael Rothgang.
This will be the topic of Samantha Naranjo's master's thesis, and it's nice to coordinate.

-/

@[expose] public noncomputable section

open scoped Topology ContDiff

open Function Set

namespace Manifold

universe u
-- We manually name the universe of `E` as `IsSubmersionAt` will use it.

variable {𝕜 E' E'' E''' F F' H H' G G' : Type*} {E : Type u} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}

variable {M M' N N' : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {n : WithTop ℕ∞}

variable (F I J M N) in
/-- The local property of being a submersion at a point: `f : M → N` is a submersion at `x` if
there exist charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively, such that in these
charts, `f` looks like the projection `(u, v) ↦ u`.
This definition has a fixed parameter `F`, which is a choice of complement of `E''` in the model
normed space `E` of `M`: being a submersion at `x` includes a choice of linear isomorphism
between `E'' × F` and `E`. -/
def SubmersionAtProp :
    (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop :=
  fun f domChart codChart ↦ ∃ equiv : E ≃L[𝕜] (E'' × F),
    EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target

omit [ChartedSpace H M] [ChartedSpace G N] in
/-- Being a submersion at `x` is a local property. -/
lemma isLocalSourceTargetProperty_submmersionAtProp :
    IsLocalSourceTargetProperty (SubmersionAtProp F I J M N) where
  mono_source {f φ ψ s} hs := fun ⟨equiv, hf⟩ ↦ ⟨equiv, hf.mono (by simp; grind)⟩
  congr {f g φ ψ} hfg := by
    intro ⟨equiv, hf⟩
    refine ⟨equiv, EqOn.trans (fun x hx ↦ ?_) (hf.mono (by simp))⟩
    have : ((φ.extend I).symm) x ∈ φ.source := by simp_all
    grind

variable (F I J n) in
/-- `f : M → N` is a `C^n` submersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `(u, v) ↦ u`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlasses used for `M` and `N`, so asking for `φ` and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficient.

This definition has a fixed parameter `F`, which is a choice of complement of `E''` in `E`:
being an immersion at `x` includes a choice of linear isomorphism between `E'' × F` and `E`.
While the particular choice of complement is often not important, choosing a complement is useful
in some settings, such as proving that embedded submanifolds are locally given either by an
immersion or a submersion.
Unless you have a particular reason, prefer to use `IsSubmersionAt` instead.
-/
irreducible_def IsSubmersionAtOfComplement (f : M → N) (x : M) : Prop :=
  LiftSourceTargetPropertyAt I J n f x (SubmersionAtProp F I J M N)
variable (I J n) in
/-- `f : M → N` is a `C^n` submersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `(u, v) ↦ u`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlasses used for `M` and `N`, so asking for `φ` and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficient.

Implicit in this definition is an abstract choice `F` of a complement of `E''` in `E`: being
a submersion at `x` includes a choice of linear isomorphism between `E` and `E'' × F`, which is
where the choice of `F` enters.
If you need stronger control over the complement `F`, use `IsSubmersionAtOfComplement` instead.
-/
irreducible_def IsSubmersionAt (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 E'' G)
    (n : WithTop ℕ∞) (f : M → N) (x : M) : Prop :=
  ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
    IsSubmersionAtOfComplement F I J n f x

variable {f g : M → N} {x : M}

namespace IsSubmersionAtOfComplement

lemma mk_of_charts (equiv : E ≃L[𝕜] (E'' × F)) (domChart : OpenPartialHomeomorph M H)
    (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hsource : domChart.source ⊆ f ⁻¹' codChart.source)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target) : IsSubmersionAtOfComplement F I J n f x := by
  rw [IsSubmersionAtOfComplement_def]
  use domChart, codChart
  use equiv

lemma mk_of_continuousAt {f : M → N} {x : M} (hf : ContinuousAt f x) (equiv : E ≃L[𝕜] (E'' × F))
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target) : IsSubmersionAtOfComplement F I J n f x := by
  rw [IsSubmersionAtOfComplement_def]
  exact LiftSourceTargetPropertyAt.mk_of_continuousAt hf
    isLocalSourceTargetProperty_submmersionAtProp
    _ _ hx hfx hdomChart hcodChart ⟨equiv, hwrittenInExtend⟩

/-- A choice of chart on the domain `M` of a submersion `f` at `x`:
w.r.t. this chart and the data `h.codChart` and `h.equiv`,
`f` will look like a projection `(u,v) ↦ u` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.codChart` and `h.codChart`. -/
def domChart (h : IsSubmersionAtOfComplement F I J n f x) : OpenPartialHomeomorph M H := by
  rw [IsSubmersionAtOfComplement_def] at h
  exact LiftSourceTargetPropertyAt.domChart h

/-- A choice of chart on the codomain `N` of a submersion `f` at `x`:
w.r.t. this chart and the data `h.domChart` and `h.equiv`,
`f` will look like a projection `(u, v) ↦ u` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.equiv` and `h.domChart`. -/
def codChart (h : IsSubmersionAtOfComplement F I J n f x) : OpenPartialHomeomorph N G := by
  rw [IsSubmersionAtOfComplement_def] at h
  exact LiftSourceTargetPropertyAt.codChart h

lemma mem_domChart_source (h : IsSubmersionAtOfComplement F I J n f x) : x ∈ h.domChart.source := by
  rw [IsSubmersionAtOfComplement_def] at h
  exact LiftSourceTargetPropertyAt.mem_domChart_source h

lemma mem_codChart_source (h : IsSubmersionAtOfComplement F I J n f x) :
    f x ∈ h.codChart.source := by
  rw [IsSubmersionAtOfComplement_def] at h
  exact LiftSourceTargetPropertyAt.mem_codChart_source h

lemma domChart_mem_maximalAtlas (h : IsSubmersionAtOfComplement F I J n f x) :
    h.domChart ∈ IsManifold.maximalAtlas I n M := by
  rw [IsSubmersionAtOfComplement_def] at h
  exact LiftSourceTargetPropertyAt.domChart_mem_maximalAtlas h

lemma codChart_mem_maximalAtlas (h : IsSubmersionAtOfComplement F I J n f x) :
    h.codChart ∈ IsManifold.maximalAtlas J n N := by
  rw [IsSubmersionAtOfComplement_def] at h
  exact LiftSourceTargetPropertyAt.codChart_mem_maximalAtlas h

lemma source_subset_preimage_source (h : IsSubmersionAtOfComplement F I J n f x) :
    h.domChart.source ⊆ f ⁻¹' h.codChart.source := by
  rw [IsSubmersionAtOfComplement_def] at h
  exact LiftSourceTargetPropertyAt.source_subset_preimage_source h

/-- A linear equivalence `E ≃L[𝕜] E'' × F` which belongs to the data of a submersion `f` at `x`:
the particular equivalence is arbitrary, but this choice matches the witnesses given by
`h.domChart` and `h.codChart`. -/
def equiv (h : IsSubmersionAtOfComplement F I J n f x) : E ≃L[𝕜] (E'' × F) := by
  rw [IsSubmersionAtOfComplement_def] at h
  exact Classical.choose <| LiftSourceTargetPropertyAt.property h

lemma writtenInCharts (h : IsSubmersionAtOfComplement F I J n f x) :
    EqOn ((h.codChart.extend J) ∘ f ∘ (h.domChart.extend I).symm) (Prod.fst ∘ h.equiv)
      (h.domChart.extend I).target := by
  rw [IsSubmersionAtOfComplement_def] at h
  exact Classical.choose_spec <| LiftSourceTargetPropertyAt.property h

lemma property (h : IsSubmersionAtOfComplement F I J n f x) :
    LiftSourceTargetPropertyAt I J n f x (SubmersionAtProp F I J M N) := by
  rwa [IsSubmersionAtOfComplement_def] at h

lemma map_target_subset_target (h : IsSubmersionAtOfComplement F I J n f x) :
    (Prod.fst ∘ h.equiv) '' (h.domChart.extend I).target ⊆ (h.codChart.extend J).target := by
  rw [← h.writtenInCharts.image_eq, Set.image_comp, Set.image_comp,
    PartialEquiv.symm_image_target_eq_source, OpenPartialHomeomorph.extend_source,
    ← PartialEquiv.image_source_eq_target]
  have : f '' h.domChart.source ⊆ h.codChart.source := by
    simp [h.source_subset_preimage_source]
  grw [this, OpenPartialHomeomorph.extend_source]

lemma target_subset_preimage_target (h : IsSubmersionAtOfComplement F I J n f x) :
    (h.domChart.extend I).target ⊆ (Prod.fst ∘ h.equiv) ⁻¹' (h.codChart.extend J).target :=
  fun _x hx ↦ h.map_target_subset_target (mem_image_of_mem _ hx)

lemma congr_of_eventuallyEq (hf : IsSubmersionAtOfComplement F I J n f x) (hfg : f =ᶠ[𝓝 x] g) :
    IsSubmersionAtOfComplement F I J n g x := by
  rw [IsSubmersionAtOfComplement_def]
  exact LiftSourceTargetPropertyAt.congr_of_eventuallyEq
    isLocalSourceTargetProperty_submmersionAtProp hf.property hfg

lemma congr_iff_of_eventuallyEq (hfg : f =ᶠ[𝓝 x] g) :
    IsSubmersionAtOfComplement F I J n f x ↔ IsSubmersionAtOfComplement F I J n g x := by
  simpa only [IsSubmersionAtOfComplement_def] using
    LiftSourceTargetPropertyAt.congr_iff_of_eventuallyEq
      isLocalSourceTargetProperty_submmersionAtProp hfg

lemma small (hf : IsSubmersionAtOfComplement F I J n f x) : Small.{u} F :=
  small_of_injective <| hf.equiv.symm.injective.comp (Prod.mk_right_injective 0)

/-- Given a submersion `f` at `x`, this is a choice of complement which lives in the same universe
as the model space for the domain of `f`: this is useful to avoid universe restrictions. -/
def smallComplement (hf : IsSubmersionAtOfComplement F I J n f x) : Type u :=
  haveI := hf.small
  Shrink.{u} F

instance (hf : IsSubmersionAtOfComplement F I J n f x) : NormedAddCommGroup hf.smallComplement :=
  haveI := hf.small
  inferInstanceAs <| NormedAddCommGroup (Shrink F)

instance (hf : IsSubmersionAtOfComplement F I J n f x) : NormedSpace 𝕜 hf.smallComplement :=
  haveI := hf.small
  inferInstanceAs <| NormedSpace 𝕜 (Shrink F)

/-- Given an submersion `f` at `x` w.r.t. a complement `F`, this construction provides
a continuous linear equivalence from `F` to the small complement of `F`:
mathematically, this is just the identity map; however, this is technically useful as it enables
us to always work with `hf.smallComplement`. -/
def smallEquiv (hf : IsSubmersionAtOfComplement F I J n f x) : F ≃L[𝕜] hf.smallComplement :=
  haveI := hf.small
  ((equivShrink F).symm.continuousLinearEquiv 𝕜).symm

lemma trans_F (h : IsSubmersionAtOfComplement F I J n f x) (e : F ≃L[𝕜] F') :
    IsSubmersionAtOfComplement F' I J n f x := by
  rw [IsSubmersionAtOfComplement_def]
  refine ⟨h.domChart, h.codChart, h.mem_domChart_source, h.mem_codChart_source,
    h.domChart_mem_maximalAtlas, h.codChart_mem_maximalAtlas, h.source_subset_preimage_source, ?_⟩
  use h.equiv.trans ((ContinuousLinearEquiv.refl 𝕜 E'').prodCongr e)
  apply Set.EqOn.trans h.writtenInCharts
  intro x hx
  simp

/-- Being an submersion at `x` w.r.t. `F` is stable under replacing `F` by an isomorphic copy. -/
lemma congr_F (e : F ≃L[𝕜] F') :
    IsSubmersionAtOfComplement F I J n f x ↔ IsSubmersionAtOfComplement F' I J n f x :=
  ⟨fun h ↦ trans_F (e := e) h, fun h ↦ trans_F (e := e.symm) h⟩

/- The set of points where `IsSubmersionAtOfComplement` holds is open. -/
lemma _root_.isOpen_isSubmersionAt :
    IsOpen {x | IsSubmersionAtOfComplement F I J n f x} := by
  simp_rw [IsSubmersionAtOfComplement_def]
  exact IsOpen.liftSourceTargetPropertyAt

set_option backward.isDefEq.respectTransparency false in
/-- If `f: M → N` and `g: M' × N'` are submersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is an submersion at `(x, x')`. -/
theorem prodMap {f : M → N} {g : M' → N'} {x' : M'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsSubmersionAtOfComplement F I J n f x)
    (hg : IsSubmersionAtOfComplement F' I' J' n g x') :
    IsSubmersionAtOfComplement (F × F') (I.prod I') (J.prod J') n (Prod.map f g) (x, x') := by
  rw [IsSubmersionAtOfComplement_def]
  apply LiftSourceTargetPropertyAt.prodMap hf.property hg.property
  rintro f φ₁ ψ₁ g φ₂ ψ₂ ⟨equiv₁, hfprop⟩ ⟨equiv₂, hgprop⟩
  use (equiv₁.prodCongr equiv₂).trans (ContinuousLinearEquiv.prodProdProdComm 𝕜 E'' F E''' F')
  rw [φ₁.extend_prod φ₂, ψ₁.extend_prod, PartialEquiv.prod_target, eqOn_prod_iff]
  exact ⟨fun x ⟨hx, hx'⟩ ↦ by simpa using hfprop hx, fun x ⟨hx, hx'⟩ ↦ by simpa using hgprop hx'⟩

/-- If `f` is an submersion at `x` w.r.t. some complement `F`, it is an submersion at `x`. -/
lemma isSubmersionAt (h : IsSubmersionAtOfComplement F I J n f x) :
    IsSubmersionAt I J n f x := by
  rw [IsSubmersionAt_def]
  use h.smallComplement, by infer_instance, by infer_instance
  exact (IsSubmersionAtOfComplement.congr_F h.smallEquiv).mp h

end IsSubmersionAtOfComplement

namespace IsSubmersionAt

lemma mk_of_charts (equiv : E ≃L[𝕜] (E'' × F))
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hsource : domChart.source ⊆ f ⁻¹' codChart.source)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target) : IsSubmersionAt I J n f x := by
  rw [IsSubmersionAt_def]
  have aux : IsSubmersionAtOfComplement F I J n f x := by
    apply IsSubmersionAtOfComplement.mk_of_charts <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsSubmersionAtOfComplement.congr_F aux.smallEquiv]

/-- `f : M → N` is a `C^n` submersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `(u, v) ↦ u`.
This version does not assume that `f` maps `φ.source` to `ψ.source`,
but that `f` is continuous at `x`. -/
lemma mk_of_continuousAt {f : M → N} {x : M} (hf : ContinuousAt f x) (equiv : E ≃L[𝕜] (E'' × F))
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target) : IsSubmersionAt I J n f x := by
  rw [IsSubmersionAt_def]
  have aux : IsSubmersionAtOfComplement F I J n f x := by
    apply IsSubmersionAtOfComplement.mk_of_continuousAt <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsSubmersionAtOfComplement.congr_F aux.smallEquiv]

/-- A choice of complement of the model normed space `E` of `M` in the model normed space
`E'` of `N` -/
def complement (h : IsSubmersionAt I J n f x) : Type u := by
  rw [IsSubmersionAt_def] at h
  exact Classical.choose h

instance (h : IsSubmersionAt I J n f x) : NormedAddCommGroup h.complement := by
  rw [IsSubmersionAt_def] at h
  exact Classical.choose <| Classical.choose_spec h

instance (h : IsSubmersionAt I J n f x) : NormedSpace 𝕜 h.complement := by
  rw [IsSubmersionAt_def] at h
  exact Classical.choose <| Classical.choose_spec <| Classical.choose_spec h

lemma isSubmersionAtOfComplement_complement (h : IsSubmersionAt I J n f x) :
    IsSubmersionAtOfComplement h.complement I J n f x := by
  rw [IsSubmersionAt_def] at h
  exact Classical.choose_spec <| Classical.choose_spec <| Classical.choose_spec h

/-- A choice of chart on the domain `M` of a submersion `f` at `x`:
w.r.t. this chart and the data `h.codChart` and `h.equiv`,
`f` will look like a projection `(u, v) ↦ u` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.codChart` and `h.codChart`. -/
def domChart (h : IsSubmersionAt I J n f x) : OpenPartialHomeomorph M H :=
  h.isSubmersionAtOfComplement_complement.domChart

/-- A choice of chart on the co-domain `N` of a submersion `f` at `x`:
w.r.t. this chart and the data `h.domChart` and `h.equiv`,
`f` will look like a projection `(u, v) ↦ u` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.equiv` and `h.domChart`. -/
def codChart (h : IsSubmersionAt I J n f x) : OpenPartialHomeomorph N G :=
  h.isSubmersionAtOfComplement_complement.codChart

lemma mem_domChart_source (h : IsSubmersionAt I J n f x) : x ∈ h.domChart.source :=
  h.isSubmersionAtOfComplement_complement.mem_domChart_source

lemma mem_codChart_source (h : IsSubmersionAt I J n f x) : f x ∈ h.codChart.source :=
  h.isSubmersionAtOfComplement_complement.mem_codChart_source

lemma domChart_mem_maximalAtlas (h : IsSubmersionAt I J n f x) :
    h.domChart ∈ IsManifold.maximalAtlas I n M :=
  h.isSubmersionAtOfComplement_complement.domChart_mem_maximalAtlas

lemma codChart_mem_maximalAtlas (h : IsSubmersionAt I J n f x) :
    h.codChart ∈ IsManifold.maximalAtlas J n N :=
  h.isSubmersionAtOfComplement_complement.codChart_mem_maximalAtlas

lemma source_subset_preimage_source (h : IsSubmersionAt I J n f x) :
    h.domChart.source ⊆ f ⁻¹' h.codChart.source :=
  h.isSubmersionAtOfComplement_complement.source_subset_preimage_source

/-- A linear equivalence `E ≃L[𝕜] (E'' × F)` which belongs to the data of a submersion `f` at `x`:
the particular equivalence is arbitrary, but this choice matches the witnesses given by
`h.domChart` and `h.codChart`. -/
def equiv (h : IsSubmersionAt I J n f x) : E ≃L[𝕜] (E'' × h.complement) :=
  h.isSubmersionAtOfComplement_complement.equiv

lemma writtenInCharts (h : IsSubmersionAt I J n f x) :
    EqOn ((h.codChart.extend J) ∘ f ∘ (h.domChart.extend I).symm) (Prod.fst ∘ h.equiv)
      (h.domChart.extend I).target :=
  h.isSubmersionAtOfComplement_complement.writtenInCharts

lemma property (h : IsSubmersionAt I J n f x) :
    LiftSourceTargetPropertyAt I J n f x (SubmersionAtProp h.complement I J M N) :=
  h.isSubmersionAtOfComplement_complement.property

lemma map_target_subset_target (h : IsSubmersionAt I J n f x) :
    (Prod.fst ∘ h.equiv) '' (h.domChart.extend I).target ⊆ (h.codChart.extend J).target :=
  h.isSubmersionAtOfComplement_complement.map_target_subset_target

/-- If `f` is a submersion at `x`, its domain chart's target `(h.domChart.extend I).target`
is mapped to it codomain chart's target `(h.domChart.extend J).target`:
see `map_target_subset_target` for a version stated using images. -/
lemma target_subset_preimage_target (h : IsSubmersionAt I J n f x) :
    (h.domChart.extend I).target ⊆ (Prod.fst ∘ h.equiv) ⁻¹' (h.codChart.extend J).target :=
  fun _x hx ↦ h.map_target_subset_target (mem_image_of_mem _ hx)

/-- If `f` is a submersion at `x` and `g = f` on some neighbourhood of `x`,
then `g` is a submersion at `x`. -/
lemma congr_of_eventuallyEq (hf : IsSubmersionAt I J n f x) (hfg : f =ᶠ[𝓝 x] g) :
    IsSubmersionAt I J n g x := by
  rw [IsSubmersionAt_def]
  use hf.complement, by infer_instance, by infer_instance
  exact hf.isSubmersionAtOfComplement_complement.congr_of_eventuallyEq hfg

/-- If `f = g` on some neighbourhood of `x`,
then `f` is a submersion at `x` if and only if `g` is an submersion at `x`. -/
lemma congr_iff (hfg : f =ᶠ[𝓝 x] g) :
    IsSubmersionAt I J n f x ↔ IsSubmersionAt I J n g x :=
  ⟨fun h ↦ h.congr_of_eventuallyEq hfg, fun h ↦ h.congr_of_eventuallyEq hfg.symm⟩

/- The set of points where `IsSubmersionAt` holds is open. -/
lemma _root_.isOpen_isSubmersionAt' :
    IsOpen {x | IsSubmersionAt I J n f x} := by
  rw [isOpen_iff_forall_mem_open]
  exact fun x hx ↦ ⟨{x | IsSubmersionAtOfComplement hx.complement I J n f x },
    fun y hy ↦ hy.isSubmersionAt,
    isOpen_isSubmersionAt, by simp [hx.isSubmersionAtOfComplement_complement]⟩

/-- If `f: M → N` and `g: M' × N'` are submersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is a submersion at `(x, x')`. -/
theorem prodMap {f : M → N} {g : M' → N'} {x' : M'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsSubmersionAt I J n f x) (hg : IsSubmersionAt I' J' n g x') :
    IsSubmersionAt (I.prod I') (J.prod J') n (Prod.map f g) (x, x') :=
  hf.isSubmersionAtOfComplement_complement.prodMap hg.isSubmersionAtOfComplement_complement
    |>.isSubmersionAt

end IsSubmersionAt

variable (F I J n) in
/-- `f : M → N` is a `C^n` submersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `(u, v) ↦ u`.

In other words, `f` is a submersion at each `x ∈ M`.
-/
def IsSubmersionOfComplement (f : M → N) : Prop := ∀ x, IsSubmersionAtOfComplement F I J n f x

variable (I J n) in
/-- `f : M → N` is a `C^n` submersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `(u, v) ↦ u`.

Implicit in this definition is an abstract choice `F` of a complement of `E` in `E'`:
being a submersion includes a choice of linear isomorphism between `E` and `E'' × F`, which is where
the choice of `F` enters. If you need stronger control over the complement `F`,
use `IsSubmersionOfComplement` instead.

Note that our global choice of complement is a bit stronger than asking `f` to be a submersion at
each `x ∈ M` w.r.t. to potentially varying complements: see `isSubmersionAt` for details.
-/
def IsSubmersion (f : M → N) : Prop :=
  ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
    IsSubmersionOfComplement F I J n f

namespace IsSubmersionOfComplement

variable {f g : M → N}

/-- If `f` is a submersion, it is a submersion at each point. -/
lemma isSubmersionAt (h : IsSubmersionOfComplement F I J n f) (x : M) :
    IsSubmersionAtOfComplement F I J n f x := h x

/-- If `f = g` and `f` is a submersion, so is `g`. -/
theorem congr (h : IsSubmersionOfComplement F I J n f) (heq : f = g) :
    IsSubmersionOfComplement F I J n g :=
  heq ▸ h

lemma trans_F (h : IsSubmersionOfComplement F I J n f) (e : F ≃L[𝕜] F') :
    IsSubmersionOfComplement F' I J n f :=
  fun x ↦ (h x).trans_F e

/-- Being an submersion w.r.t. `F` is stable under replacing `F` by an isomorphic copy. -/
lemma congr_F (e : F ≃L[𝕜] F') :
    IsSubmersionOfComplement F I J n f ↔ IsSubmersionOfComplement F' I J n f :=
  ⟨fun h ↦ trans_F (e := e) h, fun h ↦ trans_F (e := e.symm) h⟩

/-- If `f: M → N` and `g: M' × N'` are submersions at `x` and `x'` (w.r.t. `F` and `F'`),
respectively, then `f × g: M × N → M' × N'` is a submersion at `(x, x')` w.r.t. `F × F'`. -/
theorem prodMap {f : M → N} {g : M' → N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (h : IsSubmersionOfComplement F I J n f) (h' : IsSubmersionOfComplement F' I' J' n g) :
    IsSubmersionOfComplement (F × F') (I.prod I') (J.prod J') n (Prod.map f g) :=
  fun ⟨x, x'⟩ ↦ (h x).prodMap (h' x')

/-- If `f` is a submersion w.r.t. some complement `F`, it is a submersion.

Note that the proof contains a small formalisation-related subtlety: `F` can live in any universe,
while being an submersion requires the existence of a complement in the same universe as
the model normed space of `N`. This is solved by `smallComplement` and `smallEquiv`.
-/
lemma isSubmersion (h : IsSubmersionOfComplement F I J n f) : IsSubmersion I J n f := by
  by_cases! hM : IsEmpty M
  · rw [IsSubmersion]
    use PUnit, by infer_instance, by infer_instance
    exact fun x ↦ (IsEmpty.false x).elim
  inhabit M
  let x : M := Inhabited.default
  use (h x).smallComplement, by infer_instance, by infer_instance
  exact (IsSubmersionOfComplement.congr_F (h x).smallEquiv).mp h

end IsSubmersionOfComplement

namespace IsSubmersion

variable {f g : M → N}

/-- A choice of complement of the model normed space `E` of `M` in the model normed space
`E'` of `N` -/
def complement (h : IsSubmersion I J n f) : Type u := Classical.choose h

instance (h : IsSubmersion I J n f) : NormedAddCommGroup h.complement :=
  Classical.choose <| Classical.choose_spec h

instance (h : IsSubmersion I J n f) : NormedSpace 𝕜 h.complement :=
  Classical.choose <| Classical.choose_spec <| Classical.choose_spec h

lemma isSubmersionOfComplement_complement (h : IsSubmersion I J n f) :
    IsSubmersionOfComplement h.complement I J n f :=
  Classical.choose_spec <| Classical.choose_spec <| Classical.choose_spec h

/-- If `f` is a submersion, it is an submersion at each point.
-/
lemma isSubmersionAt (h : IsSubmersion I J n f) (x : M) : IsSubmersionAt I J n f x := by
  rw [IsSubmersionAt_def]
  use h.complement, by infer_instance, by infer_instance, h.isSubmersionOfComplement_complement x

/-- If `f = g` and `f` is a submersion, so is `g`. -/
theorem congr (h : IsSubmersion I J n f) (heq : f = g) : IsSubmersion I J n g :=
  heq ▸ h

/-- If `f: M → N` and `g: M' × N'` are submersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is an submersion at `(x, x')`. -/
theorem prodMap {f : M → N} {g : M' → N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsSubmersion I J n f) (hg : IsSubmersion I' J' n g) :
    IsSubmersion (I.prod I') (J.prod J') n (Prod.map f g) :=
  (hf.isSubmersionOfComplement_complement.prodMap
    hg.isSubmersionOfComplement_complement ).isSubmersion

end IsSubmersion
