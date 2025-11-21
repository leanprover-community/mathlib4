/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.LocalSourceTargetProperty
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.Shrink

/-! # Smooth immersions and embeddings

In this file, we define `C^n` immersions and embeddings between `C^n` manifolds.
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
  `isImmersion_iff_isImmersionAt` will prove this is equivalent to `f` being an
  immersion at every point `x` (i.e., with respect to a complement that can depend on `x`).

## Main results
* `IsImmersionAt.congr_of_eventuallyEq`: being an immersion is a local property.
  If `f` and `g` agree near `x` and `f` is an immersion at `x`, so is `g`
* `IsImmersionAtOfComplement.congr_F`: being an immersion at `x` is stable under replacing the
  complement `F` by an isomorphic copy

## TODO
* The converse to `IsImmersionAtOfComplement.congr_F` also holds: any two complements are
  isomorphic, as they are isomorphic to the cokernel of the differential `mfderiv I J f x`.
* `isImmersion_iff_isImmersionAt`: `f` is an immersion iff `f` is an immersion at each `x`
* The set where `LiftSourceTargetPropertyAt` holds is open.
* `IsImmersionAt.contMDiffAt`: if f is an immersion at `x`, it is `C^n` at `x`.
* `IsImmersion.contMDiff`: if f is an immersion, it is `C^n`.
* `IsImmersionAt.prodMap`: the product of two immersions is an immersion
* If `f` is an immersion at `x`, its differential splits, hence is injective.
* If `f : M → N` is a map between Banach manifolds, `mfderiv I J f x` splitting implies `f` is an
  immersion at `x`. (This requires the inverse function theorem.)
* `IsImmersionAt.comp`: if `f : M → N` and `g: N → N'` are maps between Banach manifolds such that
  `f` is an immersion at `x : M` and `g` is an immersion at `f x`, then `g ∘ f` is an immersion
  at `x`.
* `IsImmersion.comp`: the composition of immersions (between Banach manifolds) is an immersion
* If `f : M → N` is a map between finite-dimensional manifolds, `mfderiv I J f x` being injective
  implies `f` is an immersion at `x`.
* define smooth embeddings, and deduce analogous results for these

## References

* [Juan Margalef-Roig and Enrique Outerelo Dominguez, *Differential topology*][roigdomingues2012]

-/

open scoped Topology ContDiff
open Function Set Manifold

noncomputable section

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
  {n : WithTop ℕ∞}

variable (F I J M N) in
/-- The local property of being an immersion at a point: `f : M → N` is an immersion at `x` if
there exist charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively, such that in these
charts, `f` looks like the inclusion `u ↦ (u, 0)`.

This definition has a fixed parameter `F`, which is a choice of complement of `E` in `E'`:
being an immersion at `x` includes a choice of linear isomorphism between `E × F` and `E'`. -/
def ImmersionAtProp : (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop :=
  fun f domChart codChart ↦ ∃ equiv : (E × F) ≃L[𝕜] E'',
    EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target

omit [ChartedSpace H M] [ChartedSpace G N] in
/-- Being an immersion at `x` is a local property. -/
lemma isLocalSourceTargetProperty_immersionAtProp :
    IsLocalSourceTargetProperty (ImmersionAtProp F I J M N) where
  mono_source {f φ ψ s} hs hf := by
    obtain ⟨equiv, hf⟩ := hf
    exact ⟨equiv, hf.mono (by simp; grind)⟩
  congr {f g φ ψ} hfg hf := by
    obtain ⟨equiv, hf⟩ := hf
    refine ⟨equiv, EqOn.trans (fun x hx ↦ ?_) (hf.mono (by simp))⟩
    have : ((φ.extend I).symm) x ∈ φ.source := by simp_all
    grind

variable (F I J n) in
/-- `f : M → N` is a `C^n` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.
The chosen complement `F` is often not important

NB. We don't know the particular atlasses used for `M` and `N`, so asking for `φ` and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficient.

This definition has a fixed parameter `F`, which is a choice of complement of `E` in `E'`:
being an immersion at `x` includes a choice of linear isomorphism between `E × F` and `E'`.
While the particular choice of complement is often not important, chosing a complement is useful
in some settings, such as proving that embedded submanifolds are locally given either by an
immersion or a submersion.
Unless you have a particular reason, prefer to use `IsImmersionAt` instead.
-/
irreducible_def IsImmersionAtOfComplement (f : M → N) (x : M) : Prop :=
  LiftSourceTargetPropertyAt I J n f x (ImmersionAtProp F I J M N)

-- Lift the universe from E'', to avoid a free universe parameter.
variable (I J n) in
/-- `f : M → N` is a `C^n` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlasses used for `M` and `N`, so asking for `φ` and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficient.

Implicit in this definition is an abstract choice `F` of a complement of `E` in `E'`: being an
immersion at `x` includes a choice of linear isomorphism between `E × F` and `E'`, which is
where the choice of `F` enters.
If you need closer control over the complement `F`, use `IsImmersionAtOfComplement` instead.
-/
irreducible_def IsImmersionAt (f : M → N) (x : M) : Prop :=
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
  rw [IsImmersionAtOfComplement_def]
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
      (domChart.extend I).target) : IsImmersionAtOfComplement F I J n f x := by
  rw [IsImmersionAtOfComplement_def]
  exact LiftSourceTargetPropertyAt.mk_of_continuousAt hf isLocalSourceTargetProperty_immersionAtProp
    _ _ hx hfx hdomChart hcodChart ⟨equiv, hwrittenInExtend⟩

/-- A choice of chart on the domain `M` of an immersion `f` at `x`:
w.r.t. this chart and the data `h.codChart` and `h.equiv`,
`f` will look like an inclusion `u ↦ (u, 0)` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.codChart` and `h.codChart`. -/
def domChart (h : IsImmersionAtOfComplement F I J n f x) : OpenPartialHomeomorph M H := by
  rw [IsImmersionAtOfComplement_def] at h
  exact LiftSourceTargetPropertyAt.domChart h

/-- A choice of chart on the co-domain `N` of an immersion `f` at `x`:
w.r.t. this chart and the data `h.domChart` and `h.equiv`,
`f` will look like an inclusion `u ↦ (u, 0)` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.equiv` and `h.domChart`. -/
def codChart (h : IsImmersionAtOfComplement F I J n f x) : OpenPartialHomeomorph N G := by
  rw [IsImmersionAtOfComplement_def] at h
  exact LiftSourceTargetPropertyAt.codChart h

lemma mem_domChart_source (h : IsImmersionAtOfComplement F I J n f x) : x ∈ h.domChart.source := by
  rw [IsImmersionAtOfComplement_def] at h
  exact LiftSourceTargetPropertyAt.mem_domChart_source h

lemma mem_codChart_source (h : IsImmersionAtOfComplement F I J n f x) :
    f x ∈ h.codChart.source := by
  rw [IsImmersionAtOfComplement_def] at h
  exact LiftSourceTargetPropertyAt.mem_codChart_source h

lemma domChart_mem_maximalAtlas (h : IsImmersionAtOfComplement F I J n f x) :
    h.domChart ∈ IsManifold.maximalAtlas I n M := by
  rw [IsImmersionAtOfComplement_def] at h
  exact LiftSourceTargetPropertyAt.domChart_mem_maximalAtlas h

lemma codChart_mem_maximalAtlas (h : IsImmersionAtOfComplement F I J n f x) :
    h.codChart ∈ IsManifold.maximalAtlas J n N := by
  rw [IsImmersionAtOfComplement_def] at h
  exact LiftSourceTargetPropertyAt.codChart_mem_maximalAtlas h

lemma source_subset_preimage_source (h : IsImmersionAtOfComplement F I J n f x) :
    h.domChart.source ⊆ f ⁻¹' h.codChart.source := by
  rw [IsImmersionAtOfComplement_def] at h
  exact LiftSourceTargetPropertyAt.source_subset_preimage_source h

/-- A linear equivalence `E × F ≃L[𝕜] E''` which belongs to the data of an immersion `f` at `x`:
the particular equivalence is arbitrary, but this choice matches the witnesses given by
`h.domChart` and `h.codChart`. -/
def equiv (h : IsImmersionAtOfComplement F I J n f x) : (E × F) ≃L[𝕜] E'' := by
  rw [IsImmersionAtOfComplement_def] at h
  exact Classical.choose <| LiftSourceTargetPropertyAt.property h

lemma writtenInCharts (h : IsImmersionAtOfComplement F I J n f x) :
    EqOn ((h.codChart.extend J) ∘ f ∘ (h.domChart.extend I).symm) (h.equiv ∘ (·, 0))
      (h.domChart.extend I).target := by
  rw [IsImmersionAtOfComplement_def] at h
  exact Classical.choose_spec <| LiftSourceTargetPropertyAt.property h

lemma property (h : IsImmersionAtOfComplement F I J n f x) :
    LiftSourceTargetPropertyAt I J n f x (ImmersionAtProp F I J M N) := by
  rwa [IsImmersionAtOfComplement_def] at h

/--
If `f` is an immersion at `x`, it maps its domain chart's target to its codomain chart's target:
`(h.domChart.extend I).target` to `(h.domChart.extend J).target`.

Roig and Domingues' [roigdomingues1992] definition of immersions only asks for this inclusion
between the targets of the local charts: using mathlib's formalisation conventions, that condition
is *slightly* weaker than `source_subset_preimage_source`: the latter implies that
`h.codChart.extend J ∘ f` maps `h.domChart.source` to
`(h.codChart.extend J).target = (h.codChart.extend I) '' h.codChart.source`,
but that does *not* imply `f` maps `h.domChart.source` to `h.codChartSource`;
a priori `f` could map some point `f ∘ h.domChart.extend I x ∉ h.codChart.source` into the target.
Note that this difference only occurs because of our design using junk values;
this is not a mathematically meaningful difference.`

At the same time, this condition is fairly weak: it is implied, for instance, by `f` being
continuous at `x` (see `mk_of_continuousAt`), which is easy to ascertain in practice.
-/
lemma map_target_subset_target (h : IsImmersionAtOfComplement F I J n f x) :
    (h.equiv ∘ (·, 0)) '' (h.domChart.extend I).target ⊆ (h.codChart.extend J).target := by
  rw [← h.writtenInCharts.image_eq, Set.image_comp, Set.image_comp,
    PartialEquiv.symm_image_target_eq_source, OpenPartialHomeomorph.extend_source,
    ← PartialEquiv.image_source_eq_target]
  have : f '' h.domChart.source ⊆ h.codChart.source := by
    simp [h.source_subset_preimage_source]
  grw [this, OpenPartialHomeomorph.extend_source]

/-- If `f` is an immersion at `x` and `g = f` on some neighbourhood of `x`,
then `g` is an immersion at `x`. -/
lemma congr_of_eventuallyEq (hf : IsImmersionAtOfComplement F I J n f x) (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAtOfComplement F I J n g x := by
  rw [IsImmersionAtOfComplement_def]
  exact LiftSourceTargetPropertyAt.congr_of_eventuallyEq
    isLocalSourceTargetProperty_immersionAtProp hf.property hfg

/-- If `f = g` on some neighbourhood of `x`,
then `f` is an immersion at `x` if and only if `g` is an immersion at `x`. -/
lemma congr_iff (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAtOfComplement F I J n f x ↔ IsImmersionAtOfComplement F I J n g x :=
  ⟨fun h ↦ h.congr_of_eventuallyEq hfg, fun h ↦ h.congr_of_eventuallyEq hfg.symm⟩

lemma foo (hf : IsImmersionAtOfComplement F I J n f x) : Small.{u} F := sorry

/-- Given an immersion `f` at `x`, this is a choice of complement which lives in the same universe
as the model space for the co-domain of `f`: this is useful to avoid universe restrictions. -/
def smallComplement (hf : IsImmersionAtOfComplement F I J n f x) : Type u := by
  have := foo hf
  exact Shrink.{u} F

instance (hf : IsImmersionAtOfComplement F I J n f x) : NormedAddCommGroup hf.smallComplement := by
  have := foo hf
  unfold smallComplement
  infer_instance

instance (hf : IsImmersionAtOfComplement F I J n f x) : NormedSpace 𝕜 hf.smallComplement := by
  have := foo hf
  unfold smallComplement
  infer_instance

def smallComplement' (hf : IsImmersionAtOfComplement F I J n f x) : Type u :=
  ((⊥ : Submodule 𝕜 E).prod ⊤).map hf.equiv

instance (hf : IsImmersionAtOfComplement F I J n f x) : NormedAddCommGroup hf.smallComplement' := by
  unfold smallComplement'
  infer_instance

instance (hf : IsImmersionAtOfComplement F I J n f x) : NormedSpace 𝕜 hf.smallComplement' := by
  unfold smallComplement'
  infer_instance

def smallEquiv' (hf : IsImmersionAtOfComplement F I J n f x) : F ≃L[𝕜] hf.smallComplement' := by
  let φ := (hf.equiv.submoduleMap ((⊥ : Submodule 𝕜 E).prod ⊤))
  sorry

def bar : F ≃L[𝕜] (⊥ : Submodule 𝕜 E).prod (⊤ : Submodule _ F) := by
  let A : Submodule 𝕜 (E × F) := (⊥ : Submodule 𝕜 E).prod ⊤

  let B := ContinuousLinearEquiv.uniqueProd 𝕜 F (N := (⊥ : Submodule 𝕜 E)) |>.symm

  let X : F ≃L[𝕜] (⊤ : Submodule 𝕜 F) := sorry -- Submodule.topEquiv, but as a CLM!
  -- this is almost what I want... except that it's the product of types, not of submodules!
  let Yalmost /- (⊥ : Submodule 𝕜 E) × F ≃L[𝕜] A -/ :=
    (ContinuousLinearEquiv.refl 𝕜 (⊥ : Submodule 𝕜 E)).prodCongr X
  let Y : (⊥ : Submodule 𝕜 E) × F ≃L[𝕜] A := by
    unfold A
    apply Yalmost.ofSubmodules (p := ((⊥ : Submodule 𝕜 E) × F))
    let φ := ContinuousLinearEquiv.refl 𝕜 (⊥ : Submodule 𝕜 E)
    sorry -- is almost what I want apply ContinuousLinearEquiv.prodCongr φ X

  --let C := foo
  #check ContinuousLinearEquiv.ofSubmodules


  -- let B' := B.symm
  -- let C' := X.symm.trans B'
  -- have aux := B'.ofSubmodules (p := (⊤ : Submodule _ _)) --(q := A)
  --   -- compose aux and X (or X.symm)
  --   --apply B.symm.ofSubmodules (⊤ : Submodule 𝕜 F) (q := A)
  --   --apply?--apply ContinuousLinearEquiv.ofSubmodules
  --   sorry -- use ofSubmodules!
  sorry

#exit

def smallEquiv' (hf : IsImmersionAtOfComplement F I J n f x) : F ≃L[𝕜] hf.smallComplement' :=
  bar.trans (hf.equiv.submoduleMap ((⊥ : Submodule 𝕜 E).prod ⊤))

#exit
-- TODO: remove completeness hypotheses using ContinuousLinearEquiv.ofSubmodules
/-- If `f` is an immersion at `x`, then any complement used in this definition is
isomorphic to the `smallComplement`. -/
def smallEquiv (hf : IsImmersionAtOfComplement F I J n f x) : F ≃L[𝕜] hf.smallComplement := by
  have := foo hf
  unfold smallComplement
  have aux := (equivShrink F).continuousLinearEquiv 𝕜
  sorry
  --convert aux yields 4 goals, some of which seem to show diamond issues
  --dsimp at aux ⊢

  -- have h : Injective φ := by intro x y hxy; simp_all [φ]
  -- have h2 : IsClosed (range φ) := by
  --   have : (range (fun (x : F) ↦ ((0 : E), x))) = {0} ×ˢ univ := by grind
  --   convert isClosed_singleton.prod isClosed_univ
  --   infer_instance
  -- have : CompleteSpace (LinearMap.range φ) := h2.completeSpace_coe
  -- letI ψ : _ →L[𝕜] E'' := .mk (hf.equiv.domRestrict (LinearMap.range φ))
  --   (Pi.continuous_restrict_apply _ hf.equiv.continuous)
  -- have h3 : Injective ψ := by
  --   simp only [ψ, ContinuousLinearMap.coe_mk']
  --   rw [LinearMap.injective_domRestrict_iff]
  --   simp
  -- have : IsClosed (range ψ) := by
  --   simp only [ψ, ContinuousLinearMap.coe_mk']
  --   -- LinearMap.range_domRestrict does not fire, but this lemma does...
  --   have : range ((hf.equiv.toLinearEquiv).domRestrict (LinearMap.range φ)) =
  --       Submodule.map hf.equiv.toLinearEquiv (LinearMap.range φ) := by
  --     ext x
  --     simp
  --   rw [this]
  --   simpa
  -- apply (ContinuousLinearMap.equivRange h h2).trans (ContinuousLinearMap.equivRange h3 this)

-- lemma smallEquiv_coe [CompleteSpace E] [CompleteSpace E''] [CompleteSpace F]
--   (hf : IsImmersionAtOfComplement F I J n f x) :
--   letI B := Pi.prod (0 : F → E) (@id F)
--   (hf.smallEquiv : F → _) =
--     (Set.rangeFactorization ((range B).restrict hf.equiv)) ∘ (Set.rangeFactorization B) := by
--   rfl

lemma trans_F (h : IsImmersionAtOfComplement F I J n f x) (e : F ≃L[𝕜] F') :
    IsImmersionAtOfComplement F' I J n f x := by
  rewrite [IsImmersionAtOfComplement_def]
  refine ⟨h.domChart, h.codChart, h.mem_domChart_source, h.mem_codChart_source,
    h.domChart_mem_maximalAtlas, h.codChart_mem_maximalAtlas, h.source_subset_preimage_source, ?_⟩
  use ((ContinuousLinearEquiv.refl 𝕜 E).prodCongr e.symm).trans h.equiv
  apply Set.EqOn.trans h.writtenInCharts
  intro x hx
  simp

/-- Being an immersion at `x` is stable under replacing `F` by an isomorphism copy. -/
lemma congr_F (e : F ≃L[𝕜] F') :
    IsImmersionAtOfComplement F I J n f x ↔ IsImmersionAtOfComplement F' I J n f x :=
  ⟨fun h ↦ trans_F (e := e) h, fun h ↦ trans_F (e := e.symm) h⟩

end IsImmersionAtOfComplement

namespace IsImmersionAt

lemma mk_of_charts [CompleteSpace E] [CompleteSpace E''] [CompleteSpace F]
    (equiv : (E × F) ≃L[𝕜] E'')
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hsource : domChart.source ⊆ f ⁻¹' codChart.source)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAt I J n f x := by
  rw [IsImmersionAt_def]
  have aux : IsImmersionAtOfComplement F I J n f x := by
    apply IsImmersionAtOfComplement.mk_of_charts <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsImmersionAtOfComplement.congr_F aux.smallEquiv]

/-- `f : M → N` is a `C^n` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.
This version does not assume that `f` maps `φ.source` to `ψ.source`,
but that `f` is continuous at `x`. -/
lemma mk_of_continuousAt [CompleteSpace E] [CompleteSpace E''] [CompleteSpace F]
    {f : M → N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'')
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAt I J n f x := by
  rw [IsImmersionAt_def]
  have aux : IsImmersionAtOfComplement F I J n f x := by
    apply IsImmersionAtOfComplement.mk_of_continuousAt <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsImmersionAtOfComplement.congr_F aux.smallEquiv]

/-- A choice of complement of the model normed space `E` of `M` in the model normed space
`E'` of `N` -/
def complement (h : IsImmersionAt I J n f x) : Type u := by
  rw [IsImmersionAt_def] at h
  exact Classical.choose h

noncomputable instance (h : IsImmersionAt I J n f x) : NormedAddCommGroup h.complement := by
  rw [IsImmersionAt_def] at h
  exact Classical.choose <| Classical.choose_spec h

noncomputable instance (h : IsImmersionAt I J n f x) : NormedSpace 𝕜 h.complement := by
  rw [IsImmersionAt_def] at h
  exact Classical.choose <| Classical.choose_spec <| Classical.choose_spec h

lemma isImmersionAtOfComplement_complement (h : IsImmersionAt I J n f x) :
    IsImmersionAtOfComplement h.complement I J n f x := by
  rw [IsImmersionAt_def] at h
  exact Classical.choose_spec <| Classical.choose_spec <| Classical.choose_spec h

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
but that does *not* imply `f` maps `h.domChart.source` to `h.codChartSource`;
a priori `f` could map some point `f ∘ h.domChart.extend I x ∉ h.codChart.source` into the target.
Note that this difference only occurs because of our design using junk values;
this is not a mathematically meaningful difference.`

At the same time, this condition is fairly weak: it is implied, for instance, by `f` being
continuous at `x` (see `mk_of_continuousAt`), which is easy to ascertain in practice.
-/
lemma map_target_subset_target (h : IsImmersionAt I J n f x) :
    (h.equiv ∘ (·, 0)) '' (h.domChart.extend I).target ⊆ (h.codChart.extend J).target :=
  h.isImmersionAtOfComplement_complement.map_target_subset_target

/-- If `f` is an immersion at `x` and `g = f` on some neighbourhood of `x`,
then `g` is an immersion at `x`. -/
lemma congr_of_eventuallyEq (hf : IsImmersionAt I J n f x) (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAt I J n g x := by
  rw [IsImmersionAt_def]
  use hf.complement, by infer_instance, by infer_instance
  exact hf.isImmersionAtOfComplement_complement.congr_of_eventuallyEq hfg

/-- If `f = g` on some neighbourhood of `x`,
then `f` is an immersion at `x` if and only if `g` is an immersion at `x`. -/
lemma congr_iff (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAt I J n f x ↔ IsImmersionAt I J n g x :=
  ⟨fun h ↦ h.congr_of_eventuallyEq hfg, fun h ↦ h.congr_of_eventuallyEq hfg.symm⟩

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

namespace IsImmersionOfComplement

variable {f g : M → N}

/-- If `f` is an immersion, it is an immersion at each point. -/
lemma isImmersionAt (h : IsImmersionOfComplement F I J n f) (x : M) :
    IsImmersionAtOfComplement F I J n f x := h x

/-- If `f = g` and `f` is an immersion, so is `g`. -/
theorem congr (h : IsImmersionOfComplement F I J n f) (heq : f = g) :
    IsImmersionOfComplement F I J n g :=
  heq ▸ h

end IsImmersionOfComplement

variable (I J n) in
/-- `f : M → N` is a `C^n` immersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `u ↦ (u, 0)`.

In other words, `f` is an immersion at each `x ∈ M`.

Implicit in this definition is an abstract choice `F` of a complement of `E` in `E'`:
being an immersion includes a choice of linear isomorphism between `E × F` and `E'`, which is where
the choice of `F` enters. If you need closer control over the complement `F`,
use `IsImmersionOfComplement` instead.
-/
def IsImmersion (f : M → N) : Prop :=
  ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F), IsImmersionOfComplement F I J n f
  --∀ x, IsImmersionAt I J n f x

namespace IsImmersion

variable {f g : M → N}

/-- A choice of complement of the model normed space `E` of `M` in the model normed space
`E'` of `N` -/
def complement (h : IsImmersion I J n f) : Type u := Classical.choose h

noncomputable instance (h : IsImmersion I J n f) : NormedAddCommGroup h.complement :=
  Classical.choose <| Classical.choose_spec h

noncomputable instance (h : IsImmersion I J n f) : NormedSpace 𝕜 h.complement :=
  Classical.choose <| Classical.choose_spec <| Classical.choose_spec h

lemma isImmersionOfComplement_complement (h : IsImmersion I J n f) :
    IsImmersionOfComplement h.complement I J n f :=
  Classical.choose_spec <| Classical.choose_spec <| Classical.choose_spec h

/-- If `f` is an immersion, it is an immersion at each point. -/
lemma isImmersionAt (h : IsImmersion I J n f) (x : M) : IsImmersionAt I J n f x := by
  rw [IsImmersionAt_def]
  use h.complement, by infer_instance, by infer_instance, h.isImmersionOfComplement_complement x

/-- If `f = g` and `f` is an immersion, so is `g`. -/
theorem congr (h : IsImmersion I J n f) (heq : f = g) : IsImmersion I J n g :=
  heq ▸ h

end IsImmersion

end Manifold
