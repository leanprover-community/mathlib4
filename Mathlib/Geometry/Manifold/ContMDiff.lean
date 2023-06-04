/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn

! This file was ported from Lean 3 source module geometry.manifold.cont_mdiff
! leanprover-community/mathlib commit e5ab837fc252451f3eb9124ae6e7b6f57455e7b9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Geometry.Manifold.LocalInvariantProperties

/-!
# Smooth functions between smooth manifolds

We define `Cⁿ` functions between smooth manifolds, as functions which are `Cⁿ` in charts, and prove
basic properties of these notions.

## Main definitions and statements

Let `M ` and `M'` be two smooth manifolds, with respect to model with corners `I` and `I'`. Let
`f : M → M'`.

* `cont_mdiff_within_at I I' n f s x` states that the function `f` is `Cⁿ` within the set `s`
  around the point `x`.
* `cont_mdiff_at I I' n f x` states that the function `f` is `Cⁿ` around `x`.
* `cont_mdiff_on I I' n f s` states that the function `f` is `Cⁿ` on the set `s`
* `cont_mdiff I I' n f` states that the function `f` is `Cⁿ`.
* `cont_mdiff_on.comp` gives the invariance of the `Cⁿ` property under composition
* `cont_mdiff_iff_cont_diff` states that, for functions between vector spaces,
  manifold-smoothness is equivalent to usual smoothness.

We also give many basic properties of smooth functions between manifolds, following the API of
smooth functions between vector spaces.

## Implementation details

Many properties follow for free from the corresponding properties of functions in vector spaces,
as being `Cⁿ` is a local property invariant under the smooth groupoid. We take advantage of the
general machinery developed in `local_invariant_properties.lean` to get these properties
automatically. For instance, the fact that being `Cⁿ` does not depend on the chart one considers
is given by `lift_prop_within_at_indep_chart`.

For this to work, the definition of `cont_mdiff_within_at` and friends has to
follow definitionally the setup of local invariant properties. Still, we recast the definition
in terms of extended charts in `cont_mdiff_on_iff` and `cont_mdiff_iff`.
-/


open Set Function Filter ChartedSpace SmoothManifoldWithCorners

open scoped Topology Manifold

/-! ### Definition of smooth functions between manifolds -/


variable {𝕜 : Type _} [NontriviallyNormedField 𝕜]
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type _}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) {M : Type _} [TopologicalSpace M] [ChartedSpace H M]
  [Is : SmoothManifoldWithCorners I M]
  -- declare a smooth manifold `M'` over the pair `(E', H')`.
  {E' : Type _}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type _} [TopologicalSpace H']
  (I' : ModelWithCorners 𝕜 E' H') {M' : Type _} [TopologicalSpace M'] [ChartedSpace H' M']
  [I's : SmoothManifoldWithCorners I' M']
  -- declare a manifold `M''` over the pair `(E'', H'')`.
  {E'' : Type _}
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type _} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type _} [TopologicalSpace M''] [ChartedSpace H'' M'']
  -- declare a smooth manifold `N` over the pair `(F, G)`.
  {F : Type _}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type _} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type _} [TopologicalSpace N] [ChartedSpace G N]
  [Js : SmoothManifoldWithCorners J N]
  -- declare a smooth manifold `N'` over the pair `(F', G')`.
  {F' : Type _}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type _} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type _} [TopologicalSpace N'] [ChartedSpace G' N']
  [J's : SmoothManifoldWithCorners J' N']
  -- F₁, F₂, F₃, F₄ are normed spaces
  {F₁ : Type _}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {F₂ : Type _} [NormedAddCommGroup F₂]
  [NormedSpace 𝕜 F₂] {F₃ : Type _} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] {F₄ : Type _}
  [NormedAddCommGroup F₄] [NormedSpace 𝕜 F₄]
  -- declare functions, sets, points and smoothness indices
  {e : LocalHomeomorph M H}
  {e' : LocalHomeomorph M' H'} {f f₁ : M → M'} {s s₁ t : Set M} {x : M} {m n : ℕ∞}

/-- Property in the model space of a model with corners of being `C^n` within at set at a point,
when read in the model vector space. This property will be lifted to manifolds to define smooth
functions between manifolds. -/
def ContDiffWithinAtProp (n : ℕ∞) (f : H → H') (s : Set H) (x : H) : Prop :=
  ContDiffWithinAt 𝕜 n (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I x)
#align cont_diff_within_at_prop ContDiffWithinAtProp

theorem contDiffWithinAtProp_self_source {f : E → H'} {s : Set E} {x : E} :
    ContDiffWithinAtProp 𝓘(𝕜, E) I' n f s x ↔ ContDiffWithinAt 𝕜 n (I' ∘ f) s x := by
  simp_rw [ContDiffWithinAtProp, modelWithCornersSelf_coe, range_id, inter_univ]
  rfl
#align cont_diff_within_at_prop_self_source contDiffWithinAtProp_self_source

theorem contDiffWithinAtProp_self {f : E → E'} {s : Set E} {x : E} :
    ContDiffWithinAtProp 𝓘(𝕜, E) 𝓘(𝕜, E') n f s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAtProp_self_source 𝓘(𝕜, E')
#align cont_diff_within_at_prop_self contDiffWithinAtProp_self

theorem contDiffWithinAtProp_self_target {f : H → E'} {s : Set H} {x : H} :
    ContDiffWithinAtProp I 𝓘(𝕜, E') n f s x ↔
      ContDiffWithinAt 𝕜 n (f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I x) :=
  Iff.rfl
#align cont_diff_within_at_prop_self_target contDiffWithinAtProp_self_target

/-- Being `Cⁿ` in the model space is a local property, invariant under smooth maps. Therefore,
it will lift nicely to manifolds. -/
theorem cont_diff_within_at_localInvariantProp (n : ℕ∞) :
    (contDiffGroupoid ∞ I).LocalInvariantProp (contDiffGroupoid ∞ I')
      (ContDiffWithinAtProp I I' n) :=
  { is_local := by
      intro s x u f u_open xu
      have : I.symm ⁻¹' (s ∩ u) ∩ range I = I.symm ⁻¹' s ∩ range I ∩ I.symm ⁻¹' u := by
        simp only [inter_right_comm, preimage_inter]
      rw [ContDiffWithinAtProp, ContDiffWithinAtProp, this]
      symm
      apply contDiffWithinAt_inter
      have : u ∈ 𝓝 (I.symm (I x)) := by rw [ModelWithCorners.left_inv];
        exact IsOpen.mem_nhds u_open xu
      apply ContinuousAt.preimage_mem_nhds I.continuous_symm.continuous_at this
    right_invariance' := by
      intro s x f e he hx h
      rw [ContDiffWithinAtProp] at h ⊢
      have : I x = (I ∘ e.symm ∘ I.symm) (I (e x)) := by simp only [hx, mfld_simps]
      rw [this] at h 
      have : I (e x) ∈ I.symm ⁻¹' e.target ∩ range I := by simp only [hx, mfld_simps]
      have := ((mem_groupoid_of_pregroupoid.2 he).2.ContDiffWithinAt this).of_le le_top
      convert (h.comp' _ this).mono_of_mem _ using 1
      · ext y; simp only [mfld_simps]
      refine'
        mem_nhds_within.mpr
          ⟨I.symm ⁻¹' e.target, e.open_target.preimage I.continuous_symm, by
            simp_rw [mem_preimage, I.left_inv, e.maps_to hx], _⟩
      mfld_set_tac
    congr_of_forall := by
      intro s x f g h hx hf
      apply hf.congr
      · intro y hy
        simp only [mfld_simps] at hy 
        simp only [h, hy, mfld_simps]
      · simp only [hx, mfld_simps]
    left_invariance' := by
      intro s x f e' he' hs hx h
      rw [ContDiffWithinAtProp] at h ⊢
      have A : (I' ∘ f ∘ I.symm) (I x) ∈ I'.symm ⁻¹' e'.source ∩ range I' := by
        simp only [hx, mfld_simps]
      have := ((mem_groupoid_of_pregroupoid.2 he').1.ContDiffWithinAt A).of_le le_top
      convert this.comp _ h _
      · ext y; simp only [mfld_simps]
      · intro y hy; simp only [mfld_simps] at hy ; simpa only [hy, mfld_simps] using hs hy.1 }
#align cont_diff_within_at_local_invariant_prop cont_diff_within_at_localInvariantProp

theorem contDiffWithinAtProp_mono_of_mem (n : ℕ∞) ⦃s x t⦄ ⦃f : H → H'⦄ (hts : s ∈ 𝓝[t] x)
    (h : ContDiffWithinAtProp I I' n f s x) : ContDiffWithinAtProp I I' n f t x := by
  refine' h.mono_of_mem _
  refine' inter_mem _ (mem_of_superset self_mem_nhdsWithin <| inter_subset_right _ _)
  rwa [← Filter.mem_map, ← I.image_eq, I.symm_map_nhds_within_image]
#align cont_diff_within_at_prop_mono_of_mem contDiffWithinAtProp_mono_of_mem

theorem contDiffWithinAtProp_id (x : H) : ContDiffWithinAtProp I I n id univ x := by
  simp [ContDiffWithinAtProp]
  have : ContDiffWithinAt 𝕜 n id (range I) (I x) := cont_diff_id.cont_diff_at.cont_diff_within_at
  apply this.congr fun y hy => _
  · simp only [mfld_simps]
  · simp only [ModelWithCorners.right_inv I hy, mfld_simps]
#align cont_diff_within_at_prop_id contDiffWithinAtProp_id

/-- A function is `n` times continuously differentiable within a set at a point in a manifold if
it is continuous and it is `n` times continuously differentiable in this set around this point, when
read in the preferred chart at this point. -/
def ContMdiffWithinAt (n : ℕ∞) (f : M → M') (s : Set M) (x : M) :=
  LiftPropWithinAt (ContDiffWithinAtProp I I' n) f s x
#align cont_mdiff_within_at ContMdiffWithinAt

/-- Abbreviation for `cont_mdiff_within_at I I' ⊤ f s x`. See also documentation for `smooth`.
-/
@[reducible]
def SmoothWithinAt (f : M → M') (s : Set M) (x : M) :=
  ContMdiffWithinAt I I' ⊤ f s x
#align smooth_within_at SmoothWithinAt

/-- A function is `n` times continuously differentiable at a point in a manifold if
it is continuous and it is `n` times continuously differentiable around this point, when
read in the preferred chart at this point. -/
def ContMdiffAt (n : ℕ∞) (f : M → M') (x : M) :=
  ContMdiffWithinAt I I' n f univ x
#align cont_mdiff_at ContMdiffAt

theorem contMdiffAt_iff {n : ℕ∞} {f : M → M'} {x : M} :
    ContMdiffAt I I' n f x ↔
      ContinuousAt f x ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm) (range I)
          (extChartAt I x x) :=
  liftPropAt_iff.trans <| by rw [ContDiffWithinAtProp, preimage_univ, univ_inter]; rfl
#align cont_mdiff_at_iff contMdiffAt_iff

/-- Abbreviation for `cont_mdiff_at I I' ⊤ f x`. See also documentation for `smooth`. -/
@[reducible]
def SmoothAt (f : M → M') (x : M) :=
  ContMdiffAt I I' ⊤ f x
#align smooth_at SmoothAt

/-- A function is `n` times continuously differentiable in a set of a manifold if it is continuous
and, for any pair of points, it is `n` times continuously differentiable on this set in the charts
around these points. -/
def ContMdiffOn (n : ℕ∞) (f : M → M') (s : Set M) :=
  ∀ x ∈ s, ContMdiffWithinAt I I' n f s x
#align cont_mdiff_on ContMdiffOn

/-- Abbreviation for `cont_mdiff_on I I' ⊤ f s`. See also documentation for `smooth`. -/
@[reducible]
def SmoothOn (f : M → M') (s : Set M) :=
  ContMdiffOn I I' ⊤ f s
#align smooth_on SmoothOn

/-- A function is `n` times continuously differentiable in a manifold if it is continuous
and, for any pair of points, it is `n` times continuously differentiable in the charts
around these points. -/
def ContMdiff (n : ℕ∞) (f : M → M') :=
  ∀ x, ContMdiffAt I I' n f x
#align cont_mdiff ContMdiff

/-- Abbreviation for `cont_mdiff I I' ⊤ f`.
Short note to work with these abbreviations: a lemma of the form `cont_mdiff_foo.bar` will
apply fine to an assumption `smooth_foo` using dot notation or normal notation.
If the consequence `bar` of the lemma involves `cont_diff`, it is still better to restate
the lemma replacing `cont_diff` with `smooth` both in the assumption and in the conclusion,
to make it possible to use `smooth` consistently.
This also applies to `smooth_at`, `smooth_on` and `smooth_within_at`.-/
@[reducible]
def Smooth (f : M → M') :=
  ContMdiff I I' ⊤ f
#align smooth Smooth

/-! ### Basic properties of smooth functions between manifolds -/


variable {I I'}

theorem ContMdiff.smooth (h : ContMdiff I I' ⊤ f) : Smooth I I' f :=
  h
#align cont_mdiff.smooth ContMdiff.smooth

theorem Smooth.contMdiff (h : Smooth I I' f) : ContMdiff I I' ⊤ f :=
  h
#align smooth.cont_mdiff Smooth.contMdiff

theorem ContMdiffOn.smoothOn (h : ContMdiffOn I I' ⊤ f s) : SmoothOn I I' f s :=
  h
#align cont_mdiff_on.smooth_on ContMdiffOn.smoothOn

theorem SmoothOn.contMdiffOn (h : SmoothOn I I' f s) : ContMdiffOn I I' ⊤ f s :=
  h
#align smooth_on.cont_mdiff_on SmoothOn.contMdiffOn

theorem ContMdiffAt.smoothAt (h : ContMdiffAt I I' ⊤ f x) : SmoothAt I I' f x :=
  h
#align cont_mdiff_at.smooth_at ContMdiffAt.smoothAt

theorem SmoothAt.contMdiffAt (h : SmoothAt I I' f x) : ContMdiffAt I I' ⊤ f x :=
  h
#align smooth_at.cont_mdiff_at SmoothAt.contMdiffAt

theorem ContMdiffWithinAt.smoothWithinAt (h : ContMdiffWithinAt I I' ⊤ f s x) :
    SmoothWithinAt I I' f s x :=
  h
#align cont_mdiff_within_at.smooth_within_at ContMdiffWithinAt.smoothWithinAt

theorem SmoothWithinAt.contMdiffWithinAt (h : SmoothWithinAt I I' f s x) :
    ContMdiffWithinAt I I' ⊤ f s x :=
  h
#align smooth_within_at.cont_mdiff_within_at SmoothWithinAt.contMdiffWithinAt

theorem ContMdiff.contMdiffAt (h : ContMdiff I I' n f) : ContMdiffAt I I' n f x :=
  h x
#align cont_mdiff.cont_mdiff_at ContMdiff.contMdiffAt

theorem Smooth.smoothAt (h : Smooth I I' f) : SmoothAt I I' f x :=
  ContMdiff.contMdiffAt h
#align smooth.smooth_at Smooth.smoothAt

theorem contMdiffWithinAt_univ : ContMdiffWithinAt I I' n f univ x ↔ ContMdiffAt I I' n f x :=
  Iff.rfl
#align cont_mdiff_within_at_univ contMdiffWithinAt_univ

theorem smoothWithinAt_univ : SmoothWithinAt I I' f univ x ↔ SmoothAt I I' f x :=
  contMdiffWithinAt_univ
#align smooth_within_at_univ smoothWithinAt_univ

theorem contMdiffOn_univ : ContMdiffOn I I' n f univ ↔ ContMdiff I I' n f := by
  simp only [ContMdiffOn, ContMdiff, contMdiffWithinAt_univ, forall_prop_of_true, mem_univ]
#align cont_mdiff_on_univ contMdiffOn_univ

theorem smoothOn_univ : SmoothOn I I' f univ ↔ Smooth I I' f :=
  contMdiffOn_univ
#align smooth_on_univ smoothOn_univ

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart. -/
theorem contMdiffWithinAt_iff :
    ContMdiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) :=
  Iff.rfl
#align cont_mdiff_within_at_iff contMdiffWithinAt_iff

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart. This form states smoothness of `f`
written in such a way that the set is restricted to lie within the domain/codomain of the
corresponding charts.
Even though this expression is more complicated than the one in `cont_mdiff_within_at_iff`, it is
a smaller set, but their germs at `ext_chart_at I x x` are equal. It is sometimes useful to rewrite
using this in the goal.
-/
theorem contMdiffWithinAt_iff' :
    ContMdiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).target ∩
            (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' (f x)).source))
          (extChartAt I x x) := by
  rw [contMdiffWithinAt_iff, and_congr_right_iff]
  set e := extChartAt I x; set e' := extChartAt I' (f x)
  refine' fun hc => contDiffWithinAt_congr_nhds _
  rw [← e.image_source_inter_eq', ← map_extChartAt_nhdsWithin_eq_image, ← map_extChartAt_nhdsWithin,
    inter_comm, nhdsWithin_inter_of_mem]
  exact hc (extChartAt_source_mem_nhds _ _)
#align cont_mdiff_within_at_iff' contMdiffWithinAt_iff'

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart in the target. -/
theorem contMdiffWithinAt_iff_target :
    ContMdiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧ ContMdiffWithinAt I 𝓘(𝕜, E') n (extChartAt I' (f x) ∘ f) s x := by
  simp_rw [ContMdiffWithinAt, lift_prop_within_at, ← and_assoc']
  have cont :
    ContinuousWithinAt f s x ∧ ContinuousWithinAt (extChartAt I' (f x) ∘ f) s x ↔
      ContinuousWithinAt f s x := by
    refine' ⟨fun h => h.1, fun h => ⟨h, _⟩⟩
    have h₂ := (chart_at H' (f x)).continuous_toFun.ContinuousWithinAt (mem_chart_source _ _)
    refine' ((I'.continuous_at.comp_continuous_within_at h₂).comp' h).mono_of_mem _
    exact
      inter_mem self_mem_nhdsWithin
        (h.preimage_mem_nhds_within <| (chart_at _ _).open_source.mem_nhds <| mem_chart_source _ _)
  simp_rw [Cont, ContDiffWithinAtProp, extChartAt, LocalHomeomorph.extend, LocalEquiv.coe_trans,
    ModelWithCorners.toLocalEquiv_coe, LocalHomeomorph.coe_coe, modelWithCornersSelf_coe,
    chartAt_self_eq, LocalHomeomorph.refl_apply, comp.left_id]
#align cont_mdiff_within_at_iff_target contMdiffWithinAt_iff_target

theorem smoothWithinAt_iff :
    SmoothWithinAt I I' f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 ∞ (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) :=
  contMdiffWithinAt_iff
#align smooth_within_at_iff smoothWithinAt_iff

theorem smoothWithinAt_iff_target :
    SmoothWithinAt I I' f s x ↔
      ContinuousWithinAt f s x ∧ SmoothWithinAt I 𝓘(𝕜, E') (extChartAt I' (f x) ∘ f) s x :=
  contMdiffWithinAt_iff_target
#align smooth_within_at_iff_target smoothWithinAt_iff_target

theorem contMdiffAt_iff_target {x : M} :
    ContMdiffAt I I' n f x ↔
      ContinuousAt f x ∧ ContMdiffAt I 𝓘(𝕜, E') n (extChartAt I' (f x) ∘ f) x :=
  by rw [ContMdiffAt, ContMdiffAt, contMdiffWithinAt_iff_target, continuousWithinAt_univ]
#align cont_mdiff_at_iff_target contMdiffAt_iff_target

theorem smoothAt_iff_target {x : M} :
    SmoothAt I I' f x ↔ ContinuousAt f x ∧ SmoothAt I 𝓘(𝕜, E') (extChartAt I' (f x) ∘ f) x :=
  contMdiffAt_iff_target
#align smooth_at_iff_target smoothAt_iff_target

theorem contMdiffWithinAt_iff_of_mem_maximalAtlas {x : M} (he : e ∈ maximalAtlas I M)
    (he' : e' ∈ maximalAtlas I' M') (hx : x ∈ e.source) (hy : f x ∈ e'.source) :
    ContMdiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm)
          ((e.extend I).symm ⁻¹' s ∩ range I) (e.extend I x) :=
  (cont_diff_within_at_localInvariantProp I I' n).liftPropWithinAt_indep_chart he hx he' hy
#align cont_mdiff_within_at_iff_of_mem_maximal_atlas contMdiffWithinAt_iff_of_mem_maximalAtlas

/-- An alternative formulation of `cont_mdiff_within_at_iff_of_mem_maximal_atlas`
  if the set if `s` lies in `e.source`. -/
theorem contMdiffWithinAt_iff_image {x : M} (he : e ∈ maximalAtlas I M)
    (he' : e' ∈ maximalAtlas I' M') (hs : s ⊆ e.source) (hx : x ∈ e.source) (hy : f x ∈ e'.source) :
    ContMdiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s)
          (e.extend I x) := by
  rw [contMdiffWithinAt_iff_of_mem_maximalAtlas he he' hx hy, and_congr_right_iff]
  refine' fun hf => contDiffWithinAt_congr_nhds _
  simp_rw [nhdsWithin_eq_iff_eventuallyEq, e.extend_symm_preimage_inter_range_eventually_eq I hs hx]
#align cont_mdiff_within_at_iff_image contMdiffWithinAt_iff_image

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in any chart containing that point. -/
theorem contMdiffWithinAt_iff_of_mem_source {x' : M} {y : M'} (hx : x' ∈ (chartAt H x).source)
    (hy : f x' ∈ (chartAt H' y).source) :
    ContMdiffWithinAt I I' n f s x' ↔
      ContinuousWithinAt f s x' ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x') :=
  contMdiffWithinAt_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas _ x)
    (chart_mem_maximalAtlas _ y) hx hy
#align cont_mdiff_within_at_iff_of_mem_source contMdiffWithinAt_iff_of_mem_source

theorem contMdiffWithinAt_iff_of_mem_source' {x' : M} {y : M'} (hx : x' ∈ (chartAt H x).source)
    (hy : f x' ∈ (chartAt H' y).source) :
    ContMdiffWithinAt I I' n f s x' ↔
      ContinuousWithinAt f s x' ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).source))
          (extChartAt I x x') := by
  refine' (contMdiffWithinAt_iff_of_mem_source hx hy).trans _
  rw [← extChartAt_source I] at hx 
  rw [← extChartAt_source I'] at hy 
  rw [and_congr_right_iff]
  set e := extChartAt I x; set e' := extChartAt I' (f x)
  refine' fun hc => contDiffWithinAt_congr_nhds _
  rw [← e.image_source_inter_eq', ← map_extChartAt_nhdsWithin_eq_image' I x hx, ←
    map_extChartAt_nhdsWithin' I x hx, inter_comm, nhdsWithin_inter_of_mem]
  exact hc (extChartAt_source_mem_nhds' _ _ hy)
#align cont_mdiff_within_at_iff_of_mem_source' contMdiffWithinAt_iff_of_mem_source'

theorem contMdiffAt_iff_of_mem_source {x' : M} {y : M'} (hx : x' ∈ (chartAt H x).source)
    (hy : f x' ∈ (chartAt H' y).source) :
    ContMdiffAt I I' n f x' ↔
      ContinuousAt f x' ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (range I)
          (extChartAt I x x') :=
  (contMdiffWithinAt_iff_of_mem_source hx hy).trans <| by
    rw [continuousWithinAt_univ, preimage_univ, univ_inter]
#align cont_mdiff_at_iff_of_mem_source contMdiffAt_iff_of_mem_source

theorem contMdiffWithinAt_iff_target_of_mem_source {x : M} {y : M'}
    (hy : f x ∈ (chartAt H' y).source) :
    ContMdiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧ ContMdiffWithinAt I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) s x := by
  simp_rw [ContMdiffWithinAt]
  rw [(cont_diff_within_at_localInvariantProp I I' n).liftPropWithinAt_indep_chart_target
      (chart_mem_maximal_atlas I' y) hy,
    and_congr_right]
  intro hf
  simp_rw [StructureGroupoid.liftPropWithinAt_self_target]
  simp_rw [((chart_at H' y).ContinuousAt hy).comp_continuousWithinAt hf]
  rw [← extChartAt_source I'] at hy 
  simp_rw [(continuousAt_extChartAt' I' _ hy).comp_continuousWithinAt hf]
  rfl
#align cont_mdiff_within_at_iff_target_of_mem_source contMdiffWithinAt_iff_target_of_mem_source

theorem contMdiffAt_iff_target_of_mem_source {x : M} {y : M'} (hy : f x ∈ (chartAt H' y).source) :
    ContMdiffAt I I' n f x ↔ ContinuousAt f x ∧ ContMdiffAt I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) x :=
  by
  rw [ContMdiffAt, contMdiffWithinAt_iff_target_of_mem_source hy, continuousWithinAt_univ,
    ContMdiffAt]
  infer_instance
#align cont_mdiff_at_iff_target_of_mem_source contMdiffAt_iff_target_of_mem_source

theorem contMdiffWithinAt_iff_source_of_mem_maximalAtlas (he : e ∈ maximalAtlas I M)
    (hx : x ∈ e.source) :
    ContMdiffWithinAt I I' n f s x ↔
      ContMdiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (e.extend I).symm) ((e.extend I).symm ⁻¹' s ∩ range I)
        (e.extend I x) := by
  have h2x := hx; rw [← e.extend_source I] at h2x 
  simp_rw [ContMdiffWithinAt,
    (cont_diff_within_at_localInvariantProp I I' n).liftPropWithinAt_indep_chart_source he hx,
    StructureGroupoid.liftPropWithinAt_self_source,
    e.extend_symm_continuous_within_at_comp_right_iff, contDiffWithinAtProp_self_source,
    ContDiffWithinAtProp, Function.comp, e.left_inv hx, (e.extend I).left_inv h2x]
  rfl
#align cont_mdiff_within_at_iff_source_of_mem_maximal_atlas contMdiffWithinAt_iff_source_of_mem_maximalAtlas

theorem contMdiffWithinAt_iff_source_of_mem_source {x' : M} (hx' : x' ∈ (chartAt H x).source) :
    ContMdiffWithinAt I I' n f s x' ↔
      ContMdiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (extChartAt I x).symm)
        ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x') :=
  contMdiffWithinAt_iff_source_of_mem_maximalAtlas (chart_mem_maximalAtlas I x) hx'
#align cont_mdiff_within_at_iff_source_of_mem_source contMdiffWithinAt_iff_source_of_mem_source

theorem contMdiffAt_iff_source_of_mem_source {x' : M} (hx' : x' ∈ (chartAt H x).source) :
    ContMdiffAt I I' n f x' ↔
      ContMdiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x') := by
  simp_rw [ContMdiffAt, contMdiffWithinAt_iff_source_of_mem_source hx', preimage_univ, univ_inter]
#align cont_mdiff_at_iff_source_of_mem_source contMdiffAt_iff_source_of_mem_source

theorem contMdiffOn_iff_of_mem_maximalAtlas (he : e ∈ maximalAtlas I M)
    (he' : e' ∈ maximalAtlas I' M') (hs : s ⊆ e.source) (h2s : MapsTo f s e'.source) :
    ContMdiffOn I I' n f s ↔
      ContinuousOn f s ∧ ContDiffOn 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s) :=
  by
  simp_rw [ContinuousOn, ContDiffOn, Set.ball_image_iff, ← forall_and, ContMdiffOn]
  exact forall₂_congr fun x hx => contMdiffWithinAt_iff_image he he' hs (hs hx) (h2s hx)
#align cont_mdiff_on_iff_of_mem_maximal_atlas contMdiffOn_iff_of_mem_maximalAtlas

/-- If the set where you want `f` to be smooth lies entirely in a single chart, and `f` maps it
  into a single chart, the smoothness of `f` on that set can be expressed by purely looking in
  these charts.
  Note: this lemma uses `ext_chart_at I x '' s` instead of `(ext_chart_at I x).symm ⁻¹' s` to ensure
  that this set lies in `(ext_chart_at I x).target`. -/
theorem contMdiffOn_iff_of_subset_source {x : M} {y : M'} (hs : s ⊆ (chartAt H x).source)
    (h2s : MapsTo f s (chartAt H' y).source) :
    ContMdiffOn I I' n f s ↔
      ContinuousOn f s ∧
        ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (extChartAt I x '' s) :=
  contMdiffOn_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas I x) (chart_mem_maximalAtlas I' y) hs
    h2s
#align cont_mdiff_on_iff_of_subset_source contMdiffOn_iff_of_subset_source

/-- One can reformulate smoothness on a set as continuity on this set, and smoothness in any
extended chart. -/
theorem contMdiffOn_iff :
    ContMdiffOn I I' n f s ↔
      ContinuousOn f s ∧
        ∀ (x : M) (y : M'),
          ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target ∩
              (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).source)) := by
  constructor
  · intro h
    refine' ⟨fun x hx => (h x hx).1, fun x y z hz => _⟩
    simp only [mfld_simps] at hz 
    let w := (extChartAt I x).symm z
    have : w ∈ s := by simp only [w, hz, mfld_simps]
    specialize h w this
    have w1 : w ∈ (chart_at H x).source := by simp only [w, hz, mfld_simps]
    have w2 : f w ∈ (chart_at H' y).source := by simp only [w, hz, mfld_simps]
    convert ((contMdiffWithinAt_iff_of_mem_source w1 w2).mp h).2.mono _
    · simp only [w, hz, mfld_simps]
    · mfld_set_tac
  · rintro ⟨hcont, hdiff⟩ x hx
    refine' (cont_diff_within_at_localInvariantProp I I' n).liftPropWithinAt_iff.mpr _
    refine' ⟨hcont x hx, _⟩
    dsimp [ContDiffWithinAtProp]
    convert hdiff x (f x) (extChartAt I x x) (by simp only [hx, mfld_simps]) using 1
    mfld_set_tac
#align cont_mdiff_on_iff contMdiffOn_iff

/-- One can reformulate smoothness on a set as continuity on this set, and smoothness in any
extended chart in the target. -/
theorem contMdiffOn_iff_target :
    ContMdiffOn I I' n f s ↔
      ContinuousOn f s ∧
        ∀ y : M',
          ContMdiffOn I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) (s ∩ f ⁻¹' (extChartAt I' y).source) := by
  inhabit E'
  simp only [contMdiffOn_iff, ModelWithCorners.source_eq, chartAt_self_eq,
    LocalHomeomorph.refl_localEquiv, LocalEquiv.refl_trans, extChartAt, LocalHomeomorph.extend,
    Set.preimage_univ, Set.inter_univ, and_congr_right_iff]
  intro h
  constructor
  · refine' fun h' y => ⟨_, fun x _ => h' x y⟩
    have h'' : ContinuousOn _ univ := (ModelWithCorners.continuous I').ContinuousOn
    convert (h''.comp' (chart_at H' y).continuous_toFun).comp' h
    simp
  · exact fun h' x y => (h' y).2 x default
#align cont_mdiff_on_iff_target contMdiffOn_iff_target

theorem smoothOn_iff :
    SmoothOn I I' f s ↔
      ContinuousOn f s ∧
        ∀ (x : M) (y : M'),
          ContDiffOn 𝕜 ⊤ (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target ∩
              (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).source)) :=
  contMdiffOn_iff
#align smooth_on_iff smoothOn_iff

theorem smoothOn_iff_target :
    SmoothOn I I' f s ↔
      ContinuousOn f s ∧
        ∀ y : M', SmoothOn I 𝓘(𝕜, E') (extChartAt I' y ∘ f) (s ∩ f ⁻¹' (extChartAt I' y).source) :=
  contMdiffOn_iff_target
#align smooth_on_iff_target smoothOn_iff_target

/-- One can reformulate smoothness as continuity and smoothness in any extended chart. -/
theorem contMdiff_iff :
    ContMdiff I I' n f ↔
      Continuous f ∧
        ∀ (x : M) (y : M'),
          ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target ∩
              (extChartAt I x).symm ⁻¹' (f ⁻¹' (extChartAt I' y).source)) :=
  by simp [← contMdiffOn_univ, contMdiffOn_iff, continuous_iff_continuousOn_univ]
#align cont_mdiff_iff contMdiff_iff

/-- One can reformulate smoothness as continuity and smoothness in any extended chart in the
target. -/
theorem contMdiff_iff_target :
    ContMdiff I I' n f ↔
      Continuous f ∧
        ∀ y : M', ContMdiffOn I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) (f ⁻¹' (extChartAt I' y).source) :=
  by
  rw [← contMdiffOn_univ, contMdiffOn_iff_target]
  simp [continuous_iff_continuousOn_univ]
#align cont_mdiff_iff_target contMdiff_iff_target

theorem smooth_iff :
    Smooth I I' f ↔
      Continuous f ∧
        ∀ (x : M) (y : M'),
          ContDiffOn 𝕜 ⊤ (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target ∩
              (extChartAt I x).symm ⁻¹' (f ⁻¹' (extChartAt I' y).source)) :=
  contMdiff_iff
#align smooth_iff smooth_iff

theorem smooth_iff_target :
    Smooth I I' f ↔
      Continuous f ∧
        ∀ y : M', SmoothOn I 𝓘(𝕜, E') (extChartAt I' y ∘ f) (f ⁻¹' (extChartAt I' y).source) :=
  contMdiff_iff_target
#align smooth_iff_target smooth_iff_target

/-! ### Deducing smoothness from higher smoothness -/


theorem ContMdiffWithinAt.of_le (hf : ContMdiffWithinAt I I' n f s x) (le : m ≤ n) :
    ContMdiffWithinAt I I' m f s x :=
  ⟨hf.1, hf.2.of_le le⟩
#align cont_mdiff_within_at.of_le ContMdiffWithinAt.of_le

theorem ContMdiffAt.of_le (hf : ContMdiffAt I I' n f x) (le : m ≤ n) : ContMdiffAt I I' m f x :=
  ContMdiffWithinAt.of_le hf le
#align cont_mdiff_at.of_le ContMdiffAt.of_le

theorem ContMdiffOn.of_le (hf : ContMdiffOn I I' n f s) (le : m ≤ n) : ContMdiffOn I I' m f s :=
  fun x hx => (hf x hx).of_le le
#align cont_mdiff_on.of_le ContMdiffOn.of_le

theorem ContMdiff.of_le (hf : ContMdiff I I' n f) (le : m ≤ n) : ContMdiff I I' m f := fun x =>
  (hf x).of_le le
#align cont_mdiff.of_le ContMdiff.of_le

/-! ### Deducing smoothness from smoothness one step beyond -/


theorem ContMdiffWithinAt.of_succ {n : ℕ} (h : ContMdiffWithinAt I I' n.succ f s x) :
    ContMdiffWithinAt I I' n f s x :=
  h.of_le (WithTop.coe_le_coe.2 (Nat.le_succ n))
#align cont_mdiff_within_at.of_succ ContMdiffWithinAt.of_succ

theorem ContMdiffAt.of_succ {n : ℕ} (h : ContMdiffAt I I' n.succ f x) : ContMdiffAt I I' n f x :=
  ContMdiffWithinAt.of_succ h
#align cont_mdiff_at.of_succ ContMdiffAt.of_succ

theorem ContMdiffOn.of_succ {n : ℕ} (h : ContMdiffOn I I' n.succ f s) : ContMdiffOn I I' n f s :=
  fun x hx => (h x hx).of_succ
#align cont_mdiff_on.of_succ ContMdiffOn.of_succ

theorem ContMdiff.of_succ {n : ℕ} (h : ContMdiff I I' n.succ f) : ContMdiff I I' n f := fun x =>
  (h x).of_succ
#align cont_mdiff.of_succ ContMdiff.of_succ

/-! ### Deducing continuity from smoothness -/


theorem ContMdiffWithinAt.continuousWithinAt (hf : ContMdiffWithinAt I I' n f s x) :
    ContinuousWithinAt f s x :=
  hf.1
#align cont_mdiff_within_at.continuous_within_at ContMdiffWithinAt.continuousWithinAt

theorem ContMdiffAt.continuousAt (hf : ContMdiffAt I I' n f x) : ContinuousAt f x :=
  (continuousWithinAt_univ _ _).1 <| ContMdiffWithinAt.continuousWithinAt hf
#align cont_mdiff_at.continuous_at ContMdiffAt.continuousAt

theorem ContMdiffOn.continuousOn (hf : ContMdiffOn I I' n f s) : ContinuousOn f s := fun x hx =>
  (hf x hx).ContinuousWithinAt
#align cont_mdiff_on.continuous_on ContMdiffOn.continuousOn

theorem ContMdiff.continuous (hf : ContMdiff I I' n f) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (hf x).ContinuousAt
#align cont_mdiff.continuous ContMdiff.continuous

/-! ### `C^∞` smoothness -/


theorem contMdiffWithinAt_top :
    SmoothWithinAt I I' f s x ↔ ∀ n : ℕ, ContMdiffWithinAt I I' n f s x :=
  ⟨fun h n => ⟨h.1, contDiffWithinAt_top.1 h.2 n⟩, fun H =>
    ⟨(H 0).1, contDiffWithinAt_top.2 fun n => (H n).2⟩⟩
#align cont_mdiff_within_at_top contMdiffWithinAt_top

theorem contMdiffAt_top : SmoothAt I I' f x ↔ ∀ n : ℕ, ContMdiffAt I I' n f x :=
  contMdiffWithinAt_top
#align cont_mdiff_at_top contMdiffAt_top

theorem contMdiffOn_top : SmoothOn I I' f s ↔ ∀ n : ℕ, ContMdiffOn I I' n f s :=
  ⟨fun h n => h.of_le le_top, fun h x hx => contMdiffWithinAt_top.2 fun n => h n x hx⟩
#align cont_mdiff_on_top contMdiffOn_top

theorem contMdiff_top : Smooth I I' f ↔ ∀ n : ℕ, ContMdiff I I' n f :=
  ⟨fun h n => h.of_le le_top, fun h x => contMdiffWithinAt_top.2 fun n => h n x⟩
#align cont_mdiff_top contMdiff_top

theorem contMdiffWithinAt_iff_nat :
    ContMdiffWithinAt I I' n f s x ↔ ∀ m : ℕ, (m : ℕ∞) ≤ n → ContMdiffWithinAt I I' m f s x := by
  refine' ⟨fun h m hm => h.of_le hm, fun h => _⟩
  cases n
  · exact contMdiffWithinAt_top.2 fun n => h n le_top
  · exact h n le_rfl
#align cont_mdiff_within_at_iff_nat contMdiffWithinAt_iff_nat

/-! ### Restriction to a smaller set -/


theorem ContMdiffWithinAt.mono_of_mem (hf : ContMdiffWithinAt I I' n f s x) (hts : s ∈ 𝓝[t] x) :
    ContMdiffWithinAt I I' n f t x :=
  StructureGroupoid.LocalInvariantProp.liftPropWithinAt_mono_of_mem
    (contDiffWithinAtProp_mono_of_mem I I' n) hf hts
#align cont_mdiff_within_at.mono_of_mem ContMdiffWithinAt.mono_of_mem

theorem ContMdiffWithinAt.mono (hf : ContMdiffWithinAt I I' n f s x) (hts : t ⊆ s) :
    ContMdiffWithinAt I I' n f t x :=
  hf.mono_of_mem <| mem_of_superset self_mem_nhdsWithin hts
#align cont_mdiff_within_at.mono ContMdiffWithinAt.mono

theorem contMdiffWithinAt_congr_nhds (hst : 𝓝[s] x = 𝓝[t] x) :
    ContMdiffWithinAt I I' n f s x ↔ ContMdiffWithinAt I I' n f t x :=
  ⟨fun h => h.mono_of_mem <| hst ▸ self_mem_nhdsWithin, fun h =>
    h.mono_of_mem <| hst.symm ▸ self_mem_nhdsWithin⟩
#align cont_mdiff_within_at_congr_nhds contMdiffWithinAt_congr_nhds

theorem ContMdiffAt.contMdiffWithinAt (hf : ContMdiffAt I I' n f x) :
    ContMdiffWithinAt I I' n f s x :=
  ContMdiffWithinAt.mono hf (subset_univ _)
#align cont_mdiff_at.cont_mdiff_within_at ContMdiffAt.contMdiffWithinAt

theorem SmoothAt.smoothWithinAt (hf : SmoothAt I I' f x) : SmoothWithinAt I I' f s x :=
  ContMdiffAt.contMdiffWithinAt hf
#align smooth_at.smooth_within_at SmoothAt.smoothWithinAt

theorem ContMdiffOn.mono (hf : ContMdiffOn I I' n f s) (hts : t ⊆ s) : ContMdiffOn I I' n f t :=
  fun x hx => (hf x (hts hx)).mono hts
#align cont_mdiff_on.mono ContMdiffOn.mono

theorem ContMdiff.contMdiffOn (hf : ContMdiff I I' n f) : ContMdiffOn I I' n f s := fun x hx =>
  (hf x).ContMdiffWithinAt
#align cont_mdiff.cont_mdiff_on ContMdiff.contMdiffOn

theorem Smooth.smoothOn (hf : Smooth I I' f) : SmoothOn I I' f s :=
  ContMdiff.contMdiffOn hf
#align smooth.smooth_on Smooth.smoothOn

theorem contMdiffWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    ContMdiffWithinAt I I' n f (s ∩ t) x ↔ ContMdiffWithinAt I I' n f s x :=
  (cont_diff_within_at_localInvariantProp I I' n).liftPropWithinAt_inter' ht
#align cont_mdiff_within_at_inter' contMdiffWithinAt_inter'

theorem contMdiffWithinAt_inter (ht : t ∈ 𝓝 x) :
    ContMdiffWithinAt I I' n f (s ∩ t) x ↔ ContMdiffWithinAt I I' n f s x :=
  (cont_diff_within_at_localInvariantProp I I' n).liftPropWithinAt_inter ht
#align cont_mdiff_within_at_inter contMdiffWithinAt_inter

theorem ContMdiffWithinAt.contMdiffAt (h : ContMdiffWithinAt I I' n f s x) (ht : s ∈ 𝓝 x) :
    ContMdiffAt I I' n f x :=
  (cont_diff_within_at_localInvariantProp I I' n).liftPropAt_of_liftPropWithinAt h ht
#align cont_mdiff_within_at.cont_mdiff_at ContMdiffWithinAt.contMdiffAt

theorem SmoothWithinAt.smoothAt (h : SmoothWithinAt I I' f s x) (ht : s ∈ 𝓝 x) :
    SmoothAt I I' f x :=
  ContMdiffWithinAt.contMdiffAt h ht
#align smooth_within_at.smooth_at SmoothWithinAt.smoothAt

theorem ContMdiffOn.contMdiffAt (h : ContMdiffOn I I' n f s) (hx : s ∈ 𝓝 x) :
    ContMdiffAt I I' n f x :=
  (h x (mem_of_mem_nhds hx)).ContMdiffAt hx
#align cont_mdiff_on.cont_mdiff_at ContMdiffOn.contMdiffAt

theorem SmoothOn.smoothAt (h : SmoothOn I I' f s) (hx : s ∈ 𝓝 x) : SmoothAt I I' f x :=
  h.ContMdiffAt hx
#align smooth_on.smooth_at SmoothOn.smoothAt

theorem contMdiffOn_iff_source_of_mem_maximalAtlas (he : e ∈ maximalAtlas I M) (hs : s ⊆ e.source) :
    ContMdiffOn I I' n f s ↔ ContMdiffOn 𝓘(𝕜, E) I' n (f ∘ (e.extend I).symm) (e.extend I '' s) :=
  by
  simp_rw [ContMdiffOn, Set.ball_image_iff]
  refine' forall₂_congr fun x hx => _
  rw [contMdiffWithinAt_iff_source_of_mem_maximalAtlas he (hs hx)]
  apply contMdiffWithinAt_congr_nhds
  simp_rw [nhdsWithin_eq_iff_eventuallyEq,
    e.extend_symm_preimage_inter_range_eventually_eq I hs (hs hx)]
#align cont_mdiff_on_iff_source_of_mem_maximal_atlas contMdiffOn_iff_source_of_mem_maximalAtlas

/-- A function is `C^n` within a set at a point, for `n : ℕ`, if and only if it is `C^n` on
a neighborhood of this point. -/
theorem contMdiffWithinAt_iff_contMdiffOn_nhds {n : ℕ} :
    ContMdiffWithinAt I I' n f s x ↔ ∃ u ∈ 𝓝[insert x s] x, ContMdiffOn I I' n f u := by
  constructor
  · intro h
    -- the property is true in charts. We will pull such a good neighborhood in the chart to the
    -- manifold. For this, we need to restrict to a small enough set where everything makes sense
    obtain ⟨o, o_open, xo, ho, h'o⟩ :
      ∃ o : Set M,
        IsOpen o ∧ x ∈ o ∧ o ⊆ (chart_at H x).source ∧ o ∩ s ⊆ f ⁻¹' (chart_at H' (f x)).source :=
      by
      have : (chart_at H' (f x)).source ∈ 𝓝 (f x) :=
        IsOpen.mem_nhds (LocalHomeomorph.open_source _) (mem_chart_source H' (f x))
      rcases mem_nhdsWithin.1 (h.1.preimage_mem_nhdsWithin this) with ⟨u, u_open, xu, hu⟩
      refine' ⟨u ∩ (chart_at H x).source, _, ⟨xu, mem_chart_source _ _⟩, _, _⟩
      · exact IsOpen.inter u_open (LocalHomeomorph.open_source _)
      · intro y hy; exact hy.2
      · intro y hy; exact hu ⟨hy.1.1, hy.2⟩
    have h' : ContMdiffWithinAt I I' n f (s ∩ o) x := h.mono (inter_subset_left _ _)
    simp only [ContMdiffWithinAt, lift_prop_within_at, ContDiffWithinAtProp] at h' 
    -- let `u` be a good neighborhood in the chart where the function is smooth
    rcases h.2.ContDiffOn le_rfl with ⟨u, u_nhds, u_subset, hu⟩
    -- pull it back to the manifold, and intersect with a suitable neighborhood of `x`, to get the
    -- desired good neighborhood `v`.
    let v := insert x s ∩ o ∩ extChartAt I x ⁻¹' u
    have v_incl : v ⊆ (chart_at H x).source := fun y hy => ho hy.1.2
    have v_incl' : ∀ y ∈ v, f y ∈ (chart_at H' (f x)).source := by
      intro y hy
      rcases hy.1.1 with (rfl | h')
      · simp only [mfld_simps]
      · apply h'o ⟨hy.1.2, h'⟩
    refine' ⟨v, _, _⟩
    show v ∈ 𝓝[insert x s] x
    · rw [nhdsWithin_restrict _ xo o_open]
      refine' Filter.inter_mem self_mem_nhdsWithin _
      suffices : u ∈ 𝓝[extChartAt I x '' (insert x s ∩ o)] extChartAt I x x
      exact (continuousAt_extChartAt I x).ContinuousWithinAt.preimage_mem_nhdsWithin' this
      apply nhdsWithin_mono _ _ u_nhds
      rw [image_subset_iff]
      intro y hy
      rcases hy.1 with (rfl | h')
      · simp only [mem_insert_iff, mfld_simps]
      · simp only [mem_insert_iff, ho hy.2, h', h'o ⟨hy.2, h'⟩, mfld_simps]
    show ContMdiffOn I I' n f v
    · intro y hy
      have : ContinuousWithinAt f v y := by
        apply
          (((continuousOn_extChartAt_symm I' (f x) _ _).comp' (hu _ hy.2).ContinuousWithinAt).comp'
              (continuousOn_extChartAt I x _ _)).congr_mono
        · intro z hz
          simp only [v_incl hz, v_incl' z hz, mfld_simps]
        · intro z hz
          simp only [v_incl hz, v_incl' z hz, mfld_simps]
          exact hz.2
        · simp only [v_incl hy, v_incl' y hy, mfld_simps]
        · simp only [v_incl hy, v_incl' y hy, mfld_simps]
        · simp only [v_incl hy, mfld_simps]
      refine' (contMdiffWithinAt_iff_of_mem_source' (v_incl hy) (v_incl' y hy)).mpr ⟨this, _⟩
      · apply hu.mono
        · intro z hz
          simp only [v, mfld_simps] at hz 
          have : I ((chart_at H x) ((chart_at H x).symm (I.symm z))) ∈ u := by simp only [hz]
          simpa only [hz, mfld_simps] using this
        · have exty : I (chart_at H x y) ∈ u := hy.2
          simp only [v_incl hy, v_incl' y hy, exty, hy.1.1, hy.1.2, mfld_simps]
  · rintro ⟨u, u_nhds, hu⟩
    have : ContMdiffWithinAt I I' (↑n) f (insert x s ∩ u) x :=
      haveI : x ∈ insert x s := mem_insert x s
      hu.mono (inter_subset_right _ _) _ ⟨this, mem_of_mem_nhdsWithin this u_nhds⟩
    rw [contMdiffWithinAt_inter' u_nhds] at this 
    exact this.mono (subset_insert x s)
#align cont_mdiff_within_at_iff_cont_mdiff_on_nhds contMdiffWithinAt_iff_contMdiffOn_nhds

/-- A function is `C^n` at a point, for `n : ℕ`, if and only if it is `C^n` on
a neighborhood of this point. -/
theorem contMdiffAt_iff_contMdiffOn_nhds {n : ℕ} :
    ContMdiffAt I I' n f x ↔ ∃ u ∈ 𝓝 x, ContMdiffOn I I' n f u := by
  simp [← contMdiffWithinAt_univ, contMdiffWithinAt_iff_contMdiffOn_nhds, nhdsWithin_univ]
#align cont_mdiff_at_iff_cont_mdiff_on_nhds contMdiffAt_iff_contMdiffOn_nhds

/-- Note: This does not hold for `n = ∞`. `f` being `C^∞` at `x` means that for every `n`, `f` is
`C^n` on some neighborhood of `x`, but this neighborhood can depend on `n`. -/
theorem contMdiffAt_iff_contMdiffAt_nhds {n : ℕ} :
    ContMdiffAt I I' n f x ↔ ∀ᶠ x' in 𝓝 x, ContMdiffAt I I' n f x' := by
  refine' ⟨_, fun h => h.self_of_nhds⟩
  rw [contMdiffAt_iff_contMdiffOn_nhds]
  rintro ⟨u, hu, h⟩
  refine' (eventually_mem_nhds.mpr hu).mono fun x' hx' => _
  exact (h x' <| mem_of_mem_nhds hx').ContMdiffAt hx'
#align cont_mdiff_at_iff_cont_mdiff_at_nhds contMdiffAt_iff_contMdiffAt_nhds

/-! ### Congruence lemmas -/


theorem ContMdiffWithinAt.congr (h : ContMdiffWithinAt I I' n f s x) (h₁ : ∀ y ∈ s, f₁ y = f y)
    (hx : f₁ x = f x) : ContMdiffWithinAt I I' n f₁ s x :=
  (cont_diff_within_at_localInvariantProp I I' n).liftPropWithinAt_congr h h₁ hx
#align cont_mdiff_within_at.congr ContMdiffWithinAt.congr

theorem contMdiffWithinAt_congr (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : f₁ x = f x) :
    ContMdiffWithinAt I I' n f₁ s x ↔ ContMdiffWithinAt I I' n f s x :=
  (cont_diff_within_at_localInvariantProp I I' n).liftPropWithinAt_congr_iff h₁ hx
#align cont_mdiff_within_at_congr contMdiffWithinAt_congr

theorem ContMdiffWithinAt.congr_of_eventuallyEq (h : ContMdiffWithinAt I I' n f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : ContMdiffWithinAt I I' n f₁ s x :=
  (cont_diff_within_at_localInvariantProp I I' n).liftPropWithinAt_congr_of_eventuallyEq h h₁ hx
#align cont_mdiff_within_at.congr_of_eventually_eq ContMdiffWithinAt.congr_of_eventuallyEq

theorem Filter.EventuallyEq.contMdiffWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    ContMdiffWithinAt I I' n f₁ s x ↔ ContMdiffWithinAt I I' n f s x :=
  (cont_diff_within_at_localInvariantProp I I' n).liftPropWithinAt_congr_iff_of_eventuallyEq h₁ hx
#align filter.eventually_eq.cont_mdiff_within_at_iff Filter.EventuallyEq.contMdiffWithinAt_iff

theorem ContMdiffAt.congr_of_eventuallyEq (h : ContMdiffAt I I' n f x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    ContMdiffAt I I' n f₁ x :=
  (cont_diff_within_at_localInvariantProp I I' n).liftPropAt_congr_of_eventuallyEq h h₁
#align cont_mdiff_at.congr_of_eventually_eq ContMdiffAt.congr_of_eventuallyEq

theorem Filter.EventuallyEq.contMdiffAt_iff (h₁ : f₁ =ᶠ[𝓝 x] f) :
    ContMdiffAt I I' n f₁ x ↔ ContMdiffAt I I' n f x :=
  (cont_diff_within_at_localInvariantProp I I' n).liftPropAt_congr_iff_of_eventuallyEq h₁
#align filter.eventually_eq.cont_mdiff_at_iff Filter.EventuallyEq.contMdiffAt_iff

theorem ContMdiffOn.congr (h : ContMdiffOn I I' n f s) (h₁ : ∀ y ∈ s, f₁ y = f y) :
    ContMdiffOn I I' n f₁ s :=
  (cont_diff_within_at_localInvariantProp I I' n).liftPropOn_congr h h₁
#align cont_mdiff_on.congr ContMdiffOn.congr

theorem contMdiffOn_congr (h₁ : ∀ y ∈ s, f₁ y = f y) :
    ContMdiffOn I I' n f₁ s ↔ ContMdiffOn I I' n f s :=
  (cont_diff_within_at_localInvariantProp I I' n).liftPropOn_congr_iff h₁
#align cont_mdiff_on_congr contMdiffOn_congr

/-! ### Locality -/


/-- Being `C^n` is a local property. -/
theorem contMdiffOn_of_locally_contMdiffOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ ContMdiffOn I I' n f (s ∩ u)) : ContMdiffOn I I' n f s :=
  (cont_diff_within_at_localInvariantProp I I' n).liftPropOn_of_locally_liftPropOn h
#align cont_mdiff_on_of_locally_cont_mdiff_on contMdiffOn_of_locally_contMdiffOn

theorem contMdiff_of_locally_contMdiffOn (h : ∀ x, ∃ u, IsOpen u ∧ x ∈ u ∧ ContMdiffOn I I' n f u) :
    ContMdiff I I' n f :=
  (cont_diff_within_at_localInvariantProp I I' n).liftProp_of_locally_liftPropOn h
#align cont_mdiff_of_locally_cont_mdiff_on contMdiff_of_locally_contMdiffOn

/-! ### Smoothness of the composition of smooth functions between manifolds -/


section Composition

/-- The composition of `C^n` functions within domains at points is `C^n`. -/
theorem ContMdiffWithinAt.comp {t : Set M'} {g : M' → M''} (x : M)
    (hg : ContMdiffWithinAt I' I'' n g t (f x)) (hf : ContMdiffWithinAt I I' n f s x)
    (st : MapsTo f s t) : ContMdiffWithinAt I I'' n (g ∘ f) s x := by
  rw [contMdiffWithinAt_iff] at hg hf ⊢
  refine' ⟨hg.1.comp hf.1 st, _⟩
  set e := extChartAt I x
  set e' := extChartAt I' (f x)
  set e'' := extChartAt I'' (g (f x))
  have : e' (f x) = (writtenInExtChartAt I I' x f) (e x) := by simp only [e, e', mfld_simps]
  rw [this] at hg 
  have A :
    ∀ᶠ y in 𝓝[e.symm ⁻¹' s ∩ range I] e x,
      y ∈ e.target ∧ f (e.symm y) ∈ t ∧ f (e.symm y) ∈ e'.source ∧ g (f (e.symm y)) ∈ e''.source :=
    by
    simp only [← map_extChartAt_nhdsWithin, eventually_map]
    filter_upwards [hf.1.Tendsto (extChartAt_source_mem_nhds I' (f x)),
      (hg.1.comp hf.1 st).Tendsto (extChartAt_source_mem_nhds I'' (g (f x))),
      inter_mem_nhdsWithin s (extChartAt_source_mem_nhds I x)]
    rintro x' (hfx' : f x' ∈ _) (hgfx' : g (f x') ∈ _) ⟨hx's, hx'⟩
    simp only [e.map_source hx', true_and_iff, e.left_inv hx', st hx's, *]
  refine'
    ((hg.2.comp _ (hf.2.mono (inter_subset_right _ _)) (inter_subset_left _ _)).mono_of_mem
          (inter_mem _ self_mem_nhdsWithin)).congr_of_eventuallyEq
      _ _
  · filter_upwards [A]
    rintro x' ⟨hx', ht, hfx', hgfx'⟩
    simp only [*, mem_preimage, writtenInExtChartAt, (· ∘ ·), mem_inter_iff, e'.left_inv,
      true_and_iff]
    exact mem_range_self _
  · filter_upwards [A]
    rintro x' ⟨hx', ht, hfx', hgfx'⟩
    simp only [*, (· ∘ ·), writtenInExtChartAt, e'.left_inv]
  · simp only [writtenInExtChartAt, (· ∘ ·), mem_extChartAt_source, e.left_inv, e'.left_inv]
#align cont_mdiff_within_at.comp ContMdiffWithinAt.comp

/-- See note [comp_of_eq lemmas] -/
theorem ContMdiffWithinAt.comp_of_eq {t : Set M'} {g : M' → M''} {x : M} {y : M'}
    (hg : ContMdiffWithinAt I' I'' n g t y) (hf : ContMdiffWithinAt I I' n f s x)
    (st : MapsTo f s t) (hx : f x = y) : ContMdiffWithinAt I I'' n (g ∘ f) s x := by subst hx;
  exact hg.comp x hf st
#align cont_mdiff_within_at.comp_of_eq ContMdiffWithinAt.comp_of_eq

/-- The composition of `C^∞` functions within domains at points is `C^∞`. -/
theorem SmoothWithinAt.comp {t : Set M'} {g : M' → M''} (x : M)
    (hg : SmoothWithinAt I' I'' g t (f x)) (hf : SmoothWithinAt I I' f s x) (st : MapsTo f s t) :
    SmoothWithinAt I I'' (g ∘ f) s x :=
  hg.comp x hf st
#align smooth_within_at.comp SmoothWithinAt.comp

/-- The composition of `C^n` functions on domains is `C^n`. -/
theorem ContMdiffOn.comp {t : Set M'} {g : M' → M''} (hg : ContMdiffOn I' I'' n g t)
    (hf : ContMdiffOn I I' n f s) (st : s ⊆ f ⁻¹' t) : ContMdiffOn I I'' n (g ∘ f) s := fun x hx =>
  (hg _ (st hx)).comp x (hf x hx) st
#align cont_mdiff_on.comp ContMdiffOn.comp

/-- The composition of `C^∞` functions on domains is `C^∞`. -/
theorem SmoothOn.comp {t : Set M'} {g : M' → M''} (hg : SmoothOn I' I'' g t)
    (hf : SmoothOn I I' f s) (st : s ⊆ f ⁻¹' t) : SmoothOn I I'' (g ∘ f) s :=
  hg.comp hf st
#align smooth_on.comp SmoothOn.comp

/-- The composition of `C^n` functions on domains is `C^n`. -/
theorem ContMdiffOn.comp' {t : Set M'} {g : M' → M''} (hg : ContMdiffOn I' I'' n g t)
    (hf : ContMdiffOn I I' n f s) : ContMdiffOn I I'' n (g ∘ f) (s ∩ f ⁻¹' t) :=
  hg.comp (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)
#align cont_mdiff_on.comp' ContMdiffOn.comp'

/-- The composition of `C^∞` functions is `C^∞`. -/
theorem SmoothOn.comp' {t : Set M'} {g : M' → M''} (hg : SmoothOn I' I'' g t)
    (hf : SmoothOn I I' f s) : SmoothOn I I'' (g ∘ f) (s ∩ f ⁻¹' t) :=
  hg.comp' hf
#align smooth_on.comp' SmoothOn.comp'

/-- The composition of `C^n` functions is `C^n`. -/
theorem ContMdiff.comp {g : M' → M''} (hg : ContMdiff I' I'' n g) (hf : ContMdiff I I' n f) :
    ContMdiff I I'' n (g ∘ f) := by
  rw [← contMdiffOn_univ] at hf hg ⊢
  exact hg.comp hf subset_preimage_univ
#align cont_mdiff.comp ContMdiff.comp

/-- The composition of `C^∞` functions is `C^∞`. -/
theorem Smooth.comp {g : M' → M''} (hg : Smooth I' I'' g) (hf : Smooth I I' f) :
    Smooth I I'' (g ∘ f) :=
  hg.comp hf
#align smooth.comp Smooth.comp

/-- The composition of `C^n` functions within domains at points is `C^n`. -/
theorem ContMdiffWithinAt.comp' {t : Set M'} {g : M' → M''} (x : M)
    (hg : ContMdiffWithinAt I' I'' n g t (f x)) (hf : ContMdiffWithinAt I I' n f s x) :
    ContMdiffWithinAt I I'' n (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp x (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)
#align cont_mdiff_within_at.comp' ContMdiffWithinAt.comp'

/-- The composition of `C^∞` functions within domains at points is `C^∞`. -/
theorem SmoothWithinAt.comp' {t : Set M'} {g : M' → M''} (x : M)
    (hg : SmoothWithinAt I' I'' g t (f x)) (hf : SmoothWithinAt I I' f s x) :
    SmoothWithinAt I I'' (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp' x hf
#align smooth_within_at.comp' SmoothWithinAt.comp'

/-- `g ∘ f` is `C^n` within `s` at `x` if `g` is `C^n` at `f x` and
`f` is `C^n` within `s` at `x`. -/
theorem ContMdiffAt.comp_contMdiffWithinAt {g : M' → M''} (x : M)
    (hg : ContMdiffAt I' I'' n g (f x)) (hf : ContMdiffWithinAt I I' n f s x) :
    ContMdiffWithinAt I I'' n (g ∘ f) s x :=
  hg.comp x hf (mapsTo_univ _ _)
#align cont_mdiff_at.comp_cont_mdiff_within_at ContMdiffAt.comp_contMdiffWithinAt

/-- `g ∘ f` is `C^∞` within `s` at `x` if `g` is `C^∞` at `f x` and
`f` is `C^∞` within `s` at `x`. -/
theorem SmoothAt.comp_smoothWithinAt {g : M' → M''} (x : M) (hg : SmoothAt I' I'' g (f x))
    (hf : SmoothWithinAt I I' f s x) : SmoothWithinAt I I'' (g ∘ f) s x :=
  hg.comp_contMdiffWithinAt x hf
#align smooth_at.comp_smooth_within_at SmoothAt.comp_smoothWithinAt

/-- The composition of `C^n` functions at points is `C^n`. -/
theorem ContMdiffAt.comp {g : M' → M''} (x : M) (hg : ContMdiffAt I' I'' n g (f x))
    (hf : ContMdiffAt I I' n f x) : ContMdiffAt I I'' n (g ∘ f) x :=
  hg.comp x hf (mapsTo_univ _ _)
#align cont_mdiff_at.comp ContMdiffAt.comp

/-- See note [comp_of_eq lemmas] -/
theorem ContMdiffAt.comp_of_eq {g : M' → M''} {x : M} {y : M'} (hg : ContMdiffAt I' I'' n g y)
    (hf : ContMdiffAt I I' n f x) (hx : f x = y) : ContMdiffAt I I'' n (g ∘ f) x := by subst hx;
  exact hg.comp x hf
#align cont_mdiff_at.comp_of_eq ContMdiffAt.comp_of_eq

/-- The composition of `C^∞` functions at points is `C^∞`. -/
theorem SmoothAt.comp {g : M' → M''} (x : M) (hg : SmoothAt I' I'' g (f x))
    (hf : SmoothAt I I' f x) : SmoothAt I I'' (g ∘ f) x :=
  hg.comp x hf
#align smooth_at.comp SmoothAt.comp

theorem ContMdiff.comp_contMdiffOn {f : M → M'} {g : M' → M''} {s : Set M}
    (hg : ContMdiff I' I'' n g) (hf : ContMdiffOn I I' n f s) : ContMdiffOn I I'' n (g ∘ f) s :=
  hg.ContMdiffOn.comp hf Set.subset_preimage_univ
#align cont_mdiff.comp_cont_mdiff_on ContMdiff.comp_contMdiffOn

theorem Smooth.comp_smoothOn {f : M → M'} {g : M' → M''} {s : Set M} (hg : Smooth I' I'' g)
    (hf : SmoothOn I I' f s) : SmoothOn I I'' (g ∘ f) s :=
  hg.SmoothOn.comp hf Set.subset_preimage_univ
#align smooth.comp_smooth_on Smooth.comp_smoothOn

theorem ContMdiffOn.comp_contMdiff {t : Set M'} {g : M' → M''} (hg : ContMdiffOn I' I'' n g t)
    (hf : ContMdiff I I' n f) (ht : ∀ x, f x ∈ t) : ContMdiff I I'' n (g ∘ f) :=
  contMdiffOn_univ.mp <| hg.comp hf.ContMdiffOn fun x _ => ht x
#align cont_mdiff_on.comp_cont_mdiff ContMdiffOn.comp_contMdiff

theorem SmoothOn.comp_smooth {t : Set M'} {g : M' → M''} (hg : SmoothOn I' I'' g t)
    (hf : Smooth I I' f) (ht : ∀ x, f x ∈ t) : Smooth I I'' (g ∘ f) :=
  hg.comp_contMdiff hf ht
#align smooth_on.comp_smooth SmoothOn.comp_smooth

end Composition

/-! ### Atlas members are smooth -/


section Atlas

theorem contMdiff_model : ContMdiff I 𝓘(𝕜, E) n I := by
  intro x
  refine' (contMdiffAt_iff _ _).mpr ⟨I.continuous_at, _⟩
  simp only [mfld_simps]
  refine' cont_diff_within_at_id.congr_of_eventually_eq _ _
  · exact eventually_eq_of_mem self_mem_nhdsWithin fun x₂ => I.right_inv
  simp_rw [Function.comp_apply, I.left_inv, id_def]
#align cont_mdiff_model contMdiff_model

theorem contMdiffOn_model_symm : ContMdiffOn 𝓘(𝕜, E) I n I.symm (range I) := by
  rw [contMdiffOn_iff]
  refine' ⟨I.continuous_on_symm, fun x y => _⟩
  simp only [mfld_simps]
  exact cont_diff_on_id.congr fun x' => I.right_inv
#align cont_mdiff_on_model_symm contMdiffOn_model_symm

/-- An atlas member is `C^n` for any `n`. -/
theorem contMdiffOn_of_mem_maximalAtlas (h : e ∈ maximalAtlas I M) : ContMdiffOn I I n e e.source :=
  ContMdiffOn.of_le
    ((cont_diff_within_at_localInvariantProp I I ∞).liftPropOn_of_mem_maximalAtlas
      (contDiffWithinAtProp_id I) h)
    le_top
#align cont_mdiff_on_of_mem_maximal_atlas contMdiffOn_of_mem_maximalAtlas

/-- The inverse of an atlas member is `C^n` for any `n`. -/
theorem contMdiffOn_symm_of_mem_maximalAtlas (h : e ∈ maximalAtlas I M) :
    ContMdiffOn I I n e.symm e.target :=
  ContMdiffOn.of_le
    ((cont_diff_within_at_localInvariantProp I I ∞).liftPropOn_symm_of_mem_maximalAtlas
      (contDiffWithinAtProp_id I) h)
    le_top
#align cont_mdiff_on_symm_of_mem_maximal_atlas contMdiffOn_symm_of_mem_maximalAtlas

theorem contMdiffAt_of_mem_maximalAtlas (h : e ∈ maximalAtlas I M) (hx : x ∈ e.source) :
    ContMdiffAt I I n e x :=
  (contMdiffOn_of_mem_maximalAtlas h).ContMdiffAt <| e.open_source.mem_nhds hx
#align cont_mdiff_at_of_mem_maximal_atlas contMdiffAt_of_mem_maximalAtlas

theorem contMdiffAt_symm_of_mem_maximalAtlas {x : H} (h : e ∈ maximalAtlas I M)
    (hx : x ∈ e.target) : ContMdiffAt I I n e.symm x :=
  (contMdiffOn_symm_of_mem_maximalAtlas h).ContMdiffAt <| e.open_target.mem_nhds hx
#align cont_mdiff_at_symm_of_mem_maximal_atlas contMdiffAt_symm_of_mem_maximalAtlas

theorem contMdiffOn_chart : ContMdiffOn I I n (chartAt H x) (chartAt H x).source :=
  contMdiffOn_of_mem_maximalAtlas <| chart_mem_maximalAtlas I x
#align cont_mdiff_on_chart contMdiffOn_chart

theorem contMdiffOn_chart_symm : ContMdiffOn I I n (chartAt H x).symm (chartAt H x).target :=
  contMdiffOn_symm_of_mem_maximalAtlas <| chart_mem_maximalAtlas I x
#align cont_mdiff_on_chart_symm contMdiffOn_chart_symm

theorem contMdiffAt_extend {x : M} (he : e ∈ maximalAtlas I M) (hx : x ∈ e.source) :
    ContMdiffAt I 𝓘(𝕜, E) n (e.extend I) x :=
  (contMdiff_model _).comp x <| contMdiffAt_of_mem_maximalAtlas he hx
#align cont_mdiff_at_extend contMdiffAt_extend

theorem contMdiffAt_ext_chart_at' {x' : M} (h : x' ∈ (chartAt H x).source) :
    ContMdiffAt I 𝓘(𝕜, E) n (extChartAt I x) x' :=
  contMdiffAt_extend (chart_mem_maximalAtlas I x) h
#align cont_mdiff_at_ext_chart_at' contMdiffAt_ext_chart_at'

theorem contMdiffAt_extChartAt : ContMdiffAt I 𝓘(𝕜, E) n (extChartAt I x) x :=
  contMdiffAt_ext_chart_at' <| mem_chart_source H x
#align cont_mdiff_at_ext_chart_at contMdiffAt_extChartAt

theorem contMdiffOn_extChartAt : ContMdiffOn I 𝓘(𝕜, E) n (extChartAt I x) (chartAt H x).source :=
  fun x' hx' => (contMdiffAt_ext_chart_at' hx').ContMdiffWithinAt
#align cont_mdiff_on_ext_chart_at contMdiffOn_extChartAt

theorem contMdiffOn_extend_symm (he : e ∈ maximalAtlas I M) :
    ContMdiffOn 𝓘(𝕜, E) I n (e.extend I).symm (I '' e.target) := by
  have h2 := contMdiffOn_symm_of_mem_maximalAtlas he
  refine' h2.comp (cont_mdiff_on_model_symm.mono <| image_subset_range _ _) _
  simp_rw [image_subset_iff, LocalEquiv.restr_coe_symm, I.to_local_equiv_coe_symm,
    preimage_preimage, I.left_inv, preimage_id']
#align cont_mdiff_on_extend_symm contMdiffOn_extend_symm

theorem contMdiffOn_extChartAt_symm (x : M) :
    ContMdiffOn 𝓘(𝕜, E) I n (extChartAt I x).symm (extChartAt I x).target := by
  convert contMdiffOn_extend_symm (chart_mem_maximal_atlas I x)
  rw [extChartAt_target, I.image_eq]
#align cont_mdiff_on_ext_chart_at_symm contMdiffOn_extChartAt_symm

/-- An element of `cont_diff_groupoid ⊤ I` is `C^n` for any `n`. -/
theorem contMdiffOn_of_mem_contDiffGroupoid {e' : LocalHomeomorph H H}
    (h : e' ∈ contDiffGroupoid ⊤ I) : ContMdiffOn I I n e' e'.source :=
  (cont_diff_within_at_localInvariantProp I I n).liftPropOn_of_mem_groupoid
    (contDiffWithinAtProp_id I) h
#align cont_mdiff_on_of_mem_cont_diff_groupoid contMdiffOn_of_mem_contDiffGroupoid

end Atlas

/-! ### The identity is smooth -/


section id

theorem contMdiff_id : ContMdiff I I n (id : M → M) :=
  ContMdiff.of_le
    ((cont_diff_within_at_localInvariantProp I I ∞).liftProp_id (contDiffWithinAtProp_id I)) le_top
#align cont_mdiff_id contMdiff_id

theorem smooth_id : Smooth I I (id : M → M) :=
  contMdiff_id
#align smooth_id smooth_id

theorem contMdiffOn_id : ContMdiffOn I I n (id : M → M) s :=
  contMdiff_id.ContMdiffOn
#align cont_mdiff_on_id contMdiffOn_id

theorem smoothOn_id : SmoothOn I I (id : M → M) s :=
  contMdiffOn_id
#align smooth_on_id smoothOn_id

theorem contMdiffAt_id : ContMdiffAt I I n (id : M → M) x :=
  contMdiff_id.ContMdiffAt
#align cont_mdiff_at_id contMdiffAt_id

theorem smoothAt_id : SmoothAt I I (id : M → M) x :=
  contMdiffAt_id
#align smooth_at_id smoothAt_id

theorem contMdiffWithinAt_id : ContMdiffWithinAt I I n (id : M → M) s x :=
  contMdiffAt_id.ContMdiffWithinAt
#align cont_mdiff_within_at_id contMdiffWithinAt_id

theorem smoothWithinAt_id : SmoothWithinAt I I (id : M → M) s x :=
  contMdiffWithinAt_id
#align smooth_within_at_id smoothWithinAt_id

end id

/-! ### Constants are smooth -/


section id

variable {c : M'}

theorem contMdiff_const : ContMdiff I I' n fun x : M => c := by
  intro x
  refine' ⟨continuousWithinAt_const, _⟩
  simp only [ContDiffWithinAtProp, (· ∘ ·)]
  exact contDiffWithinAt_const
#align cont_mdiff_const contMdiff_const

@[to_additive]
theorem contMdiff_one [One M'] : ContMdiff I I' n (1 : M → M') := by
  simp only [Pi.one_def, contMdiff_const]
#align cont_mdiff_one contMdiff_one
#align cont_mdiff_zero contMdiff_zero

theorem smooth_const : Smooth I I' fun x : M => c :=
  contMdiff_const
#align smooth_const smooth_const

@[to_additive]
theorem smooth_one [One M'] : Smooth I I' (1 : M → M') := by simp only [Pi.one_def, smooth_const]
#align smooth_one smooth_one
#align smooth_zero smooth_zero

theorem contMdiffOn_const : ContMdiffOn I I' n (fun x : M => c) s :=
  contMdiff_const.ContMdiffOn
#align cont_mdiff_on_const contMdiffOn_const

@[to_additive]
theorem contMdiffOn_one [One M'] : ContMdiffOn I I' n (1 : M → M') s :=
  contMdiff_one.ContMdiffOn
#align cont_mdiff_on_one contMdiffOn_one
#align cont_mdiff_on_zero contMdiffOn_zero

theorem smoothOn_const : SmoothOn I I' (fun x : M => c) s :=
  contMdiffOn_const
#align smooth_on_const smoothOn_const

@[to_additive]
theorem smoothOn_one [One M'] : SmoothOn I I' (1 : M → M') s :=
  contMdiffOn_one
#align smooth_on_one smoothOn_one
#align smooth_on_zero smoothOn_zero

theorem contMdiffAt_const : ContMdiffAt I I' n (fun x : M => c) x :=
  contMdiff_const.ContMdiffAt
#align cont_mdiff_at_const contMdiffAt_const

@[to_additive]
theorem contMdiffAt_one [One M'] : ContMdiffAt I I' n (1 : M → M') x :=
  contMdiff_one.ContMdiffAt
#align cont_mdiff_at_one contMdiffAt_one
#align cont_mdiff_at_zero contMdiffAt_zero

theorem smoothAt_const : SmoothAt I I' (fun x : M => c) x :=
  contMdiffAt_const
#align smooth_at_const smoothAt_const

@[to_additive]
theorem smoothAt_one [One M'] : SmoothAt I I' (1 : M → M') x :=
  contMdiffAt_one
#align smooth_at_one smoothAt_one
#align smooth_at_zero smoothAt_zero

theorem contMdiffWithinAt_const : ContMdiffWithinAt I I' n (fun x : M => c) s x :=
  contMdiffAt_const.ContMdiffWithinAt
#align cont_mdiff_within_at_const contMdiffWithinAt_const

@[to_additive]
theorem contMdiffWithinAt_one [One M'] : ContMdiffWithinAt I I' n (1 : M → M') s x :=
  contMdiffAt_const.ContMdiffWithinAt
#align cont_mdiff_within_at_one contMdiffWithinAt_one
#align cont_mdiff_within_at_zero contMdiffWithinAt_zero

theorem smoothWithinAt_const : SmoothWithinAt I I' (fun x : M => c) s x :=
  contMdiffWithinAt_const
#align smooth_within_at_const smoothWithinAt_const

@[to_additive]
theorem smoothWithinAt_one [One M'] : SmoothWithinAt I I' (1 : M → M') s x :=
  contMdiffWithinAt_one
#align smooth_within_at_one smoothWithinAt_one
#align smooth_within_at_zero smoothWithinAt_zero

end id

theorem contMdiff_of_support {f : M → F} (hf : ∀ x ∈ tsupport f, ContMdiffAt I 𝓘(𝕜, F) n f x) :
    ContMdiff I 𝓘(𝕜, F) n f := by
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hf x hx
  · refine' ContMdiffAt.congr_of_eventuallyEq _ (eventuallyEq_zero_nhds.2 hx)
    exact contMdiffAt_const
#align cont_mdiff_of_support contMdiff_of_support

/-! ### The inclusion map from one open set to another is smooth -/


section

open TopologicalSpace

theorem contMdiff_inclusion {n : ℕ∞} {U V : Opens M} (h : U ≤ V) :
    ContMdiff I I n (Set.inclusion h : U → V) := by
  rintro ⟨x, hx : x ∈ U⟩
  apply (cont_diff_within_at_localInvariantProp I I n).liftProp_inclusion
  intro y
  dsimp [ContDiffWithinAtProp]
  rw [Set.univ_inter]
  refine' cont_diff_within_at_id.congr _ _
  · exact I.right_inv_on
  · exact congr_arg I (I.left_inv y)
#align cont_mdiff_inclusion contMdiff_inclusion

theorem smooth_inclusion {U V : Opens M} (h : U ≤ V) : Smooth I I (Set.inclusion h : U → V) :=
  contMdiff_inclusion h
#align smooth_inclusion smooth_inclusion

end

/-! ### Equivalence with the basic definition for functions between vector spaces -/


section Module

theorem contMdiffWithinAt_iff_contDiffWithinAt {f : E → E'} {s : Set E} {x : E} :
    ContMdiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') n f s x ↔ ContDiffWithinAt 𝕜 n f s x := by
  simp (config := { contextual := true }) only [ContMdiffWithinAt, lift_prop_within_at,
    ContDiffWithinAtProp, iff_def, mfld_simps]
  exact ContDiffWithinAt.continuousWithinAt
#align cont_mdiff_within_at_iff_cont_diff_within_at contMdiffWithinAt_iff_contDiffWithinAt

alias contMdiffWithinAt_iff_contDiffWithinAt ↔ ContMdiffWithinAt.contDiffWithinAt
  ContDiffWithinAt.contMdiffWithinAt
#align cont_mdiff_within_at.cont_diff_within_at ContMdiffWithinAt.contDiffWithinAt
#align cont_diff_within_at.cont_mdiff_within_at ContDiffWithinAt.contMdiffWithinAt

theorem contMdiffAt_iff_contDiffAt {f : E → E'} {x : E} :
    ContMdiffAt 𝓘(𝕜, E) 𝓘(𝕜, E') n f x ↔ ContDiffAt 𝕜 n f x := by
  rw [← contMdiffWithinAt_univ, contMdiffWithinAt_iff_contDiffWithinAt, contDiffWithinAt_univ]
#align cont_mdiff_at_iff_cont_diff_at contMdiffAt_iff_contDiffAt

alias contMdiffAt_iff_contDiffAt ↔ ContMdiffAt.contDiffAt ContDiffAt.contMdiffAt
#align cont_mdiff_at.cont_diff_at ContMdiffAt.contDiffAt
#align cont_diff_at.cont_mdiff_at ContDiffAt.contMdiffAt

theorem contMdiffOn_iff_contDiffOn {f : E → E'} {s : Set E} :
    ContMdiffOn 𝓘(𝕜, E) 𝓘(𝕜, E') n f s ↔ ContDiffOn 𝕜 n f s :=
  forall_congr' <| by simp [contMdiffWithinAt_iff_contDiffWithinAt]
#align cont_mdiff_on_iff_cont_diff_on contMdiffOn_iff_contDiffOn

alias contMdiffOn_iff_contDiffOn ↔ ContMdiffOn.contDiffOn ContDiffOn.contMdiffOn
#align cont_mdiff_on.cont_diff_on ContMdiffOn.contDiffOn
#align cont_diff_on.cont_mdiff_on ContDiffOn.contMdiffOn

theorem contMdiff_iff_contDiff {f : E → E'} : ContMdiff 𝓘(𝕜, E) 𝓘(𝕜, E') n f ↔ ContDiff 𝕜 n f := by
  rw [← contDiffOn_univ, ← contMdiffOn_univ, contMdiffOn_iff_contDiffOn]
#align cont_mdiff_iff_cont_diff contMdiff_iff_contDiff

alias contMdiff_iff_contDiff ↔ ContMdiff.contDiff ContDiff.contMdiff
#align cont_mdiff.cont_diff ContMdiff.contDiff
#align cont_diff.cont_mdiff ContDiff.contMdiff

theorem ContDiffWithinAt.comp_contMdiffWithinAt {g : F → F'} {f : M → F} {s : Set M} {t : Set F}
    {x : M} (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContMdiffWithinAt I 𝓘(𝕜, F) n f s x)
    (h : s ⊆ f ⁻¹' t) : ContMdiffWithinAt I 𝓘(𝕜, F') n (g ∘ f) s x := by
  rw [contMdiffWithinAt_iff] at *
  refine' ⟨hg.continuous_within_at.comp hf.1 h, _⟩
  rw [← (extChartAt I x).left_inv (mem_extChartAt_source I x)] at hg 
  apply ContDiffWithinAt.comp _ hg hf.2 _
  exact (inter_subset_left _ _).trans (preimage_mono h)
#align cont_diff_within_at.comp_cont_mdiff_within_at ContDiffWithinAt.comp_contMdiffWithinAt

theorem ContDiffAt.comp_contMdiffAt {g : F → F'} {f : M → F} {x : M} (hg : ContDiffAt 𝕜 n g (f x))
    (hf : ContMdiffAt I 𝓘(𝕜, F) n f x) : ContMdiffAt I 𝓘(𝕜, F') n (g ∘ f) x :=
  hg.comp_contMdiffWithinAt hf Subset.rfl
#align cont_diff_at.comp_cont_mdiff_at ContDiffAt.comp_contMdiffAt

theorem ContDiff.comp_contMdiff {g : F → F'} {f : M → F} (hg : ContDiff 𝕜 n g)
    (hf : ContMdiff I 𝓘(𝕜, F) n f) : ContMdiff I 𝓘(𝕜, F') n (g ∘ f) := fun x =>
  hg.ContDiffAt.comp_contMdiffAt (hf x)
#align cont_diff.comp_cont_mdiff ContDiff.comp_contMdiff

end Module

/-! ### Smoothness of standard maps associated to the product of manifolds -/


section ProdMk

theorem ContMdiffWithinAt.prod_mk {f : M → M'} {g : M → N'} (hf : ContMdiffWithinAt I I' n f s x)
    (hg : ContMdiffWithinAt I J' n g s x) :
    ContMdiffWithinAt I (I'.Prod J') n (fun x => (f x, g x)) s x := by
  rw [contMdiffWithinAt_iff] at *
  exact ⟨hf.1.Prod hg.1, hf.2.Prod hg.2⟩
#align cont_mdiff_within_at.prod_mk ContMdiffWithinAt.prod_mk

theorem ContMdiffWithinAt.prod_mk_space {f : M → E'} {g : M → F'}
    (hf : ContMdiffWithinAt I 𝓘(𝕜, E') n f s x) (hg : ContMdiffWithinAt I 𝓘(𝕜, F') n g s x) :
    ContMdiffWithinAt I 𝓘(𝕜, E' × F') n (fun x => (f x, g x)) s x := by
  rw [contMdiffWithinAt_iff] at *
  exact ⟨hf.1.Prod hg.1, hf.2.Prod hg.2⟩
#align cont_mdiff_within_at.prod_mk_space ContMdiffWithinAt.prod_mk_space

theorem ContMdiffAt.prod_mk {f : M → M'} {g : M → N'} (hf : ContMdiffAt I I' n f x)
    (hg : ContMdiffAt I J' n g x) : ContMdiffAt I (I'.Prod J') n (fun x => (f x, g x)) x :=
  hf.prod_mk hg
#align cont_mdiff_at.prod_mk ContMdiffAt.prod_mk

theorem ContMdiffAt.prod_mk_space {f : M → E'} {g : M → F'} (hf : ContMdiffAt I 𝓘(𝕜, E') n f x)
    (hg : ContMdiffAt I 𝓘(𝕜, F') n g x) : ContMdiffAt I 𝓘(𝕜, E' × F') n (fun x => (f x, g x)) x :=
  hf.prod_mk_space hg
#align cont_mdiff_at.prod_mk_space ContMdiffAt.prod_mk_space

theorem ContMdiffOn.prod_mk {f : M → M'} {g : M → N'} (hf : ContMdiffOn I I' n f s)
    (hg : ContMdiffOn I J' n g s) : ContMdiffOn I (I'.Prod J') n (fun x => (f x, g x)) s :=
  fun x hx => (hf x hx).prod_mk (hg x hx)
#align cont_mdiff_on.prod_mk ContMdiffOn.prod_mk

theorem ContMdiffOn.prod_mk_space {f : M → E'} {g : M → F'} (hf : ContMdiffOn I 𝓘(𝕜, E') n f s)
    (hg : ContMdiffOn I 𝓘(𝕜, F') n g s) : ContMdiffOn I 𝓘(𝕜, E' × F') n (fun x => (f x, g x)) s :=
  fun x hx => (hf x hx).prod_mk_space (hg x hx)
#align cont_mdiff_on.prod_mk_space ContMdiffOn.prod_mk_space

theorem ContMdiff.prod_mk {f : M → M'} {g : M → N'} (hf : ContMdiff I I' n f)
    (hg : ContMdiff I J' n g) : ContMdiff I (I'.Prod J') n fun x => (f x, g x) := fun x =>
  (hf x).prod_mk (hg x)
#align cont_mdiff.prod_mk ContMdiff.prod_mk

theorem ContMdiff.prod_mk_space {f : M → E'} {g : M → F'} (hf : ContMdiff I 𝓘(𝕜, E') n f)
    (hg : ContMdiff I 𝓘(𝕜, F') n g) : ContMdiff I 𝓘(𝕜, E' × F') n fun x => (f x, g x) := fun x =>
  (hf x).prod_mk_space (hg x)
#align cont_mdiff.prod_mk_space ContMdiff.prod_mk_space

theorem SmoothWithinAt.prod_mk {f : M → M'} {g : M → N'} (hf : SmoothWithinAt I I' f s x)
    (hg : SmoothWithinAt I J' g s x) : SmoothWithinAt I (I'.Prod J') (fun x => (f x, g x)) s x :=
  hf.prod_mk hg
#align smooth_within_at.prod_mk SmoothWithinAt.prod_mk

theorem SmoothWithinAt.prod_mk_space {f : M → E'} {g : M → F'}
    (hf : SmoothWithinAt I 𝓘(𝕜, E') f s x) (hg : SmoothWithinAt I 𝓘(𝕜, F') g s x) :
    SmoothWithinAt I 𝓘(𝕜, E' × F') (fun x => (f x, g x)) s x :=
  hf.prod_mk_space hg
#align smooth_within_at.prod_mk_space SmoothWithinAt.prod_mk_space

theorem SmoothAt.prod_mk {f : M → M'} {g : M → N'} (hf : SmoothAt I I' f x)
    (hg : SmoothAt I J' g x) : SmoothAt I (I'.Prod J') (fun x => (f x, g x)) x :=
  hf.prod_mk hg
#align smooth_at.prod_mk SmoothAt.prod_mk

theorem SmoothAt.prod_mk_space {f : M → E'} {g : M → F'} (hf : SmoothAt I 𝓘(𝕜, E') f x)
    (hg : SmoothAt I 𝓘(𝕜, F') g x) : SmoothAt I 𝓘(𝕜, E' × F') (fun x => (f x, g x)) x :=
  hf.prod_mk_space hg
#align smooth_at.prod_mk_space SmoothAt.prod_mk_space

theorem SmoothOn.prod_mk {f : M → M'} {g : M → N'} (hf : SmoothOn I I' f s)
    (hg : SmoothOn I J' g s) : SmoothOn I (I'.Prod J') (fun x => (f x, g x)) s :=
  hf.prod_mk hg
#align smooth_on.prod_mk SmoothOn.prod_mk

theorem SmoothOn.prod_mk_space {f : M → E'} {g : M → F'} (hf : SmoothOn I 𝓘(𝕜, E') f s)
    (hg : SmoothOn I 𝓘(𝕜, F') g s) : SmoothOn I 𝓘(𝕜, E' × F') (fun x => (f x, g x)) s :=
  hf.prod_mk_space hg
#align smooth_on.prod_mk_space SmoothOn.prod_mk_space

theorem Smooth.prod_mk {f : M → M'} {g : M → N'} (hf : Smooth I I' f) (hg : Smooth I J' g) :
    Smooth I (I'.Prod J') fun x => (f x, g x) :=
  hf.prod_mk hg
#align smooth.prod_mk Smooth.prod_mk

theorem Smooth.prod_mk_space {f : M → E'} {g : M → F'} (hf : Smooth I 𝓘(𝕜, E') f)
    (hg : Smooth I 𝓘(𝕜, F') g) : Smooth I 𝓘(𝕜, E' × F') fun x => (f x, g x) :=
  hf.prod_mk_space hg
#align smooth.prod_mk_space Smooth.prod_mk_space

end ProdMk

section Projections

theorem contMdiffWithinAt_fst {s : Set (M × N)} {p : M × N} :
    ContMdiffWithinAt (I.Prod J) I n Prod.fst s p := by
  rw [contMdiffWithinAt_iff']
  refine' ⟨continuousWithinAt_fst, _⟩
  refine' cont_diff_within_at_fst.congr (fun y hy => _) _
  · simp only [mfld_simps] at hy 
    simp only [hy, mfld_simps]
  · simp only [mfld_simps]
#align cont_mdiff_within_at_fst contMdiffWithinAt_fst

theorem ContMdiffWithinAt.fst {f : N → M × M'} {s : Set N} {x : N}
    (hf : ContMdiffWithinAt J (I.Prod I') n f s x) :
    ContMdiffWithinAt J I n (fun x => (f x).1) s x :=
  contMdiffWithinAt_fst.comp x hf (mapsTo_image f s)
#align cont_mdiff_within_at.fst ContMdiffWithinAt.fst

theorem contMdiffAt_fst {p : M × N} : ContMdiffAt (I.Prod J) I n Prod.fst p :=
  contMdiffWithinAt_fst
#align cont_mdiff_at_fst contMdiffAt_fst

theorem contMdiffOn_fst {s : Set (M × N)} : ContMdiffOn (I.Prod J) I n Prod.fst s := fun x hx =>
  contMdiffWithinAt_fst
#align cont_mdiff_on_fst contMdiffOn_fst

theorem contMdiff_fst : ContMdiff (I.Prod J) I n (@Prod.fst M N) := fun x => contMdiffAt_fst
#align cont_mdiff_fst contMdiff_fst

theorem smoothWithinAt_fst {s : Set (M × N)} {p : M × N} :
    SmoothWithinAt (I.Prod J) I Prod.fst s p :=
  contMdiffWithinAt_fst
#align smooth_within_at_fst smoothWithinAt_fst

theorem smoothAt_fst {p : M × N} : SmoothAt (I.Prod J) I Prod.fst p :=
  contMdiffAt_fst
#align smooth_at_fst smoothAt_fst

theorem smoothOn_fst {s : Set (M × N)} : SmoothOn (I.Prod J) I Prod.fst s :=
  contMdiffOn_fst
#align smooth_on_fst smoothOn_fst

theorem smooth_fst : Smooth (I.Prod J) I (@Prod.fst M N) :=
  contMdiff_fst
#align smooth_fst smooth_fst

theorem ContMdiffAt.fst {f : N → M × M'} {x : N} (hf : ContMdiffAt J (I.Prod I') n f x) :
    ContMdiffAt J I n (fun x => (f x).1) x :=
  contMdiffAt_fst.comp x hf
#align cont_mdiff_at.fst ContMdiffAt.fst

theorem ContMdiff.fst {f : N → M × M'} (hf : ContMdiff J (I.Prod I') n f) :
    ContMdiff J I n fun x => (f x).1 :=
  contMdiff_fst.comp hf
#align cont_mdiff.fst ContMdiff.fst

theorem SmoothAt.fst {f : N → M × M'} {x : N} (hf : SmoothAt J (I.Prod I') f x) :
    SmoothAt J I (fun x => (f x).1) x :=
  smoothAt_fst.comp x hf
#align smooth_at.fst SmoothAt.fst

theorem Smooth.fst {f : N → M × M'} (hf : Smooth J (I.Prod I') f) : Smooth J I fun x => (f x).1 :=
  smooth_fst.comp hf
#align smooth.fst Smooth.fst

theorem contMdiffWithinAt_snd {s : Set (M × N)} {p : M × N} :
    ContMdiffWithinAt (I.Prod J) J n Prod.snd s p := by
  rw [contMdiffWithinAt_iff']
  refine' ⟨continuousWithinAt_snd, _⟩
  refine' cont_diff_within_at_snd.congr (fun y hy => _) _
  · simp only [mfld_simps] at hy 
    simp only [hy, mfld_simps]
  · simp only [mfld_simps]
#align cont_mdiff_within_at_snd contMdiffWithinAt_snd

theorem ContMdiffWithinAt.snd {f : N → M × M'} {s : Set N} {x : N}
    (hf : ContMdiffWithinAt J (I.Prod I') n f s x) :
    ContMdiffWithinAt J I' n (fun x => (f x).2) s x :=
  contMdiffWithinAt_snd.comp x hf (mapsTo_image f s)
#align cont_mdiff_within_at.snd ContMdiffWithinAt.snd

theorem contMdiffAt_snd {p : M × N} : ContMdiffAt (I.Prod J) J n Prod.snd p :=
  contMdiffWithinAt_snd
#align cont_mdiff_at_snd contMdiffAt_snd

theorem contMdiffOn_snd {s : Set (M × N)} : ContMdiffOn (I.Prod J) J n Prod.snd s := fun x hx =>
  contMdiffWithinAt_snd
#align cont_mdiff_on_snd contMdiffOn_snd

theorem contMdiff_snd : ContMdiff (I.Prod J) J n (@Prod.snd M N) := fun x => contMdiffAt_snd
#align cont_mdiff_snd contMdiff_snd

theorem smoothWithinAt_snd {s : Set (M × N)} {p : M × N} :
    SmoothWithinAt (I.Prod J) J Prod.snd s p :=
  contMdiffWithinAt_snd
#align smooth_within_at_snd smoothWithinAt_snd

theorem smoothAt_snd {p : M × N} : SmoothAt (I.Prod J) J Prod.snd p :=
  contMdiffAt_snd
#align smooth_at_snd smoothAt_snd

theorem smoothOn_snd {s : Set (M × N)} : SmoothOn (I.Prod J) J Prod.snd s :=
  contMdiffOn_snd
#align smooth_on_snd smoothOn_snd

theorem smooth_snd : Smooth (I.Prod J) J (@Prod.snd M N) :=
  contMdiff_snd
#align smooth_snd smooth_snd

theorem ContMdiffAt.snd {f : N → M × M'} {x : N} (hf : ContMdiffAt J (I.Prod I') n f x) :
    ContMdiffAt J I' n (fun x => (f x).2) x :=
  contMdiffAt_snd.comp x hf
#align cont_mdiff_at.snd ContMdiffAt.snd

theorem ContMdiff.snd {f : N → M × M'} (hf : ContMdiff J (I.Prod I') n f) :
    ContMdiff J I' n fun x => (f x).2 :=
  contMdiff_snd.comp hf
#align cont_mdiff.snd ContMdiff.snd

theorem SmoothAt.snd {f : N → M × M'} {x : N} (hf : SmoothAt J (I.Prod I') f x) :
    SmoothAt J I' (fun x => (f x).2) x :=
  smoothAt_snd.comp x hf
#align smooth_at.snd SmoothAt.snd

theorem Smooth.snd {f : N → M × M'} (hf : Smooth J (I.Prod I') f) : Smooth J I' fun x => (f x).2 :=
  smooth_snd.comp hf
#align smooth.snd Smooth.snd

end Projections

theorem contMdiffWithinAt_prod_iff (f : M → M' × N') {s : Set M} {x : M} :
    ContMdiffWithinAt I (I'.Prod J') n f s x ↔
      ContMdiffWithinAt I I' n (Prod.fst ∘ f) s x ∧ ContMdiffWithinAt I J' n (Prod.snd ∘ f) s x :=
  by refine' ⟨fun h => ⟨h.fst, h.snd⟩, fun h => _⟩; simpa only [Prod.mk.eta] using h.1.prod_mk h.2
#align cont_mdiff_within_at_prod_iff contMdiffWithinAt_prod_iff

theorem contMdiffAt_prod_iff (f : M → M' × N') {x : M} :
    ContMdiffAt I (I'.Prod J') n f x ↔
      ContMdiffAt I I' n (Prod.fst ∘ f) x ∧ ContMdiffAt I J' n (Prod.snd ∘ f) x :=
  by simp_rw [← contMdiffWithinAt_univ, contMdiffWithinAt_prod_iff]
#align cont_mdiff_at_prod_iff contMdiffAt_prod_iff

theorem contMdiff_prod_iff (f : M → M' × N') :
    ContMdiff I (I'.Prod J') n f ↔
      ContMdiff I I' n (Prod.fst ∘ f) ∧ ContMdiff I J' n (Prod.snd ∘ f) :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => by convert h.1.prod_mk h.2; ext <;> rfl⟩
#align cont_mdiff_prod_iff contMdiff_prod_iff

theorem smoothAt_prod_iff (f : M → M' × N') {x : M} :
    SmoothAt I (I'.Prod J') f x ↔ SmoothAt I I' (Prod.fst ∘ f) x ∧ SmoothAt I J' (Prod.snd ∘ f) x :=
  contMdiffAt_prod_iff f
#align smooth_at_prod_iff smoothAt_prod_iff

theorem smooth_prod_iff (f : M → M' × N') :
    Smooth I (I'.Prod J') f ↔ Smooth I I' (Prod.fst ∘ f) ∧ Smooth I J' (Prod.snd ∘ f) :=
  contMdiff_prod_iff f
#align smooth_prod_iff smooth_prod_iff

theorem smooth_prod_assoc :
    Smooth ((I.Prod I').Prod J) (I.Prod (I'.Prod J)) fun x : (M × M') × N => (x.1.1, x.1.2, x.2) :=
  smooth_fst.fst.prod_mk <| smooth_fst.snd.prod_mk smooth_snd
#align smooth_prod_assoc smooth_prod_assoc

section Prod_map

variable {g : N → N'} {r : Set N} {y : N}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem ContMdiffWithinAt.prod_map' {p : M × N} (hf : ContMdiffWithinAt I I' n f s p.1)
    (hg : ContMdiffWithinAt J J' n g r p.2) :
    ContMdiffWithinAt (I.Prod J) (I'.Prod J') n (Prod.map f g) (s ×ˢ r) p :=
  (hf.comp p contMdiffWithinAt_fst (prod_subset_preimage_fst _ _)).prod_mk <|
    hg.comp p contMdiffWithinAt_snd (prod_subset_preimage_snd _ _)
#align cont_mdiff_within_at.prod_map' ContMdiffWithinAt.prod_map'

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem ContMdiffWithinAt.prod_map (hf : ContMdiffWithinAt I I' n f s x)
    (hg : ContMdiffWithinAt J J' n g r y) :
    ContMdiffWithinAt (I.Prod J) (I'.Prod J') n (Prod.map f g) (s ×ˢ r) (x, y) :=
  ContMdiffWithinAt.prod_map' hf hg
#align cont_mdiff_within_at.prod_map ContMdiffWithinAt.prod_map

theorem ContMdiffAt.prod_map (hf : ContMdiffAt I I' n f x) (hg : ContMdiffAt J J' n g y) :
    ContMdiffAt (I.Prod J) (I'.Prod J') n (Prod.map f g) (x, y) := by
  rw [← contMdiffWithinAt_univ] at *
  convert hf.prod_map hg
  exact univ_prod_univ.symm
#align cont_mdiff_at.prod_map ContMdiffAt.prod_map

theorem ContMdiffAt.prod_map' {p : M × N} (hf : ContMdiffAt I I' n f p.1)
    (hg : ContMdiffAt J J' n g p.2) : ContMdiffAt (I.Prod J) (I'.Prod J') n (Prod.map f g) p := by
  rcases p with ⟨⟩
  exact hf.prod_map hg
#align cont_mdiff_at.prod_map' ContMdiffAt.prod_map'

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem ContMdiffOn.prod_map (hf : ContMdiffOn I I' n f s) (hg : ContMdiffOn J J' n g r) :
    ContMdiffOn (I.Prod J) (I'.Prod J') n (Prod.map f g) (s ×ˢ r) :=
  (hf.comp contMdiffOn_fst (prod_subset_preimage_fst _ _)).prod_mk <|
    hg.comp contMdiffOn_snd (prod_subset_preimage_snd _ _)
#align cont_mdiff_on.prod_map ContMdiffOn.prod_map

theorem ContMdiff.prod_map (hf : ContMdiff I I' n f) (hg : ContMdiff J J' n g) :
    ContMdiff (I.Prod J) (I'.Prod J') n (Prod.map f g) := by
  intro p
  exact (hf p.1).prod_map' (hg p.2)
#align cont_mdiff.prod_map ContMdiff.prod_map

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem SmoothWithinAt.prod_map (hf : SmoothWithinAt I I' f s x) (hg : SmoothWithinAt J J' g r y) :
    SmoothWithinAt (I.Prod J) (I'.Prod J') (Prod.map f g) (s ×ˢ r) (x, y) :=
  hf.Prod_map hg
#align smooth_within_at.prod_map SmoothWithinAt.prod_map

theorem SmoothAt.prod_map (hf : SmoothAt I I' f x) (hg : SmoothAt J J' g y) :
    SmoothAt (I.Prod J) (I'.Prod J') (Prod.map f g) (x, y) :=
  hf.Prod_map hg
#align smooth_at.prod_map SmoothAt.prod_map

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem SmoothOn.prod_map (hf : SmoothOn I I' f s) (hg : SmoothOn J J' g r) :
    SmoothOn (I.Prod J) (I'.Prod J') (Prod.map f g) (s ×ˢ r) :=
  hf.Prod_map hg
#align smooth_on.prod_map SmoothOn.prod_map

theorem Smooth.prod_map (hf : Smooth I I' f) (hg : Smooth J J' g) :
    Smooth (I.Prod J) (I'.Prod J') (Prod.map f g) :=
  hf.Prod_map hg
#align smooth.prod_map Smooth.prod_map

end Prod_map

section PiSpace

/-!
### Smoothness of functions with codomain `Π i, F i`

We have no `model_with_corners.pi` yet, so we prove lemmas about functions `f : M → Π i, F i` and
use `𝓘(𝕜, Π i, F i)` as the model space.
-/


variable {ι : Type _} [Fintype ι] {Fi : ι → Type _} [∀ i, NormedAddCommGroup (Fi i)]
  [∀ i, NormedSpace 𝕜 (Fi i)] {φ : M → ∀ i, Fi i}

theorem contMdiffWithinAt_pi_space :
    ContMdiffWithinAt I 𝓘(𝕜, ∀ i, Fi i) n φ s x ↔
      ∀ i, ContMdiffWithinAt I 𝓘(𝕜, Fi i) n (fun x => φ x i) s x := by
  simp only [contMdiffWithinAt_iff, continuousWithinAt_pi, contDiffWithinAt_pi, forall_and,
    writtenInExtChartAt, extChartAt_model_space_eq_id, (· ∘ ·), LocalEquiv.refl_coe, id]
#align cont_mdiff_within_at_pi_space contMdiffWithinAt_pi_space

theorem contMdiffOn_pi_space :
    ContMdiffOn I 𝓘(𝕜, ∀ i, Fi i) n φ s ↔ ∀ i, ContMdiffOn I 𝓘(𝕜, Fi i) n (fun x => φ x i) s :=
  ⟨fun h i x hx => contMdiffWithinAt_pi_space.1 (h x hx) i, fun h x hx =>
    contMdiffWithinAt_pi_space.2 fun i => h i x hx⟩
#align cont_mdiff_on_pi_space contMdiffOn_pi_space

theorem contMdiffAt_pi_space :
    ContMdiffAt I 𝓘(𝕜, ∀ i, Fi i) n φ x ↔ ∀ i, ContMdiffAt I 𝓘(𝕜, Fi i) n (fun x => φ x i) x :=
  contMdiffWithinAt_pi_space
#align cont_mdiff_at_pi_space contMdiffAt_pi_space

theorem contMdiff_pi_space :
    ContMdiff I 𝓘(𝕜, ∀ i, Fi i) n φ ↔ ∀ i, ContMdiff I 𝓘(𝕜, Fi i) n fun x => φ x i :=
  ⟨fun h i x => contMdiffAt_pi_space.1 (h x) i, fun h x => contMdiffAt_pi_space.2 fun i => h i x⟩
#align cont_mdiff_pi_space contMdiff_pi_space

theorem smoothWithinAt_pi_space :
    SmoothWithinAt I 𝓘(𝕜, ∀ i, Fi i) φ s x ↔
      ∀ i, SmoothWithinAt I 𝓘(𝕜, Fi i) (fun x => φ x i) s x :=
  contMdiffWithinAt_pi_space
#align smooth_within_at_pi_space smoothWithinAt_pi_space

theorem smoothOn_pi_space :
    SmoothOn I 𝓘(𝕜, ∀ i, Fi i) φ s ↔ ∀ i, SmoothOn I 𝓘(𝕜, Fi i) (fun x => φ x i) s :=
  contMdiffOn_pi_space
#align smooth_on_pi_space smoothOn_pi_space

theorem smoothAt_pi_space :
    SmoothAt I 𝓘(𝕜, ∀ i, Fi i) φ x ↔ ∀ i, SmoothAt I 𝓘(𝕜, Fi i) (fun x => φ x i) x :=
  contMdiffAt_pi_space
#align smooth_at_pi_space smoothAt_pi_space

theorem smooth_pi_space : Smooth I 𝓘(𝕜, ∀ i, Fi i) φ ↔ ∀ i, Smooth I 𝓘(𝕜, Fi i) fun x => φ x i :=
  contMdiff_pi_space
#align smooth_pi_space smooth_pi_space

end PiSpace

/-! ### Linear maps between normed spaces are smooth -/


theorem ContinuousLinearMap.contMdiff (L : E →L[𝕜] F) : ContMdiff 𝓘(𝕜, E) 𝓘(𝕜, F) n L :=
  L.ContDiff.ContMdiff
#align continuous_linear_map.cont_mdiff ContinuousLinearMap.contMdiff

theorem ContMdiffWithinAt.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁} {s : Set M} {x : M}
    (hg : ContMdiffWithinAt I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g s x)
    (hf : ContMdiffWithinAt I 𝓘(𝕜, F₂ →L[𝕜] F₁) n f s x) :
    ContMdiffWithinAt I 𝓘(𝕜, F₂ →L[𝕜] F₃) n (fun x => (g x).comp (f x)) s x :=
  @ContDiffWithinAt.comp_contMdiffWithinAt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun x : (F₁ →L[𝕜] F₃) × (F₂ →L[𝕜] F₁) => x.1.comp x.2) (fun x => (g x, f x)) s _ x
    (by apply ContDiff.contDiffAt; exact cont_diff_fst.clm_comp contDiff_snd) (hg.prod_mk_space hf)
    (by simp_rw [preimage_univ, subset_univ])
#align cont_mdiff_within_at.clm_comp ContMdiffWithinAt.clm_comp

theorem ContMdiffAt.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁} {x : M}
    (hg : ContMdiffAt I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g x) (hf : ContMdiffAt I 𝓘(𝕜, F₂ →L[𝕜] F₁) n f x) :
    ContMdiffAt I 𝓘(𝕜, F₂ →L[𝕜] F₃) n (fun x => (g x).comp (f x)) x :=
  (hg.ContMdiffWithinAt.clm_comp hf.ContMdiffWithinAt).ContMdiffAt univ_mem
#align cont_mdiff_at.clm_comp ContMdiffAt.clm_comp

theorem ContMdiffOn.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁} {s : Set M}
    (hg : ContMdiffOn I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g s) (hf : ContMdiffOn I 𝓘(𝕜, F₂ →L[𝕜] F₁) n f s) :
    ContMdiffOn I 𝓘(𝕜, F₂ →L[𝕜] F₃) n (fun x => (g x).comp (f x)) s := fun x hx =>
  (hg x hx).clm_comp (hf x hx)
#align cont_mdiff_on.clm_comp ContMdiffOn.clm_comp

theorem ContMdiff.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁}
    (hg : ContMdiff I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g) (hf : ContMdiff I 𝓘(𝕜, F₂ →L[𝕜] F₁) n f) :
    ContMdiff I 𝓘(𝕜, F₂ →L[𝕜] F₃) n fun x => (g x).comp (f x) := fun x => (hg x).clm_comp (hf x)
#align cont_mdiff.clm_comp ContMdiff.clm_comp

theorem ContMdiffWithinAt.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {s : Set M} {x : M}
    (hg : ContMdiffWithinAt I 𝓘(𝕜, F₁ →L[𝕜] F₂) n g s x)
    (hf : ContMdiffWithinAt I 𝓘(𝕜, F₁) n f s x) :
    ContMdiffWithinAt I 𝓘(𝕜, F₂) n (fun x => g x (f x)) s x :=
  @ContDiffWithinAt.comp_contMdiffWithinAt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun x : (F₁ →L[𝕜] F₂) × F₁ => x.1 x.2) (fun x => (g x, f x)) s _ x
    (by apply ContDiff.contDiffAt; exact cont_diff_fst.clm_apply contDiff_snd) (hg.prod_mk_space hf)
    (by simp_rw [preimage_univ, subset_univ])
#align cont_mdiff_within_at.clm_apply ContMdiffWithinAt.clm_apply

theorem ContMdiffAt.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {x : M}
    (hg : ContMdiffAt I 𝓘(𝕜, F₁ →L[𝕜] F₂) n g x) (hf : ContMdiffAt I 𝓘(𝕜, F₁) n f x) :
    ContMdiffAt I 𝓘(𝕜, F₂) n (fun x => g x (f x)) x :=
  (hg.ContMdiffWithinAt.clm_apply hf.ContMdiffWithinAt).ContMdiffAt univ_mem
#align cont_mdiff_at.clm_apply ContMdiffAt.clm_apply

theorem ContMdiffOn.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {s : Set M}
    (hg : ContMdiffOn I 𝓘(𝕜, F₁ →L[𝕜] F₂) n g s) (hf : ContMdiffOn I 𝓘(𝕜, F₁) n f s) :
    ContMdiffOn I 𝓘(𝕜, F₂) n (fun x => g x (f x)) s := fun x hx => (hg x hx).clm_apply (hf x hx)
#align cont_mdiff_on.clm_apply ContMdiffOn.clm_apply

theorem ContMdiff.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁}
    (hg : ContMdiff I 𝓘(𝕜, F₁ →L[𝕜] F₂) n g) (hf : ContMdiff I 𝓘(𝕜, F₁) n f) :
    ContMdiff I 𝓘(𝕜, F₂) n fun x => g x (f x) := fun x => (hg x).clm_apply (hf x)
#align cont_mdiff.clm_apply ContMdiff.clm_apply

theorem ContMdiffWithinAt.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄} {s : Set M}
    {x : M} (hg : ContMdiffWithinAt I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g s x)
    (hf : ContMdiffWithinAt I 𝓘(𝕜, F₂ →L[𝕜] F₄) n f s x) :
    ContMdiffWithinAt I 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₃ × F₄) n (fun x => (g x).Prod_map (f x)) s x :=
  @ContDiffWithinAt.comp_contMdiffWithinAt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun x : (F₁ →L[𝕜] F₃) × (F₂ →L[𝕜] F₄) => x.1.Prod_map x.2) (fun x => (g x, f x)) s _ x
    (by
      apply ContDiff.contDiffAt
      exact (ContinuousLinearMap.prodMapL 𝕜 F₁ F₃ F₂ F₄).ContDiff)
    (hg.prod_mk_space hf) (by simp_rw [preimage_univ, subset_univ])
#align cont_mdiff_within_at.clm_prod_map ContMdiffWithinAt.clm_prodMap

theorem ContMdiffAt.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄} {x : M}
    (hg : ContMdiffAt I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g x) (hf : ContMdiffAt I 𝓘(𝕜, F₂ →L[𝕜] F₄) n f x) :
    ContMdiffAt I 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₃ × F₄) n (fun x => (g x).Prod_map (f x)) x :=
  (hg.ContMdiffWithinAt.clm_prodMap hf.ContMdiffWithinAt).ContMdiffAt univ_mem
#align cont_mdiff_at.clm_prod_map ContMdiffAt.clm_prodMap

theorem ContMdiffOn.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄} {s : Set M}
    (hg : ContMdiffOn I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g s) (hf : ContMdiffOn I 𝓘(𝕜, F₂ →L[𝕜] F₄) n f s) :
    ContMdiffOn I 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₃ × F₄) n (fun x => (g x).Prod_map (f x)) s := fun x hx =>
  (hg x hx).clm_prodMap (hf x hx)
#align cont_mdiff_on.clm_prod_map ContMdiffOn.clm_prodMap

theorem ContMdiff.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄}
    (hg : ContMdiff I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g) (hf : ContMdiff I 𝓘(𝕜, F₂ →L[𝕜] F₄) n f) :
    ContMdiff I 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₃ × F₄) n fun x => (g x).Prod_map (f x) := fun x =>
  (hg x).clm_prodMap (hf x)
#align cont_mdiff.clm_prod_map ContMdiff.clm_prodMap

/-! ### Smoothness of standard operations -/


variable {V : Type _} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- On any vector space, multiplication by a scalar is a smooth operation. -/
theorem smooth_smul : Smooth (𝓘(𝕜).Prod 𝓘(𝕜, V)) 𝓘(𝕜, V) fun p : 𝕜 × V => p.1 • p.2 :=
  smooth_iff.2 ⟨continuous_smul, fun x y => contDiff_smul.ContDiffOn⟩
#align smooth_smul smooth_smul

theorem ContMdiffWithinAt.smul {f : M → 𝕜} {g : M → V} (hf : ContMdiffWithinAt I 𝓘(𝕜) n f s x)
    (hg : ContMdiffWithinAt I 𝓘(𝕜, V) n g s x) :
    ContMdiffWithinAt I 𝓘(𝕜, V) n (fun p => f p • g p) s x :=
  (smooth_smul.of_le le_top).ContMdiffAt.comp_contMdiffWithinAt x (hf.prod_mk hg)
#align cont_mdiff_within_at.smul ContMdiffWithinAt.smul

theorem ContMdiffAt.smul {f : M → 𝕜} {g : M → V} (hf : ContMdiffAt I 𝓘(𝕜) n f x)
    (hg : ContMdiffAt I 𝓘(𝕜, V) n g x) : ContMdiffAt I 𝓘(𝕜, V) n (fun p => f p • g p) x :=
  hf.smul hg
#align cont_mdiff_at.smul ContMdiffAt.smul

theorem ContMdiffOn.smul {f : M → 𝕜} {g : M → V} (hf : ContMdiffOn I 𝓘(𝕜) n f s)
    (hg : ContMdiffOn I 𝓘(𝕜, V) n g s) : ContMdiffOn I 𝓘(𝕜, V) n (fun p => f p • g p) s :=
  fun x hx => (hf x hx).smul (hg x hx)
#align cont_mdiff_on.smul ContMdiffOn.smul

theorem ContMdiff.smul {f : M → 𝕜} {g : M → V} (hf : ContMdiff I 𝓘(𝕜) n f)
    (hg : ContMdiff I 𝓘(𝕜, V) n g) : ContMdiff I 𝓘(𝕜, V) n fun p => f p • g p := fun x =>
  (hf x).smul (hg x)
#align cont_mdiff.smul ContMdiff.smul

theorem SmoothWithinAt.smul {f : M → 𝕜} {g : M → V} (hf : SmoothWithinAt I 𝓘(𝕜) f s x)
    (hg : SmoothWithinAt I 𝓘(𝕜, V) g s x) : SmoothWithinAt I 𝓘(𝕜, V) (fun p => f p • g p) s x :=
  hf.smul hg
#align smooth_within_at.smul SmoothWithinAt.smul

theorem SmoothAt.smul {f : M → 𝕜} {g : M → V} (hf : SmoothAt I 𝓘(𝕜) f x)
    (hg : SmoothAt I 𝓘(𝕜, V) g x) : SmoothAt I 𝓘(𝕜, V) (fun p => f p • g p) x :=
  hf.smul hg
#align smooth_at.smul SmoothAt.smul

theorem SmoothOn.smul {f : M → 𝕜} {g : M → V} (hf : SmoothOn I 𝓘(𝕜) f s)
    (hg : SmoothOn I 𝓘(𝕜, V) g s) : SmoothOn I 𝓘(𝕜, V) (fun p => f p • g p) s :=
  hf.smul hg
#align smooth_on.smul SmoothOn.smul

theorem Smooth.smul {f : M → 𝕜} {g : M → V} (hf : Smooth I 𝓘(𝕜) f) (hg : Smooth I 𝓘(𝕜, V) g) :
    Smooth I 𝓘(𝕜, V) fun p => f p • g p :=
  hf.smul hg
#align smooth.smul Smooth.smul

/-! ### Smoothness of (local) structomorphisms -/


section

variable [ChartedSpace H M'] [IsM' : SmoothManifoldWithCorners I M']

theorem is_local_structomorph_on_contDiffGroupoid_iff_aux {f : LocalHomeomorph M M'}
    (hf : LiftPropOn (contDiffGroupoid ⊤ I).IsLocalStructomorphWithinAt f f.source) :
    SmoothOn I I f f.source := by
  -- It suffices to show smoothness near each `x`
  apply contMdiffOn_of_locally_contMdiffOn
  intro x hx
  let c := chart_at H x
  let c' := chart_at H (f x)
  obtain ⟨-, hxf⟩ := hf x hx
  -- Since `f` is a local structomorph, it is locally equal to some transferred element `e` of
  -- the `cont_diff_groupoid`.
  obtain
    ⟨e, he, he' : eq_on (c' ∘ f ∘ c.symm) e (c.symm ⁻¹' f.source ∩ e.source), hex :
      c x ∈ e.source⟩ :=
    hxf (by simp only [hx, mfld_simps])
  -- We choose a convenient set `s` in `M`.
  let s : Set M := (f.trans c').source ∩ ((c.trans e).trans c'.symm).source
  refine' ⟨s, (f.trans c').open_source.inter ((c.trans e).trans c'.symm).open_source, _, _⟩
  · simp only [mfld_simps]
    rw [← he'] <;> simp only [hx, hex, mfld_simps]
  -- We need to show `f` is `cont_mdiff_on` the domain `s ∩ f.source`.  We show this in two
  -- steps: `f` is equal to `c'.symm ∘ e ∘ c` on that domain and that function is
  -- `cont_mdiff_on` it.
  have H₁ : ContMdiffOn I I ⊤ (c'.symm ∘ e ∘ c) s := by
    have hc' : ContMdiffOn I I ⊤ c'.symm _ := contMdiffOn_chart_symm
    have he'' : ContMdiffOn I I ⊤ e _ := contMdiffOn_of_mem_contDiffGroupoid he
    have hc : ContMdiffOn I I ⊤ c _ := contMdiffOn_chart
    refine' (hc'.comp' (he''.comp' hc)).mono _
    mfld_set_tac
  have H₂ : eq_on f (c'.symm ∘ e ∘ c) s := by
    intro y hy
    simp only [mfld_simps] at hy 
    have hy₁ : f y ∈ c'.source := by simp only [hy, mfld_simps]
    have hy₂ : y ∈ c.source := by simp only [hy, mfld_simps]
    have hy₃ : c y ∈ c.symm ⁻¹' f.source ∩ e.source := by simp only [hy, mfld_simps]
    calc
      f y = c'.symm (c' (f y)) := by rw [c'.left_inv hy₁]
      _ = c'.symm (c' (f (c.symm (c y)))) := by rw [c.left_inv hy₂]
      _ = c'.symm (e (c y)) := by rw [← he' hy₃]
  refine' (H₁.congr H₂).mono _
  mfld_set_tac
#align is_local_structomorph_on_cont_diff_groupoid_iff_aux is_local_structomorph_on_contDiffGroupoid_iff_aux

/-- Let `M` and `M'` be smooth manifolds with the same model-with-corners, `I`.  Then `f : M → M'`
is a local structomorphism for `I`, if and only if it is manifold-smooth on the domain of definition
in both directions. -/
theorem is_local_structomorph_on_contDiffGroupoid_iff (f : LocalHomeomorph M M') :
    LiftPropOn (contDiffGroupoid ⊤ I).IsLocalStructomorphWithinAt f f.source ↔
      SmoothOn I I f f.source ∧ SmoothOn I I f.symm f.target := by
  constructor
  · intro h
    refine'
      ⟨is_local_structomorph_on_contDiffGroupoid_iff_aux h,
        is_local_structomorph_on_contDiffGroupoid_iff_aux _⟩
    -- todo: we can generalize this part of the proof to a lemma
    intro X hX
    let x := f.symm X
    have hx : x ∈ f.source := f.symm.maps_to hX
    let c := chart_at H x
    let c' := chart_at H X
    obtain ⟨-, hxf⟩ := h x hx
    refine' ⟨(f.symm.continuous_at hX).ContinuousWithinAt, fun h2x => _⟩
    obtain ⟨e, he, h2e, hef, hex⟩ :
      ∃ e : LocalHomeomorph H H,
        e ∈ contDiffGroupoid ⊤ I ∧
          e.source ⊆ (c.symm ≫ₕ f ≫ₕ c').source ∧
            eq_on (c' ∘ f ∘ c.symm) e e.source ∧ c x ∈ e.source := by
      have h1 : c' = chart_at H (f x) := by simp only [f.right_inv hX]
      have h2 : ⇑c' ∘ ⇑f ∘ ⇑c.symm = ⇑(c.symm ≫ₕ f ≫ₕ c') := rfl
      have hcx : c x ∈ c.symm ⁻¹' f.source := by simp only [hx, mfld_simps]
      rw [h2]
      rw [← h1, h2, LocalHomeomorph.isLocalStructomorphWithinAt_iff'] at hxf 
      · exact hxf hcx
      · mfld_set_tac
      · apply Or.inl
        simp only [hx, h1, mfld_simps]
    have h2X : c' X = e (c (f.symm X)) := by
      rw [← hef hex]
      dsimp only [Function.comp]
      have hfX : f.symm X ∈ c.source := by simp only [hX, mfld_simps]
      rw [c.left_inv hfX, f.right_inv hX]
    have h3e : eq_on (c ∘ f.symm ∘ c'.symm) e.symm (c'.symm ⁻¹' f.target ∩ e.target) := by
      have h1 : eq_on (c.symm ≫ₕ f ≫ₕ c').symm e.symm (e.target ∩ e.target) := by
        apply eq_on.symm
        refine' e.is_image_source_target.symm_eq_on_of_inter_eq_of_eq_on _ _
        · rw [inter_self, inter_eq_right_iff_subset.mpr h2e]
        rw [inter_self]; exact hef.symm
      have h2 : e.target ⊆ (c.symm ≫ₕ f ≫ₕ c').target := by
        intro x hx; rw [← e.right_inv hx, ← hef (e.symm.maps_to hx)]
        exact LocalHomeomorph.mapsTo _ (h2e <| e.symm.maps_to hx)
      rw [inter_self] at h1 
      rwa [inter_eq_right_iff_subset.mpr]
      refine' h2.trans _
      mfld_set_tac
    refine' ⟨e.symm, StructureGroupoid.symm _ he, h3e, _⟩
    rw [h2X]; exact e.maps_to hex
  · -- We now show the converse: a local homeomorphism `f : M → M'` which is smooth in both
    -- directions is a local structomorphism.  We do this by proposing
    -- `((chart_at H x).symm.trans f).trans (chart_at H (f x))` as a candidate for a structomorphism
    -- of `H`.
    rintro ⟨h₁, h₂⟩ x hx
    refine' ⟨(h₁ x hx).ContinuousWithinAt, _⟩
    let c := chart_at H x
    let c' := chart_at H (f x)
    rintro (hx' : c x ∈ c.symm ⁻¹' f.source)
    -- propose `(c.symm.trans f).trans c'` as a candidate for a local structomorphism of `H`
    refine' ⟨(c.symm.trans f).trans c', ⟨_, _⟩, (_ : eq_on (c' ∘ f ∘ c.symm) _ _), _⟩
    · -- smoothness of the candidate local structomorphism in the forward direction
      intro y hy
      simp only [mfld_simps] at hy 
      have H : ContMdiffWithinAt I I ⊤ f (f ≫ₕ c').source ((extChartAt I x).symm y) := by
        refine' (h₁ ((extChartAt I x).symm y) _).mono _
        · simp only [hy, mfld_simps]
        · mfld_set_tac
      have hy' : (extChartAt I x).symm y ∈ c.source := by simp only [hy, mfld_simps]
      have hy'' : f ((extChartAt I x).symm y) ∈ c'.source := by simp only [hy, mfld_simps]
      rw [contMdiffWithinAt_iff_of_mem_source hy' hy''] at H 
      · convert H.2.mono _
        · simp only [hy, mfld_simps]
        · mfld_set_tac
      · infer_instance
      · infer_instance
    · -- smoothness of the candidate local structomorphism in the reverse direction
      intro y hy
      simp only [mfld_simps] at hy 
      have H : ContMdiffWithinAt I I ⊤ f.symm (f.symm ≫ₕ c).source ((extChartAt I (f x)).symm y) :=
        by
        refine' (h₂ ((extChartAt I (f x)).symm y) _).mono _
        · simp only [hy, mfld_simps]
        · mfld_set_tac
      have hy' : (extChartAt I (f x)).symm y ∈ c'.source := by simp only [hy, mfld_simps]
      have hy'' : f.symm ((extChartAt I (f x)).symm y) ∈ c.source := by simp only [hy, mfld_simps]
      rw [contMdiffWithinAt_iff_of_mem_source hy' hy''] at H 
      · convert H.2.mono _
        · simp only [hy, mfld_simps]
        · mfld_set_tac
      · infer_instance
      · infer_instance
    -- now check the candidate local structomorphism agrees with `f` where it is supposed to
    · simp only [mfld_simps]
    · simp only [hx', mfld_simps]
#align is_local_structomorph_on_cont_diff_groupoid_iff is_local_structomorph_on_contDiffGroupoid_iff

end

