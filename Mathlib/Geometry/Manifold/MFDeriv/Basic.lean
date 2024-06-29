/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Geometry.Manifold.MFDeriv.Defs

#align_import geometry.manifold.mfderiv from "leanprover-community/mathlib"@"e473c3198bb41f68560cab68a0529c854b618833"

/-!
# Basic properties of the manifold Fréchet derivative

In this file, we show various properties of the manifold Fréchet derivative,
mimicking the API for Fréchet derivatives.
- basic properties of unique differentiability sets
- various general lemmas about the manifold Fréchet derivative
- deducing differentiability from smoothness,
- deriving continuity from differentiability on manifolds,
- congruence lemmas for derivatives on manifolds
- composition lemmas and the chain rule

-/

noncomputable section

open scoped Topology Manifold
open Set Bundle

section DerivativesProperties

/-! ### Unique differentiability sets in manifolds -/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {f f₀ f₁ : M → M'} {x : M} {s t : Set M} {g : M' → M''} {u : Set M'}

theorem uniqueMDiffWithinAt_univ : UniqueMDiffWithinAt I univ x := by
  unfold UniqueMDiffWithinAt
  simp only [preimage_univ, univ_inter]
  exact I.unique_diff _ (mem_range_self _)
#align unique_mdiff_within_at_univ uniqueMDiffWithinAt_univ

variable {I}

theorem uniqueMDiffWithinAt_iff {s : Set M} {x : M} :
    UniqueMDiffWithinAt I s x ↔
      UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s ∩ (extChartAt I x).target)
        ((extChartAt I x) x) := by
  apply uniqueDiffWithinAt_congr
  rw [nhdsWithin_inter, nhdsWithin_inter, nhdsWithin_extChartAt_target_eq]
#align unique_mdiff_within_at_iff uniqueMDiffWithinAt_iff

nonrec theorem UniqueMDiffWithinAt.mono_nhds {s t : Set M} {x : M} (hs : UniqueMDiffWithinAt I s x)
    (ht : 𝓝[s] x ≤ 𝓝[t] x) : UniqueMDiffWithinAt I t x :=
  hs.mono_nhds <| by simpa only [← map_extChartAt_nhdsWithin] using Filter.map_mono ht

theorem UniqueMDiffWithinAt.mono_of_mem {s t : Set M} {x : M} (hs : UniqueMDiffWithinAt I s x)
    (ht : t ∈ 𝓝[s] x) : UniqueMDiffWithinAt I t x :=
  hs.mono_nhds (nhdsWithin_le_iff.2 ht)

theorem UniqueMDiffWithinAt.mono (h : UniqueMDiffWithinAt I s x) (st : s ⊆ t) :
    UniqueMDiffWithinAt I t x :=
  UniqueDiffWithinAt.mono h <| inter_subset_inter (preimage_mono st) (Subset.refl _)
#align unique_mdiff_within_at.mono UniqueMDiffWithinAt.mono

theorem UniqueMDiffWithinAt.inter' (hs : UniqueMDiffWithinAt I s x) (ht : t ∈ 𝓝[s] x) :
    UniqueMDiffWithinAt I (s ∩ t) x :=
  hs.mono_of_mem (Filter.inter_mem self_mem_nhdsWithin ht)
#align unique_mdiff_within_at.inter' UniqueMDiffWithinAt.inter'

theorem UniqueMDiffWithinAt.inter (hs : UniqueMDiffWithinAt I s x) (ht : t ∈ 𝓝 x) :
    UniqueMDiffWithinAt I (s ∩ t) x :=
  hs.inter' (nhdsWithin_le_nhds ht)
#align unique_mdiff_within_at.inter UniqueMDiffWithinAt.inter

theorem IsOpen.uniqueMDiffWithinAt (hs : IsOpen s) (xs : x ∈ s) : UniqueMDiffWithinAt I s x :=
  (uniqueMDiffWithinAt_univ I).mono_of_mem <| nhdsWithin_le_nhds <| hs.mem_nhds xs
#align is_open.unique_mdiff_within_at IsOpen.uniqueMDiffWithinAt

theorem UniqueMDiffOn.inter (hs : UniqueMDiffOn I s) (ht : IsOpen t) : UniqueMDiffOn I (s ∩ t) :=
  fun _x hx => UniqueMDiffWithinAt.inter (hs _ hx.1) (ht.mem_nhds hx.2)
#align unique_mdiff_on.inter UniqueMDiffOn.inter

theorem IsOpen.uniqueMDiffOn (hs : IsOpen s) : UniqueMDiffOn I s :=
  fun _x hx => hs.uniqueMDiffWithinAt hx
#align is_open.unique_mdiff_on IsOpen.uniqueMDiffOn

theorem uniqueMDiffOn_univ : UniqueMDiffOn I (univ : Set M) :=
  isOpen_univ.uniqueMDiffOn
#align unique_mdiff_on_univ uniqueMDiffOn_univ

/- We name the typeclass variables related to `SmoothManifoldWithCorners` structure as they are
necessary in lemmas mentioning the derivative, but not in lemmas about differentiability, so we
want to include them or omit them when necessary. -/
variable [Is : SmoothManifoldWithCorners I M] [I's : SmoothManifoldWithCorners I' M']
  [I''s : SmoothManifoldWithCorners I'' M'']
  {f' f₀' f₁' : TangentSpace I x →L[𝕜] TangentSpace I' (f x)}
  {g' : TangentSpace I' (f x) →L[𝕜] TangentSpace I'' (g (f x))}

/-- `UniqueMDiffWithinAt` achieves its goal: it implies the uniqueness of the derivative. -/
nonrec theorem UniqueMDiffWithinAt.eq (U : UniqueMDiffWithinAt I s x)
    (h : HasMFDerivWithinAt I I' f s x f') (h₁ : HasMFDerivWithinAt I I' f s x f₁') : f' = f₁' := by
  -- Porting note: didn't need `convert` because of finding instances by unification
  convert U.eq h.2 h₁.2
#align unique_mdiff_within_at.eq UniqueMDiffWithinAt.eq

theorem UniqueMDiffOn.eq (U : UniqueMDiffOn I s) (hx : x ∈ s) (h : HasMFDerivWithinAt I I' f s x f')
    (h₁ : HasMFDerivWithinAt I I' f s x f₁') : f' = f₁' :=
  UniqueMDiffWithinAt.eq (U _ hx) h h₁
#align unique_mdiff_on.eq UniqueMDiffOn.eq

nonrec theorem UniqueMDiffWithinAt.prod {x : M} {y : M'} {s t} (hs : UniqueMDiffWithinAt I s x)
    (ht : UniqueMDiffWithinAt I' t y) : UniqueMDiffWithinAt (I.prod I') (s ×ˢ t) (x, y) := by
  refine (hs.prod ht).mono ?_
  rw [ModelWithCorners.range_prod, ← prod_inter_prod]
  rfl

theorem UniqueMDiffOn.prod {s : Set M} {t : Set M'} (hs : UniqueMDiffOn I s)
    (ht : UniqueMDiffOn I' t) : UniqueMDiffOn (I.prod I') (s ×ˢ t) := fun x h ↦
  (hs x.1 h.1).prod (ht x.2 h.2)

/-!
### General lemmas on derivatives of functions between manifolds

We mimick the API for functions between vector spaces
-/

theorem mdifferentiableWithinAt_iff {f : M → M'} {s : Set M} {x : M} :
    MDifferentiableWithinAt I I' f s x ↔
      ContinuousWithinAt f s x ∧
        DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f)
          ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) := by
  rw [mdifferentiableWithinAt_iff']
  refine and_congr Iff.rfl (exists_congr fun f' => ?_)
  rw [inter_comm]
  simp only [HasFDerivWithinAt, nhdsWithin_inter, nhdsWithin_extChartAt_target_eq]
#align mdifferentiable_within_at_iff mdifferentiableWithinAt_iff

/-- One can reformulate differentiability within a set at a point as continuity within this set at
this point, and differentiability in any chart containing that point. -/
theorem mdifferentiableWithinAt_iff_of_mem_source {x' : M} {y : M'}
    (hx : x' ∈ (chartAt H x).source) (hy : f x' ∈ (chartAt H' y).source) :
    MDifferentiableWithinAt I I' f s x' ↔
      ContinuousWithinAt f s x' ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s ∩ Set.range I) ((extChartAt I x) x') :=
  (differentiable_within_at_localInvariantProp I I').liftPropWithinAt_indep_chart
    (StructureGroupoid.chart_mem_maximalAtlas _ x) hx (StructureGroupoid.chart_mem_maximalAtlas _ y)
    hy
#align mdifferentiable_within_at_iff_of_mem_source mdifferentiableWithinAt_iff_of_mem_source

theorem mfderivWithin_zero_of_not_mdifferentiableWithinAt
    (h : ¬MDifferentiableWithinAt I I' f s x) : mfderivWithin I I' f s x = 0 := by
  simp only [mfderivWithin, h, if_neg, not_false_iff]
#align mfderiv_within_zero_of_not_mdifferentiable_within_at mfderivWithin_zero_of_not_mdifferentiableWithinAt

theorem mfderiv_zero_of_not_mdifferentiableAt (h : ¬MDifferentiableAt I I' f x) :
    mfderiv I I' f x = 0 := by simp only [mfderiv, h, if_neg, not_false_iff]
#align mfderiv_zero_of_not_mdifferentiable_at mfderiv_zero_of_not_mdifferentiableAt

theorem HasMFDerivWithinAt.mono (h : HasMFDerivWithinAt I I' f t x f') (hst : s ⊆ t) :
    HasMFDerivWithinAt I I' f s x f' :=
  ⟨ContinuousWithinAt.mono h.1 hst,
    HasFDerivWithinAt.mono h.2 (inter_subset_inter (preimage_mono hst) (Subset.refl _))⟩
#align has_mfderiv_within_at.mono HasMFDerivWithinAt.mono

theorem HasMFDerivAt.hasMFDerivWithinAt (h : HasMFDerivAt I I' f x f') :
    HasMFDerivWithinAt I I' f s x f' :=
  ⟨ContinuousAt.continuousWithinAt h.1, HasFDerivWithinAt.mono h.2 inter_subset_right⟩
#align has_mfderiv_at.has_mfderiv_within_at HasMFDerivAt.hasMFDerivWithinAt

theorem HasMFDerivWithinAt.mdifferentiableWithinAt (h : HasMFDerivWithinAt I I' f s x f') :
    MDifferentiableWithinAt I I' f s x :=
  ⟨h.1, ⟨f', h.2⟩⟩
#align has_mfderiv_within_at.mdifferentiable_within_at HasMFDerivWithinAt.mdifferentiableWithinAt

theorem HasMFDerivAt.mdifferentiableAt (h : HasMFDerivAt I I' f x f') :
    MDifferentiableAt I I' f x := by
  rw [mdifferentiableAt_iff]
  exact ⟨h.1, ⟨f', h.2⟩⟩
#align has_mfderiv_at.mdifferentiable_at HasMFDerivAt.mdifferentiableAt

@[simp, mfld_simps]
theorem hasMFDerivWithinAt_univ :
    HasMFDerivWithinAt I I' f univ x f' ↔ HasMFDerivAt I I' f x f' := by
  simp only [HasMFDerivWithinAt, HasMFDerivAt, continuousWithinAt_univ, mfld_simps]
#align has_mfderiv_within_at_univ hasMFDerivWithinAt_univ

theorem hasMFDerivAt_unique (h₀ : HasMFDerivAt I I' f x f₀') (h₁ : HasMFDerivAt I I' f x f₁') :
    f₀' = f₁' := by
  rw [← hasMFDerivWithinAt_univ] at h₀ h₁
  exact (uniqueMDiffWithinAt_univ I).eq h₀ h₁
#align has_mfderiv_at_unique hasMFDerivAt_unique

theorem hasMFDerivWithinAt_inter' (h : t ∈ 𝓝[s] x) :
    HasMFDerivWithinAt I I' f (s ∩ t) x f' ↔ HasMFDerivWithinAt I I' f s x f' := by
  rw [HasMFDerivWithinAt, HasMFDerivWithinAt, extChartAt_preimage_inter_eq,
    hasFDerivWithinAt_inter', continuousWithinAt_inter' h]
  exact extChartAt_preimage_mem_nhdsWithin I h
#align has_mfderiv_within_at_inter' hasMFDerivWithinAt_inter'

theorem hasMFDerivWithinAt_inter (h : t ∈ 𝓝 x) :
    HasMFDerivWithinAt I I' f (s ∩ t) x f' ↔ HasMFDerivWithinAt I I' f s x f' := by
  rw [HasMFDerivWithinAt, HasMFDerivWithinAt, extChartAt_preimage_inter_eq, hasFDerivWithinAt_inter,
    continuousWithinAt_inter h]
  exact extChartAt_preimage_mem_nhds I h
#align has_mfderiv_within_at_inter hasMFDerivWithinAt_inter

theorem HasMFDerivWithinAt.union (hs : HasMFDerivWithinAt I I' f s x f')
    (ht : HasMFDerivWithinAt I I' f t x f') : HasMFDerivWithinAt I I' f (s ∪ t) x f' := by
  constructor
  · exact ContinuousWithinAt.union hs.1 ht.1
  · convert HasFDerivWithinAt.union hs.2 ht.2 using 1
    simp only [union_inter_distrib_right, preimage_union]
#align has_mfderiv_within_at.union HasMFDerivWithinAt.union

theorem HasMFDerivWithinAt.mono_of_mem (h : HasMFDerivWithinAt I I' f s x f') (ht : s ∈ 𝓝[t] x) :
    HasMFDerivWithinAt I I' f t x f' :=
  (hasMFDerivWithinAt_inter' ht).1 (h.mono inter_subset_right)
#align has_mfderiv_within_at.nhds_within HasMFDerivWithinAt.mono_of_mem

theorem HasMFDerivWithinAt.hasMFDerivAt (h : HasMFDerivWithinAt I I' f s x f') (hs : s ∈ 𝓝 x) :
    HasMFDerivAt I I' f x f' := by
  rwa [← univ_inter s, hasMFDerivWithinAt_inter hs, hasMFDerivWithinAt_univ] at h
#align has_mfderiv_within_at.has_mfderiv_at HasMFDerivWithinAt.hasMFDerivAt

theorem MDifferentiableWithinAt.hasMFDerivWithinAt (h : MDifferentiableWithinAt I I' f s x) :
    HasMFDerivWithinAt I I' f s x (mfderivWithin I I' f s x) := by
  refine ⟨h.1, ?_⟩
  simp only [mfderivWithin, h, if_pos, mfld_simps]
  exact DifferentiableWithinAt.hasFDerivWithinAt h.2
#align mdifferentiable_within_at.has_mfderiv_within_at MDifferentiableWithinAt.hasMFDerivWithinAt

protected theorem MDifferentiableWithinAt.mfderivWithin (h : MDifferentiableWithinAt I I' f s x) :
    mfderivWithin I I' f s x =
      fderivWithin 𝕜 (writtenInExtChartAt I I' x f : _) ((extChartAt I x).symm ⁻¹' s ∩ range I)
        ((extChartAt I x) x) := by
  simp only [mfderivWithin, h, if_pos]
#align mdifferentiable_within_at.mfderiv_within MDifferentiableWithinAt.mfderivWithin

theorem MDifferentiableAt.hasMFDerivAt (h : MDifferentiableAt I I' f x) :
    HasMFDerivAt I I' f x (mfderiv I I' f x) := by
  refine ⟨h.continuousAt, ?_⟩
  simp only [mfderiv, h, if_pos, mfld_simps]
  exact DifferentiableWithinAt.hasFDerivWithinAt h.differentiableWithinAt_writtenInExtChartAt
#align mdifferentiable_at.has_mfderiv_at MDifferentiableAt.hasMFDerivAt

protected theorem MDifferentiableAt.mfderiv (h : MDifferentiableAt I I' f x) :
    mfderiv I I' f x =
      fderivWithin 𝕜 (writtenInExtChartAt I I' x f : _) (range I) ((extChartAt I x) x) := by
  simp only [mfderiv, h, if_pos]
#align mdifferentiable_at.mfderiv MDifferentiableAt.mfderiv

protected theorem HasMFDerivAt.mfderiv (h : HasMFDerivAt I I' f x f') : mfderiv I I' f x = f' :=
  (hasMFDerivAt_unique h h.mdifferentiableAt.hasMFDerivAt).symm
#align has_mfderiv_at.mfderiv HasMFDerivAt.mfderiv

theorem HasMFDerivWithinAt.mfderivWithin (h : HasMFDerivWithinAt I I' f s x f')
    (hxs : UniqueMDiffWithinAt I s x) : mfderivWithin I I' f s x = f' := by
  ext
  rw [hxs.eq h h.mdifferentiableWithinAt.hasMFDerivWithinAt]
#align has_mfderiv_within_at.mfderiv_within HasMFDerivWithinAt.mfderivWithin

theorem MDifferentiable.mfderivWithin (h : MDifferentiableAt I I' f x)
    (hxs : UniqueMDiffWithinAt I s x) : mfderivWithin I I' f s x = mfderiv I I' f x := by
  apply HasMFDerivWithinAt.mfderivWithin _ hxs
  exact h.hasMFDerivAt.hasMFDerivWithinAt
#align mdifferentiable.mfderiv_within MDifferentiable.mfderivWithin

theorem mfderivWithin_subset (st : s ⊆ t) (hs : UniqueMDiffWithinAt I s x)
    (h : MDifferentiableWithinAt I I' f t x) :
    mfderivWithin I I' f s x = mfderivWithin I I' f t x :=
  ((MDifferentiableWithinAt.hasMFDerivWithinAt h).mono st).mfderivWithin hs
#align mfderiv_within_subset mfderivWithin_subset

theorem MDifferentiableWithinAt.mono (hst : s ⊆ t) (h : MDifferentiableWithinAt I I' f t x) :
    MDifferentiableWithinAt I I' f s x :=
  ⟨ContinuousWithinAt.mono h.1 hst, DifferentiableWithinAt.mono
    h.differentiableWithinAt_writtenInExtChartAt
    (inter_subset_inter_left _ (preimage_mono hst))⟩
#align mdifferentiable_within_at.mono MDifferentiableWithinAt.mono

theorem mdifferentiableWithinAt_univ :
    MDifferentiableWithinAt I I' f univ x ↔ MDifferentiableAt I I' f x := by
  simp_rw [MDifferentiableWithinAt, MDifferentiableAt, ChartedSpace.LiftPropAt]
#align mdifferentiable_within_at_univ mdifferentiableWithinAt_univ

theorem mdifferentiableWithinAt_inter (ht : t ∈ 𝓝 x) :
    MDifferentiableWithinAt I I' f (s ∩ t) x ↔ MDifferentiableWithinAt I I' f s x := by
  rw [MDifferentiableWithinAt, MDifferentiableWithinAt,
    (differentiable_within_at_localInvariantProp I I').liftPropWithinAt_inter ht]
#align mdifferentiable_within_at_inter mdifferentiableWithinAt_inter

theorem mdifferentiableWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    MDifferentiableWithinAt I I' f (s ∩ t) x ↔ MDifferentiableWithinAt I I' f s x := by
  rw [MDifferentiableWithinAt, MDifferentiableWithinAt,
    (differentiable_within_at_localInvariantProp I I').liftPropWithinAt_inter' ht]
#align mdifferentiable_within_at_inter' mdifferentiableWithinAt_inter'

theorem MDifferentiableAt.mdifferentiableWithinAt (h : MDifferentiableAt I I' f x) :
    MDifferentiableWithinAt I I' f s x :=
  MDifferentiableWithinAt.mono (subset_univ _) (mdifferentiableWithinAt_univ.2 h)
#align mdifferentiable_at.mdifferentiable_within_at MDifferentiableAt.mdifferentiableWithinAt

theorem MDifferentiableWithinAt.mdifferentiableAt (h : MDifferentiableWithinAt I I' f s x)
    (hs : s ∈ 𝓝 x) : MDifferentiableAt I I' f x := by
  have : s = univ ∩ s := by rw [univ_inter]
  rwa [this, mdifferentiableWithinAt_inter hs, mdifferentiableWithinAt_univ] at h
#align mdifferentiable_within_at.mdifferentiable_at MDifferentiableWithinAt.mdifferentiableAt

theorem MDifferentiableOn.mdifferentiableAt (h : MDifferentiableOn I I' f s) (hx : s ∈ 𝓝 x) :
    MDifferentiableAt I I' f x :=
  (h x (mem_of_mem_nhds hx)).mdifferentiableAt hx

theorem MDifferentiableOn.mono (h : MDifferentiableOn I I' f t) (st : s ⊆ t) :
    MDifferentiableOn I I' f s := fun x hx => (h x (st hx)).mono st
#align mdifferentiable_on.mono MDifferentiableOn.mono

theorem mdifferentiableOn_univ : MDifferentiableOn I I' f univ ↔ MDifferentiable I I' f := by
  simp only [MDifferentiableOn, mdifferentiableWithinAt_univ, mfld_simps]; rfl
#align mdifferentiable_on_univ mdifferentiableOn_univ

theorem MDifferentiable.mdifferentiableOn (h : MDifferentiable I I' f) :
    MDifferentiableOn I I' f s :=
  (mdifferentiableOn_univ.2 h).mono (subset_univ _)
#align mdifferentiable.mdifferentiable_on MDifferentiable.mdifferentiableOn

theorem mdifferentiableOn_of_locally_mdifferentiableOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ MDifferentiableOn I I' f (s ∩ u)) :
    MDifferentiableOn I I' f s := by
  intro x xs
  rcases h x xs with ⟨t, t_open, xt, ht⟩
  exact (mdifferentiableWithinAt_inter (t_open.mem_nhds xt)).1 (ht x ⟨xs, xt⟩)
#align mdifferentiable_on_of_locally_mdifferentiable_on mdifferentiableOn_of_locally_mdifferentiableOn

@[simp, mfld_simps]
theorem mfderivWithin_univ : mfderivWithin I I' f univ = mfderiv I I' f := by
  ext x : 1
  simp only [mfderivWithin, mfderiv, mfld_simps]
  rw [mdifferentiableWithinAt_univ]
#align mfderiv_within_univ mfderivWithin_univ

theorem mfderivWithin_inter (ht : t ∈ 𝓝 x) :
    mfderivWithin I I' f (s ∩ t) x = mfderivWithin I I' f s x := by
  rw [mfderivWithin, mfderivWithin, extChartAt_preimage_inter_eq, mdifferentiableWithinAt_inter ht,
    fderivWithin_inter (extChartAt_preimage_mem_nhds I ht)]
#align mfderiv_within_inter mfderivWithin_inter

theorem mfderivWithin_of_mem_nhds (h : s ∈ 𝓝 x) : mfderivWithin I I' f s x = mfderiv I I' f x := by
  rw [← mfderivWithin_univ, ← univ_inter s, mfderivWithin_inter h]

lemma mfderivWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) :
    mfderivWithin I I' f s x = mfderiv I I' f x :=
  mfderivWithin_of_mem_nhds (hs.mem_nhds hx)

theorem mfderivWithin_eq_mfderiv (hs : UniqueMDiffWithinAt I s x) (h : MDifferentiableAt I I' f x) :
    mfderivWithin I I' f s x = mfderiv I I' f x := by
  rw [← mfderivWithin_univ]
  exact mfderivWithin_subset (subset_univ _) hs h.mdifferentiableWithinAt

theorem mdifferentiableAt_iff_of_mem_source {x' : M} {y : M'}
    (hx : x' ∈ (chartAt H x).source) (hy : f x' ∈ (chartAt H' y).source) :
    MDifferentiableAt I I' f x' ↔
      ContinuousAt f x' ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (Set.range I)
          ((extChartAt I x) x') :=
  mdifferentiableWithinAt_univ.symm.trans <|
    (mdifferentiableWithinAt_iff_of_mem_source hx hy).trans <| by
      rw [continuousWithinAt_univ, Set.preimage_univ, Set.univ_inter]
#align mdifferentiable_at_iff_of_mem_source mdifferentiableAt_iff_of_mem_source

/-! ### Deducing differentiability from smoothness -/

-- Porting note: moved from `ContMDiffMFDeriv`
variable {n : ℕ∞}

theorem ContMDiffWithinAt.mdifferentiableWithinAt (hf : ContMDiffWithinAt I I' n f s x)
    (hn : 1 ≤ n) : MDifferentiableWithinAt I I' f s x := by
  suffices h : MDifferentiableWithinAt I I' f (s ∩ f ⁻¹' (extChartAt I' (f x)).source) x by
    rwa [mdifferentiableWithinAt_inter'] at h
    apply hf.1.preimage_mem_nhdsWithin
    exact extChartAt_source_mem_nhds I' (f x)
  rw [mdifferentiableWithinAt_iff]
  exact ⟨hf.1.mono inter_subset_left, (hf.2.differentiableWithinAt hn).mono (by mfld_set_tac)⟩
#align cont_mdiff_within_at.mdifferentiable_within_at ContMDiffWithinAt.mdifferentiableWithinAt

theorem ContMDiffAt.mdifferentiableAt (hf : ContMDiffAt I I' n f x) (hn : 1 ≤ n) :
    MDifferentiableAt I I' f x :=
  mdifferentiableWithinAt_univ.1 <| ContMDiffWithinAt.mdifferentiableWithinAt hf hn
#align cont_mdiff_at.mdifferentiable_at ContMDiffAt.mdifferentiableAt

theorem ContMDiffOn.mdifferentiableOn (hf : ContMDiffOn I I' n f s) (hn : 1 ≤ n) :
    MDifferentiableOn I I' f s := fun x hx => (hf x hx).mdifferentiableWithinAt hn
#align cont_mdiff_on.mdifferentiable_on ContMDiffOn.mdifferentiableOn

theorem ContMDiff.mdifferentiable (hf : ContMDiff I I' n f) (hn : 1 ≤ n) : MDifferentiable I I' f :=
  fun x => (hf x).mdifferentiableAt hn
#align cont_mdiff.mdifferentiable ContMDiff.mdifferentiable

nonrec theorem SmoothWithinAt.mdifferentiableWithinAt (hf : SmoothWithinAt I I' f s x) :
    MDifferentiableWithinAt I I' f s x :=
  hf.mdifferentiableWithinAt le_top
#align smooth_within_at.mdifferentiable_within_at SmoothWithinAt.mdifferentiableWithinAt

nonrec theorem SmoothAt.mdifferentiableAt (hf : SmoothAt I I' f x) : MDifferentiableAt I I' f x :=
  hf.mdifferentiableAt le_top
#align smooth_at.mdifferentiable_at SmoothAt.mdifferentiableAt

nonrec theorem SmoothOn.mdifferentiableOn (hf : SmoothOn I I' f s) : MDifferentiableOn I I' f s :=
  hf.mdifferentiableOn le_top
#align smooth_on.mdifferentiable_on SmoothOn.mdifferentiableOn

theorem Smooth.mdifferentiable (hf : Smooth I I' f) : MDifferentiable I I' f :=
  ContMDiff.mdifferentiable hf le_top
#align smooth.mdifferentiable Smooth.mdifferentiable

theorem Smooth.mdifferentiableAt (hf : Smooth I I' f) : MDifferentiableAt I I' f x :=
  hf.mdifferentiable x
#align smooth.mdifferentiable_at Smooth.mdifferentiableAt

theorem Smooth.mdifferentiableWithinAt (hf : Smooth I I' f) : MDifferentiableWithinAt I I' f s x :=
  hf.mdifferentiableAt.mdifferentiableWithinAt
#align smooth.mdifferentiable_within_at Smooth.mdifferentiableWithinAt

/-! ### Deriving continuity from differentiability on manifolds -/

theorem HasMFDerivWithinAt.continuousWithinAt (h : HasMFDerivWithinAt I I' f s x f') :
    ContinuousWithinAt f s x :=
  h.1
#align has_mfderiv_within_at.continuous_within_at HasMFDerivWithinAt.continuousWithinAt

theorem HasMFDerivAt.continuousAt (h : HasMFDerivAt I I' f x f') : ContinuousAt f x :=
  h.1
#align has_mfderiv_at.continuous_at HasMFDerivAt.continuousAt

theorem MDifferentiableOn.continuousOn (h : MDifferentiableOn I I' f s) : ContinuousOn f s :=
  fun x hx => (h x hx).continuousWithinAt
#align mdifferentiable_on.continuous_on MDifferentiableOn.continuousOn

theorem MDifferentiable.continuous (h : MDifferentiable I I' f) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (h x).continuousAt
#align mdifferentiable.continuous MDifferentiable.continuous

theorem tangentMapWithin_subset {p : TangentBundle I M} (st : s ⊆ t)
    (hs : UniqueMDiffWithinAt I s p.1) (h : MDifferentiableWithinAt I I' f t p.1) :
    tangentMapWithin I I' f s p = tangentMapWithin I I' f t p := by
  simp only [tangentMapWithin, mfld_simps]
  rw [mfderivWithin_subset st hs h]
#align tangent_map_within_subset tangentMapWithin_subset

theorem tangentMapWithin_univ : tangentMapWithin I I' f univ = tangentMap I I' f := by
  ext p : 1
  simp only [tangentMapWithin, tangentMap, mfld_simps]
#align tangent_map_within_univ tangentMapWithin_univ

theorem tangentMapWithin_eq_tangentMap {p : TangentBundle I M} (hs : UniqueMDiffWithinAt I s p.1)
    (h : MDifferentiableAt I I' f p.1) : tangentMapWithin I I' f s p = tangentMap I I' f p := by
  rw [← mdifferentiableWithinAt_univ] at h
  rw [← tangentMapWithin_univ]
  exact tangentMapWithin_subset (subset_univ _) hs h
#align tangent_map_within_eq_tangent_map tangentMapWithin_eq_tangentMap

@[simp, mfld_simps]
theorem tangentMapWithin_proj {p : TangentBundle I M} :
    (tangentMapWithin I I' f s p).proj = f p.proj :=
  rfl
#align tangent_map_within_proj tangentMapWithin_proj

@[simp, mfld_simps]
theorem tangentMap_proj {p : TangentBundle I M} : (tangentMap I I' f p).proj = f p.proj :=
  rfl
#align tangent_map_proj tangentMap_proj

theorem MDifferentiableWithinAt.prod_mk {f : M → M'} {g : M → M''}
    (hf : MDifferentiableWithinAt I I' f s x) (hg : MDifferentiableWithinAt I I'' g s x) :
    MDifferentiableWithinAt I (I'.prod I'') (fun x => (f x, g x)) s x :=
  ⟨hf.1.prod hg.1, hf.2.prod hg.2⟩
#align mdifferentiable_within_at.prod_mk MDifferentiableWithinAt.prod_mk

theorem MDifferentiableAt.prod_mk {f : M → M'} {g : M → M''} (hf : MDifferentiableAt I I' f x)
    (hg : MDifferentiableAt I I'' g x) :
    MDifferentiableAt I (I'.prod I'') (fun x => (f x, g x)) x :=
  ⟨hf.1.prod hg.1, hf.2.prod hg.2⟩
#align mdifferentiable_at.prod_mk MDifferentiableAt.prod_mk

theorem MDifferentiableOn.prod_mk {f : M → M'} {g : M → M''} (hf : MDifferentiableOn I I' f s)
    (hg : MDifferentiableOn I I'' g s) :
    MDifferentiableOn I (I'.prod I'') (fun x => (f x, g x)) s := fun x hx =>
  (hf x hx).prod_mk (hg x hx)
#align mdifferentiable_on.prod_mk MDifferentiableOn.prod_mk

theorem MDifferentiable.prod_mk {f : M → M'} {g : M → M''} (hf : MDifferentiable I I' f)
    (hg : MDifferentiable I I'' g) : MDifferentiable I (I'.prod I'') fun x => (f x, g x) := fun x =>
  (hf x).prod_mk (hg x)
#align mdifferentiable.prod_mk MDifferentiable.prod_mk

theorem MDifferentiableWithinAt.prod_mk_space {f : M → E'} {g : M → E''}
    (hf : MDifferentiableWithinAt I 𝓘(𝕜, E') f s x)
    (hg : MDifferentiableWithinAt I 𝓘(𝕜, E'') g s x) :
    MDifferentiableWithinAt I 𝓘(𝕜, E' × E'') (fun x => (f x, g x)) s x :=
  ⟨hf.1.prod hg.1, hf.2.prod hg.2⟩
#align mdifferentiable_within_at.prod_mk_space MDifferentiableWithinAt.prod_mk_space

theorem MDifferentiableAt.prod_mk_space {f : M → E'} {g : M → E''}
    (hf : MDifferentiableAt I 𝓘(𝕜, E') f x) (hg : MDifferentiableAt I 𝓘(𝕜, E'') g x) :
    MDifferentiableAt I 𝓘(𝕜, E' × E'') (fun x => (f x, g x)) x :=
  ⟨hf.1.prod hg.1, hf.2.prod hg.2⟩
#align mdifferentiable_at.prod_mk_space MDifferentiableAt.prod_mk_space

theorem MDifferentiableOn.prod_mk_space {f : M → E'} {g : M → E''}
    (hf : MDifferentiableOn I 𝓘(𝕜, E') f s) (hg : MDifferentiableOn I 𝓘(𝕜, E'') g s) :
    MDifferentiableOn I 𝓘(𝕜, E' × E'') (fun x => (f x, g x)) s := fun x hx =>
  (hf x hx).prod_mk_space (hg x hx)
#align mdifferentiable_on.prod_mk_space MDifferentiableOn.prod_mk_space

theorem MDifferentiable.prod_mk_space {f : M → E'} {g : M → E''} (hf : MDifferentiable I 𝓘(𝕜, E') f)
    (hg : MDifferentiable I 𝓘(𝕜, E'') g) : MDifferentiable I 𝓘(𝕜, E' × E'') fun x => (f x, g x) :=
  fun x => (hf x).prod_mk_space (hg x)
#align mdifferentiable.prod_mk_space MDifferentiable.prod_mk_space

/-! ### Congruence lemmas for derivatives on manifolds -/

theorem HasMFDerivAt.congr_mfderiv (h : HasMFDerivAt I I' f x f') (h' : f' = f₁') :
    HasMFDerivAt I I' f x f₁' :=
  h' ▸ h

theorem HasMFDerivWithinAt.congr_mfderiv (h : HasMFDerivWithinAt I I' f s x f') (h' : f' = f₁') :
    HasMFDerivWithinAt I I' f s x f₁' :=
  h' ▸ h

theorem HasMFDerivWithinAt.congr_of_eventuallyEq (h : HasMFDerivWithinAt I I' f s x f')
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasMFDerivWithinAt I I' f₁ s x f' := by
  refine ⟨ContinuousWithinAt.congr_of_eventuallyEq h.1 h₁ hx, ?_⟩
  apply HasFDerivWithinAt.congr_of_eventuallyEq h.2
  · have :
      (extChartAt I x).symm ⁻¹' {y | f₁ y = f y} ∈
        𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x :=
      extChartAt_preimage_mem_nhdsWithin I h₁
    apply Filter.mem_of_superset this fun y => _
    simp (config := { contextual := true }) only [hx, mfld_simps]
  · simp only [hx, mfld_simps]
#align has_mfderiv_within_at.congr_of_eventually_eq HasMFDerivWithinAt.congr_of_eventuallyEq

theorem HasMFDerivWithinAt.congr_mono (h : HasMFDerivWithinAt I I' f s x f')
    (ht : ∀ x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasMFDerivWithinAt I I' f₁ t x f' :=
  (h.mono h₁).congr_of_eventuallyEq (Filter.mem_inf_of_right ht) hx
#align has_mfderiv_within_at.congr_mono HasMFDerivWithinAt.congr_mono

theorem HasMFDerivAt.congr_of_eventuallyEq (h : HasMFDerivAt I I' f x f') (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasMFDerivAt I I' f₁ x f' := by
  rw [← hasMFDerivWithinAt_univ] at h ⊢
  apply h.congr_of_eventuallyEq _ (mem_of_mem_nhds h₁ : _)
  rwa [nhdsWithin_univ]
#align has_mfderiv_at.congr_of_eventually_eq HasMFDerivAt.congr_of_eventuallyEq

theorem MDifferentiableWithinAt.congr_of_eventuallyEq (h : MDifferentiableWithinAt I I' f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : MDifferentiableWithinAt I I' f₁ s x :=
  (h.hasMFDerivWithinAt.congr_of_eventuallyEq h₁ hx).mdifferentiableWithinAt
#align mdifferentiable_within_at.congr_of_eventually_eq MDifferentiableWithinAt.congr_of_eventuallyEq

variable (I I')

theorem Filter.EventuallyEq.mdifferentiableWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    MDifferentiableWithinAt I I' f s x ↔ MDifferentiableWithinAt I I' f₁ s x := by
  constructor
  · intro h
    apply h.congr_of_eventuallyEq h₁ hx
  · intro h
    apply h.congr_of_eventuallyEq _ hx.symm
    apply h₁.mono
    intro y
    apply Eq.symm
#align filter.eventually_eq.mdifferentiable_within_at_iff Filter.EventuallyEq.mdifferentiableWithinAt_iff

variable {I I'}

theorem MDifferentiableWithinAt.congr_mono (h : MDifferentiableWithinAt I I' f s x)
    (ht : ∀ x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t ⊆ s) :
    MDifferentiableWithinAt I I' f₁ t x :=
  (HasMFDerivWithinAt.congr_mono h.hasMFDerivWithinAt ht hx h₁).mdifferentiableWithinAt
#align mdifferentiable_within_at.congr_mono MDifferentiableWithinAt.congr_mono

theorem MDifferentiableWithinAt.congr (h : MDifferentiableWithinAt I I' f s x)
    (ht : ∀ x ∈ s, f₁ x = f x) (hx : f₁ x = f x) : MDifferentiableWithinAt I I' f₁ s x :=
  (HasMFDerivWithinAt.congr_mono h.hasMFDerivWithinAt ht hx (Subset.refl _)).mdifferentiableWithinAt
#align mdifferentiable_within_at.congr MDifferentiableWithinAt.congr

theorem MDifferentiableOn.congr_mono (h : MDifferentiableOn I I' f s) (h' : ∀ x ∈ t, f₁ x = f x)
    (h₁ : t ⊆ s) : MDifferentiableOn I I' f₁ t := fun x hx =>
  (h x (h₁ hx)).congr_mono h' (h' x hx) h₁
#align mdifferentiable_on.congr_mono MDifferentiableOn.congr_mono

theorem MDifferentiableAt.congr_of_eventuallyEq (h : MDifferentiableAt I I' f x)
    (hL : f₁ =ᶠ[𝓝 x] f) : MDifferentiableAt I I' f₁ x :=
  (h.hasMFDerivAt.congr_of_eventuallyEq hL).mdifferentiableAt
#align mdifferentiable_at.congr_of_eventually_eq MDifferentiableAt.congr_of_eventuallyEq

theorem MDifferentiableWithinAt.mfderivWithin_congr_mono (h : MDifferentiableWithinAt I I' f s x)
    (hs : ∀ x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (hxt : UniqueMDiffWithinAt I t x) (h₁ : t ⊆ s) :
    mfderivWithin I I' f₁ t x = (mfderivWithin I I' f s x : _) :=
  (HasMFDerivWithinAt.congr_mono h.hasMFDerivWithinAt hs hx h₁).mfderivWithin hxt
#align mdifferentiable_within_at.mfderiv_within_congr_mono MDifferentiableWithinAt.mfderivWithin_congr_mono

theorem Filter.EventuallyEq.mfderivWithin_eq (hs : UniqueMDiffWithinAt I s x) (hL : f₁ =ᶠ[𝓝[s] x] f)
    (hx : f₁ x = f x) : mfderivWithin I I' f₁ s x = (mfderivWithin I I' f s x : _) := by
  by_cases h : MDifferentiableWithinAt I I' f s x
  · exact (h.hasMFDerivWithinAt.congr_of_eventuallyEq hL hx).mfderivWithin hs
  · unfold mfderivWithin
    rw [if_neg h, if_neg]
    rwa [← hL.mdifferentiableWithinAt_iff I I' hx]
#align filter.eventually_eq.mfderiv_within_eq Filter.EventuallyEq.mfderivWithin_eq

theorem mfderivWithin_congr (hs : UniqueMDiffWithinAt I s x) (hL : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : mfderivWithin I I' f₁ s x = (mfderivWithin I I' f s x : _) :=
  Filter.EventuallyEq.mfderivWithin_eq hs (Filter.eventuallyEq_of_mem self_mem_nhdsWithin hL) hx
#align mfderiv_within_congr mfderivWithin_congr

theorem tangentMapWithin_congr (h : ∀ x ∈ s, f x = f₁ x) (p : TangentBundle I M) (hp : p.1 ∈ s)
    (hs : UniqueMDiffWithinAt I s p.1) :
    tangentMapWithin I I' f s p = tangentMapWithin I I' f₁ s p := by
  refine TotalSpace.ext _ _ (h p.1 hp) ?_
  -- This used to be `simp only`, but we need `erw` after leanprover/lean4#2644
  rw [tangentMapWithin, h p.1 hp, tangentMapWithin, mfderivWithin_congr hs h (h _ hp)]
#align tangent_map_within_congr tangentMapWithin_congr

theorem Filter.EventuallyEq.mfderiv_eq (hL : f₁ =ᶠ[𝓝 x] f) :
    mfderiv I I' f₁ x = (mfderiv I I' f x : _) := by
  have A : f₁ x = f x := (mem_of_mem_nhds hL : _)
  rw [← mfderivWithin_univ, ← mfderivWithin_univ]
  rw [← nhdsWithin_univ] at hL
  exact hL.mfderivWithin_eq (uniqueMDiffWithinAt_univ I) A
#align filter.eventually_eq.mfderiv_eq Filter.EventuallyEq.mfderiv_eq

/-- A congruence lemma for `mfderiv`, (ab)using the fact that `TangentSpace I' (f x)` is
definitionally equal to `E'`. -/
theorem mfderiv_congr_point {x' : M} (h : x = x') :
    @Eq (E →L[𝕜] E') (mfderiv I I' f x) (mfderiv I I' f x') := by subst h; rfl
#align mfderiv_congr_point mfderiv_congr_point

/-- A congruence lemma for `mfderiv`, (ab)using the fact that `TangentSpace I' (f x)` is
definitionally equal to `E'`. -/
theorem mfderiv_congr {f' : M → M'} (h : f = f') :
    @Eq (E →L[𝕜] E') (mfderiv I I' f x) (mfderiv I I' f' x) := by subst h; rfl
#align mfderiv_congr mfderiv_congr

/-! ### Composition lemmas -/

theorem writtenInExtChartAt_comp (h : ContinuousWithinAt f s x) :
    {y | writtenInExtChartAt I I'' x (g ∘ f) y =
          (writtenInExtChartAt I' I'' (f x) g ∘ writtenInExtChartAt I I' x f) y} ∈
      𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x := by
  apply
    @Filter.mem_of_superset _ _ (f ∘ (extChartAt I x).symm ⁻¹' (extChartAt I' (f x)).source) _
      (extChartAt_preimage_mem_nhdsWithin I
        (h.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds _ _)))
  mfld_set_tac
#align written_in_ext_chart_comp writtenInExtChartAt_comp

variable (x)

theorem HasMFDerivWithinAt.comp (hg : HasMFDerivWithinAt I' I'' g u (f x) g')
    (hf : HasMFDerivWithinAt I I' f s x f') (hst : s ⊆ f ⁻¹' u) :
    HasMFDerivWithinAt I I'' (g ∘ f) s x (g'.comp f') := by
  refine ⟨ContinuousWithinAt.comp hg.1 hf.1 hst, ?_⟩
  have A :
    HasFDerivWithinAt (writtenInExtChartAt I' I'' (f x) g ∘ writtenInExtChartAt I I' x f)
      (ContinuousLinearMap.comp g' f' : E →L[𝕜] E'') ((extChartAt I x).symm ⁻¹' s ∩ range I)
      ((extChartAt I x) x) := by
    have :
      (extChartAt I x).symm ⁻¹' (f ⁻¹' (extChartAt I' (f x)).source) ∈
        𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x :=
      extChartAt_preimage_mem_nhdsWithin I
        (hf.1.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds _ _))
    unfold HasMFDerivWithinAt at *
    rw [← hasFDerivWithinAt_inter' this, ← extChartAt_preimage_inter_eq] at hf ⊢
    have : writtenInExtChartAt I I' x f ((extChartAt I x) x) = (extChartAt I' (f x)) (f x) := by
      simp only [mfld_simps]
    rw [← this] at hg
    apply HasFDerivWithinAt.comp ((extChartAt I x) x) hg.2 hf.2 _
    intro y hy
    simp only [mfld_simps] at hy
    have : f (((chartAt H x).symm : H → M) (I.symm y)) ∈ u := hst hy.1.1
    simp only [hy, this, mfld_simps]
  apply A.congr_of_eventuallyEq (writtenInExtChartAt_comp hf.1)
  simp only [mfld_simps]
#align has_mfderiv_within_at.comp HasMFDerivWithinAt.comp

/-- The **chain rule for manifolds**. -/
theorem HasMFDerivAt.comp (hg : HasMFDerivAt I' I'' g (f x) g') (hf : HasMFDerivAt I I' f x f') :
    HasMFDerivAt I I'' (g ∘ f) x (g'.comp f') := by
  rw [← hasMFDerivWithinAt_univ] at *
  exact HasMFDerivWithinAt.comp x (hg.mono (subset_univ _)) hf subset_preimage_univ
#align has_mfderiv_at.comp HasMFDerivAt.comp

theorem HasMFDerivAt.comp_hasMFDerivWithinAt (hg : HasMFDerivAt I' I'' g (f x) g')
    (hf : HasMFDerivWithinAt I I' f s x f') :
    HasMFDerivWithinAt I I'' (g ∘ f) s x (g'.comp f') := by
  rw [← hasMFDerivWithinAt_univ] at *
  exact HasMFDerivWithinAt.comp x (hg.mono (subset_univ _)) hf subset_preimage_univ
#align has_mfderiv_at.comp_has_mfderiv_within_at HasMFDerivAt.comp_hasMFDerivWithinAt

theorem MDifferentiableWithinAt.comp (hg : MDifferentiableWithinAt I' I'' g u (f x))
    (hf : MDifferentiableWithinAt I I' f s x) (h : s ⊆ f ⁻¹' u) :
    MDifferentiableWithinAt I I'' (g ∘ f) s x := by
  rcases hf.2 with ⟨f', hf'⟩
  have F : HasMFDerivWithinAt I I' f s x f' := ⟨hf.1, hf'⟩
  rcases hg.2 with ⟨g', hg'⟩
  have G : HasMFDerivWithinAt I' I'' g u (f x) g' := ⟨hg.1, hg'⟩
  exact (HasMFDerivWithinAt.comp x G F h).mdifferentiableWithinAt
#align mdifferentiable_within_at.comp MDifferentiableWithinAt.comp

theorem MDifferentiableAt.comp (hg : MDifferentiableAt I' I'' g (f x))
    (hf : MDifferentiableAt I I' f x) : MDifferentiableAt I I'' (g ∘ f) x :=
  (hg.hasMFDerivAt.comp x hf.hasMFDerivAt).mdifferentiableAt
#align mdifferentiable_at.comp MDifferentiableAt.comp

theorem mfderivWithin_comp (hg : MDifferentiableWithinAt I' I'' g u (f x))
    (hf : MDifferentiableWithinAt I I' f s x) (h : s ⊆ f ⁻¹' u) (hxs : UniqueMDiffWithinAt I s x) :
    mfderivWithin I I'' (g ∘ f) s x =
      (mfderivWithin I' I'' g u (f x)).comp (mfderivWithin I I' f s x) := by
  apply HasMFDerivWithinAt.mfderivWithin _ hxs
  exact HasMFDerivWithinAt.comp x hg.hasMFDerivWithinAt hf.hasMFDerivWithinAt h
#align mfderiv_within_comp mfderivWithin_comp

theorem mfderiv_comp (hg : MDifferentiableAt I' I'' g (f x)) (hf : MDifferentiableAt I I' f x) :
    mfderiv I I'' (g ∘ f) x = (mfderiv I' I'' g (f x)).comp (mfderiv I I' f x) := by
  apply HasMFDerivAt.mfderiv
  exact HasMFDerivAt.comp x hg.hasMFDerivAt hf.hasMFDerivAt
#align mfderiv_comp mfderiv_comp

theorem mfderiv_comp_of_eq {x : M} {y : M'} (hg : MDifferentiableAt I' I'' g y)
    (hf : MDifferentiableAt I I' f x) (hy : f x = y) :
    mfderiv I I'' (g ∘ f) x = (mfderiv I' I'' g (f x)).comp (mfderiv I I' f x) := by
  subst hy; exact mfderiv_comp x hg hf
#align mfderiv_comp_of_eq mfderiv_comp_of_eq

theorem MDifferentiableOn.comp (hg : MDifferentiableOn I' I'' g u) (hf : MDifferentiableOn I I' f s)
    (st : s ⊆ f ⁻¹' u) : MDifferentiableOn I I'' (g ∘ f) s := fun x hx =>
  MDifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st
#align mdifferentiable_on.comp MDifferentiableOn.comp

theorem MDifferentiable.comp (hg : MDifferentiable I' I'' g) (hf : MDifferentiable I I' f) :
    MDifferentiable I I'' (g ∘ f) := fun x => MDifferentiableAt.comp x (hg (f x)) (hf x)
#align mdifferentiable.comp MDifferentiable.comp

theorem tangentMapWithin_comp_at (p : TangentBundle I M)
    (hg : MDifferentiableWithinAt I' I'' g u (f p.1)) (hf : MDifferentiableWithinAt I I' f s p.1)
    (h : s ⊆ f ⁻¹' u) (hps : UniqueMDiffWithinAt I s p.1) :
    tangentMapWithin I I'' (g ∘ f) s p =
      tangentMapWithin I' I'' g u (tangentMapWithin I I' f s p) := by
  simp only [tangentMapWithin, mfld_simps]
  rw [mfderivWithin_comp p.1 hg hf h hps]
  rfl
#align tangent_map_within_comp_at tangentMapWithin_comp_at

theorem tangentMap_comp_at (p : TangentBundle I M) (hg : MDifferentiableAt I' I'' g (f p.1))
    (hf : MDifferentiableAt I I' f p.1) :
    tangentMap I I'' (g ∘ f) p = tangentMap I' I'' g (tangentMap I I' f p) := by
  simp only [tangentMap, mfld_simps]
  rw [mfderiv_comp p.1 hg hf]
  rfl
#align tangent_map_comp_at tangentMap_comp_at

theorem tangentMap_comp (hg : MDifferentiable I' I'' g) (hf : MDifferentiable I I' f) :
    tangentMap I I'' (g ∘ f) = tangentMap I' I'' g ∘ tangentMap I I' f := by
  ext p : 1; exact tangentMap_comp_at _ (hg _) (hf _)
#align tangent_map_comp tangentMap_comp

end DerivativesProperties
