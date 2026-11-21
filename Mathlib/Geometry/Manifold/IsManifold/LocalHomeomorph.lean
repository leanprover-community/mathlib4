/-
Copyright (c) 2025 Pepa Montero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pepa Montero
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Topology.Covering.Quotient


/-!
# Manifold structure induced by a local homeomorphism

Let `M` be a `C^n` manifold and let `f : M → M'` be a local homeomorphism with a right inverse.

This file gives a condition under which this makes `M'` a `C^n` manifold.

## Main results

TODO: rewrite this

If this condition holds:

* `IsLocalHomeomorph.isManifold_of_rightInverse`: `M'` is a smooth manifold.
* `f` is `C^n` as a map between maninfolds.
* `hf.localInverseAt` is `C^n` on its source.
* `f` is a local diffeomorphism.

## Tags

smooth manifold, local homeomorphism
-/

public noncomputable section

open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M]
  {H : Type*} [TopologicalSpace H] [ChartedSpace H M]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {M' : Type*} [TopologicalSpace M']
  {f : M → M'} (hf : IsLocalHomeomorph f)
  {g : M' → M} (hg : Function.RightInverse g f)

-- TODO: find a proper name for `Foo`
variable (I n f) in
structure Foo : Prop where
  exists_contMDiffAt {x y : M} (hxy : f x = f y) :
    ∃ σ : M → M, σ x = y ∧ CMDiffAt n σ x ∧ f ∘ σ =ᶠ[𝓝 x] f

/-- If `f` satisfies the condition, the transition map between two local inverses of `f`
is `C^n` on its source. -/
lemma IsLocalHomeomorph.contMDiffOn_localInverseAt_symm_trans
    (h : Foo I n f) (x y : M) :
    CMDiff[((hf.localInverseAt x).symm ≫ₕ hf.localInverseAt y).source] n
      ((hf.localInverseAt x).symm ≫ₕ hf.localInverseAt y) := by
  set τ := (hf.localInverseAt x).symm ≫ₕ hf.localInverseAt y
  have hτ {z : M} (hz : z ∈ τ.source) : f (τ z) = f z := by
    simp only [τ, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage,
      hf.localInverseAt_symm] at hz
    simpa [τ] using hf.apply_localInverseAt_of_mem hz.2
  intro z hz
  obtain ⟨σ, hσz, hσ, hfσ⟩ := h.exists_contMDiffAt (hτ hz).symm
  refine (hσ.congr_of_eventuallyEq ?_).contMDiffWithinAt
  have ht : (hf.localInverseAt y).target ∈ 𝓝 (σ z) :=
    (hf.localInverseAt y).open_target.mem_nhds (hσz ▸ (τ.map_source hz).1)
  filter_upwards [τ.open_source.mem_nhds hz, hσ.continuousAt.preimage_mem_nhds ht, hfσ]
    with z' hz' hσz' hfσz'
  exact hf.injOn_localInverseAt_target (τ.map_source hz').1 hσz' ((hτ hz').trans hfσz'.symm)

theorem IsLocalHomeomorph.isManifold_of_rightInverse [IsManifold I n M] (h : Foo I n f) :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    IsManifold I n M' := by
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  refine { compatible := ?_ }
  rintro - - ⟨y, rfl⟩ ⟨y', rfl⟩
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, (chartAt H (g y)).symm.trans_assoc,
    ← (hf.localInverseAt (g y)).symm.trans_assoc]
  exact symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn
    (IsManifold.chart_mem_maximalAtlas _) (IsManifold.chart_mem_maximalAtlas _)
    (hf.contMDiffOn_localInverseAt_symm_trans h _ _)
    (hf.contMDiffOn_localInverseAt_symm_trans h _ _)

-- TODO: this and the lemma below use a very similar argument. can this be simplified?
lemma IsLocalHomeomorph.contMDiffAt_localInverseAt_rightInverse (y : M') :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    CMDiffAt n (hf.localInverseAt (g y)) y := by
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  rw [contMDiffAt_iff]
  constructor
  · apply OpenPartialHomeomorph.continuousAt
    simpa [hg y] using hf.apply_self_mem_localInverseAt_source (x := g y)
  · rw [show hf.localInverseAt (g y) y = g y by
      simpa [hg y] using hf.localInverseAt_apply_self (x := g y)]
    have hc : chartAt H y = hf.localInverseAt (g y) ≫ₕ chartAt H (g y) := rfl
    rw [extChartAt_coe, extChartAt_coe_symm, hc, OpenPartialHomeomorph.coe_trans_symm]
    refine contDiffWithinAt_id.congr_of_eventuallyEq_of_mem ?_ (Set.mem_range_self _)
    filter_upwards [extChartAt_target_mem_nhdsWithin y] with z hz
    exact (extChartAt I y).right_inv hz

lemma IsLocalHomeomorph.contMDiffAt_localInverseAt_symm_rightInverse (y : M') :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    CMDiffAt n (hf.localInverseAt (g y)).symm (g y) := by
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  rw [contMDiffAt_iff]
  constructor
  · exact OpenPartialHomeomorph.continuousAt _ (by simp)
  · rw [show (hf.localInverseAt (g y)).symm (g y) = y by simpa using hg y]
    refine contDiffWithinAt_id.congr_of_eventuallyEq_of_mem ?_ (Set.mem_range_self _)
    have hgy : extChartAt I (g y) (g y) ∈ (extChartAt I y).target := by
      have := mem_extChartAt_target (I := I) y
      change extChartAt I (g y) (hf.localInverseAt (g y) y) ∈ _ at this
      rwa [show hf.localInverseAt (g y) y = g y by
        simpa [hg y] using hf.localInverseAt_apply_self (x := g y)] at this
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hgy] with z hz
    exact (extChartAt I y).right_inv hz

theorem IsLocalHomeomorph.contMDiff_of_rightInverse
    (h : Foo I n f) :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    CMDiff n f := by
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  intro x
  obtain ⟨σ, hσx, hσ, hfσ⟩ := h.exists_contMDiffAt (hg (f x)).symm
  have : f =ᶠ[𝓝 x] (hf.localInverseAt (g (f x))).symm ∘ σ := by
    refine hfσ.symm.trans ?_
    have : f =ᶠ[𝓝 (g (f x))] (hf.localInverseAt (g (f x))).symm := by simp
    exact this.comp_tendsto (hσx.symm ▸ hσ.continuousAt.tendsto)
  refine ContMDiffAt.congr_of_eventuallyEq ?_ this
  refine ContMDiffAt.comp x ?_ hσ
  rw [hσx]
  exact hf.contMDiffAt_localInverseAt_symm_rightInverse hg (f x)

variable {H' : Type*} [TopologicalSpace H']
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {J : ModelWithCorners 𝕜 E' H'}

/-- Given `φ : M' → N` and `y : M'`, if `φ ∘ f` is `C^n` at `g y` then `φ` is `C^n` at `y`. -/
lemma IsLocalHomeomorph.contMDiffAt_of_contMDiffAt_comp {φ : M' → N} {y : M'}
    (hφ : CMDiffAt n (φ ∘ f) (g y)) :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    CMDiffAt n φ y := by
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  have : φ =ᶠ[𝓝 y] (φ ∘ f) ∘ hf.localInverseAt (g y) := by
    have hs : (hf.localInverseAt (g y)).source ∈ 𝓝 y := by
      refine (hf.localInverseAt (g y)).open_source.mem_nhds ?_
      simpa [hg y] using hf.apply_self_mem_localInverseAt_source (x := g y)
    filter_upwards [hs] with y' hy'
    simp [hf.apply_localInverseAt_of_mem hy']
  refine ContMDiffAt.congr_of_eventuallyEq ?_ this
  refine ContMDiffAt.comp y ?_ (hf.contMDiffAt_localInverseAt_rightInverse hg y)
  rwa [show hf.localInverseAt (g y) y = g y by
    simpa [hg y] using hf.localInverseAt_apply_self (x := g y)]

/-- Given `φ : M' → N`, if `φ ∘ f` is `C^n` then so is `φ`. -/
lemma IsLocalHomeomorph.contMDiff_of_contMDiff_comp
    {φ : M' → N} (hφ : CMDiff n (φ ∘ f)) :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    CMDiff n φ :=
  fun y ↦ hf.contMDiffAt_of_contMDiffAt_comp hg (hφ (g y))

/-- If `F : M → N` is `C^n` and factors through `f`, the map `F ∘ g : M' → N` is also `C^n`. -/
lemma IsLocalHomeomorph.contMDiff_comp_rightInverse_of_contMDiff {F : M → N}
    (hFf : F.FactorsThrough f) (hF : CMDiff n F) :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    CMDiff n (F ∘ g) :=
  hf.contMDiff_of_contMDiff_comp hg <| hF.congr fun x ↦ hFf (hg (f x))

/-- For any point `x` in `M`, if `f` satisfies the condition then its local inverse at `x`
is `C^n` on its source -/
theorem IsLocalHomeomorph.contMDiffOn_localInverseAt_rightInverse (h : Foo I n f) (x : M) :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    CMDiff[(hf.localInverseAt x).source] n (hf.localInverseAt x) := by
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  intro y hy
  refine (hf.contMDiffAt_of_contMDiffAt_comp hg ?_).contMDiffWithinAt
  simpa using (hf.contMDiffOn_localInverseAt_symm_trans h (g y) x).contMDiffAt <|
    (OpenPartialHomeomorph.open_source _).mem_nhds (by simpa [hg y] using hy)

/-- If `f` satisfies the condition, then `φ : M' → N` is `C^n` if and only if `φ ∘ f` is. -/
theorem IsLocalHomeomorph.contMDiff_iff_contMDiff_comp
    (h : Foo I n f) {φ : M' → N} :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    CMDiff n φ ↔ CMDiff n (φ ∘ f) :=
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  ⟨fun hφ ↦ hφ.comp (hf.contMDiff_of_rightInverse hg h), hf.contMDiff_of_contMDiff_comp hg⟩

end
