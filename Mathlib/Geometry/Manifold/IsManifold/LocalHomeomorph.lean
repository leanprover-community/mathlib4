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

* `IsLocalHomeomorph.isManifoldOfRightInverse`: `M'` is a smooth manifold.
* `f` is `C^n` as a map between maninfolds.
* `hf.localInverseAt` is `C^n` on its source.
* `f` is a local diffeomorphism.

## Tags

smooth manifold, local homeomorphism
-/

public noncomputable section

variable {M : Type*} [TopologicalSpace M]
  {H : Type*} [TopologicalSpace H] [ChartedSpace H M]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
  {M' : Type*} [TopologicalSpace M']
  {f : M → M'} (hf : IsLocalHomeomorph f)
  {g : M' → M} (hg : Function.RightInverse g f)

open scoped ContDiff Manifold Topology

-- TODO: find a proper name for `Foo`
variable (I n f) in
structure Foo : Prop where
  exists_contMDiffAt (p q : M) (hpq : f p = f q) :
    ∃ σ : M → M, σ p = q ∧ ContMDiffAt I I n σ p ∧ f ∘ σ =ᶠ[𝓝 p] f

/-- If `f` satisfies the condition, the transition map between two local inverses of `f`
is `C^n` on its source. -/
lemma IsLocalHomeomorph.contMDiffOn_localInverseAt_symm_trans
    (h : Foo I n f) (p q : M) :
    ContMDiffOn I I n ((hf.localInverseAt p).symm ≫ₕ hf.localInverseAt q)
      ((hf.localInverseAt p).symm ≫ₕ hf.localInverseAt q).source := by
  set τ := (hf.localInverseAt p).symm ≫ₕ hf.localInverseAt q
  have hτ {r : M} (hr : r ∈ τ.source) : f (τ r) = f r := by
    simp only [τ, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage,
      hf.localInverseAt_symm] at hr
    simpa [τ] using hf.apply_localInverseAt_of_mem hr.2
  intro r hr
  obtain ⟨σ, hσr, hσ, hfσ⟩ := h.exists_contMDiffAt r (τ r) (hτ hr).symm
  refine (hσ.congr_of_eventuallyEq ?_).contMDiffWithinAt
  have hT : (hf.localInverseAt q).target ∈ 𝓝 (σ r) :=
    (hf.localInverseAt q).open_target.mem_nhds (hσr ▸ (τ.map_source hr).1)
  filter_upwards [τ.open_source.mem_nhds hr, hσ.continuousAt.preimage_mem_nhds hT, hfσ]
    with r' hr' hσr' hfσr'
  exact hf.injOn_localInverseAt_target (τ.map_source hr').1 hσr' ((hτ hr').trans hfσr'.symm)

lemma IsLocalHomeomorph.isManifoldOfRightInverse [IsManifold I n M] (h : Foo I n f) :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    IsManifold I n M' := by
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  refine { compatible := ?_ } -- Why does `constructor` fail here?
  rintro - - ⟨x, rfl⟩ ⟨y, rfl⟩
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, (chartAt H (g x)).symm.trans_assoc,
    ← (hf.localInverseAt (g x)).symm.trans_assoc]
  refine symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn
    (IsManifold.chart_mem_maximalAtlas _) (IsManifold.chart_mem_maximalAtlas _)
    (contMDiffOn_localInverseAt_symm_trans hf h _ _)
    (contMDiffOn_localInverseAt_symm_trans hf h _ _)

-- TODO: this and the lemma below use a very similar argument. can this be simplified?
lemma IsLocalHomeomorph.contMDiffAt_localInverseAt_rightInverse (y : M') :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    ContMDiffAt I I n (hf.localInverseAt (g y)) y := by
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  rw [contMDiffAt_iff]
  constructor
  · apply OpenPartialHomeomorph.continuousAt
    simpa [hg y] using hf.apply_self_mem_localInverseAt_source (x := g y)
  · rw [show hf.localInverseAt (g y) y = g y by
      simpa [hg y] using (hf.localInverseAt_apply_self (x := g y))]
    have hc : chartAt H y = (hf.localInverseAt (g y)).trans (chartAt H (g y)) := rfl
    rw [extChartAt_coe, extChartAt_coe_symm, hc, OpenPartialHomeomorph.coe_trans_symm]
    refine contDiffWithinAt_id.congr_of_eventuallyEq_of_mem ?_
      (Set.mem_range_self (((chartAt H y).symm.restr I.source).symm y))
    filter_upwards [extChartAt_target_mem_nhdsWithin y] with x hx
    simp only [Function.comp_apply, id]
    rw [extChartAt_target, hc, OpenPartialHomeomorph.trans_target, Set.mem_inter_iff,
      Set.mem_preimage] at hx
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    rw [(hf.localInverseAt (g y)).right_inv h2, (chartAt H (g y)).right_inv h1, I.right_inv h3]

lemma IsLocalHomeomorph.contMDiffAt_localInverseAt_symm_rightInverse (y : M') :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    ContMDiffAt I I n (hf.localInverseAt (g y)).symm (g y) := by
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  rw [contMDiffAt_iff]
  constructor
  · apply OpenPartialHomeomorph.continuousAt
    simp
  · rw [show (hf.localInverseAt (g y)).symm (g y) = y by simpa using hg y]
    refine contDiffWithinAt_id.congr_of_eventuallyEq_of_mem ?_ (Set.mem_range_self _)
    have hy : extChartAt I (g y) (g y) ∈ (extChartAt I y).target := by
      have := mem_extChartAt_target (I := I) y
      change extChartAt I (g y) (hf.localInverseAt (g y) y) ∈ _ at this
      rwa [show hf.localInverseAt (g y) y = g y by
        simpa [hg y] using hf.localInverseAt_apply_self (x := g y)] at this
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hy] with x hx
    exact (extChartAt I y).right_inv hx

lemma IsLocalHomeomorph.isContMDiffOfRightInverse
    (h : Foo I n f) :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    ContMDiff I I n f := by
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  intro p
  obtain ⟨σ, hσ1, hσ2, hσ3⟩ := h.exists_contMDiffAt p (g (f p)) (hg (f p)).symm
  have : f =ᶠ[𝓝 p] (hf.localInverseAt (g (f p))).symm ∘ σ := by
    apply Filter.EventuallyEq.trans hσ3.symm
    have : f =ᶠ[𝓝 (g (f p))] (hf.localInverseAt (g (f p))).symm := by simp
    exact this.comp_tendsto (hσ1.symm ▸ hσ2.continuousAt.tendsto)
  refine ContMDiffAt.congr_of_eventuallyEq ?_ this
  refine ContMDiffAt.comp p ?_ hσ2
  rw [hσ1]
  exact contMDiffAt_localInverseAt_symm_rightInverse hf hg (f p)

variable {H' : Type*} [TopologicalSpace H']
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {J : ModelWithCorners 𝕜 E' H'}

/-- Given `φ : M' → N` and `y : M'`, if `φ ∘ f` is `C^n` at `g y` then `φ` is `C^n` at `y`. -/
lemma IsLocalHomeomorph.contMDiffAt_of_contMDiffAt_comp {φ : M' → N} {y : M'}
    (hφ : ContMDiffAt I J n (φ ∘ f) (g y)) :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    ContMDiffAt I J n φ y := by
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  have : φ =ᶠ[𝓝 y] (φ ∘ f) ∘ hf.localInverseAt (g y) := by
    have hT : (hf.localInverseAt (g y)).source ∈ 𝓝 y := by
      refine (hf.localInverseAt (g y)).open_source.mem_nhds ?_
      simpa [hg y] using hf.apply_self_mem_localInverseAt_source (x := g y)
    filter_upwards [hT] with x hx
    simp [hf.apply_localInverseAt_of_mem hx]
  refine ContMDiffAt.congr_of_eventuallyEq ?_ this
  refine ContMDiffAt.comp y ?_ (contMDiffAt_localInverseAt_rightInverse hf hg y)
  rwa [show hf.localInverseAt (g y) y = g y by
    simpa [hg y] using hf.localInverseAt_apply_self (x := g y)]

/-- Given `φ : M' → N`, if `φ ∘ f` is `C^n` then so is `φ`. -/
lemma IsLocalHomeomorph.contMDiff_of_contMDiff_comp
    {φ : M' → N} (hφ : ContMDiff I J n (φ ∘ f)) :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    ContMDiff I J n φ :=
  fun y ↦ hf.contMDiffAt_of_contMDiffAt_comp hg (hφ (g y))

/-- If `F : M → N` is `C^n` and invariant under `f`, the map `F ∘ g : M' → N` is also `C^n`. -/
lemma IsLocalHomeomorph.contMDiff_comp_rightInverse_of_contMDiff {F : M → N}
    (hF : ∀ p q, f p = f q → F p = F q) (hF' : CMDiff n F) :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    ContMDiff I J n (F ∘ g) :=
  IsLocalHomeomorph.contMDiff_of_contMDiff_comp hf hg <| hF'.congr (fun y ↦ hF _ _ (hg (f y)))

/-- For any point `x` in `M`, if `f` satisfies the condition then its local inverse at `x`
is `C^n` on its source -/
lemma IsLocalHomeomorph.contMDiffOn_localInverseAt_rightInverse (x : M)
    (h : Foo I n f) :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    ContMDiffOn I I n ((hf.localInverseAt x)) (hf.localInverseAt x).source := by
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  intro y hy
  refine (hf.contMDiffAt_of_contMDiffAt_comp hg ?_).contMDiffWithinAt
  simpa using (contMDiffOn_localInverseAt_symm_trans hf h (g y) x).contMDiffAt
    <| (OpenPartialHomeomorph.open_source _).mem_nhds (by simpa [hg y] using hy)

/-- If `f` satisfies the condition, then `φ : M' → N` is `C^n` if and only if `φ ∘ f` is. -/
lemma IsLocalHomeomorph.contMDiff_iff_contMDiff_comp
    (h : Foo I n f) {φ : M' → N} :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    ContMDiff I J n φ ↔ ContMDiff I J n (φ ∘ f) :=
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  ⟨fun hφ ↦ hφ.comp (hf.isContMDiffOfRightInverse hg h), hf.contMDiff_of_contMDiff_comp hg⟩

end
