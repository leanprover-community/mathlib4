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
  --[T2Space M] [LocallyCompactSpace M]
  {H : Type*} [TopologicalSpace H] [ChartedSpace H M]

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}

variable {M' : Type*} [TopologicalSpace M']

open scoped ContDiff Manifold Topology

variable {f : M → M'} (hf : IsLocalHomeomorph f)
  {g : M' → M} (hg : Function.RightInverse g f)

lemma foo (h : ∀ p q, f p = f q → ∃ σ : M → M, σ p = q ∧
      ContMDiffAt I I n σ p ∧ f ∘ σ =ᶠ[𝓝 p] f) (p q : M) :
    ContMDiffOn I I n ((hf.localInverseAt p).symm ≫ₕ hf.localInverseAt q)
      ((hf.localInverseAt p).symm ≫ₕ hf.localInverseAt q).source := by
  set τ := (hf.localInverseAt p).symm ≫ₕ hf.localInverseAt q
  have hτ {r : M} (hr : r ∈ τ.source) : f (τ r) = f r := by
    simp only [τ, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage,
      hf.localInverseAt_symm] at hr
    simpa [τ] using hf.apply_localInverseAt_of_mem hr.2
  intro r hr
  obtain ⟨σ, hσr, hσ, hfσ⟩ := h r (τ r) (hτ hr).symm
  refine (hσ.congr_of_eventuallyEq ?_).contMDiffWithinAt
  have hT : (hf.localInverseAt q).target ∈ 𝓝 (σ r) :=
    (hf.localInverseAt q).open_target.mem_nhds (hσr ▸ (τ.map_source hr).1)
  filter_upwards [τ.open_source.mem_nhds hr, hσ.continuousAt.preimage_mem_nhds hT, hfσ]
    with r' hr' hσr' hfσr'
  exact hf.injOn_localInverseAt_target (τ.map_source hr').1 hσr' ((hτ hr').trans hfσr'.symm)

lemma IsLocalHomeomorph.contMDiffAt_localInverseAt_rightInverse (y : M') :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    ContMDiffAt I I n (hf.localInverseAt (g y)) y := by
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  rw [contMDiffAt_iff]
  constructor
  · apply OpenPartialHomeomorph.continuousAt
    simpa [hg y] using hf.apply_self_mem_localInverseAt_source (x:= g y)
  · rw [show hf.localInverseAt (g y) y = g y by
      simpa [hg y] using (hf.localInverseAt_apply_self (x:=g y))]
    have hc : chartAt H y = (hf.localInverseAt (g y)).trans (chartAt H (g y)) := rfl
    rw [extChartAt_coe, extChartAt_coe_symm, hc]
    simp only [OpenPartialHomeomorph.coe_trans_symm]
    refine contDiffWithinAt_id.congr_of_eventuallyEq_of_mem ?_
      (Set.mem_range_self (((chartAt H y).symm.restr I.source).symm y))
    filter_upwards [extChartAt_target_mem_nhdsWithin y] with x hx
    simp only [Function.comp_apply, id]
    rw [extChartAt_target, hc, OpenPartialHomeomorph.trans_target] at hx
    rw [Set.mem_inter_iff, Set.mem_preimage] at hx
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    rw [(hf.localInverseAt (g y)).right_inv h2, (chartAt H (g y)).right_inv h1, I.right_inv h3]

variable {H' : Type*} [TopologicalSpace H']
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {J : ModelWithCorners 𝕜 E' H'}

lemma IsLocalHomeomorph.contMDiff_of_contMDiff_comp
    {φ : M' → N} (hφ : ContMDiff I J n (φ ∘ f)) :
    let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    ContMDiff I J n φ := by
  intro _ x'
  have : φ =ᶠ[𝓝 x'] ((φ ∘ f) ∘ (hf.localInverseAt (g x'))) := by
    have hT : (hf.localInverseAt (g x')).source ∈ 𝓝 x' := by
      refine (hf.localInverseAt (g x')).open_source.mem_nhds ?_
      simpa [hg x'] using hf.apply_self_mem_localInverseAt_source (x:= g x')
    filter_upwards [hT] with x hx
    simp [hf.apply_localInverseAt_of_mem hx]
  apply ContMDiffAt.congr_of_eventuallyEq (h₁ := this)
  apply ContMDiffAt.comp (I' := I) x'
  · exact hφ.contMDiffAt
  · exact IsLocalHomeomorph.contMDiffAt_localInverseAt_rightInverse hf hg x'

-- maybe this could be just dropped
/-- Suppose `F : M → N` is `C^n` and invariant under `f`,
the induced map `F ∘ g : M' → N` is also `C^n`. -/
lemma IsLocalHomeomorph.contMDiff_comp_rightInverse_of_contMDiff
    {F : M → N} (hF : ∀ p q, f p = f q → F p = F q)
    (hF' : CMDiff n F) :
    let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    ContMDiff I J n (F ∘ g) := by
  apply IsLocalHomeomorph.contMDiff_of_contMDiff_comp hf hg
  exact hF'.congr (fun y ↦ hF _ _ (hg (f y)))

variable [IsManifold I n M]

lemma IsLocalHomeomorph.isManifoldOfRightInverse
    -- TODO Is `h` below the most useful hypothesis?
    (h : ∀ p q, f p = f q → ∃ σ : M → M, σ p = q ∧ ContMDiffAt I I n σ p ∧ f ∘ σ =ᶠ[𝓝 p] f) :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    IsManifold I n M' := by
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  refine { compatible := ?_ } -- Why does `constructor` fail here?
  rintro - - ⟨x, rfl⟩ ⟨y, rfl⟩
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, (chartAt H (g x)).symm.trans_assoc,
    ← (hf.localInverseAt (g x)).symm.trans_assoc]
  refine symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn
    (IsManifold.chart_mem_maximalAtlas _) (IsManifold.chart_mem_maximalAtlas _) (foo hf h _ _) ?_
  simpa only [← OpenPartialHomeomorph.symm_source,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm] using
    foo hf h (g y) (g x)

lemma IsLocalHomeomorph.isContMDiffOfRightInverse
    (h : ∀ p q, f p = f q → ∃ σ : M → M, σ p = q ∧ ContMDiffAt I I n σ p ∧ f ∘ σ =ᶠ[𝓝 p] f)
    :
    let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    ContMDiff I I n f := by

  sorry

lemma IsLocalHomeomorph.contMDiffOn_localInverseAt_rightInverse (x : M)
    (h : ∀ p q, f p = f q → ∃ σ : M → M, σ p = q ∧ ContMDiffAt I I n σ p ∧ f ∘ σ =ᶠ[𝓝 p] f) :
    let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    ContMDiffOn I I n (↑(hf.localInverseAt x)) (hf.localInverseAt x).source := by
  intro y
  have aux := foo hf h

  sorry

/-- Suppose `F : M → N` is invariant under `f`
and the map `F ∘ g : M' → N` is `C^n`, then so is `F`. -/
lemma IsLocalHomeomorph.contMDiff_of_contMDiff_comp_rightInverse
    (h : ∀ p q, f p = f q → ∃ σ : M → M, σ p = q ∧ ContMDiffAt I I n σ p ∧ f ∘ σ =ᶠ[𝓝 p] f)
    {F : M → N} (hF : ∀ p q, f p = f q → F p = F q)
    (hFg : letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg;
      ContMDiff I J n (F ∘ g)) :
    ContMDiff I J n F := by
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  apply (hFg.comp (IsLocalHomeomorph.isContMDiffOfRightInverse hf hg h)).congr
  exact fun y ↦ hF _ _ (hg (f y)).symm

/-- Suppose `f : M → N` is invariant under `f`. Then `f` is `C^n` if and only if
the map `F ∘ g : M' → N` is. -/
lemma IsLocalHomeomorph.contMDiff_comp_rightInverse_iff_contMDiff
    (h : ∀ p q, f p = f q → ∃ σ : M → M, σ p = q ∧ ContMDiffAt I I n σ p ∧ f ∘ σ =ᶠ[𝓝 p] f)
    {F : M → N} (hF : ∀ p q, f p = f q → F p = F q) :
    let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    ContMDiff I J n (F ∘ g) ↔ CMDiff n F :=
  ⟨fun h' ↦ IsLocalHomeomorph.contMDiff_of_contMDiff_comp_rightInverse hf hg h hF h',
    fun h' ↦ IsLocalHomeomorph.contMDiff_comp_rightInverse_of_contMDiff hf hg hF h'⟩

end
