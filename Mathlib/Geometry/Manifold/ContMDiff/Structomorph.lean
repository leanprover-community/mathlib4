/-
Copyright (c) 2026 Ryan Shin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Shin
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# `C^n` structomorphisms are `C^n` diffeomorphisms, and conversely

For manifolds `M`, `M'` modelled on the same model with corners `I`, we relate
the two notions of isomorphism available in Mathlib: `Structomorph` for the
groupoid `contDiffGroupoid n I` (a homeomorphism whose chart transports lie in
the groupoid) and `Diffeomorph` (`M ≃ₘ^n⟮I, I⟯ M'`, a `C^n` map with `C^n`
inverse). They coincide:

* `Structomorph.toDiffeomorph` : a structomorphism for the `C^n` groupoid is a
  `C^n` diffeomorphism. At each point, the chart-composed structomorphism is
  definitionally the witness for
  `StructureGroupoid.IsLocalStructomorphWithinAt`, and
  `isLocalStructomorphOn_contDiffGroupoid_iff` converts the resulting lift
  property to `ContMDiffOn`, in both directions via `Structomorph.symm`.
* `Diffeomorph.toStructomorph` : a `C^n` diffeomorphism is a structomorphism.
  `ContMDiff` in both directions gives the lift property by the same `iff`;
  `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart`
  re-expresses it in an arbitrary pair of atlas charts; and the resulting
  local groupoid elements glue by `StructureGroupoid.locality`, using closure
  under restriction and `StructureGroupoid.mem_of_eqOnSource`.
-/

@[expose] public section

open Set ChartedSpace

open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  {n : ℕ∞ω}

/-- A structomorphism for the `C^n` groupoid satisfies the
local-structomorphism lift property on its whole source: at each point, the
witnessing groupoid element is the chart-composed structomorphism itself. -/
theorem Structomorph.liftPropOn (h : Structomorph (contDiffGroupoid n I) M M') :
    LiftPropOn (contDiffGroupoid n I).IsLocalStructomorphWithinAt
      h.toHomeomorph.toOpenPartialHomeomorph
      h.toHomeomorph.toOpenPartialHomeomorph.source := by
  intro x _
  refine ⟨h.continuous.continuousWithinAt, fun _ => ?_⟩
  refine ⟨(chartAt H x).symm ≫ₕ h.toHomeomorph.toOpenPartialHomeomorph ≫ₕ
      chartAt H (h.toHomeomorph x),
    h.mem_groupoid _ _ (chart_mem_atlas _ _) (chart_mem_atlas _ _), ?_, ?_⟩
  · exact fun y _ => rfl
  · simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage]
    refine ⟨?_, ?_, ?_⟩
    · exact (chartAt H x).map_source (mem_chart_source H x)
    · simp [Homeomorph.toOpenPartialHomeomorph_source,
        (chartAt H x).left_inv (mem_chart_source H x)]
    · simp [Homeomorph.toOpenPartialHomeomorph_apply,
        (chartAt H x).left_inv (mem_chart_source H x), mem_chart_source]

variable [IsManifold I n M] [IsManifold I n M']

/-- A structomorphism for the `C^n` groupoid is `C^n`. -/
theorem Structomorph.contMDiff (h : Structomorph (contDiffGroupoid n I) M M') :
    ContMDiff I I n h.toHomeomorph := by
  have h2 := (isLocalStructomorphOn_contDiffGroupoid_iff
    h.toHomeomorph.toOpenPartialHomeomorph).mp h.liftPropOn
  have hs : h.toHomeomorph.toOpenPartialHomeomorph.source = univ :=
    Homeomorph.toOpenPartialHomeomorph_source _
  rw [← contMDiffOn_univ, ← hs]
  exact h2.1

/-- A structomorphism for the `C^n` groupoid is a `C^n` diffeomorphism. -/
def Structomorph.toDiffeomorph (h : Structomorph (contDiffGroupoid n I) M M') :
    M ≃ₘ^n⟮I, I⟯ M' where
  toEquiv := h.toHomeomorph.toEquiv
  contMDiff_toFun := h.contMDiff
  contMDiff_invFun := h.symm.contMDiff

/-- A `C^n` diffeomorphism is a structomorphism for the `C^n` groupoid. -/
def Diffeomorph.toStructomorph (φ : M ≃ₘ^n⟮I, I⟯ M') :
    Structomorph (contDiffGroupoid n I) M M' where
  toHomeomorph := φ.toHomeomorph
  mem_groupoid := by
    intro c c' hc hc'
    set fm := φ.toHomeomorph.toOpenPartialHomeomorph with hfm
    have hsrc : fm.source = univ := Homeomorph.toOpenPartialHomeomorph_source _
    have htgt : fm.target = univ := Homeomorph.toOpenPartialHomeomorph_target _
    have hLP : LiftPropOn (contDiffGroupoid n I).IsLocalStructomorphWithinAt
        fm fm.source :=
      (isLocalStructomorphOn_contDiffGroupoid_iff fm).mpr
        ⟨hsrc ▸ φ.contMDiff.contMDiffOn, htgt ▸ φ.symm.contMDiff.contMDiffOn⟩
    apply StructureGroupoid.locality
    intro z hz
    have hz' : z ∈ c.target ∧ φ.toHomeomorph (c.symm z) ∈ c'.source := by
      simpa [hfm, OpenPartialHomeomorph.trans_source, hsrc] using hz
    set x := c.symm z with hxdef
    have hxc : x ∈ c.source := c.map_target hz'.1
    have hcx : c x = z := c.right_inv hz'.1
    have hLPx := hLP x (by simp [hsrc])
    rw [hsrc] at hLPx
    have h2 := ((StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp
        (contDiffGroupoid n I)).liftPropWithinAt_indep_chart
        ((contDiffGroupoid n I).subset_maximalAtlas hc) hxc
        ((contDiffGroupoid n I).subset_maximalAtlas hc') hz'.2).mp hLPx
    obtain ⟨e₀, he₀G, he₀eq, he₀z⟩ := h2.2 (by simp)
    rw [hcx] at he₀z
    set g := c.symm ≫ₕ fm ≫ₕ c' with hgdef
    have hgopen : IsOpen (e₀.source ∩ g.source) :=
      e₀.open_source.inter g.open_source
    refine ⟨e₀.source ∩ g.source, hgopen, ⟨he₀z, hz⟩, ?_⟩
    apply (contDiffGroupoid n I).mem_of_eqOnSource
      (closedUnderRestriction' he₀G hgopen)
    constructor
    · simp only [OpenPartialHomeomorph.restr_source, hgopen.interior_eq]
      mfld_set_tac
    · intro y hy
      have hy' : y ∈ univ ∩ e₀.source := by
        simp only [OpenPartialHomeomorph.restr_source, hgopen.interior_eq] at hy
        exact ⟨trivial, hy.2.1⟩
      exact he₀eq hy'

theorem Structomorph.toHomeomorph_injective {G : StructureGroupoid H} :
    Function.Injective (Structomorph.toHomeomorph : Structomorph G M M' → M ≃ₜ M')
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- `C^n` structomorphisms and `C^n` diffeomorphisms coincide, as types. -/
def structomorphEquivDiffeomorph :
    Structomorph (contDiffGroupoid n I) M M' ≃ (M ≃ₘ^n⟮I, I⟯ M') where
  toFun := Structomorph.toDiffeomorph
  invFun := Diffeomorph.toStructomorph
  left_inv _ := Structomorph.toHomeomorph_injective (Homeomorph.toEquiv_injective rfl)
  right_inv _ := Diffeomorph.toEquiv_injective rfl
