/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
## Smoothness of charts and local structomorphisms

We show that the model with corners, charts, extended charts and their inverses are smooth,
and that local structomorphisms are smooth with smooth inverses.
-/

open Set ChartedSpace SmoothManifoldWithCorners
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]
  -- declare a smooth manifold `M'` over the pair `(E', H')`.
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [SmoothManifoldWithCorners I' M']
  -- declare functions, sets, points and smoothness indices
  {e : PartialHomeomorph M H} {x : M} {m n : ℕ∞}

/-! ### Atlas members are smooth -/

section Atlas

theorem contMDiff_model : ContMDiff I 𝓘(𝕜, E) n I := by
  intro x
  refine' (contMDiffAt_iff _ _).mpr ⟨I.continuousAt, _⟩
  simp only [mfld_simps]
  refine' contDiffWithinAt_id.congr_of_eventuallyEq _ _
  · exact Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x₂ => I.right_inv
  simp_rw [Function.comp_apply, I.left_inv, Function.id_def]
#align cont_mdiff_model contMDiff_model

theorem contMDiffOn_model_symm : ContMDiffOn 𝓘(𝕜, E) I n I.symm (range I) := by
  rw [contMDiffOn_iff]
  refine' ⟨I.continuousOn_symm, fun x y => _⟩
  simp only [mfld_simps]
  exact contDiffOn_id.congr fun x' => I.right_inv
#align cont_mdiff_on_model_symm contMDiffOn_model_symm

/-- An atlas member is `C^n` for any `n`. -/
theorem contMDiffOn_of_mem_maximalAtlas (h : e ∈ maximalAtlas I M) : ContMDiffOn I I n e e.source :=
  ContMDiffOn.of_le
    ((contDiffWithinAt_localInvariantProp I I ∞).liftPropOn_of_mem_maximalAtlas
      (contDiffWithinAtProp_id I) h)
    le_top
#align cont_mdiff_on_of_mem_maximal_atlas contMDiffOn_of_mem_maximalAtlas

/-- The inverse of an atlas member is `C^n` for any `n`. -/
theorem contMDiffOn_symm_of_mem_maximalAtlas (h : e ∈ maximalAtlas I M) :
    ContMDiffOn I I n e.symm e.target :=
  ContMDiffOn.of_le
    ((contDiffWithinAt_localInvariantProp I I ∞).liftPropOn_symm_of_mem_maximalAtlas
      (contDiffWithinAtProp_id I) h)
    le_top
#align cont_mdiff_on_symm_of_mem_maximal_atlas contMDiffOn_symm_of_mem_maximalAtlas

theorem contMDiffAt_of_mem_maximalAtlas (h : e ∈ maximalAtlas I M) (hx : x ∈ e.source) :
    ContMDiffAt I I n e x :=
  (contMDiffOn_of_mem_maximalAtlas h).contMDiffAt <| e.open_source.mem_nhds hx
#align cont_mdiff_at_of_mem_maximal_atlas contMDiffAt_of_mem_maximalAtlas

theorem contMDiffAt_symm_of_mem_maximalAtlas {x : H} (h : e ∈ maximalAtlas I M)
    (hx : x ∈ e.target) : ContMDiffAt I I n e.symm x :=
  (contMDiffOn_symm_of_mem_maximalAtlas h).contMDiffAt <| e.open_target.mem_nhds hx
#align cont_mdiff_at_symm_of_mem_maximal_atlas contMDiffAt_symm_of_mem_maximalAtlas

theorem contMDiffOn_chart : ContMDiffOn I I n (chartAt H x) (chartAt H x).source :=
  contMDiffOn_of_mem_maximalAtlas <| chart_mem_maximalAtlas I x
#align cont_mdiff_on_chart contMDiffOn_chart

theorem contMDiffOn_chart_symm : ContMDiffOn I I n (chartAt H x).symm (chartAt H x).target :=
  contMDiffOn_symm_of_mem_maximalAtlas <| chart_mem_maximalAtlas I x
#align cont_mdiff_on_chart_symm contMDiffOn_chart_symm

theorem contMDiffAt_extend {x : M} (he : e ∈ maximalAtlas I M) (hx : x ∈ e.source) :
    ContMDiffAt I 𝓘(𝕜, E) n (e.extend I) x :=
  (contMDiff_model _).comp x <| contMDiffAt_of_mem_maximalAtlas he hx
#align cont_mdiff_at_extend contMDiffAt_extend

theorem contMDiffOn_extend (he : e ∈ maximalAtlas I M) :
    ContMDiffOn I 𝓘(𝕜, E) n (e.extend I) e.source :=
  fun _x' hx' => (contMDiffAt_extend he hx').contMDiffWithinAt

theorem contMDiffAt_extChartAt' {x' : M} (h : x' ∈ (chartAt H x).source) :
    ContMDiffAt I 𝓘(𝕜, E) n (extChartAt I x) x' :=
  contMDiffAt_extend (chart_mem_maximalAtlas I x) h
#align cont_mdiff_at_ext_chart_at' contMDiffAt_extChartAt'

theorem contMDiffAt_extChartAt : ContMDiffAt I 𝓘(𝕜, E) n (extChartAt I x) x :=
  contMDiffAt_extChartAt' <| mem_chart_source H x
#align cont_mdiff_at_ext_chart_at contMDiffAt_extChartAt

theorem contMDiffOn_extChartAt : ContMDiffOn I 𝓘(𝕜, E) n (extChartAt I x) (chartAt H x).source :=
  fun _x' hx' => (contMDiffAt_extChartAt' hx').contMDiffWithinAt
#align cont_mdiff_on_ext_chart_at contMDiffOn_extChartAt

theorem contMDiffOn_extend_symm (he : e ∈ maximalAtlas I M) :
    ContMDiffOn 𝓘(𝕜, E) I n (e.extend I).symm (I '' e.target) := by
  refine (contMDiffOn_symm_of_mem_maximalAtlas he).comp
    (contMDiffOn_model_symm.mono <| image_subset_range _ _) ?_
  simp_rw [image_subset_iff, PartialEquiv.restr_coe_symm, I.toPartialEquiv_coe_symm,
    preimage_preimage, I.left_inv, preimage_id']; rfl
#align cont_mdiff_on_extend_symm contMDiffOn_extend_symm

theorem contMDiffOn_extChartAt_symm (x : M) :
    ContMDiffOn 𝓘(𝕜, E) I n (extChartAt I x).symm (extChartAt I x).target := by
  convert contMDiffOn_extend_symm (chart_mem_maximalAtlas I x)
  rw [extChartAt_target, I.image_eq]
#align cont_mdiff_on_ext_chart_at_symm contMDiffOn_extChartAt_symm

/-- An element of `contDiffGroupoid ⊤ I` is `C^n` for any `n`. -/
theorem contMDiffOn_of_mem_contDiffGroupoid {e' : PartialHomeomorph H H}
    (h : e' ∈ contDiffGroupoid ⊤ I) : ContMDiffOn I I n e' e'.source :=
  (contDiffWithinAt_localInvariantProp I I n).liftPropOn_of_mem_groupoid
    (contDiffWithinAtProp_id I) h
#align cont_mdiff_on_of_mem_cont_diff_groupoid contMDiffOn_of_mem_contDiffGroupoid

end Atlas

/-! ### Smoothness of (local) structomorphisms -/

section IsLocalStructomorph

variable [ChartedSpace H M'] [IsM' : SmoothManifoldWithCorners I M']

theorem isLocalStructomorphOn_contDiffGroupoid_iff_aux {f : PartialHomeomorph M M'}
    (hf : LiftPropOn (contDiffGroupoid ⊤ I).IsLocalStructomorphWithinAt f f.source) :
    SmoothOn I I f f.source := by
  -- It suffices to show smoothness near each `x`
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  let c := chartAt H x
  let c' := chartAt H (f x)
  obtain ⟨-, hxf⟩ := hf x hx
  -- Since `f` is a local structomorph, it is locally equal to some transferred element `e` of
  -- the `contDiffGroupoid`.
  obtain
    ⟨e, he, he' : EqOn (c' ∘ f ∘ c.symm) e (c.symm ⁻¹' f.source ∩ e.source), hex :
      c x ∈ e.source⟩ :=
    hxf (by simp only [hx, mfld_simps])
  -- We choose a convenient set `s` in `M`.
  let s : Set M := (f.trans c').source ∩ ((c.trans e).trans c'.symm).source
  refine' ⟨s, (f.trans c').open_source.inter ((c.trans e).trans c'.symm).open_source, _, _⟩
  · simp only [s, mfld_simps]
    rw [← he'] <;> simp only [c, c', hx, hex, mfld_simps]
  -- We need to show `f` is `ContMDiffOn` the domain `s ∩ f.source`.  We show this in two
  -- steps: `f` is equal to `c'.symm ∘ e ∘ c` on that domain and that function is
  -- `ContMDiffOn` it.
  have H₁ : ContMDiffOn I I ⊤ (c'.symm ∘ e ∘ c) s := by
    have hc' : ContMDiffOn I I ⊤ c'.symm _ := contMDiffOn_chart_symm
    have he'' : ContMDiffOn I I ⊤ e _ := contMDiffOn_of_mem_contDiffGroupoid he
    have hc : ContMDiffOn I I ⊤ c _ := contMDiffOn_chart
    refine' (hc'.comp' (he''.comp' hc)).mono _
    dsimp [s]
    mfld_set_tac
  have H₂ : EqOn f (c'.symm ∘ e ∘ c) s := by
    intro y hy
    simp only [s, mfld_simps] at hy
    have hy₁ : f y ∈ c'.source := by simp only [hy, mfld_simps]
    have hy₂ : y ∈ c.source := by simp only [hy, mfld_simps]
    have hy₃ : c y ∈ c.symm ⁻¹' f.source ∩ e.source := by simp only [hy, mfld_simps]
    calc
      f y = c'.symm (c' (f y)) := by rw [c'.left_inv hy₁]
      _ = c'.symm (c' (f (c.symm (c y)))) := by rw [c.left_inv hy₂]
      _ = c'.symm (e (c y)) := by rw [← he' hy₃]; rfl
  refine' (H₁.congr H₂).mono _
  mfld_set_tac
#align is_local_structomorph_on_cont_diff_groupoid_iff_aux isLocalStructomorphOn_contDiffGroupoid_iff_aux

/-- Let `M` and `M'` be smooth manifolds with the same model-with-corners, `I`.  Then `f : M → M'`
is a local structomorphism for `I`, if and only if it is manifold-smooth on the domain of definition
in both directions. -/
theorem isLocalStructomorphOn_contDiffGroupoid_iff (f : PartialHomeomorph M M') :
    LiftPropOn (contDiffGroupoid ⊤ I).IsLocalStructomorphWithinAt f f.source ↔
      SmoothOn I I f f.source ∧ SmoothOn I I f.symm f.target := by
  constructor
  · intro h
    refine' ⟨isLocalStructomorphOn_contDiffGroupoid_iff_aux h,
      isLocalStructomorphOn_contDiffGroupoid_iff_aux _⟩
    -- todo: we can generalize this part of the proof to a lemma
    intro X hX
    let x := f.symm X
    have hx : x ∈ f.source := f.symm.mapsTo hX
    let c := chartAt H x
    let c' := chartAt H X
    obtain ⟨-, hxf⟩ := h x hx
    refine' ⟨(f.symm.continuousAt hX).continuousWithinAt, fun h2x => _⟩
    obtain ⟨e, he, h2e, hef, hex⟩ :
      ∃ e : PartialHomeomorph H H,
        e ∈ contDiffGroupoid ⊤ I ∧
          e.source ⊆ (c.symm ≫ₕ f ≫ₕ c').source ∧
            EqOn (c' ∘ f ∘ c.symm) e e.source ∧ c x ∈ e.source := by
      have h1 : c' = chartAt H (f x) := by simp only [f.right_inv hX]
      have h2 : c' ∘ f ∘ c.symm = ⇑(c.symm ≫ₕ f ≫ₕ c') := rfl
      have hcx : c x ∈ c.symm ⁻¹' f.source := by simp only [c, hx, mfld_simps]
      rw [h2]
      rw [← h1, h2, PartialHomeomorph.isLocalStructomorphWithinAt_iff'] at hxf
      · exact hxf hcx
      · mfld_set_tac
      · apply Or.inl
        simp only [c, hx, h1, mfld_simps]
    have h2X : c' X = e (c (f.symm X)) := by
      rw [← hef hex]
      dsimp only [Function.comp_def]
      have hfX : f.symm X ∈ c.source := by simp only [c, hX, mfld_simps]
      rw [c.left_inv hfX, f.right_inv hX]
    have h3e : EqOn (c ∘ f.symm ∘ c'.symm) e.symm (c'.symm ⁻¹' f.target ∩ e.target) := by
      have h1 : EqOn (c.symm ≫ₕ f ≫ₕ c').symm e.symm (e.target ∩ e.target) := by
        apply EqOn.symm
        refine' e.isImage_source_target.symm_eqOn_of_inter_eq_of_eqOn _ _
        · rw [inter_self, inter_eq_right.mpr h2e]
        · rw [inter_self]; exact hef.symm
      have h2 : e.target ⊆ (c.symm ≫ₕ f ≫ₕ c').target := by
        intro x hx; rw [← e.right_inv hx, ← hef (e.symm.mapsTo hx)]
        exact PartialHomeomorph.mapsTo _ (h2e <| e.symm.mapsTo hx)
      rw [inter_self] at h1
      rwa [inter_eq_right.mpr]
      refine' h2.trans _
      mfld_set_tac
    refine' ⟨e.symm, StructureGroupoid.symm _ he, h3e, _⟩
    rw [h2X]; exact e.mapsTo hex
  · -- We now show the converse: a partial homeomorphism `f : M → M'` which is smooth in both
    -- directions is a local structomorphism.  We do this by proposing
    -- `((chart_at H x).symm.trans f).trans (chart_at H (f x))` as a candidate for a structomorphism
    -- of `H`.
    rintro ⟨h₁, h₂⟩ x hx
    refine' ⟨(h₁ x hx).continuousWithinAt, _⟩
    let c := chartAt H x
    let c' := chartAt H (f x)
    rintro (hx' : c x ∈ c.symm ⁻¹' f.source)
    -- propose `(c.symm.trans f).trans c'` as a candidate for a local structomorphism of `H`
    refine' ⟨(c.symm.trans f).trans c', ⟨_, _⟩, (_ : EqOn (c' ∘ f ∘ c.symm) _ _), _⟩
    · -- smoothness of the candidate local structomorphism in the forward direction
      intro y hy
      simp only [mfld_simps] at hy
      have H : ContMDiffWithinAt I I ⊤ f (f ≫ₕ c').source ((extChartAt I x).symm y) := by
        refine' (h₁ ((extChartAt I x).symm y) _).mono _
        · simp only [hy, mfld_simps]
        · mfld_set_tac
      have hy' : (extChartAt I x).symm y ∈ c.source := by simp only [hy, mfld_simps]
      have hy'' : f ((extChartAt I x).symm y) ∈ c'.source := by simp only [hy, mfld_simps]
      rw [contMDiffWithinAt_iff_of_mem_source hy' hy''] at H
      convert H.2.mono _
      · simp only [hy, mfld_simps]
      · mfld_set_tac
    · -- smoothness of the candidate local structomorphism in the reverse direction
      intro y hy
      simp only [mfld_simps] at hy
      have H : ContMDiffWithinAt I I ⊤ f.symm (f.symm ≫ₕ c).source
          ((extChartAt I (f x)).symm y) := by
        refine' (h₂ ((extChartAt I (f x)).symm y) _).mono _
        · simp only [hy, mfld_simps]
        · mfld_set_tac
      have hy' : (extChartAt I (f x)).symm y ∈ c'.source := by simp only [hy, mfld_simps]
      have hy'' : f.symm ((extChartAt I (f x)).symm y) ∈ c.source := by simp only [hy, mfld_simps]
      rw [contMDiffWithinAt_iff_of_mem_source hy' hy''] at H
      convert H.2.mono _
      · simp only [hy, mfld_simps]
      · mfld_set_tac
    -- now check the candidate local structomorphism agrees with `f` where it is supposed to
    · simp only [mfld_simps]; apply eqOn_refl
    · simp only [c, c', hx', mfld_simps]
#align is_local_structomorph_on_cont_diff_groupoid_iff isLocalStructomorphOn_contDiffGroupoid_iff

end IsLocalStructomorph
