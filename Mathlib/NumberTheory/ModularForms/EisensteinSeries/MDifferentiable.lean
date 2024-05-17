/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Holomorphicity of Eisenstein series

We show that Eisenstein series of weight `k` and level `Γ(N)` with congruence condition
`a : Fin 2 → ZMod N` are holomorphic on the upper half plane.
-/

noncomputable section

open ModularForm EisensteinSeries UpperHalfPlane Set Filter Function Complex Manifold

open scoped Topology BigOperators Nat Classical

namespace EisensteinSeries

local notation "↑ₕ" f => f ∘ (PartialHomeomorph.symm
          (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe))

variable (k : ℤ) (a : Fin 2 → ℤ)

lemma mem_img_UpperHalfPlane {x : ℂ} (hx : x ∈ UpperHalfPlane.coe '' ⊤) : 0 < x.im := by
  obtain ⟨y, _, hy⟩ := hx
  rw [← hy]
  exact y.2

lemma complex_summand_differentiableOn :
    DifferentiableOn ℂ (fun z : ℂ => 1 / (a 0 * z + a 1) ^ k) (UpperHalfPlane.coe '' ⊤) := by
  by_cases ha :  a ≠ 0
  · apply DifferentiableOn.div (differentiableOn_const 1)
    · apply DifferentiableOn.zpow
      fun_prop
      left
      exact fun z hz ↦
        UpperHalfPlane.linear_ne_zero ((Int.cast (R := ℝ)) ∘ a) ⟨z, mem_img_UpperHalfPlane hz⟩
        ((Function.comp_ne_zero_iff _ Int.cast_injective Int.cast_zero ).mpr ha)
    · exact fun z hz ↦ zpow_ne_zero k (UpperHalfPlane.linear_ne_zero ((Int.cast (R := ℝ)) ∘ a)
        ⟨z, mem_img_UpperHalfPlane hz⟩
          ((Function.comp_ne_zero_iff _ Int.cast_injective Int.cast_zero ).mpr ha))
  · rw [ne_eq, not_not] at ha
    simp only [ha, Fin.isValue, Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, one_div,
      top_eq_univ, image_univ]
    exact differentiableOn_const (0 ^ k)⁻¹

lemma eisSummad_complex_extension_differentiableOn :
    DifferentiableOn ℂ (↑ₕeisSummand k a) (UpperHalfPlane.coe '' ⊤) := by
  apply DifferentiableOn.congr (complex_summand_differentiableOn k a)
  intro z hz
  have := PartialHomeomorph.left_inv (PartialHomeomorph.symm
    (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe)) hz
  simp only [ne_eq, top_eq_univ, image_univ, mem_range, PartialHomeomorph.symm_symm,
    OpenEmbedding.toPartialHomeomorph_apply, UpperHalfPlane.coe] at this
  simp only [comp_apply, eisSummand, Fin.isValue, this, one_div]

lemma eisensteinSeries_SIF_complex_differentiableOn {N : ℕ} (a : Fin 2 → ZMod N) (hk : 3 ≤ k) :
    DifferentiableOn ℂ (↑ₕ(eisensteinSeries_SIF a k).toFun) (UpperHalfPlane.coe '' ⊤) := by
  apply @TendstoLocallyUniformlyOn.differentiableOn (E := ℂ) (ι := (Finset ↑(gammaSet N a))) _ _ _
    (U := UpperHalfPlane.coe '' ⊤) atTop (fun (s : Finset (gammaSet N a)) =>
      ↑ₕ(fun (z : ℍ) => ∑ x in s, eisSummand k x z )) (↑ₕ((eisensteinSeries_SIF a k).toFun ))
        (by apply atTop_neBot) (eisensteinSeries_tendstoLocallyUniformlyOn hk a)
          ((eventually_of_forall fun s =>
            DifferentiableOn.sum fun s _ ↦ eisSummad_complex_extension_differentiableOn _ _)) ?_
  rw [← OpenEmbedding.open_iff_image_open openEmbedding_coe, top_eq_univ]
  exact isOpen_univ

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' E') {M' : Type*}
  [NormedAddCommGroup M'] [NormedSpace 𝕜 M']  [ChartedSpace E' M]

lemma af (f e : M → E') [Nonempty M]
  (he : OpenEmbedding e) : MDifferentiable 𝓘(𝕜, E') 𝓘(𝕜, E') f ↔
  DifferentiableOn 𝕜 (f ∘ (PartialHomeomorph.symm (he.toPartialHomeomorph ))) (e '' ⊤) := by
  constructor
  intro h
  sorry
  intro h
  rw [MDifferentiable]
  intro x
  have ha : (e '' ⊤) ∈ 𝓝 (e x) := by
    apply IsOpenMap.image_mem_nhds (OpenEmbedding.isOpenMap he)
    simp

  constructor
  · rw [continuousWithinAt_univ, PartialHomeomorph.continuousAt_iff_continuousAt_comp_right
      (e := (PartialHomeomorph.symm (he.toPartialHomeomorph)))]
    · apply ContinuousOn.continuousAt (s := (e '' ⊤))
      have := h.continuousOn
      convert this
      apply ha
      --(h.continuousOn) (s := (e '' ⊤)) (x := e x) (by sorry)
    · simp only [PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_target,
      OpenEmbedding.toPartialHomeomorph_source, mem_univ]
  · rw [DifferentiableWithinAtProp]
    simp  [modelWithCornersSelf_coe, SlashInvariantForm.toFun_eq_coe,
      PartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_source,
      PartialHomeomorph.singletonChartedSpace_chartAt_eq, PartialHomeomorph.refl_apply,
      OpenEmbedding.toPartialHomeomorph_source, CompTriple.comp_eq, modelWithCornersSelf_coe_symm,
      preimage_univ, range_id, inter_self, OpenEmbedding.toPartialHomeomorph_apply, id_eq,
      differentiableWithinAt_univ]
    have := h.differentiableAt (s := e '' ⊤) ha

    exact eisensteinSeries_SIF_complex_differentiableOn k a hk


theorem eisensteinSeries_SIF_MDifferentiable {N : ℕ} (a : Fin 2 → ZMod N) (hk : 3 ≤ k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (eisensteinSeries_SIF a k).toFun := by
  rw [MDifferentiable]
  intro z
  have ha : UpperHalfPlane.coe '' ⊤ ∈ 𝓝 ↑z := by
    exact IsOpenMap.image_mem_nhds (OpenEmbedding.isOpenMap openEmbedding_coe)
      (by simp only [top_eq_univ,univ_mem])
  constructor
  · rw [continuousWithinAt_univ, PartialHomeomorph.continuousAt_iff_continuousAt_comp_right
      (e := (PartialHomeomorph.symm (OpenEmbedding.toPartialHomeomorph
      UpperHalfPlane.coe openEmbedding_coe)))]
    · exact ContinuousOn.continuousAt
        ((eisensteinSeries_SIF_complex_differentiableOn k a hk).continuousOn)
          (s := (UpperHalfPlane.coe '' ⊤)) (x := z) ha
    · simp only [PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_target,
      OpenEmbedding.toPartialHomeomorph_source, mem_univ]
  · rw [DifferentiableWithinAtProp]
    simp only [modelWithCornersSelf_coe, SlashInvariantForm.toFun_eq_coe,
      PartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_source,
      PartialHomeomorph.singletonChartedSpace_chartAt_eq, PartialHomeomorph.refl_apply,
      OpenEmbedding.toPartialHomeomorph_source, CompTriple.comp_eq, modelWithCornersSelf_coe_symm,
      preimage_univ, range_id, inter_self, OpenEmbedding.toPartialHomeomorph_apply, id_eq,
      differentiableWithinAt_univ]
    apply DifferentiableOn.differentiableAt (s := UpperHalfPlane.coe '' ⊤) _ ha
    exact eisensteinSeries_SIF_complex_differentiableOn k a hk
