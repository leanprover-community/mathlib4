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

theorem linear_HasDerivAt (z : ℂ) (h : (a 0 : ℂ) * z + a 1 ≠ 0) :
    HasDerivAt (fun z : ℂ => (a 0 * z + a 1) ^ k) (k * (a 0 * z + a 1) ^ (k - 1) * a 0) z := by
  rw [← Function.comp_def (fun x : ℂ => x ^ k) ((a 0) * · + (a 1))]
  apply HasDerivAt.comp
  · exact hasDerivAt_zpow k ((a 0 ) * z + a 1 ) (Or.inl h)
  · simpa using (hasDerivAt_id' z).const_mul (a 0 : ℂ) |>.add_const _

lemma UpperHalfPlane.coe_linear_ne_zero (a : Fin 2 → ℤ) (x : UpperHalfPlane.coe '' ⊤) (ha : a ≠ 0) :
    ((a 0 : ℂ) * x + a 1) ≠ 0 := by
  obtain ⟨y, _, hy⟩ := x.2
  rw [← hy]
  apply UpperHalfPlane.linear_ne_zero ((Int.cast (R := ℝ)) ∘ a) y
      ((Function.comp_ne_zero_iff _ Int.cast_injective Int.cast_zero ).mpr ha)

lemma complex_eisSummand_differentiableOn :
    DifferentiableOn ℂ (fun z : ℂ => 1 / (a 0 * z + a 1) ^ k) (UpperHalfPlane.coe '' ⊤) := by
  by_cases ha : a ≠ 0
  · apply DifferentiableOn.div (differentiableOn_const 1)
    · intro z hz
      apply DifferentiableAt.differentiableWithinAt (linear_HasDerivAt k a z
        (UpperHalfPlane.coe_linear_ne_zero a ⟨z, hz⟩ ha)).differentiableAt
    · intro z hz
      apply zpow_ne_zero k (UpperHalfPlane.coe_linear_ne_zero a ⟨z, hz⟩ ha)
  · simp only [ne_eq, not_not] at ha
    rw [ha]
    simp only [Fin.isValue, Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, one_div, top_eq_univ,
      image_univ]
    fun_prop

lemma eisSummad_complex_extension_differentiableOn :
    DifferentiableOn ℂ (↑ₕeisSummand k a) (UpperHalfPlane.coe '' ⊤) := by
  apply DifferentiableOn.congr (complex_eisSummand_differentiableOn k a)
  intro z hz
  simp only [eisSummand, one_div, comp_apply, inv_inj]
  have := PartialHomeomorph.left_inv (PartialHomeomorph.symm
    (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe)) hz
  simp only [ne_eq, top_eq_univ, image_univ, mem_range, PartialHomeomorph.symm_symm,
    OpenEmbedding.toPartialHomeomorph_apply, UpperHalfPlane.coe] at this
  rw [this]

lemma eisensteinSeries_SIF_complex_differentiableOn {N : ℕ} (a : Fin 2 → ZMod N) (hk : 3 ≤ k) :
    DifferentiableOn ℂ (↑ₕ(eisensteinSeries_SIF a k).toFun) (UpperHalfPlane.coe '' ⊤) := by
  convert @TendstoLocallyUniformlyOn.differentiableOn (E := ℂ) (ι := (Finset ↑(gammaSet N a))) _ _ _
    (UpperHalfPlane.coe '' ⊤) atTop (fun (s : Finset (gammaSet N a )) =>
      ↑ₕ(fun (z : ℍ) => ∑ x in s, eisSummand k x z )) (↑ₕ((eisensteinSeries_SIF a k).toFun ))
        (by apply atTop_neBot) (eisensteinSeries_tendstoLocallyUniformlyOn hk a)
          ((eventually_of_forall fun s => ?_)) ?_
  · apply DifferentiableOn.sum
    intro v _
    apply eisSummad_complex_extension_differentiableOn
  · rw [← OpenEmbedding.open_iff_image_open]
    simp only [top_eq_univ, isOpen_univ]
    exact openEmbedding_coe

theorem eisensteinSeries_SIF_MDifferentiable {N : ℕ} (a : Fin 2 → ZMod N) (hk : 3 ≤ k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (eisensteinSeries_SIF a k).toFun := by
  simp only [MDifferentiable, MDifferentiableAt, differentiableWithinAt_univ, mfld_simps]
  intro z
  have ha : UpperHalfPlane.coe '' ⊤ ∈ 𝓝 ↑z := by
    exact IsOpenMap.image_mem_nhds (OpenEmbedding.isOpenMap openEmbedding_coe) (by simp)
  constructor
  rw [continuousWithinAt_univ, PartialHomeomorph.continuousAt_iff_continuousAt_comp_right
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
      preimage_univ, range_id, inter_self, OpenEmbedding.toPartialHomeomorph_apply, id_eq]
    rw [ differentiableWithinAt_univ]
    apply DifferentiableOn.differentiableAt (s := UpperHalfPlane.coe '' ⊤) _ ha
    exact eisensteinSeries_SIF_complex_differentiableOn k a hk
