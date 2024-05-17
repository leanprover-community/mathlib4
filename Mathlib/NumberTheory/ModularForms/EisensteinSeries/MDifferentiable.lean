/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.HalfPlane

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

lemma complex_summand_differentiableOn (k : ℤ) (a : Fin 2 → ℤ) :
    DifferentiableOn ℂ (fun z : ℂ => 1 / (a 0 * z + a 1) ^ k) {z : ℂ | 0 < z.im} := by
  by_cases ha : a ≠ 0
  · apply DifferentiableOn.div (differentiableOn_const 1)
    · apply DifferentiableOn.zpow
      fun_prop
      left
      exact fun z hz ↦ linear_ne_zero ((Int.cast (R := ℝ)) ∘ a) ⟨z, hz⟩
        ((Function.comp_ne_zero_iff _ Int.cast_injective Int.cast_zero ).mpr ha)
    · exact fun z hz ↦ zpow_ne_zero k (linear_ne_zero ((Int.cast (R := ℝ)) ∘ a)
        ⟨z, hz⟩ ((Function.comp_ne_zero_iff _ Int.cast_injective Int.cast_zero ).mpr ha))
  · rw [ne_eq, not_not] at ha
    simp only [ha, Fin.isValue, Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, one_div,
      top_eq_univ, image_univ]
    exact differentiableOn_const (0 ^ k)⁻¹

lemma eisSummad_extension_differentiableOn (k : ℤ) (a : Fin 2 → ℤ) :
    DifferentiableOn ℂ (↑ₕeisSummand k a) {z : ℂ | 0 < z.im} := by
  apply DifferentiableOn.congr (complex_summand_differentiableOn k a)
  intro z hz
  rw [← coe_image_eq] at hz
  have := PartialHomeomorph.left_inv (PartialHomeomorph.symm
    (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe)) hz
  simp only [ne_eq, top_eq_univ, image_univ, mem_range, PartialHomeomorph.symm_symm,
    OpenEmbedding.toPartialHomeomorph_apply, UpperHalfPlane.coe] at this
  simp only [comp_apply, eisSummand, Fin.isValue, this, one_div]

theorem eisensteinSeries_SIF_MDifferentiable  {k : ℤ} {N : ℕ} (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (eisensteinSeries_SIF a k).toFun := by
  rw [MDifferentiable_iff_extension_DifferentiableOn, coe_image_eq]
  apply @TendstoLocallyUniformlyOn.differentiableOn (E := ℂ) (ι := (Finset ↑(gammaSet N a))) _ _ _
    (U := {z : ℂ | 0 < z.im}) atTop (fun (s : Finset (gammaSet N a)) =>
      ↑ₕ(fun (z : ℍ) => ∑ x in s, eisSummand k x z )) (↑ₕ((eisensteinSeries_SIF a k).toFun ))
        (by apply atTop_neBot) (eisensteinSeries_tendstoLocallyUniformlyOn hk a)
          ((eventually_of_forall fun s =>
            DifferentiableOn.sum fun s _ ↦ eisSummad_extension_differentiableOn _ _)) ?_
  simpa only [EReal.coe_pos] using Complex.isOpen_im_gt_EReal 0
