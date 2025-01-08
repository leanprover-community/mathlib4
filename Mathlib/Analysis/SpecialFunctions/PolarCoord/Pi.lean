/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Analysis.SpecialFunctions.PolarCoord.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Polar coordinates change of variables for pi-types

The polar coordinates change of variables formulas for the Lebesgue integral for a function
defined on the pi-space `ι → ℝ × ℝ` or `ι → ℂ`.

-/

open ENNReal MeasureTheory MeasureTheory.Measure

variable {ι : Type*} [DecidableEq ι]

private theorem lintegral_comp_pi_polarCoord_symm_aux {f : (ι → ℝ × ℝ) → ℝ≥0∞} (hf : Measurable f)
    (s : Finset ι) (a : ι → ℝ × ℝ) :
    (∫⋯∫⁻_s, f) (fun i ↦ polarCoord.symm (a i)) =
      (∫⋯∫⁻_s, fun p ↦
          ((∏ i ∈ s, .ofReal (p i).1) * f (fun i ↦ polarCoord.symm (p i)))
            ∂fun _ ↦ ((volume : Measure (ℝ × ℝ)).restrict polarCoord.target)) a := by
  induction s using Finset.induction generalizing f a with
  | empty => simp only [polarCoord_symm_apply, lmarginal_empty, polarCoord_target,
      Finset.prod_empty, one_mul]
  | @insert i₀ s hi₀ h_ind =>
      have h : ∀ t : Finset ι, Measurable fun p : ι → ℝ × ℝ ↦
          (∏ i ∈ t, .ofReal (p i).1) * f fun i ↦ polarCoord.symm (p i) := by
        intro _
        refine Measurable.mul ?_ ?_
        · exact Finset.measurable_prod _ (fun _ _ ↦ by fun_prop)
        · exact hf.comp <| measurable_pi_lambda _ fun _ ↦
            continuous_polarCoord_symm.measurable.comp (measurable_pi_apply _)
      calc
        _ = ∫⁻ x in polarCoord.target, ENNReal.ofReal x.1 •
              (∫⋯∫⁻_s, f ∂fun _ ↦ volume)
                fun j ↦ polarCoord.symm (Function.update a i₀ x j) := ?_
        _ = ∫⁻ (x : ℝ × ℝ) in polarCoord.target,
              (∫⋯∫⁻_s,
                (fun p ↦ ↑(∏ i ∈ insert i₀ s, .ofReal (p i).1) *
                  (f fun i ↦ polarCoord.symm (p i))) ∘ fun p ↦ Function.update p i₀ x
              ∂fun _ ↦ volume.restrict polarCoord.target) a := ?_
        _ = (∫⋯∫⁻_insert i₀ s, fun p ↦ (∏ i ∈ insert i₀ s, .ofReal (p i).1) *
              f (fun i ↦ polarCoord.symm (p i)) ∂fun _ ↦ volume.restrict polarCoord.target) a := ?_
      · simp_rw [lmarginal_insert _ hf hi₀, ← lintegral_comp_polarCoord_symm,
          Function.apply_update (f := fun _ ↦ polarCoord.symm)]
      · simp_rw [h_ind hf, lmarginal_update_of_not_mem (h s) hi₀, Function.comp_def,
          Finset.prod_insert hi₀, Function.update_self, smul_eq_mul, mul_assoc,
          ← lmarginal_const_smul' _ ofReal_ne_top, Pi.smul_def, smul_eq_mul]
      · simp_rw [← lmarginal_update_of_not_mem (h _) hi₀, lmarginal_insert _ (h _) hi₀]

theorem lintegral_comp_pi_polarCoord_symm {f : (ι → ℝ × ℝ) → ℝ≥0∞} [Fintype ι] (hf : Measurable f) :
    ∫⁻ p in (Set.univ.pi fun _ : ι ↦ polarCoord.target),
      (∏ i, .ofReal (p i).1) * f (fun i ↦ polarCoord.symm (p i)) = ∫⁻ p, f p := by
  rw [volume_pi, lintegral_eq_lmarginal_univ (fun _ ↦ polarCoord.symm 0),
    lintegral_comp_pi_polarCoord_symm_aux hf, lmarginal_univ, ← restrict_pi_pi]

protected theorem Complex.lintegral_comp_pi_polarCoord_symm {f : (ι → ℂ) → ℝ≥0∞} [Fintype ι]
    (hf : Measurable f) :
    ∫⁻ p in (Set.univ.pi fun _ : ι ↦ Complex.polarCoord.target),
      (∏ i, .ofReal (p i).1) * f (fun i ↦ Complex.polarCoord.symm (p i)) = ∫⁻ p, f p := by
  let e := MeasurableEquiv.piCongrRight (fun _ : ι ↦ measurableEquivRealProd.symm)
  rw [← MeasurePreserving.lintegral_comp_emb ?_ e.measurableEmbedding]
  · exact lintegral_comp_pi_polarCoord_symm <| (MeasurableEquiv.measurable_comp_iff e).mpr hf
  · exact volume_preserving_pi (fun _ : ι ↦ Complex.volume_preserving_equiv_real_prod.symm)
