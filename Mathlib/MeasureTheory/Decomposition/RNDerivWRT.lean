
/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Decomposition.RadonNikodym

/-!
# ZeroTopSet

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν ξ : Measure α} {s : Set α}

namespace Measure

lemma rnDeriv_add_self_right (ν μ : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    ν.rnDeriv (μ + ν) =ᵐ[ν] fun x ↦ (μ.rnDeriv ν x + 1)⁻¹ := by
  have hν_ac : ν ≪ μ + ν := by rw [add_comm]; exact rfl.absolutelyContinuous.add_right _
  filter_upwards [Measure.rnDeriv_add' μ ν ν, Measure.rnDeriv_self ν,
    Measure.inv_rnDeriv hν_ac] with a h1 h2 h3
  rw [Pi.inv_apply, h1, Pi.add_apply, h2, inv_eq_iff_eq_inv] at h3
  rw [h3]

lemma rnDeriv_add_self_left (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.rnDeriv (μ + ν) =ᵐ[ν] fun x ↦ μ.rnDeriv ν x / (μ.rnDeriv ν x + 1) := by
  have h_add : (μ + ν).rnDeriv (μ + ν) =ᵐ[ν] μ.rnDeriv (μ + ν) + ν.rnDeriv (μ + ν) :=
    (ae_add_measure_iff.mp (Measure.rnDeriv_add' μ ν (μ + ν))).2
  have h_one_add := (ae_add_measure_iff.mp (Measure.rnDeriv_self (μ + ν))).2
  have : (μ.rnDeriv (μ + ν)) =ᵐ[ν] fun x ↦ 1 - (μ.rnDeriv ν x + 1)⁻¹ := by
    filter_upwards [h_add, h_one_add, rnDeriv_add_self_right ν μ] with a h4 h5 h6
    rw [h5, Pi.add_apply] at h4
    nth_rewrite 1 [h4]
    rw [h6]
    simp only [ne_eq, ENNReal.inv_eq_top, add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      ENNReal.add_sub_cancel_right]
  filter_upwards [this, Measure.rnDeriv_lt_top μ ν] with a ha ha_lt_top
  rw [ha, div_eq_mul_inv]
  refine ENNReal.sub_eq_of_eq_add (by simp) ?_
  nth_rewrite 2 [← one_mul (μ.rnDeriv ν a + 1)⁻¹]
  have h := add_mul (μ.rnDeriv ν a) 1 (μ.rnDeriv ν a + 1)⁻¹
  rw [ENNReal.mul_inv_cancel] at h
  · exact h
  · simp
  · simp [ha_lt_top.ne]

noncomputable
def rnDerivWRT (μ ν ξ : Measure α) : α → ℝ≥0∞ := μ.rnDeriv ξ / ν.rnDeriv ξ

lemma measurable_rnDerivWRT (μ ν ξ : Measure α) : Measurable (μ.rnDerivWRT ν ξ) :=
  (measurable_rnDeriv μ ξ).div (measurable_rnDeriv ν ξ)

lemma rnDeriv_eq_div_add (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.rnDeriv ν =ᵐ[ν] μ.rnDeriv (μ + ν) / ν.rnDeriv (μ + ν) := by
  filter_upwards [rnDeriv_add_self_right ν μ, rnDeriv_add_self_left μ ν, Measure.rnDeriv_lt_top μ ν]
      with a ha1 ha2 ha_lt_top
  rw [Pi.div_apply, ha1, ha2, ENNReal.div_eq_inv_mul, inv_inv, ENNReal.div_eq_inv_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel, one_mul]
  · simp
  · simp [ha_lt_top.ne]

lemma rnDerivWRT_add_ae_eq (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.rnDerivWRT ν (μ + ν) =ᵐ[ν] μ.rnDeriv ν := by
  filter_upwards [rnDeriv_eq_div_add μ ν] with x hx
  rw [hx, rnDerivWRT, Pi.div_apply]

lemma rnDeriv_div_rnDeriv [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    μ.rnDeriv ξ / ν.rnDeriv ξ =ᵐ[μ + ν] μ.rnDeriv (μ + ν) / ν.rnDeriv (μ + ν) := by
  have h1 : μ.rnDeriv (μ + ν) * (μ + ν).rnDeriv ξ =ᵐ[ξ] μ.rnDeriv ξ :=
    Measure.rnDeriv_mul_rnDeriv (rfl.absolutelyContinuous.add_right _)
  have h2 : ν.rnDeriv (μ + ν) * (μ + ν).rnDeriv ξ =ᵐ[ξ] ν.rnDeriv ξ :=
    Measure.rnDeriv_mul_rnDeriv ?_
  swap; · rw [add_comm]; exact rfl.absolutelyContinuous.add_right _
  have h_ac : μ + ν ≪ ξ := by
    refine (Measure.AbsolutelyContinuous.add hμ hν).trans ?_
    have : ξ + ξ = (2 : ℝ≥0∞) • ξ := by
      ext
      simp only [Measure.add_toOuterMeasure, OuterMeasure.coe_add, Pi.add_apply,
        Measure.smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [two_mul]
    rw [this]
    exact Measure.absolutelyContinuous_of_le_smul le_rfl
  filter_upwards [h_ac h1, h_ac h2, h_ac <| Measure.rnDeriv_lt_top (μ + ν) ξ,
    Measure.rnDeriv_lt_top ν (μ + ν), Measure.rnDeriv_pos h_ac]
    with a h1 h2 h_lt_top1 h_lt_top2 h_pos
  rw [Pi.div_apply, Pi.div_apply, ← h1, ← h2, Pi.mul_apply, Pi.mul_apply, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr h_lt_top1.ne) (Or.inl h_lt_top2.ne), div_eq_mul_inv, mul_assoc,
    mul_comm ((μ + ν).rnDeriv ξ a), mul_assoc, ENNReal.inv_mul_cancel h_pos.ne' h_lt_top1.ne,
    mul_one]

lemma rnDerivWRT_ae_eq_add [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    μ.rnDerivWRT ν ξ =ᵐ[μ + ν] μ.rnDerivWRT ν (μ + ν) := by
  filter_upwards [rnDeriv_div_rnDeriv hμ hν] with x hx
  rw [rnDerivWRT, hx, rnDerivWRT]

lemma rnDeriv_eq_div [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    μ.rnDeriv ν =ᵐ[ν] μ.rnDeriv ξ / ν.rnDeriv ξ := by
  have hν_ac : ν ≪ μ + ν := by rw [add_comm]; exact rfl.absolutelyContinuous.add_right _
  filter_upwards [rnDeriv_eq_div_add μ ν, hν_ac (rnDeriv_div_rnDeriv hμ hν)] with a h1 h2
  exact h1.trans h2.symm

lemma rnDerivWRT_ae_eq [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    μ.rnDerivWRT ν ξ =ᵐ[ν] μ.rnDeriv ν := by
  filter_upwards [rnDeriv_eq_div hμ hν] with x hx
  rw [hx, rnDerivWRT, Pi.div_apply]

lemma lintegral_comp_rnDerivWRT [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) {f : ℝ≥0∞ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, ν.rnDeriv ξ x * f (μ.rnDerivWRT ν ξ x) ∂ξ = ∫⁻ x, f (μ.rnDeriv ν x) ∂ν := by
  rw [lintegral_rnDeriv_mul hν]
  swap; · exact (hf.comp (measurable_rnDerivWRT μ ν ξ)).aemeasurable
  refine lintegral_congr_ae ?_
  filter_upwards [rnDerivWRT_ae_eq hμ hν] with x hx
  rw [hx]

lemma rnDeriv_add_ne_zero (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    ∀ᵐ x ∂(μ + ν), μ.rnDeriv (μ + ν) x ≠ 0 ∨ ν.rnDeriv (μ + ν) x ≠ 0 := by
  suffices ∀ᵐ x ∂(μ + ν), μ.rnDeriv (μ + ν) x + ν.rnDeriv (μ + ν) x ≠ 0 by
    filter_upwards [this] with x hx
    simpa only [ne_eq, add_eq_zero, Decidable.not_and_iff_or_not] using hx
  filter_upwards [rnDeriv_self (μ + ν), rnDeriv_add' μ ν (μ + ν)] with x hx_one hx_add
  rw [hx_one, Pi.add_apply] at hx_add
  rw [← hx_add]
  exact one_ne_zero

lemma inv_rnDerivWRT_add (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    (μ.rnDerivWRT ν (μ + ν))⁻¹ =ᵐ[μ + ν] ν.rnDerivWRT μ (μ + ν) := by
  filter_upwards [rnDeriv_ne_top μ (μ + ν), rnDeriv_add_ne_zero μ ν] with x hxμ hx_ne_zero
  rw [rnDerivWRT, rnDerivWRT, Pi.div_apply, Pi.inv_apply, Pi.div_apply,
    div_eq_mul_inv, div_eq_mul_inv]
  rw [ENNReal.mul_inv, inv_inv, mul_comm]
  · simp only [ne_eq, ENNReal.inv_eq_top]
    exact hx_ne_zero
  · simp only [ne_eq, ENNReal.inv_eq_zero]
    left
    exact hxμ

lemma rnDeriv_ae_eq_zero_singularPart (hμν : μ ≪ ν) :
    μ.rnDeriv ν =ᵐ[ν.singularPart μ] 0 := by
  sorry

lemma singularPart_mono_right (μ : Measure α) (hνξ : ν ≪ ξ) :
    μ.singularPart ξ ≤ μ.singularPart ν := by
  sorry

lemma rnDerivWRT_singularPart (hμ : μ ≪ ξ) (ν : Measure α) :
    μ.rnDerivWRT ν ξ =ᵐ[ξ.singularPart (μ + ν)] 0 := by
  suffices μ.rnDeriv ξ =ᵐ[ξ.singularPart (μ + ν)] 0 by
    filter_upwards [this] with x hx
    rw [rnDerivWRT, Pi.div_apply, hx]
    simp
  have h_ae := rnDeriv_ae_eq_zero_singularPart hμ
  have h_le : ξ.singularPart (μ + ν) ≤ ξ.singularPart μ :=
    singularPart_mono_right ξ (rfl.absolutelyContinuous.add_right _)
  exact ae_mono h_le h_ae

lemma inv_toReal_rnDerivWRT [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    (fun x ↦ (μ.rnDerivWRT ν ξ x).toReal⁻¹) =ᵐ[ξ] fun x ↦ (ν.rnDerivWRT μ ξ x).toReal := by
  have h := haveLebesgueDecomposition_add ξ (μ + ν)
  sorry

end Measure

end MeasureTheory
