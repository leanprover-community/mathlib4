/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# Scalar multiplication on ℒp space
-/

public noncomputable section

open Filter

open scoped ENNReal

namespace MeasureTheory

variable {α F : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ : Measure α}
  [NormedAddCommGroup F] {f : α → F}

section Lp

/-!
### Bounded actions by normed rings
In this section we show inequalities on the norm.
-/

section IsBoundedSMul

variable {𝕜 : Type*} [NormedRing 𝕜] [MulActionWithZero 𝕜 F] [IsBoundedSMul 𝕜 F] {c : 𝕜}

theorem eLpNorm'_const_smul_le (hq : 0 < q) : eLpNorm' (c • f) q μ ≤ ‖c‖ₑ * eLpNorm' f q μ :=
  eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul (Eventually.of_forall fun _ => nnnorm_smul_le ..) hq

theorem eLpNormEssSup_const_smul_le : eLpNormEssSup (c • f) μ ≤ ‖c‖ₑ * eLpNormEssSup f μ :=
  eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul
    (Eventually.of_forall fun _ => by simp [nnnorm_smul_le])

theorem eLpNorm_const_smul_le :
    eLpNorm (c • f) p μ ≤ ‖c‖ₑ * eLpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · exact eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (hf.const_smul c)
      (Eventually.of_forall fun _ => by simp [nnnorm_smul_le]) _
  rw [eLpNorm_of_not_aestronglyMeasurable hf]
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [ENNReal.mul_top (by simpa)]
    exact le_top

theorem MemLp.const_smul (hf : MemLp f p μ) (c : 𝕜) : MemLp (c • f) p μ :=
  (eLpNorm_const_smul_le).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf)

theorem MemLp.const_mul {f : α → 𝕜} (hf : MemLp f p μ) (c : 𝕜) : MemLp (fun x => c * f x) p μ :=
  hf.const_smul c

theorem MemLp.mul_const {f : α → 𝕜} (hf : MemLp f p μ) (c : 𝕜) :
    MemLp (fun x => f x * c) p μ :=
  hf.const_smul (MulOpposite.op c)

end IsBoundedSMul

section ENormSMulClass

variable {𝕜 : Type*} [NormedRing 𝕜]
  {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε] [SMul 𝕜 ε] [ENormSMulClass 𝕜 ε]
  {c : 𝕜} {f : α → ε}

theorem eLpNorm'_const_smul_le' (hq : 0 < q) : eLpNorm' (c • f) q μ ≤ ‖c‖ₑ * eLpNorm' f q μ :=
  eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul'
    (Eventually.of_forall fun _ ↦ le_of_eq (enorm_smul ..)) hq

theorem eLpNormEssSup_const_smul_le' : eLpNormEssSup (c • f) μ ≤ ‖c‖ₑ * eLpNormEssSup f μ :=
  eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul'
    (Eventually.of_forall fun _ => by simp [enorm_smul])

end ENormSMulClass

section ENormSMulClass

variable {𝕜 : Type*} [NormedRing 𝕜]
  {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε] [SMulWithZero 𝕜 ε] [ENormSMulClass 𝕜 ε]
  {c : 𝕜} {f : α → ε}

theorem eLpNorm_const_smul_le' [ContinuousConstSMul 𝕜 ε] :
    eLpNorm (c • f) p μ ≤ ‖c‖ₑ * eLpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (hf.const_smul c)
      (Eventually.of_forall fun _ => le_of_eq (enorm_smul ..)) _
  rw [eLpNorm_of_not_aestronglyMeasurable hf]
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [ENNReal.mul_top (by simpa)]
    exact le_top

theorem MemLp.const_smul' [ContinuousConstSMul 𝕜 ε] (hf : MemLp f p μ) (c : 𝕜) :
    MemLp (c • f) p μ :=
  eLpNorm_const_smul_le'.trans_lt
      (ENNReal.mul_lt_top ENNReal.coe_lt_top hf)

theorem MemLp.const_mul' {f : α → 𝕜} (hf : MemLp f p μ) (c : 𝕜) : MemLp (fun x => c * f x) p μ :=
  hf.const_smul c

end ENormSMulClass

/-!
### Bounded actions by normed division rings
The inequalities in the previous section are now tight.

TODO: do these results hold for any `NormedRing` assuming `NormSMulClass`?
-/

section NormedSpace

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 F] [NormSMulClass 𝕜 F]

theorem eLpNorm'_const_smul {f : α → F} (c : 𝕜) (hq_pos : 0 < q) :
    eLpNorm' (c • f) q μ = ‖c‖ₑ * eLpNorm' f q μ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp [eLpNorm'_eq_lintegral_enorm, hq_pos]
  refine le_antisymm (eLpNorm'_const_smul_le hq_pos) <| ENNReal.mul_le_of_le_div' ?_
  simpa [enorm_inv, hc, ENNReal.div_eq_inv_mul]
    using eLpNorm'_const_smul_le (c := c⁻¹) (f := c • f) hq_pos

theorem eLpNormEssSup_const_smul (c : 𝕜) (f : α → F) :
    eLpNormEssSup (c • f) μ = ‖c‖ₑ * eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup_eq_essSup_enorm, Pi.smul_apply, enorm_smul,
    ENNReal.essSup_const_mul]

theorem eLpNorm_const_smul (c : 𝕜) (f : α → F) (p : ℝ≥0∞) (μ : Measure α) :
    eLpNorm (c • f) p μ = ‖c‖ₑ * eLpNorm f p μ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  refine le_antisymm eLpNorm_const_smul_le <| ENNReal.mul_le_of_le_div' ?_
  simpa [enorm_inv, hc, ENNReal.div_eq_inv_mul]
    using eLpNorm_const_smul_le (c := c⁻¹) (f := c • f)

lemma eLpNorm_nsmul [NormedSpace ℝ F] (n : ℕ) (f : α → F) :
    eLpNorm (n • f) p μ = n * eLpNorm f p μ := by
  simpa [Nat.cast_smul_eq_nsmul] using eLpNorm_const_smul (n : ℝ) f p μ

end NormedSpace

section NNReal

open scoped NNReal

variable {ε : Type*} [TopologicalSpace ε] [ENormedAddMonoid ε] [SMulWithZero ℝ≥0 ε]
  [ContinuousConstSMul ℝ≥0 ε]

@[simp] lemma glou : ‖(0 : ℝ≥0)‖ₑ = 0 := rfl

@[simp] lemma glouk (c : ℝ≥0) : ‖c‖ₑ = 0 ↔ c = 0 := by simp [enorm]

#check aestronglyMeasurable_const_smul_iff₀

lemma eLpNorm_smul_nnreal {f : α → ε} {c : ℝ≥0} :
    eLpNorm (c • f) p μ = ‖c‖ₑ * eLpNorm f p μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  by_cases hf : AEStronglyMeasurable f μ; swap
  · simp only [hf, not_false_eq_true, eLpNorm_of_not_aestronglyMeasurable, ne_eq, glouk, hc,
      ENNReal.mul_top]
    apply eLpNorm_of_not_aestronglyMeasurable
    rw [aestronglyMeasurable_const_smul_iff₀]

    contrapose hf


  apply le_antisymm
  · apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'


#where


end NNReal


section ENNReal

#check eLpNorm_le_mul_eLpNorm_of_ae_le_mul''

theorem eLpNorm_const_mul_ennreal {f : α → ℝ≥0∞} {c : ℝ≥0∞} (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x ↦ c * f x) p μ = c * eLpNorm f p μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rcases eq_or_ne c ∞ with rfl | h'c; swap
  · apply le_antisymm
    · exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' _
        (hf.aemeasurable.const_mul c).aestronglyMeasurable (by simp)
    rw [ENNReal.mul_le_iff_le_inv hc h'c]
    have : f = fun x ↦ c⁻¹ * (c * f x) := by
      simp [ENNReal.inv_mul_cancel_left hc h'c]
    nth_rw 1 [this]
    exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' _  (by rwa [← this]) (by simp)
  rcases eq_or_ne p 0 with rfl | hp
  · simp [eLpNorm_exponent_zero, hf, (hf.aemeasurable.const_mul ∞).aestronglyMeasurable]
  by_cases h'f : eLpNorm f p μ = 0
  · have : (fun x ↦ ∞ * f x) =ᵐ[μ] 0 := by
      filter_upwards [(eLpNorm_eq_zero_iff hp).mp h'f] with x hx using by simp [hx]
    rw [eLpNorm_congr_ae this]
    simp [h'f]






theorem eLpNorm_const_mul_ennreal_of_pos {f : α → ℝ≥0∞} {c : ℝ≥0∞} (hc : 0 < p) :
    eLpNorm (fun x ↦ c * f x) p μ = c * eLpNorm f p μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  by_cases hf : AEStronglyMeasurable f μ
  · apply eLpNorm_const_mul_ennreal hf
  simp [eLpNorm_of_not_aestronglyMeasurable, hf, ENNReal.mul_top hc]
  by_cases h'f : AEStronglyMeasurable (fun x ↦ c * f x) μ; swap
  · simp [eLpNorm_of_not_aestronglyMeasurable, h'f]
  rcases eq_or_ne c ∞ with rfl | h'c; swap
  · apply (hf ?_).elim
    convert (h'f.aemeasurable.const_mul (c⁻¹)).aestronglyMeasurable with x
    rw [← mul_assoc, ENNReal.inv_mul_cancel hc h'c, one_mul]
  let s := (fun x ↦ ∞ * f x) ⁻¹' (Set.Ioi 0)



end ENNReal

end Lp
end MeasureTheory
