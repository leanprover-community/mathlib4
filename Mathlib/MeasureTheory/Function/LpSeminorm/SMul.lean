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

open scoped ENNReal NNReal Topology

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

section ENNReal

theorem eLpNorm'_const_mul_ennreal {f : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hq_pos : 0 < q) (hf : AEStronglyMeasurable f μ) :
    eLpNorm' (fun x ↦ c * f x) q μ = c * eLpNorm' f q μ := by
  simp [eLpNorm', lintegral_const_mul'' _ (hf.aemeasurable.pow_const q),
    ENNReal.mul_rpow_of_nonneg (z := q⁻¹) (c ^ q) _ (by simp [hq_pos.le]),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    hq_pos.ne']

theorem eLpNorm_const_mul_ennreal {f : α → ℝ≥0∞} {c : ℝ≥0∞} (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x ↦ c * f x) p μ = c * eLpNorm f p μ := by
  have hcf := (hf.aemeasurable.const_mul c).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp
  · simp [hf, hcf]
  rcases eq_or_ne p ∞ with rfl | hp'
  · simp only [eLpNorm_exponent_top, hf, hcf, eLpNormEssSup, enorm_eq_self, c.essSup_const_mul]
  simp only [eLpNorm_eq_eLpNorm' hp hp', hf, (hf.aemeasurable.const_mul c).aestronglyMeasurable]
  exact eLpNorm'_const_mul_ennreal (ENNReal.toReal_pos hp hp') hf

theorem eLpNorm_const_mul_ennreal_of_pos {f : α → ℝ≥0∞} {c : ℝ≥0∞} (hp : 0 < p) :
    eLpNorm (fun x ↦ c * f x) p μ = c * eLpNorm f p μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  by_cases hf : AEStronglyMeasurable f μ
  · apply eLpNorm_const_mul_ennreal hf
  simp only [hf, not_false_eq_true, eLpNorm_of_not_aestronglyMeasurable, ENNReal.mul_top hc]
  by_cases h'f : AEStronglyMeasurable (fun x ↦ c * f x) μ; swap
  · simp [eLpNorm_of_not_aestronglyMeasurable, h'f]
  rcases eq_or_ne c ∞ with rfl | h'c; swap
  · apply (hf ?_).elim
    convert (h'f.aemeasurable.const_mul (c⁻¹)).aestronglyMeasurable with x
    rw [← mul_assoc, ENNReal.inv_mul_cancel hc h'c, one_mul]
  have : (fun x ↦ ∞ * f x) =  (fun x ↦ ∞ * (∞ * f x)) := by simp [← mul_assoc]
  rw [this, eLpNorm_const_mul_ennreal h'f, ENNReal.top_mul]
  contrapose! hf
  rw [eLpNorm_eq_zero_iff hp.ne'] at hf
  apply h'f.congr
  filter_upwards [hf] with x hx
  simp at hx
  simp [hx]

end ENNReal

section NNReal

variable {ε : Type*} [TopologicalSpace ε] [ENormedAddMonoid ε] [MulActionWithZero ℝ≥0 ε]
  [ContinuousConstSMul ℝ≥0 ε] [ENormSMulClass ℝ≥0 ε]

lemma eLpNorm_const_smul_nnreal {f : α → ε} {c : ℝ≥0} :
    eLpNorm (c • f) p μ = ‖c‖ₑ * eLpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · simpa [enorm_smul, ← eLpNorm_enorm _ (hf.const_smul _), ← eLpNorm_enorm _ hf]
      using eLpNorm_const_mul_ennreal hf.enorm.aestronglyMeasurable
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  simp only [NNReal.enorm_eq_coe, hf, not_false_eq_true, eLpNorm_of_not_aestronglyMeasurable,
    ne_eq, ENNReal.coe_eq_zero, hc, ENNReal.mul_top]
  apply eLpNorm_of_not_aestronglyMeasurable
  rwa [aestronglyMeasurable_const_smul_iff₀ hc (f := f)]

end NNReal

end Lp
end MeasureTheory
