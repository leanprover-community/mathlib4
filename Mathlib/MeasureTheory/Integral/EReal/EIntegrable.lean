/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Map


/-!
# TODO

## Main definitions

* `EIntegrable`: A condition ensuring the integral is well-defined (avoiding `⊤ - ⊤`).

## Main statements


-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f g : α → EReal}

/-- Condition for a function to have a well-defined extended integral,
avoiding the `⊤ - ⊤` bad case in the definition. -/
def EIntegrable (f : α → EReal) (μ : Measure α := by volume_tac) : Prop :=
  ∫⁻ x, (f x).toENNReal ∂μ ≠ ⊤ ∨ ∫⁻ x, (-f x).toENNReal ∂μ ≠ ⊤

lemma eintegrable_congr {f g : α → EReal} (h_ae : f =ᵐ[μ] g) :
    EIntegrable f μ ↔ EIntegrable g μ := by
  suffices ∀ {f g : α → EReal} (h_ae : f =ᵐ[μ] g) (hf : EIntegrable f μ), EIntegrable g μ from
    ⟨fun h ↦ this h_ae h, fun h ↦ this h_ae.symm h⟩
  intro f g h_ae hf
  cases hf with
  | inl hf =>
    left
    convert hf using 1
    refine lintegral_congr_ae ?_
    filter_upwards [h_ae] with x hx using by simp [hx]
  | inr hf =>
    right
    convert hf using 1
    refine lintegral_congr_ae ?_
    filter_upwards [h_ae] with x hx using by simp [hx]

lemma eintegrable_of_nonneg {f : α → EReal} (hf : ∀ x, 0 ≤ f x) : EIntegrable f μ := by
  right; simp [hf]

lemma eintegrable_of_nonpos {f : α → EReal} (hf : ∀ x, f x ≤ 0) : EIntegrable f μ := by
  left; simp [hf]

@[simp]
lemma eintegrable_const {μ : Measure α} {c : EReal} : EIntegrable (fun _ ↦ c) μ := by
  rcases le_total c 0 with hc | hc <;> simp [EIntegrable, hc]

@[simp]
lemma eintegrable_zero {μ : Measure α} : EIntegrable 0 μ := by simp [EIntegrable]

lemma EIntegrable.neg {f : α → EReal} (hf : EIntegrable f μ) : EIntegrable (fun x ↦ - f x) μ := by
  cases hf with
  | inl h => right; simpa
  | inr h => left; simpa

lemma EIntegrable.real_const_mul {c : ℝ} {f : α → EReal} (hf : EIntegrable f μ) :
    EIntegrable (fun x ↦ c * f x) μ := by
  rcases le_total 0 c with hc | hc
  · have hc' : 0 ≤ (c : EReal) := by simp [hc]
    cases hf with
    | inl h =>
      left
      simp only [EReal.toENNReal_mul hc', ne_eq, EReal.coe_ne_top, not_false_eq_true,
        EReal.toENNReal_of_ne_top, EReal.toReal_coe]
      rw [lintegral_const_mul' _ _ (by simp)]
      exact ENNReal.mul_ne_top (by simp) h
    | inr h =>
      right
      simp_rw [mul_comm _ (f _), ← EReal.neg_mul, EReal.toENNReal_mul' hc']
      rw [lintegral_mul_const' _ _ (by simp)]
      exact ENNReal.mul_ne_top h (by simp)
  · have hc' : 0 ≤ -(c : EReal) := by simp [hc]
    cases hf with
    | inl h =>
      right
      simp only [ne_eq]
      simp_rw [← EReal.neg_mul, EReal.toENNReal_mul hc']
      rw [lintegral_const_mul' _ _ (by simp)]
      exact ENNReal.mul_ne_top (by simp) h
    | inr h =>
      left
      have h_eq_neg x : c * f x = (-(c : EReal) * -f x) := by simp
      simp_rw [h_eq_neg, EReal.toENNReal_mul hc']
      rw [lintegral_const_mul' _ _ (by simp)]
      exact ENNReal.mul_ne_top (by simp) h

lemma EIntegrable.const_mul {c : EReal} {f : α → EReal}
    (hf : EIntegrable f μ) (hc_bot : c ≠ ⊥) (hc_top : c ≠ ⊤) :
    EIntegrable (fun x ↦ c * f x) μ := by
  lift c to ℝ using ⟨hc_top, hc_bot⟩
  exact hf.real_const_mul

lemma EIntegrable.add_real_const [IsFiniteMeasure μ] {c : ℝ} {f : α → EReal}
    (hf : EIntegrable f μ) :
    EIntegrable (fun x ↦ f x + c) μ := by
  cases hf with
  | inl h =>
    left
    have h' : ∫⁻ x, (f x).toENNReal + ENNReal.ofReal c ∂μ ≠ ∞ := by
      rw [lintegral_add_right _ (by fun_prop)]
      simp only [lintegral_const, ne_eq, ENNReal.add_eq_top, h, false_or]
      exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
    refine ne_top_of_le_ne_top h' ?_
    gcongr with x
    exact EReal.toENNReal_add_le
  | inr h =>
    right
    simp_rw [EReal.neg_add (.inr (by simp : (c : EReal) ≠ ⊤)) (.inr (by simp : (c : EReal) ≠ ⊥))]
    have h' : ∫⁻ x, (-f x).toENNReal + ENNReal.ofReal (-c) ∂μ ≠ ∞ := by
      rw [lintegral_add_right _ (by fun_prop)]
      simp only [lintegral_const, ne_eq, ENNReal.add_eq_top, h, false_or]
      exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
    refine ne_top_of_le_ne_top h' ?_
    gcongr with x
    simp_rw [sub_eq_add_neg]
    exact EReal.toENNReal_add_le

lemma EIntegrable.real_const_add [IsFiniteMeasure μ] {c : ℝ} {f : α → EReal}
    (hf : EIntegrable f μ) :
    EIntegrable (fun x ↦ c + f x) μ := by
  simp_rw [add_comm]
  exact hf.add_real_const

lemma EIntegrable.add_const [IsFiniteMeasure μ] {c : EReal} {f : α → EReal}
    (hf : EIntegrable f μ) (hc_bot : c ≠ ⊥) (hc_top : c ≠ ⊤) :
    EIntegrable (fun x ↦ f x + c) μ := by
  lift c to ℝ using ⟨hc_top, hc_bot⟩
  exact hf.add_real_const

lemma EIntegrable.const_add [IsFiniteMeasure μ] {c : EReal} {f : α → EReal}
    (hf : EIntegrable f μ) (hc_bot : c ≠ ⊥) (hc_top : c ≠ ⊤) :
    EIntegrable (fun x ↦ c + f x) μ := by
  lift c to ℝ using ⟨hc_top, hc_bot⟩
  exact hf.real_const_add

lemma EIntegrable.sub_real_const [IsFiniteMeasure μ] {c : ℝ} {f : α → EReal}
    (hf : EIntegrable f μ) :
    EIntegrable (fun x ↦ f x - c) μ := by
  simp_rw [sub_eq_add_neg]
  exact hf.add_real_const

lemma EIntegrable.sub_const [IsFiniteMeasure μ] {c : EReal} {f : α → EReal}
    (hf : EIntegrable f μ) (hc_bot : c ≠ ⊥) (hc_top : c ≠ ⊤) :
    EIntegrable (fun x ↦ f x - c) μ := by
  simp_rw [sub_eq_add_neg]
  exact hf.add_const (by simp [hc_top]) (by simp [hc_bot])

lemma EIntegrable.real_const_sub [IsFiniteMeasure μ] {c : ℝ} {f : α → EReal}
    (hf : EIntegrable f μ) :
    EIntegrable (fun x ↦ c - f x) μ := by
  simp_rw [sub_eq_add_neg]
  exact hf.neg.real_const_add

lemma EIntegrable.const_sub [IsFiniteMeasure μ] {c : EReal} {f : α → EReal}
    (hf : EIntegrable f μ) (hc_bot : c ≠ ⊥) (hc_top : c ≠ ⊤) :
    EIntegrable (fun x ↦ c - f x) μ := by
  simp_rw [sub_eq_add_neg]
  exact hf.neg.const_add hc_bot hc_top

lemma EIntegrable.smul_measure {X : α → EReal} (hX : EIntegrable X μ) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    EIntegrable X (c • μ) := by
  cases hX with
  | inl hX => left; simp [hc, hX, ENNReal.mul_eq_top]
  | inr hX => right; simp [hc, hX, ENNReal.mul_eq_top]

lemma eintegrable_map {β : Type*} {mβ : MeasurableSpace β} {f : α → β} {g : β → EReal}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g (μ.map f)) :
     EIntegrable g (μ.map f) ↔ EIntegrable (g ∘ f) μ := by
  unfold EIntegrable
  congr!
  · rw [lintegral_map' (by fun_prop) hf]
    rfl
  · rw [lintegral_map' (by fun_prop) hf]
    rfl

lemma eintegrable_of_le {f : α → EReal} {b : EReal} (hf : ∀ x, f x ≤ b) (hb : b ≠ ⊤)
    (P : Measure α) [IsFiniteMeasure P] :
    EIntegrable f P := by
  refine .inl (ne_of_lt ?_)
  calc ∫⁻ x, (f x).toENNReal ∂P
  _ ≤ ∫⁻ x, b.toENNReal ∂P := by
    gcongr
    exact EReal.toENNReal_le_toENNReal (hf _) -- missing gcongr
  _ = b.toENNReal * P .univ := by simp [lintegral_const]
  _ < ⊤ := by simp [hb, lt_top_iff_ne_top, ENNReal.mul_eq_top]

end MeasureTheory
