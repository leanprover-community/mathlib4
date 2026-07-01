/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.EReal.AuxLemmas
public import Mathlib.MeasureTheory.Integral.EReal.EIntegrable

/-!
# Extended Real Integral

This file defines integration for functions taking values in `EReal` (the extended reals).

## Main definitions

* `eintegral`: The integral of an `EReal`-valued function, defined as the difference
  between the lower Lebesgue integrals of the positive and negative parts.
* `EIntegrable`: A condition ensuring the integral is well-defined (avoiding `⊤ - ⊤`).
* instances for positive and negative parts of an `EReal`-valued function.

## Main statements

* `eintegral_add`: The integral of a sum is the sum of integrals (under suitable integrability
  conditions to avoid indeterminate forms).
* `eintegral_sub`: The integral of a difference is the difference of integrals (under suitable
  integrability conditions).

## Notation

* `∫ᵉ x, f x ∂μ`: The extended integral of `f` with respect to measure `μ`.
* `f⁺` and `f⁻`: Positive and negative parts of a function.

-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f g : α → EReal}

/-- The integral of an `EReal`-valued function with respect to a measure `μ`, defined as the
difference of two lower Lebesgue integrals. -/
noncomputable def eintegral (μ : Measure α) (f : α → EReal) : EReal :=
    ∫⁻ x, (f x).toENNReal ∂μ - ∫⁻ x, (-f x).toENNReal ∂μ

@[inherit_doc MeasureTheory.eintegral]
notation3 "∫ᵉ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => eintegral μ r

@[inherit_doc MeasureTheory.eintegral]
notation3 "∫ᵉ "(...)", "r:60:(scoped f => eintegral volume f) => r

@[inherit_doc MeasureTheory.eintegral]
notation3 "∫ᵉ "(...)" in "s", "r:60:(scoped f => f)" ∂"μ:70 =>
    eintegral (Measure.restrict μ s) r

@[inherit_doc MeasureTheory.eintegral]
notation3 "∫ᵉ "(...)" in "s", "r:60:(scoped f => eintegral (Measure.restrict volume s) f) => r

@[simp]
lemma eintegral_of_not_eintegrable (hf : ¬ EIntegrable f μ) :
    ∫ᵉ x, f x ∂μ = ⊥ := by
  simp only [EIntegrable, ne_eq, not_or, Decidable.not_not] at hf
  simp [eintegral, hf]

lemma eintegrable_of_eintegral_ne_bot (hf : ∫ᵉ x, f x ∂μ ≠ ⊥) : EIntegrable f μ := by
  contrapose! hf
  exact eintegral_of_not_eintegrable hf

@[simp]
lemma eintegral_zero (μ : Measure α) : ∫ᵉ _, (0 : EReal) ∂μ = 0 := by simp [eintegral]

@[simp]
lemma eintegral_zero_measure (f : α → EReal) : ∫ᵉ x, f x ∂(0 : Measure α) = 0 := by
  simp [eintegral]

lemma eintegral_congr (h : ∀ x, f x = g x) : ∫ᵉ x, f x ∂μ = ∫ᵉ x, g x ∂μ := by
  simp_rw [h]

/-- The extended integral is compatible with almost-everywhere equality. -/
lemma eintegral_congr_ae (h : ∀ᵐ x ∂μ, f x = g x) : ∫ᵉ x, f x ∂μ = ∫ᵉ x, g x ∂μ := by
  simp_rw [eintegral]
  congr 2 <;> exact lintegral_congr_ae <| by filter_upwards [h] with x hx using by rw [hx]

lemma eintegral_of_nonneg (hf : ∀ x, 0 ≤ f x) :
    ∫ᵉ x, f x ∂μ = ∫⁻ x, (f x).toENNReal ∂μ := by
  simp [eintegral, hf]

lemma eintegral_of_ae_nonneg (hf : AEMeasurable f μ)
    (hf_nonneg : ∀ᵐ x ∂μ, 0 ≤ f x) : ∫ᵉ x, f x ∂μ = ∫⁻ x, (f x).toENNReal ∂μ := by
  rw [eintegral]
  suffices ∫⁻ x, (-f x).toENNReal ∂μ = 0 by simp [this]
  rw [lintegral_eq_zero_iff']
  · filter_upwards [hf_nonneg] with x hx using by simp [hx]
  · fun_prop

lemma eintegral_of_nonpos (hf : ∀ x, f x ≤ 0) :
    ∫ᵉ x, f x ∂μ = - ∫⁻ x, (-f x).toENNReal ∂μ := by
  simp [eintegral, hf]

lemma eintegral_of_ae_nonpos (hf : AEMeasurable f μ)
    (hf_nonpos : ∀ᵐ x ∂μ, f x ≤ 0) : ∫ᵉ x, f x ∂μ = - ∫⁻ x, (-f x).toENNReal ∂μ := by
  rw [eintegral]
  suffices ∫⁻ x, (f x).toENNReal ∂μ = 0 by simp [this]
  rw [lintegral_eq_zero_iff']
  · filter_upwards [hf_nonpos] with x hx using by simp [hx]
  · fun_prop

lemma eintegral_nonneg (hf : ∀ x, 0 ≤ f x) : 0 ≤ ∫ᵉ x, f x ∂μ := by
  rw [eintegral_of_nonneg hf]
  positivity

lemma eintegral_nonneg' (hf_meas : AEMeasurable f μ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x) :
    0 ≤ ∫ᵉ x, f x ∂μ := by
  rw [eintegral_of_ae_nonneg hf_meas hf]
  positivity

lemma eintegral_nonpos (hf : ∀ x, f x ≤ 0) : ∫ᵉ x, f x ∂μ ≤ 0 := by
  rw [eintegral_of_nonpos hf]
  simp only [EReal.neg_le_zero]
  positivity

lemma eintegral_nonpos' (hf_meas : AEMeasurable f μ) (hf : ∀ᵐ x ∂μ, f x ≤ 0) :
    ∫ᵉ x, f x ∂μ ≤ 0 := by
  rw [eintegral_of_ae_nonpos hf_meas hf]
  simp only [EReal.neg_le_zero]
  positivity

@[simp]
lemma eintegral_const (c : EReal) (μ : Measure α) : ∫ᵉ _, c ∂μ = c * (μ Set.univ : EReal) := by
  rcases le_total 0 c with hc | hc
  · rw [eintegral_of_nonneg (fun _ ↦ hc)]
    simp only [lintegral_const, EReal.coe_ennreal_mul]
    rw [EReal.coe_toENNReal hc]
  · rw [eintegral_of_nonpos (fun _ ↦ hc)]
    simp only [lintegral_const, EReal.coe_ennreal_mul]
    rw [EReal.coe_toENNReal]
    · simp
    · exact EReal.neg_nonneg.mpr hc

lemma eintegral_lt_top_of_le {f : α → EReal} {b : EReal} (hf : ∀ x, f x ≤ b) (hb : b ≠ ⊤)
    (P : Measure α) [IsFiniteMeasure P] :
    ∫ᵉ x, f x ∂P < ⊤ := by
  rw [eintegral]
  calc (∫⁻ x, (f x).toENNReal ∂P : EReal) - ∫⁻ x, (-f x).toENNReal ∂P
  _ ≤ ∫⁻ x, (f x).toENNReal ∂P - 0 := EReal.sub_le_sub le_rfl (by positivity)
  _ ≤ ∫⁻ x, b.toENNReal ∂P := by
    simp only [sub_zero]
    refine EReal.coe_ennreal_le_coe_ennreal_iff.mpr ?_ -- missing gcongr
    gcongr
    exact EReal.toENNReal_le_toENNReal (hf _)
  _ = b.toENNReal * P .univ := by simp [lintegral_const]
  _ < ⊤ := by
    norm_cast
    rw [lt_top_iff_ne_top, ne_eq, EReal.coe_ennreal_eq_top_iff]
    simp [hb, ENNReal.mul_eq_top]

lemma setEIntegral_measure_zero {μ : Measure α} (s : Set α) (f : α → EReal) (hs' : μ s = 0) :
    ∫ᵉ x in s, f x ∂μ = 0 := by
  simp [eintegral, setLIntegral_measure_zero s _ hs']

/-- The extended integral is monotone with respect to almost-everywhere inequality. -/
lemma eintegral_mono_ae (hfg : f ≤ᵐ[μ] g) : ∫ᵉ x, f x ∂μ ≤ ∫ᵉ x, g x ∂μ := by
  refine EReal.sub_le_sub ?_ ?_
  · rw [EReal.coe_ennreal_le_coe_ennreal_iff]
    refine lintegral_mono_ae ?_
    filter_upwards [hfg] with x hfgx
    exact EReal.toENNReal_le_toENNReal hfgx
  · rw [EReal.coe_ennreal_le_coe_ennreal_iff]
    refine lintegral_mono_ae ?_
    filter_upwards [hfg] with x hfgx
    rw [← EReal.neg_le_neg_iff] at hfgx
    exact EReal.toENNReal_le_toENNReal hfgx

@[gcongr]
lemma eintegral_mono (hfg : f ≤ g) : ∫ᵉ x, f x ∂μ ≤ ∫ᵉ x, g x ∂μ :=
  eintegral_mono_ae <| ae_of_all _ hfg

-- TODO: rename
lemma eintegral_neg_eq_top_eq_bot (hf_neg_top : ∫⁻ x, (-f x).toENNReal ∂μ = ⊤) :
    ∫ᵉ x, f x ∂μ = ⊥ := by
  simp [eintegral, hf_neg_top]

/-- The extended integral is strictly monotone with respect to almost-everywhere strict
inequality. -/
lemma eintegral_strict_mono_ae (hμ : μ ≠ 0) (hg : AEMeasurable g μ) (hf : AEMeasurable f μ)
    (hfg : ∀ᵐ x ∂μ, f x < g x) (hfi : ∫ᵉ x, f x ∂μ < ⊤) (hgi : ∫ᵉ x, g x ∂μ ≠ ⊥) :
    ∫ᵉ x, f x ∂μ < ∫ᵉ x, g x ∂μ := by
  by_cases hg_top : ∫ᵉ x, g x ∂μ = ⊤
  · simpa [hg_top]
  by_cases hf_neg_top : ∫⁻ x, (-f x).toENNReal ∂μ = ⊤
  · have := eintegral_neg_eq_top_eq_bot hf_neg_top
    simp_all only [bot_lt_top, gt_iff_lt]
    exact Ne.bot_lt' hgi.symm
  obtain ⟨s, hμs, h_cases⟩ : ∃ s, μ s ≠ 0 ∧
      ((∀ ⦃x⦄, x ∈ s → 0 ≤ f x ∧ f x < g x) ∨
      (∀ ⦃x⦄, x ∈ s → g x ≤ 0 ∧ f x < g x) ∨
      (∀ ⦃x⦄, x ∈ s → f x < 0 ∧ 0 < g x ∧ f x < g x)) := by
    let S := {x | f x < g x}
    let S₁ := S ∩ {x | 0 ≤ f x}
    let S₂ := S ∩ {x | g x ≤ 0}
    let S₃ := S ∩ {x | f x < 0 ∧ 0 < g x}
    have : μ S₁ ≠ 0 ∨ μ S₂ ≠ 0 ∨ μ S₃ ≠ 0 := by
      by_contra! h_zero
      have : 0 < μ (S₁ ∪ S₂ ∪ S₃) := by
        have hS_eq_union : S = S₁ ∪ S₂ ∪ S₃ := by ext; grind
        rw [← hS_eq_union]
        refine pos_of_ne_zero ?_
        rw [measure_of_measure_compl_eq_zero hfg]
        exact μ.measure_univ_ne_zero.mpr hμ
      have : μ (S₁ ∪ S₂ ∪ S₃) ≤ 0 := by
        calc
        _ ≤ μ (S₁ ∪ S₂) + μ S₃ := measure_union_le _ _
        _ ≤ μ S₁ + μ S₂ + μ S₃ := by
          gcongr
          exact measure_union_le _ _
        _ = 0 := by simp [h_zero]
      grind
    rcases this with hμ1 | hμ2 | hμ3
    · exact ⟨S₁, hμ1, by grind⟩
    · exact ⟨S₂, hμ2, by grind⟩
    · exact ⟨S₃, hμ3, by grind⟩
  simp only [eintegral]
  rcases h_cases with h_pos | h_neg | h_mixed
  · refine EReal.sub_lt_sub_of_lt_of_le ?_ ?_ (by simp) (by simpa)
    · norm_cast
      refine lintegral_strict_mono_of_ae_le_of_ae_lt_on (by fun_prop) ?_ ?_ hμs ?_
      · by_contra!
        simp_all [eintegral]
      · filter_upwards [hfg] with x hx
        exact EReal.toENNReal_le_toENNReal hx.le
      · filter_upwards with x hxs
        exact EReal.toENNReal_lt_toENNReal (h_pos hxs).1 (h_pos hxs).2
    · norm_cast
      refine lintegral_mono_ae ?_
      filter_upwards [hfg] with x hx
      refine EReal.toENNReal_le_toENNReal ?_
      exact EReal.neg_le_neg_iff.mpr hx.le
  · refine EReal.sub_lt_sub_of_le_of_lt ?_ ?_ ?_ (by simp)
    · norm_cast
      refine lintegral_mono_ae ?_
      filter_upwards [hfg] with x hx
      exact EReal.toENNReal_le_toENNReal hx.le
    · norm_cast
      refine lintegral_strict_mono_of_ae_le_of_ae_lt_on (by fun_prop) ?_ ?_ hμs ?_
      · by_contra!
        simp_all [eintegral]
      · filter_upwards [hfg] with x hx
        refine EReal.toENNReal_le_toENNReal ?_
        exact EReal.neg_le_neg_iff.mpr hx.le
      · filter_upwards with x hxs
        refine EReal.toENNReal_lt_toENNReal ?_ ?_
        · exact EReal.neg_nonneg.mpr (h_neg hxs).1
        · exact EReal.neg_lt_neg_iff.mpr (h_neg hxs).2
    · by_contra! h
      simp_all only [ne_eq, eintegral, EReal.coe_ennreal_eq_top_iff]
      cases EReal.top_sub_eq_top_or_bot (a := ∫⁻ (x : α), (-g x).toENNReal ∂μ) <;> simp_all
  · refine EReal.sub_lt_sub_of_lt_of_le ?_ ?_ (by simp) (by simpa)
    · norm_cast
      refine lintegral_strict_mono_of_ae_le_of_ae_lt_on (by fun_prop) ?_ ?_ hμs ?_
      · by_contra!
        simp_all [eintegral]
      · filter_upwards [hfg] with x hx
        exact EReal.toENNReal_le_toENNReal hx.le
      · filter_upwards with x hxs
        specialize h_mixed hxs
        have : f x ≤ 0 := h_mixed.1.le
        simp_all
    · norm_cast
      refine lintegral_mono_ae ?_
      filter_upwards [hfg] with x hx
      refine EReal.toENNReal_le_toENNReal ?_
      exact EReal.neg_le_neg_iff.mpr hx.le

lemma eintegral_strict_mono (hμ : μ ≠ 0) (hg : AEMeasurable g μ) (hf : AEMeasurable f μ)
    (hfg : ∀ x, f x < g x) (hfi : ∫ᵉ x, f x ∂μ < ⊤) (hgi : ∫ᵉ x, g x ∂μ ≠ ⊥) :
    ∫ᵉ x, f x ∂μ < ∫ᵉ x, g x ∂μ :=
  eintegral_strict_mono_ae hμ hg hf (ae_of_all μ hfg) hfi hgi

lemma eintegral_add_compl {A : Set α} (hA : MeasurableSet A) :
    ∫ᵉ x in A, f x ∂μ + ∫ᵉ x in Aᶜ, f x ∂μ = ∫ᵉ x, f x ∂μ := by
  simp only [eintegral]
  symm
  rw [← lintegral_add_compl (f := fun x ↦ (f x).toENNReal) hA,
    ← lintegral_add_compl (f := fun x ↦ (-f x).toENNReal) hA]
  push_cast
  rw [EReal.add_sub_add_comm (by simp) (by simp)]

lemma ae_ne_bot_of_eintegral_ne_bot (hf_meas : AEMeasurable f μ) (hf : ∫ᵉ x, f x ∂μ ≠ ⊥) :
    ∀ᵐ x ∂μ, f x ≠ ⊥ := by
  rw [eintegral, sub_eq_add_neg, ne_eq, EReal.add_eq_bot_iff] at hf
  simp only [EReal.coe_ennreal_ne_bot, EReal.neg_eq_bot_iff, EReal.coe_ennreal_eq_top_iff,
    false_or] at hf
  have h := ae_lt_top' (by fun_prop) hf
  filter_upwards [h] with x hx
  rw [lt_top_iff_ne_top, ne_eq, EReal.toENNReal_eq_top_iff] at hx
  simpa using hx

lemma eintegral_sub_of_nonneg_of_eq_zero (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (h_or : ∀ x, f x = 0 ∨ g x = 0) :
    ∫ᵉ x, f x - g x ∂μ = ∫ᵉ x, f x ∂μ - ∫ᵉ x, g x ∂μ := by
  simp_rw [eintegral_of_nonneg hf, eintegral_of_nonneg hg, eintegral]
  congr with x
  · cases h_or x with
    | inl h =>
      simp only [h, zero_sub, ne_eq, EReal.zero_ne_top, not_false_eq_true,
        EReal.toENNReal_of_ne_top, EReal.toReal_zero, ENNReal.ofReal_zero]
      rw [EReal.toENNReal_of_nonpos]
      simp [hg x]
    | inr h => simp [h]
  · by_cases hg_top : g x = ⊤
    · simp [hg_top]
    rw [EReal.neg_sub]
    · cases h_or x with
      | inl h => simp [h]
      | inr h =>
        simp only [h, add_zero, ne_eq, EReal.zero_ne_top, not_false_eq_true,
          EReal.toENNReal_of_ne_top, EReal.toReal_zero, ENNReal.ofReal_zero]
        rw [EReal.toENNReal_of_nonpos]
        simp [hf x]
    · left
      specialize hf x
      intro h_false
      simp [h_false] at hf
    · exact .inr hg_top

lemma eintegral_sub_of_nonneg_of_eq_zero_ae (hf : ∀ᵐ x ∂μ, 0 ≤ f x) (hg : ∀ᵐ x ∂μ, 0 ≤ g x)
    (h_or : ∀ᵐ x ∂μ, f x = 0 ∨ g x = 0) :
    ∫ᵉ x, f x - g x ∂μ = ∫ᵉ x, f x ∂μ - ∫ᵉ x, g x ∂μ := by
  let f' := fun x ↦ if (0 ≤ f x ∧ 0 ≤ g x ∧ (f x = 0 ∨ g x = 0)) then f x else 0
  let g' := fun x ↦ if (0 ≤ f x ∧ 0 ≤ g x ∧ (f x = 0 ∨ g x = 0)) then g x else 0
  have hf' x : 0 ≤ f' x := by simp only [f']; split_ifs with h <;> simp [h]
  have hg' x : 0 ≤ g' x := by simp only [g']; split_ifs with h <;> simp [h]
  have h_or' x : f' x = 0 ∨ g' x = 0 := by
    simp only [f', g']; split_ifs with h <;> simp [h]
  have hf_eq : ∀ᵐ x ∂μ, f x = f' x := by
    filter_upwards [hf, hg, h_or] with x hf_x hg_x h_or_x
    simp [f', hf_x, hg_x, h_or_x]
  have hg_eq : ∀ᵐ x ∂μ, g x = g' x := by
    filter_upwards [hf, hg, h_or] with x hf_x hg_x h_or_x
    simp [g', hf_x, hg_x, h_or_x]
  have hf_sub_g : ∀ᵐ x ∂μ, f x - g x = f' x - g' x := by
    filter_upwards [hf_eq, hg_eq] with x hfx hgx
    rw [hfx, hgx]
  rw [eintegral_congr_ae hf_eq, eintegral_congr_ae hg_eq, eintegral_congr_ae hf_sub_g,
    eintegral_sub_of_nonneg_of_eq_zero hf' hg' h_or']

/-- The extended integral decomposes as the difference between the integrals of the positive
and negative parts of the function. -/
lemma eintegral_eq_posPartFun_sub_negPartFun (f : α → EReal) :
    ∫ᵉ x, f x ∂μ = ∫ᵉ x, f⁺ x ∂μ - ∫ᵉ x, f⁻ x ∂μ := by
  rw [← eintegral_sub_of_nonneg_of_eq_zero (posPartFun_nonneg f) (negPartFun_nonneg f)
      (posPartFun_eq_zero_or_negPartFun_eq_zero f)]
  simp_rw [← posPartFun_sub_negPartFun f]

lemma EIntegrable.eintegral_posPartFun_ne_top_or_eintegral_negPartFun_ne_top
    (hf : EIntegrable f μ) :
    ∫ᵉ x, f⁺ x ∂μ ≠ ⊤ ∨ ∫ᵉ x, f⁻ x ∂μ ≠ ⊤ := by
  rcases hf with h | h
  · left
    rw [eintegral_of_nonneg (posPartFun_nonneg f)]
    simp only [ne_eq, EReal.coe_ennreal_eq_top_iff, posPartFun_def]
    convert h using 4 with x
    rcases le_total 0 (f x) with h | h <;> simp [h]
  · right
    rw [eintegral_of_nonneg (negPartFun_nonneg f)]
    simp only [ne_eq, EReal.coe_ennreal_eq_top_iff, negPartFun_def]
    convert h using 4 with x
    rcases le_total 0 (f x) with h | h <;> simp [h]

lemma eintegral_negPartFun_ne_top (hf_bot : ∫ᵉ x, f x ∂μ ≠ ⊥) :
    ∫ᵉ x, f⁻ x ∂μ ≠ ⊤ := by
  rw [eintegral_eq_posPartFun_sub_negPartFun, sub_eq_add_neg, ne_eq, EReal.add_eq_bot_iff] at hf_bot
  simp only [EReal.neg_eq_bot_iff, not_or] at hf_bot
  exact hf_bot.2

lemma eintegral_posPartFun_ne_top (hf_bot : ∫ᵉ x, f x ∂μ ≠ ⊥) (hf_top : ∫ᵉ x, f x ∂μ ≠ ⊤) :
    ∫ᵉ x, f⁺ x ∂μ ≠ ⊤ := by
  by_contra h
  rw [eintegral_eq_posPartFun_sub_negPartFun, h, EReal.top_sub] at hf_top
  · exact hf_top rfl
  · exact eintegral_negPartFun_ne_top hf_bot

lemma ae_ne_top_of_eintegral_ne_top (hf_meas : AEMeasurable f μ) (hf_bot : ∫ᵉ x, f x ∂μ ≠ ⊥)
    (hf_top : ∫ᵉ x, f x ∂μ ≠ ⊤) :
    ∀ᵐ x ∂μ, f x ≠ ⊤ := by
  suffices ∀ᵐ x ∂μ, f⁺ x < ⊤ by
    filter_upwards [this] with x hfx using by simpa [posPartFun_def, lt_top_iff_ne_top] using hfx
  have h_pos_ne_top : ∫ᵉ x, f⁺ x ∂μ ≠ ⊤ := eintegral_posPartFun_ne_top hf_bot hf_top
  rw [eintegral_of_nonneg (posPartFun_nonneg f), ne_eq, EReal.coe_ennreal_eq_top_iff]
    at h_pos_ne_top
  have h_lt_top : ∀ᵐ x ∂μ, (f⁺ x).toENNReal < ⊤ := ae_lt_top' (by fun_prop) h_pos_ne_top
  filter_upwards [h_lt_top] with x hx
  rwa [lt_top_iff_ne_top, ne_eq, EReal.toENNReal_eq_top_iff, ← ne_eq, ← lt_top_iff_ne_top] at hx

lemma lintegral_enorm_eq_posPartFun_add_negPartFun (hf : AEMeasurable f μ) :
    ∫⁻ x, ‖f x‖ₑ ∂μ = ∫ᵉ x, f⁺ x ∂μ + ∫ᵉ x, f⁻ x ∂μ := by
  simp_rw [enorm]
  rw [lintegral_add_left' (by fun_prop), eintegral_of_nonneg (posPartFun_nonneg f),
    eintegral_of_nonneg (negPartFun_nonneg f)]
  norm_cast

lemma eintegral_eq_lintegral (f : α → ℝ≥0∞) : ∫ᵉ x, f x ∂μ = ∫⁻ x, f x ∂μ := by
  rw [eintegral_of_nonneg (fun _ ↦ by positivity)]
  simp

lemma lintegral_eq_eintegral (f : α → ℝ≥0∞) : ∫⁻ x, f x ∂μ = (∫ᵉ x, f x ∂μ).toENNReal := by
  rw [eintegral_of_nonneg (fun _ ↦ by positivity)]
  simp

lemma eintegral_real_const_mul_of_nonneg (c : ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∫ᵉ x, c * f x ∂μ = c * ∫ᵉ x, f x ∂μ := by
  rcases le_total 0 c with hc | hc
  · have hc' : 0 ≤ (c : EReal) := mod_cast hc
    rw [eintegral_of_nonneg (fun x ↦ mul_nonneg hc' (hf x)), eintegral_of_nonneg hf]
    simp_rw [EReal.toENNReal_mul hc']
    simp only [ne_eq, EReal.coe_ne_top, not_false_eq_true, EReal.toENNReal_of_ne_top,
      EReal.toReal_coe]
    rw [lintegral_const_mul' _ _ (by simp)]
    simp [hc]
  · have hc' : (c : EReal) ≤ 0 := mod_cast hc
    rw [eintegral_of_nonpos, eintegral_of_nonneg hf]
    swap; · exact fun x ↦ EReal.mul_nonpos_iff.mpr <| by simp [hc, hf]
    have : 0 ≤ - (c : EReal) := by simp [hc']
    simp_rw [← EReal.neg_mul, EReal.toENNReal_mul this]
    simp only [ne_eq, EReal.neg_eq_top_iff, EReal.coe_ne_bot, not_false_eq_true,
      EReal.toENNReal_of_ne_top]
    rw [lintegral_const_mul' _ _ (by simp)]
    simp [hc]

lemma eintegral_real_const_mul (c : ℝ) (hf : EIntegrable f μ) :
    ∫ᵉ x, c * f x ∂μ = c * ∫ᵉ x, f x ∂μ := by
  simp_rw [eintegral_eq_posPartFun_sub_negPartFun f, ← posPartFun_sub_negPartFun f,
    EReal.mul_sub_of_eq_zero (posPartFun_eq_zero_or_negPartFun_eq_zero f _)]
  rcases le_total 0 c with hc | hc
  · have hc' : 0 ≤ (c : EReal) := mod_cast hc
    rw [eintegral_sub_of_nonneg_of_eq_zero (fun x ↦ ?_) (fun x ↦ ?_) (fun x ↦ ?_),
      eintegral_real_const_mul_of_nonneg _ (by simp),
      eintegral_real_const_mul_of_nonneg _ (by simp)]
    · rw [EReal.mul_sub_of_nonneg_of_ne_top hc' (by simp)]
    · have : 0 ≤ f⁺ x := posPartFun_nonneg f x
      positivity
    · have : 0 ≤ f⁻ x := negPartFun_nonneg f x
      positivity
    · rcases posPartFun_eq_zero_or_negPartFun_eq_zero f x with h | h <;> simp [h]
  · have hc' : (c : EReal) ≤ 0 := mod_cast hc
    have h_sub x : c * f⁺ x - c * f⁻ x = (-c) * f⁻ x - (-c) * f⁺ x := by
      rw [EReal.neg_mul, EReal.neg_mul, sub_eq_add_neg, sub_eq_add_neg, add_comm, neg_neg]
    simp_rw [h_sub]
    rw [eintegral_sub_of_nonneg_of_eq_zero]
    rotate_left
    · intro x
      rw [EReal.mul_nonneg_iff]
      simp [hc, negPartFun_nonneg f x]
    · intro x
      rw [EReal.mul_nonneg_iff]
      simp [hc, posPartFun_nonneg f x]
    · intro x
      rcases posPartFun_eq_zero_or_negPartFun_eq_zero f x with h | h <;> simp [h]
    simp_rw [← EReal.coe_neg]
    rw [eintegral_real_const_mul_of_nonneg _ (by simp),
      eintegral_real_const_mul_of_nonneg _ (by simp)]
    · conv_rhs => rw [← neg_neg (c : EReal), neg_mul]
      rw [EReal.mul_sub_of_nonneg_of_ne_top (by simp [hc]) (by simp)]
      suffices ∀ (a b : EReal), 0 ≤ a → 0 ≤ b → (a ≠ ⊤ ∨ b ≠ ⊤) →
          -c * b - -c * a = -(-c * a - -c * b) from
        this _ _ (eintegral_nonneg (by simp)) (eintegral_nonneg (by simp))
          hf.eintegral_posPartFun_ne_top_or_eintegral_negPartFun_ne_top
      rcases eq_or_lt_of_le hc with rfl | hc
      · simp
      intro a b ha hb h_or
      cases a <;> cases b
      · simp at ha
      · simp at ha
      · simp at ha
      · simp at hb
      · rw [EReal.neg_sub, sub_eq_add_neg, neg_mul, neg_mul, neg_neg, add_comm]
        · left
          rw [neg_mul, ← EReal.coe_mul]
          simp only [ne_eq, EReal.neg_eq_bot_iff]
          exact EReal.coe_ne_top _
        · left
          rw [neg_mul, ← EReal.coe_mul]
          exact EReal.coe_ne_top _
      · rw [EReal.mul_top_of_pos (by simp [hc]), EReal.top_sub, EReal.sub_top, EReal.neg_bot]
        rw [neg_mul, ← EReal.coe_mul]
        simp only [EReal.coe_mul, ne_eq, EReal.neg_eq_top_iff]
        exact EReal.coe_ne_bot _
      · simp at hb
      · rw [EReal.mul_top_of_pos (by simp [hc]), EReal.sub_top, EReal.top_sub, EReal.neg_top]
        rw [neg_mul, ← EReal.coe_mul]
        exact EReal.coe_ne_top _
      · simp at h_or

lemma eintegral_const_mul {c : EReal} (hc_bot : c ≠ ⊥) (hc_top : c ≠ ⊤) (hf : EIntegrable f μ) :
    ∫ᵉ x, c * f x ∂μ = c * ∫ᵉ x, f x ∂μ := by
  lift c to ℝ using ⟨hc_top, hc_bot⟩ with c
  exact eintegral_real_const_mul c hf

lemma eintegral_neg (hf : EIntegrable f μ) :
    ∫ᵉ x, -f x ∂μ = - ∫ᵉ x, f x ∂μ := by
  have h₁ : ∀ x, -f x = (-1 : EReal) * f x := fun _ ↦ (neg_one_mul _).symm
  simp_rw [h₁]
  rw [eintegral_const_mul (by norm_cast) (by norm_cast) hf]
  simp

lemma eintegral_add_of_nonneg (hf_meas : AEMeasurable f μ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    ∫ᵉ x, f x + g x ∂μ = ∫ᵉ x, f x ∂μ + ∫ᵉ x, g x ∂μ := by
  rw [eintegral_of_nonneg (fun x ↦ add_nonneg (hf x) (hg x)),
    eintegral_of_nonneg hf, eintegral_of_nonneg hg, ← EReal.coe_ennreal_add,
    ← lintegral_add_left' (by fun_prop)]
  simp_rw [EReal.toENNReal_add (hf _) (hg _)]

lemma eintegral_add_of_nonneg_of_measurable'
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x) (hg : ∀ᵐ x ∂μ, 0 ≤ g x) :
    ∫ᵉ x, f x + g x ∂μ = ∫ᵉ x, f x ∂μ + ∫ᵉ x, g x ∂μ := by
  let f' := fun x ↦ if (0 ≤ f x ∧ 0 ≤ g x) then f x else 0
  let g' := fun x ↦ if (0 ≤ f x ∧ 0 ≤ g x) then g x else 0
  have hf' x : 0 ≤ f' x := by simp only [f']; split_ifs with h <;> simp [h]
  have hg' x : 0 ≤ g' x := by simp only [g']; split_ifs with h <;> simp [h]
  have hf_eq : ∀ᵐ x ∂μ, f x = f' x := by
    filter_upwards [hf, hg] with x hf_x hg_x using by simp [f', hf_x, hg_x]
  have hg_eq : ∀ᵐ x ∂μ, g x = g' x := by
    filter_upwards [hf, hg] with x hf_x hg_x using by simp [g', hf_x, hg_x]
  have hf_add_g : ∀ᵐ x ∂μ, f x + g x = f' x + g' x := by
    filter_upwards [hf_eq, hg_eq] with x hfx hgx
    rw [hfx, hgx]
  rw [eintegral_congr_ae hf_eq, eintegral_congr_ae hg_eq, eintegral_congr_ae hf_add_g,
    eintegral_add_of_nonneg _ hf' hg']
  refine (Measurable.ite ?_ hf_meas measurable_const).aemeasurable
  exact MeasurableSet.inter (measurableSet_le measurable_const hf_meas)
    (measurableSet_le measurable_const hg_meas)

lemma eintegral_add_of_nonneg_ae (hf_meas : AEMeasurable f μ) (hg_meas : AEMeasurable g μ)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x) (hg : ∀ᵐ x ∂μ, 0 ≤ g x) :
    ∫ᵉ x, f x + g x ∂μ = ∫ᵉ x, f x ∂μ + ∫ᵉ x, g x ∂μ := by
  rw [eintegral_congr_ae hf_meas.ae_eq_mk, eintegral_congr_ae hg_meas.ae_eq_mk,
    ← eintegral_add_of_nonneg_of_measurable' hf_meas.measurable_mk hg_meas.measurable_mk]
  · refine eintegral_congr_ae ?_
    filter_upwards [hf_meas.ae_eq_mk, hg_meas.ae_eq_mk] with x hfx hgx using by rw [hfx, hgx]
  · filter_upwards [hf_meas.ae_eq_mk, hf] with x hfx hfx_nonneg using by rwa [← hfx]
  · filter_upwards [hg_meas.ae_eq_mk, hg] with x hgx hgx_nonneg using by rwa [← hgx]

lemma eintegral_sub_of_nonneg (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hf_meas : AEMeasurable f μ) (hg_meas : AEMeasurable g μ)
    (hfg : ∫ᵉ x, min (f x) (g x) ∂μ ≠ ⊤) :
    ∫ᵉ x, f x - g x ∂μ = ∫ᵉ x, f x ∂μ - ∫ᵉ x, g x ∂μ := by
  have hf_ne_bot x : f x ≠ ⊥ := fun h_false ↦ by simpa [h_false] using hf x
  have hg_ne_bot x : g x ≠ ⊥ := fun h_false ↦ by simpa [h_false] using hg x
  by_cases hg_top : ∀ᵐ x ∂μ, g x ≠ ⊤
  swap
  · -- right side is `⊥`
    have h_imp : ∫ᵉ x, -g x ∂μ ≠ ⊥ → ∀ᵐ x ∂μ, -g x ≠ ⊥ := ae_ne_bot_of_eintegral_ne_bot hg_meas.neg
    rw [← not_imp_not] at h_imp
    simp only [ne_eq, EReal.neg_eq_bot_iff, Decidable.not_not] at h_imp
    specialize h_imp hg_top
    rw [eintegral_neg] at h_imp
    swap; · exact eintegrable_of_nonneg hg
    rw [sub_eq_add_neg, h_imp, EReal.add_bot]
    -- left side is also `⊥`
    have h_imp' : ∫ᵉ x, f x - g x ∂μ ≠ ⊥ → ∀ᵐ x ∂μ, f x - g x ≠ ⊥ :=
      ae_ne_bot_of_eintegral_ne_bot (hf_meas.sub hg_meas)
    rw [← not_imp_not] at h_imp'
    simp only [ne_eq, Filter.not_eventually, Decidable.not_not] at h_imp'
    refine h_imp' ?_
    simp only [ne_eq, Filter.not_eventually, Decidable.not_not] at hg_top
    exact hg_top.mono fun x hx ↦ by simp [hx]
  let f' := fun x ↦ f x - min (f x) (g x)
  let g' := fun x ↦ g x - min (f x) (g x)
  have hf' : ∀ᵐ x ∂μ, 0 ≤ f' x := by
    filter_upwards [hg_top] with x hgx
    unfold f'
    rw [EReal.sub_nonneg (by simp [hgx]) (by simp [hf_ne_bot])]
    simp
  have hg' : ∀ᵐ x ∂μ, 0 ≤ g' x := by
    filter_upwards [hg_top] with x hgx
    unfold g'
    rw [EReal.sub_nonneg (by simp [hgx]) (by simp [hg_ne_bot])]
    simp
  have hf_eq : ∀ᵐ x ∂μ, f x = f' x + min (f x) (g x) := by
    unfold f'
    filter_upwards [hg_top] with x hgx
    rcases le_total (f x) (g x) with h | h
    · simp only [h, inf_of_le_left]
      rw [EReal.sub_self (ne_top_of_le_ne_top hgx h) (hf_ne_bot x), zero_add]
    · simp only [h, inf_of_le_right]
      lift g x to ℝ using ⟨hgx, hg_ne_bot x⟩ with gx
      rw [EReal.sub_add_cancel]
  have hg_eq : ∀ᵐ x ∂μ, g x = g' x + min (f x) (g x) := by
    unfold g'
    filter_upwards [hg_top] with x hgx
    rcases le_total (f x) (g x) with h | h
    · simp only [h, inf_of_le_left]
      lift f x to ℝ using ⟨ne_top_of_le_ne_top hgx h, hf_ne_bot x⟩ with gx
      rw [EReal.sub_add_cancel]
    · simp only [h, inf_of_le_right]
      rw [EReal.sub_self hgx (hg_ne_bot x), zero_add]
  have h_or : ∀ᵐ x ∂μ, f' x = 0 ∨ g' x = 0 := by
    filter_upwards [hg_top] with x hgx
    unfold f' g'
    rcases le_total (f x) (g x) with h | h
    · left
      simp only [h, inf_of_le_left]
      rw [EReal.sub_self _ (hf_ne_bot x)]
      exact ne_top_of_le_ne_top hgx h
    · right
      simp only [h, inf_of_le_right]
      rw [EReal.sub_self hgx (hg_ne_bot x)]
  have hf_sub_g : ∀ᵐ x ∂μ, f x - g x = f' x - g' x := by
    filter_upwards [hg_top] with x hgx
    unfold f' g'
    rcases le_total (f x) (g x) with h | h
    · simp only [h, inf_of_le_left]
      rw [EReal.sub_self, zero_sub, EReal.neg_sub, add_comm, ← sub_eq_add_neg]
      · simp [hf_ne_bot x]
      · simp [hgx]
      · exact ne_top_of_le_ne_top hgx h
      · exact hf_ne_bot x
    · simp [h, inf_of_le_right, EReal.sub_self hgx (hg_ne_bot x)]
  rw [eintegral_congr_ae hf_sub_g, eintegral_congr_ae hf_eq, eintegral_congr_ae hg_eq,
    eintegral_sub_of_nonneg_of_eq_zero_ae hf' hg' h_or,
    eintegral_add_of_nonneg_ae (by fun_prop) (by fun_prop) hg',
    eintegral_add_of_nonneg_ae (by fun_prop) (by fun_prop) hf']
  rotate_left
  · filter_upwards with x using by simp [hf, hg]
  · filter_upwards with x using by simp [hf, hg]
  rw [EReal.add_sub_add]
  rotate_left
  · refine EReal.ne_bot_of_nonneg <| eintegral_nonneg' ?_ hg'
    simp only [g']; fun_prop
  · exact EReal.ne_bot_of_nonneg <| eintegral_nonneg (by simp [hf, hg])
  rw [EReal.sub_self hfg]
  · simp
  · exact EReal.ne_bot_of_nonneg <| eintegral_nonneg (by simp [hf, hg])

/-- The extended integral of the difference of two ENNReal-valued functions (coerced to EReal) is
the difference of their Lebesgue integrals, provided at least one of the integrals is finite. -/
lemma eintegral_coe_ennreal_sub {u v : α → ℝ≥0∞} (hu : AEMeasurable u μ) (hv : AEMeasurable v μ)
    (h : ∫⁻ x, u x ∂μ ≠ ⊤ ∨ ∫⁻ x, v x ∂μ ≠ ⊤) :
    ∫ᵉ x, u x - v x ∂μ = ∫⁻ x, u x ∂μ - ∫⁻ x, v x ∂μ := by
  rw [eintegral_sub_of_nonneg (fun _ ↦ by positivity) (fun _ ↦ by positivity)
      (by fun_prop) (by fun_prop),
    eintegral_eq_lintegral, eintegral_eq_lintegral]
  rcases h with h | h
  · have h' : ∫ᵉ x, u x ∂μ ≠ ⊤ := by simpa [eintegral_eq_lintegral]
    exact ne_top_of_le_ne_top h' (eintegral_mono fun _ ↦ min_le_left _ _)
  · have h' : ∫ᵉ x, v x ∂μ ≠ ⊤ := by simpa [eintegral_eq_lintegral]
    exact ne_top_of_le_ne_top h' (eintegral_mono fun _ ↦ min_le_right _ _)

/-- The integral of a sum is the sum of integrals (requires compatibility conditions to
avoid `⊤ - ⊤`).

See also `eintegral_add'` for a version with stronger hypotheses on `g` and weaker hypotheses
on `f`. -/
lemma eintegral_add (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hf_int : EIntegrable f μ) (hg_int : EIntegrable g μ)
    (h_ne_bot_1 : ∫ᵉ x, f x ∂μ ≠ ⊥ ∨ ∫ᵉ x, g x ∂μ ≠ ⊤)
    (h_ne_bot_2 : ∫ᵉ x, f x ∂μ ≠ ⊤ ∨ ∫ᵉ x, g x ∂μ ≠ ⊥) :
    ∫ᵉ x, f x + g x ∂μ = ∫ᵉ x, f x ∂μ + ∫ᵉ x, g x ∂μ := by
  have hf_add_g : ∀ x, f x + g x = (f⁺ x + g⁺ x) - (f⁻ x + g⁻ x) := by
    intro x
    rw [← posPartFun_sub_negPartFun f x, ← posPartFun_sub_negPartFun g x, EReal.add_sub_add]
    · exact EReal.ne_bot_of_nonneg <| negPartFun_nonneg f x
    · exact EReal.ne_bot_of_nonneg <| negPartFun_nonneg g x
  simp_rw [hf_add_g, ← posPartFun_sub_negPartFun f, ← posPartFun_sub_negPartFun g]
  rw [eintegral_sub_of_nonneg_of_eq_zero (by simp) (by simp)
      (posPartFun_eq_zero_or_negPartFun_eq_zero f),
    eintegral_sub_of_nonneg_of_eq_zero (by simp) (by simp)
      (posPartFun_eq_zero_or_negPartFun_eq_zero g)]
  have : ∫ᵉ x, f⁺ x ∂μ - ∫ᵉ x, f⁻ x ∂μ + (∫ᵉ x, g⁺ x ∂μ - ∫ᵉ x, g⁻ x ∂μ)
      = ∫ᵉ x, f⁺ x ∂μ + ∫ᵉ x, g⁺ x ∂μ - (∫ᵉ x, f⁻ x ∂μ + ∫ᵉ x, g⁻ x ∂μ) := by
    rw [EReal.add_sub_add]
    · exact EReal.ne_bot_of_nonneg <| eintegral_nonneg (by simp)
    · exact EReal.ne_bot_of_nonneg <| eintegral_nonneg (by simp)
  rw [this, ← eintegral_add_of_nonneg (by fun_prop) (by simp) (by simp),
    ← eintegral_add_of_nonneg (by fun_prop) (by simp) (by simp),
    ← eintegral_sub_of_nonneg _ _ (by fun_prop) (by fun_prop)]
  · have h_le x : min (f⁺ x + g⁺ x) (f⁻ x + g⁻ x) ≤ min (f⁺ x) (g⁻ x) + min (f⁻ x) (g⁺ x) := by
      rcases posPartFun_eq_zero_or_negPartFun_eq_zero f x with hf | hf <;>
        rcases posPartFun_eq_zero_or_negPartFun_eq_zero g x with hg | hg
      · simp [hf, hg, negPartFun_nonneg f x, negPartFun_nonneg g x]
      · simp [hf, hg]
      · simp [hf, hg]
      · simp [hf, hg, posPartFun_nonneg f x, posPartFun_nonneg g x]
    refine ne_of_lt ?_
    refine lt_of_le_of_lt (eintegral_mono h_le) ?_
    rw [eintegral_add_of_nonneg_ae (by fun_prop) (by fun_prop) (by simp) (by simp)]
    rw [eintegral_eq_posPartFun_sub_negPartFun f, eintegral_eq_posPartFun_sub_negPartFun g]
      at h_ne_bot_1 h_ne_bot_2
    refine EReal.add_lt_top (ne_of_lt ?_) (ne_of_lt ?_)
    · cases h_ne_bot_2 with
      | inl h =>
        refine lt_of_le_of_lt (eintegral_mono (fun _ ↦ min_le_left _ _)) (Ne.lt_top ?_)
        cases hf_int.eintegral_posPartFun_ne_top_or_eintegral_negPartFun_ne_top with
        | inl h' => exact h'
        | inr h' =>
          intro h_false
          simp [h_false, EReal.top_sub h'] at h
      | inr h =>
        refine lt_of_le_of_lt (eintegral_mono (fun _ ↦ min_le_right _ _)) (Ne.lt_top ?_)
        intro h_false
        simp [h_false] at h
    · cases h_ne_bot_1 with
      | inl h =>
        refine lt_of_le_of_lt (eintegral_mono (fun _ ↦ min_le_left _ _)) (Ne.lt_top ?_)
        intro h_false
        simp [h_false] at h
      | inr h =>
        refine lt_of_le_of_lt (eintegral_mono (fun _ ↦ min_le_right _ _)) (Ne.lt_top ?_)
        cases hg_int.eintegral_posPartFun_ne_top_or_eintegral_negPartFun_ne_top with
        | inl h' => exact h'
        | inr h' =>
          intro h_false
          simp [h_false, EReal.top_sub h'] at h
  · exact fun _ ↦ add_nonneg (by simp) (by simp)
  · exact fun _ ↦ add_nonneg (by simp) (by simp)

/-- The integral of a sum is the sum of integrals (requires compatibility conditions to
avoid `⊤ - ⊤`).

See also `eintegral_add` for a version with balanced hypotheses for `f` and `g`. -/
lemma eintegral_add' (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hg_ne_top : ∫ᵉ x, g x ∂μ ≠ ⊤) (hg_ne_bot : ∫ᵉ x, g x ∂μ ≠ ⊥) :
    ∫ᵉ x, f x + g x ∂μ = ∫ᵉ x, f x ∂μ + ∫ᵉ x, g x ∂μ := by
  have hg_int : EIntegrable g μ := by
    by_contra h_false
    simp [eintegral_of_not_eintegrable h_false] at hg_ne_bot
  by_cases hf_int : EIntegrable f μ
  · rw [eintegral_add hf hg hf_int hg_int (.inr hg_ne_top) (.inr hg_ne_bot)]
  simp only [eintegral_of_not_eintegrable hf_int, EReal.bot_add]
  have hf₂_int : ∫ᵉ x, f⁻ x ∂μ = ⊤ := by
    have hf_int_eq_bot : ∫ᵉ x, f x ∂μ = ⊥ := by simp [hf_int]
    simp only [eintegral_eq_posPartFun_sub_negPartFun f, sub_eq_add_neg, EReal.add_eq_bot_iff,
      EReal.neg_eq_bot_iff] at hf_int_eq_bot
    have : ∫ᵉ x, f⁺ x ∂μ ≠ ⊥ := EReal.ne_bot_of_nonneg <| eintegral_nonneg (by simp)
    simpa [this] using hf_int_eq_bot
  have hg₂_int : ∫ᵉ x, g⁻ x ∂μ ≠ ⊤ := by
    intro h_false
    simp [eintegral_eq_posPartFun_sub_negPartFun g, h_false] at hg_ne_bot
  have hg₁_int : ∫ᵉ x, g⁺ x ∂μ ≠ ⊤ := by
    intro h_false
    rw [eintegral_eq_posPartFun_sub_negPartFun g, h_false, EReal.top_sub hg₂_int] at hg_ne_top
    simp at hg_ne_top
  have hf_add_g : ∀ x, f x + g x = (f⁺ x + g⁺ x) - (f⁻ x + g⁻ x) := by
    intro x
    rw [← posPartFun_sub_negPartFun f x, ← posPartFun_sub_negPartFun g x, EReal.add_sub_add]
    · exact EReal.ne_bot_of_nonneg (by simp)
    · exact EReal.ne_bot_of_nonneg (by simp)
  simp_rw [hf_add_g]
  rw [eintegral_sub_of_nonneg (fun _ ↦ add_nonneg (by simp) (by simp))
    (fun _ ↦ add_nonneg (by simp) (by simp)) (by fun_prop) (by fun_prop)]
  · suffices ∫ᵉ x, f⁻ x + g⁻ x ∂μ = ⊤ by simp [this]
    rw [← top_le_iff]
    calc ⊤
    _ = ∫ᵉ x, f⁻ x ∂μ := by rw [hf₂_int]
    _ ≤ ∫ᵉ x, f⁻ x + g⁻ x ∂μ := eintegral_mono (fun _ ↦ le_add_of_nonneg_right (by simp))
  · have h_le x : min (f⁺ x + g⁺ x) (f⁻ x + g⁻ x) ≤ min (f⁺ x) (g⁻ x) + min (f⁻ x) (g⁺ x) := by
      rcases posPartFun_eq_zero_or_negPartFun_eq_zero f x with hf | hf <;>
        rcases posPartFun_eq_zero_or_negPartFun_eq_zero g x with hg | hg <;>
        simp [hf, hg]
    refine (lt_of_le_of_lt (eintegral_mono h_le) ?_).ne
    rw [eintegral_add_of_nonneg_ae (by fun_prop) (by fun_prop) (by simp) (by simp)]
    refine EReal.add_lt_top (ne_of_lt ?_) (ne_of_lt ?_)
    · calc ∫ᵉ x, min (f⁺ x) (g⁻ x) ∂μ
      _ ≤ ∫ᵉ x, g⁻ x ∂μ := eintegral_mono (fun _ ↦ min_le_right _ _)
      _ < ⊤ := hg₂_int.lt_top
    · calc ∫ᵉ x, min (f⁻ x) (g⁺ x) ∂μ
      _ ≤ ∫ᵉ x, g⁺ x ∂μ := eintegral_mono (fun _ ↦ min_le_right _ _)
      _ < ⊤ := hg₁_int.lt_top

/-- The integral of a difference is the difference of integrals (requires compatibility
conditions to avoid `⊤ - ⊤`). -/
lemma eintegral_sub (hf : EIntegrable f μ)
    (hf_meas : AEMeasurable f μ) (hg : EIntegrable g μ) (hg_meas : AEMeasurable g μ)
    (h_ne_top : ∫ᵉ x, f x ∂μ ≠ ⊤ ∨ ∫ᵉ x, g x ∂μ ≠ ⊤)
    (h_ne_bot : ∫ᵉ x, f x ∂μ ≠ ⊥ ∨ ∫ᵉ x, g x ∂μ ≠ ⊥) :
    ∫ᵉ x, f x - g x ∂μ = ∫ᵉ x, f x ∂μ - ∫ᵉ x, g x ∂μ := by
  simp_rw [sub_eq_add_neg, ← Pi.neg_apply]
  rw [eintegral_add hf_meas hg_meas.neg hf hg.neg]
  · simp_rw [Pi.neg_apply]
    rw [eintegral_neg hg]
  · cases h_ne_bot with
    | inl h => exact .inl h
    | inr h => right; simp_rw [Pi.neg_apply]; rw [eintegral_neg hg]; simpa
  · cases h_ne_top with
    | inl h => exact .inl h
    | inr h => right; simp_rw [Pi.neg_apply]; rw [eintegral_neg hg]; simpa

lemma eintegral_sub' (hf_meas : AEMeasurable f μ) (hg_meas : AEMeasurable g μ)
    (hg_ne_top : ∫ᵉ x, g x ∂μ ≠ ⊤) (hg_ne_bot : ∫ᵉ x, g x ∂μ ≠ ⊥) :
    ∫ᵉ x, f x - g x ∂μ = ∫ᵉ x, f x ∂μ - ∫ᵉ x, g x ∂μ := by
  have hg_int : EIntegrable g μ := by
    by_contra h_false
    simp [eintegral_of_not_eintegrable h_false] at hg_ne_bot
  simp_rw [sub_eq_add_neg, ← Pi.neg_apply]
  rw [eintegral_add' hf_meas hg_meas.neg]
  · simp_rw [Pi.neg_apply]
    rw [eintegral_neg hg_int]
  · simpa [eintegral_neg hg_int]
  · simpa [eintegral_neg hg_int]

lemma eintegral_sub'' (hf_meas : AEMeasurable f μ) (hg_meas : AEMeasurable g μ)
    (hf_ne_top : ∫ᵉ x, f x ∂μ ≠ ⊤) (hf_ne_bot : ∫ᵉ x, f x ∂μ ≠ ⊥) (hg_int : EIntegrable g μ) :
    ∫ᵉ x, f x - g x ∂μ = ∫ᵉ x, f x ∂μ - ∫ᵉ x, g x ∂μ := by
  rw [eintegral_sub _ hf_meas hg_int hg_meas (by simp [hf_ne_top]) (by simp [hf_ne_bot])]
  by_contra h_false
  simp [eintegral_of_not_eintegrable h_false] at hf_ne_bot

lemma eintegral_add_ne_bot (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hf_int : ∫ᵉ x, f x ∂μ ≠ ⊥) (hg_int : ∫ᵉ x, g x ∂μ ≠ ⊥) :
    ∫ᵉ x, f x + g x ∂μ ≠ ⊥ := by
  rw [eintegral_add (by fun_prop) (by fun_prop) (eintegrable_of_eintegral_ne_bot hf_int)
    (eintegrable_of_eintegral_ne_bot hg_int)]
  · simp [hf_int, hg_int]
  · simp [hf_int]
  · simp [hg_int]

lemma eintegrable_add_of_ne_bot (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hf_int : ∫ᵉ x, f x ∂μ ≠ ⊥) (hg_int : ∫ᵉ x, g x ∂μ ≠ ⊥) :
    EIntegrable (fun x ↦ f x + g x) μ :=
  eintegrable_of_eintegral_ne_bot (eintegral_add_ne_bot hf hg hf_int hg_int)

theorem eintegral_map {β : Type*} {mβ : MeasurableSpace β} {f : β → EReal} {g : α → β}
    (hf : Measurable f) (hg : Measurable g) : ∫ᵉ a, f a ∂μ.map g = ∫ᵉ a, f (g a) ∂μ := by
  simp only [eintegral]
  repeat rw [lintegral_map (by fun_prop) hg]

theorem eintegral_map' {β : Type*} {mβ : MeasurableSpace β} {f : β → EReal} {g : α → β}
    (hf : AEMeasurable f (μ.map g)) (hg : AEMeasurable g μ) :
    ∫ᵉ a, f a ∂μ.map g = ∫ᵉ a, f (g a) ∂μ := by
  simp only [eintegral]
  repeat rw [lintegral_map' (by fun_prop) hg]

lemma eintegral_add_measure {ν : Measure α} (f : α → EReal) :
    ∫ᵉ x, f x ∂(μ + ν) = ∫ᵉ x, f x ∂μ + ∫ᵉ x, f x ∂ν := by
  simp only [eintegral, lintegral_add_measure, EReal.coe_ennreal_add]
  rw [EReal.add_sub_add _ _ (by simp) (by simp)]

lemma eintegral_smul_measure {c : ℝ≥0∞} (hc : c ≠ ∞) (f : α → EReal) :
    ∫ᵉ x, f x ∂(c • μ) = c * ∫ᵉ x, f x ∂μ := by
  simp only [eintegral, lintegral_smul_measure, smul_eq_mul, EReal.coe_ennreal_mul]
  rw [EReal.mul_sub_of_nonneg_of_ne_top _ (by simp [hc])]
  norm_cast
  exact zero_le

@[simp]
lemma eintegral_dirac {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {x₀ : α} {f : α → EReal} :
    ∫ᵉ x, f x ∂(Measure.dirac x₀) = f x₀ := by
  simp only [eintegral, lintegral_dirac]
  rcases le_total (f x₀) 0 with (h | h) <;> simp [h]

end MeasureTheory
