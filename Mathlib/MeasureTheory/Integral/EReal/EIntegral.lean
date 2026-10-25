/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.EReal.EIntegrable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Integral of extended real-valued functions

This file defines the integral of functions with values in `EReal` (the extended reals), as the
difference of the Lebesgue integrals of their positive and negative parts.

## Main definitions

* `MeasureTheory.eintegral μ f`: the integral of `f : α → EReal` with respect to `μ`, defined as
  `∫⁻ x, (f x).toENNReal ∂μ - ∫⁻ x, (-f x).toENNReal ∂μ`.

## Main statements

* `eintegral_coe_ennreal_sub`: if `f = u - v` with `u v : α → ℝ≥0∞` and one of `∫⁻ x, u x ∂μ` and
  `∫⁻ x, v x ∂μ` is finite, then `∫ᵉ x, f x ∂μ = ∫⁻ x, u x ∂μ - ∫⁻ x, v x ∂μ`. That is, the
  integral does not depend on the way `f` is written as a difference of nonnegative functions.
  This is the main tool to prove the linearity properties.
* `eintegral_add`, `eintegral_add'`: the integral of a sum is the sum of the integrals, under
  conditions which avoid the indeterminate forms `⊥ + ⊤` and `⊤ + ⊥`.
* `eintegral_sub`, `eintegral_sub'`: the integral of a difference is the difference of the
  integrals, under conditions which avoid the indeterminate forms `⊤ - ⊤` and `⊥ - ⊥`.
* `eintegral_real_const_mul`, `eintegral_neg`: compatibility with multiplication by a constant.
* `eintegral_mono_ae`, `eintegral_strict_mono_ae`: monotonicity.

## Notation

* `∫ᵉ x, f x ∂μ`: the integral of `f` with respect to the measure `μ`.
* `∫ᵉ x in s, f x ∂μ`: the integral of `f` with respect to the restriction of `μ` to `s`.

## Implementation notes

In `EReal`, `⊤ - ⊤ = ⊥`. As a consequence, the integral of a function for which both the
positive and negative parts have infinite integrals is `⊥`. The predicate `EIntegrable f μ` states
that this does not happen.

-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f g : α → EReal}

/-- The integral of an `EReal`-valued function with respect to a measure `μ`, defined as the
difference of the Lebesgue integrals of its positive and negative parts.

If both integrals are infinite, the result is `⊥`. See also `EIntegrable`, which is the property
that at least one of the integrals is finite. -/
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

/-! ### Basic properties -/

@[simp]
lemma eintegral_of_not_eintegrable (hf : ¬ EIntegrable f μ) :
    ∫ᵉ x, f x ∂μ = ⊥ := by
  simp only [EIntegrable, ne_eq, not_or, Decidable.not_not] at hf
  simp [eintegral, hf]

lemma eintegrable_of_eintegral_ne_bot (hf : ∫ᵉ x, f x ∂μ ≠ ⊥) : EIntegrable f μ := by
  by_contra h
  exact hf (eintegral_of_not_eintegrable h)

lemma lintegral_toENNReal_neg_ne_top_of_eintegral_ne_bot (hf : ∫ᵉ x, f x ∂μ ≠ ⊥) :
    ∫⁻ x, (-f x).toENNReal ∂μ ≠ ⊤ := by
  intro h
  simp [eintegral, h] at hf

lemma lintegral_toENNReal_ne_top_of_eintegral_ne_top (hf_int : EIntegrable f μ)
    (hf : ∫ᵉ x, f x ∂μ ≠ ⊤) :
    ∫⁻ x, (f x).toENNReal ∂μ ≠ ⊤ := by
  intro h
  have h_neg : ∫⁻ x, (-f x).toENNReal ∂μ ≠ ⊤ := by simpa [EIntegrable, h] using hf_int
  simp [eintegral, h, EReal.top_sub, h_neg] at hf

@[simp]
lemma eintegral_zero (μ : Measure α) : ∫ᵉ _, (0 : EReal) ∂μ = 0 := by simp [eintegral]

@[simp]
lemma eintegral_zero_measure (f : α → EReal) : ∫ᵉ x, f x ∂(0 : Measure α) = 0 := by simp [eintegral]

lemma eintegral_congr (h : ∀ x, f x = g x) : ∫ᵉ x, f x ∂μ = ∫ᵉ x, g x ∂μ := by simp_rw [h]

/-- The extended integral is compatible with almost-everywhere equality. -/
lemma eintegral_congr_ae (h : ∀ᵐ x ∂μ, f x = g x) : ∫ᵉ x, f x ∂μ = ∫ᵉ x, g x ∂μ := by
  simp_rw [eintegral]
  congr 2 <;> exact lintegral_congr_ae <| by filter_upwards [h] with x hx using by rw [hx]

lemma eintegral_eq_lintegral_of_nonneg_ae (hf : ∀ᵐ x ∂μ, 0 ≤ f x) :
    ∫ᵉ x, f x ∂μ = ∫⁻ x, (f x).toENNReal ∂μ := by
  have h : ∫⁻ x, (-f x).toENNReal ∂μ = 0 :=
    (lintegral_congr_ae (g := 0) <| by filter_upwards [hf] with x hx using by simp [hx]).trans
      lintegral_zero
  simp [eintegral, h]

lemma eintegral_eq_lintegral_of_nonneg (hf : ∀ x, 0 ≤ f x) :
    ∫ᵉ x, f x ∂μ = ∫⁻ x, (f x).toENNReal ∂μ :=
  eintegral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf)

lemma eintegral_eq_neg_lintegral_of_nonpos_ae (hf : ∀ᵐ x ∂μ, f x ≤ 0) :
    ∫ᵉ x, f x ∂μ = - ∫⁻ x, (-f x).toENNReal ∂μ := by
  have h : ∫⁻ x, (f x).toENNReal ∂μ = 0 :=
    (lintegral_congr_ae (g := 0) <| by filter_upwards [hf] with x hx using by simp [hx]).trans
      lintegral_zero
  simp [eintegral, h]

lemma eintegral_eq_neg_lintegral_of_nonpos (hf : ∀ x, f x ≤ 0) :
    ∫ᵉ x, f x ∂μ = - ∫⁻ x, (-f x).toENNReal ∂μ :=
  eintegral_eq_neg_lintegral_of_nonpos_ae (ae_of_all _ hf)

lemma eintegral_nonneg_of_ae (hf : ∀ᵐ x ∂μ, 0 ≤ f x) : 0 ≤ ∫ᵉ x, f x ∂μ := by
  rw [eintegral_eq_lintegral_of_nonneg_ae hf]
  positivity

lemma eintegral_nonneg (hf : ∀ x, 0 ≤ f x) : 0 ≤ ∫ᵉ x, f x ∂μ :=
  eintegral_nonneg_of_ae (ae_of_all _ hf)

lemma eintegral_nonpos_of_ae (hf : ∀ᵐ x ∂μ, f x ≤ 0) : ∫ᵉ x, f x ∂μ ≤ 0 := by
  rw [eintegral_eq_neg_lintegral_of_nonpos_ae hf, EReal.neg_le_zero]
  positivity

lemma eintegral_nonpos (hf : ∀ x, f x ≤ 0) : ∫ᵉ x, f x ∂μ ≤ 0 :=
  eintegral_nonpos_of_ae (ae_of_all _ hf)

@[simp]
lemma eintegral_coe_ennreal (f : α → ℝ≥0∞) : ∫ᵉ x, f x ∂μ = ∫⁻ x, f x ∂μ := by
  rw [eintegral_eq_lintegral_of_nonneg (fun _ ↦ by positivity)]
  simp

@[simp]
lemma eintegral_const (c : EReal) (μ : Measure α) : ∫ᵉ _, c ∂μ = c * (μ Set.univ : EReal) := by
  rcases le_total 0 c with hc | hc
  · rw [eintegral_eq_lintegral_of_nonneg (fun _ ↦ hc)]
    simp only [lintegral_const, EReal.coe_ennreal_mul]
    rw [EReal.coe_toENNReal hc]
  · rw [eintegral_eq_neg_lintegral_of_nonpos (fun _ ↦ hc)]
    simp only [lintegral_const, EReal.coe_ennreal_mul]
    rw [EReal.coe_toENNReal]
    · simp
    · exact EReal.neg_nonneg.mpr hc

lemma eintegral_lt_top_of_le {b : EReal} (hf : ∀ᵐ x ∂μ, f x ≤ b) (hb : b ≠ ⊤)
    [IsFiniteMeasure μ] :
    ∫ᵉ x, f x ∂μ < ⊤ := by
  have h : ∫⁻ x, (f x).toENNReal ∂μ < ⊤ := by
    calc ∫⁻ x, (f x).toENNReal ∂μ
    _ ≤ ∫⁻ x, b.toENNReal ∂μ := lintegral_mono_ae <| by
      filter_upwards [hf] with x hx using EReal.toENNReal_le_toENNReal hx
    _ = b.toENNReal * μ .univ := by simp [lintegral_const]
    _ < ⊤ := by simp [hb, lt_top_iff_ne_top, ENNReal.mul_eq_top]
  calc ∫ᵉ x, f x ∂μ
  _ ≤ ∫⁻ x, (f x).toENNReal ∂μ - 0 := EReal.sub_le_sub le_rfl (by positivity)
  _ < ⊤ := by simpa [lt_top_iff_ne_top] using h.ne

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
lemma eintegral_mono (hfg : ∀ x, f x ≤ g x) : ∫ᵉ x, f x ∂μ ≤ ∫ᵉ x, g x ∂μ :=
  eintegral_mono_ae <| ae_of_all _ hfg

lemma eintegral_add_compl₀ {s : Set α} (hs : NullMeasurableSet s μ) :
    ∫ᵉ x in s, f x ∂μ + ∫ᵉ x in sᶜ, f x ∂μ = ∫ᵉ x, f x ∂μ := by
  simp only [eintegral]
  symm
  rw [← lintegral_add_compl₀ (fun x ↦ (f x).toENNReal) hs,
    ← lintegral_add_compl₀ (fun x ↦ (-f x).toENNReal) hs]
  push_cast
  rw [EReal.add_sub_add_comm (by simp) (by simp)]

lemma eintegral_add_compl {s : Set α} (hs : MeasurableSet s) :
    ∫ᵉ x in s, f x ∂μ + ∫ᵉ x in sᶜ, f x ∂μ = ∫ᵉ x, f x ∂μ :=
  eintegral_add_compl₀ hs.nullMeasurableSet

lemma ae_ne_bot_of_eintegral_ne_bot (hf_meas : AEMeasurable f μ) (hf : ∫ᵉ x, f x ∂μ ≠ ⊥) :
    ∀ᵐ x ∂μ, f x ≠ ⊥ := by
  filter_upwards [ae_lt_top' (by fun_prop) (lintegral_toENNReal_neg_ne_top_of_eintegral_ne_bot hf)]
    with x hx
  simpa [lt_top_iff_ne_top] using hx

lemma ae_ne_top_of_eintegral_ne_top (hf_meas : AEMeasurable f μ) (hf_int : EIntegrable f μ)
    (hf : ∫ᵉ x, f x ∂μ ≠ ⊤) :
    ∀ᵐ x ∂μ, f x ≠ ⊤ := by
  filter_upwards [ae_lt_top' (by fun_prop)
    (lintegral_toENNReal_ne_top_of_eintegral_ne_top hf_int hf)] with x hx
  simpa [lt_top_iff_ne_top] using hx

/-- The extended integral decomposes as the difference between the integrals of the positive
and negative parts of the function. -/
lemma eintegral_eq_eintegral_posPart_sub_eintegral_negPart (f : α → EReal) :
    ∫ᵉ x, f x ∂μ = ∫ᵉ x, f⁺ x ∂μ - ∫ᵉ x, f⁻ x ∂μ := by
  rw [eintegral_eq_lintegral_of_nonneg (posPart_nonneg f),
    eintegral_eq_lintegral_of_nonneg (negPart_nonneg f), eintegral]
  simp

/-! ### Difference of nonnegative functions -/

/-- The extended integral of the difference of two `ℝ≥0∞`-valued functions (coerced to `EReal`) is
the difference of their Lebesgue integrals, provided at least one of the integrals is finite.

That is, the integral of `f` does not depend on how `f` is written as a difference of nonnegative
functions. -/
lemma eintegral_coe_ennreal_sub {u v : α → ℝ≥0∞} (hu : AEMeasurable u μ) (hv : AEMeasurable v μ)
    (h : ∫⁻ x, u x ∂μ ≠ ⊤ ∨ ∫⁻ x, v x ∂μ ≠ ⊤) :
    ∫ᵉ x, u x - v x ∂μ = ∫⁻ x, u x ∂μ - ∫⁻ x, v x ∂μ := by
  -- Write `P` and `N` for the integrals of the positive and negative parts of `u - v`, and
  -- `U` and `V` for those of `u` and `v`. Then `P + V = N + U`, `P ≤ U` and `N ≤ V`.
  have h_eq : ∫⁻ x, ((u x : EReal) - v x).toENNReal ∂μ + ∫⁻ x, v x ∂μ
      = ∫⁻ x, (-((u x : EReal) - v x)).toENNReal ∂μ + ∫⁻ x, u x ∂μ := by
    rw [← lintegral_add_left' (by fun_prop), ← lintegral_add_left' (by fun_prop)]
    simp_rw [EReal.toENNReal_coe_ennreal_sub_add]
  have h_pos : ∫⁻ x, ((u x : EReal) - v x).toENNReal ∂μ ≤ ∫⁻ x, u x ∂μ :=
    lintegral_mono fun x ↦ EReal.toENNReal_coe_ennreal_sub_le _ _
  have h_neg : ∫⁻ x, (-((u x : EReal) - v x)).toENNReal ∂μ ≤ ∫⁻ x, v x ∂μ :=
    lintegral_mono fun x ↦ EReal.toENNReal_neg_coe_ennreal_sub_le _ _
  rcases h with h | h
  · exact EReal.coe_ennreal_sub_eq_of_add_eq' h_eq (ne_top_of_le_ne_top h h_pos) h
  · exact EReal.coe_ennreal_sub_eq_of_add_eq h_eq (ne_top_of_le_ne_top h h_neg) h

/-! ### Linearity -/

lemma eintegral_add_of_nonneg_ae (hf_meas : AEMeasurable f μ)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x) (hg : ∀ᵐ x ∂μ, 0 ≤ g x) :
    ∫ᵉ x, f x + g x ∂μ = ∫ᵉ x, f x ∂μ + ∫ᵉ x, g x ∂μ := by
  have hfg : ∀ᵐ x ∂μ, 0 ≤ f x + g x := by
    filter_upwards [hf, hg] with x hfx hgx using add_nonneg hfx hgx
  rw [eintegral_eq_lintegral_of_nonneg_ae hfg, eintegral_eq_lintegral_of_nonneg_ae hf,
    eintegral_eq_lintegral_of_nonneg_ae hg, ← EReal.coe_ennreal_add,
    ← lintegral_add_left' (by fun_prop)]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [hf, hg] with x hfx hgx using EReal.toENNReal_add hfx hgx

lemma eintegral_add_of_nonneg (hf_meas : AEMeasurable f μ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    ∫ᵉ x, f x + g x ∂μ = ∫ᵉ x, f x ∂μ + ∫ᵉ x, g x ∂μ :=
  eintegral_add_of_nonneg_ae hf_meas (ae_of_all _ hf) (ae_of_all _ hg)

/-- The integral of a sum is the sum of integrals, provided that `g` is `EIntegrable` and that
the sum of the integrals is not of the form `⊥ + ⊤` or `⊤ + ⊥`.

If `f` is not `EIntegrable`, both sides are `⊥`.
See also `eintegral_add'` for the case where the integral of `g` is finite. -/
lemma eintegral_add (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hg_int : EIntegrable g μ)
    (h_bot_top : ∫ᵉ x, f x ∂μ ≠ ⊥ ∨ ∫ᵉ x, g x ∂μ ≠ ⊤)
    (h_top_bot : ∫ᵉ x, f x ∂μ ≠ ⊤ ∨ ∫ᵉ x, g x ∂μ ≠ ⊥) :
    ∫ᵉ x, f x + g x ∂μ = ∫ᵉ x, f x ∂μ + ∫ᵉ x, g x ∂μ := by
  by_cases hf_int : EIntegrable f μ
  swap
  · -- If `f` is not integrable, the negative part of `f + g` has infinite integral, since
    -- the positive part of `g` has finite integral. Both sides are then `⊥`.
    have hg_pos : ∫⁻ x, (g x).toENNReal ∂μ ≠ ⊤ :=
      lintegral_toENNReal_ne_top_of_eintegral_ne_top hg_int
        (h_bot_top.resolve_left (not_not.mpr (eintegral_of_not_eintegrable hf_int)))
    have hf_neg : ∫⁻ x, (-f x).toENNReal ∂μ = ⊤ := by
      simp only [EIntegrable, not_or, not_not] at hf_int
      exact hf_int.2
    have h_le : ∫⁻ x, (-f x).toENNReal ∂μ
        ≤ ∫⁻ x, (-(f x + g x)).toENNReal ∂μ + ∫⁻ x, (g x).toENNReal ∂μ := by
      rw [← lintegral_add_left' (by fun_prop)]
      exact lintegral_mono fun x ↦ EReal.toENNReal_neg_le_toENNReal_neg_add_add_toENNReal _ _
    rw [hf_neg, top_le_iff, ENNReal.add_eq_top] at h_le
    rw [eintegral_of_not_eintegrable hf_int, EReal.bot_add]
    simp [eintegral, h_le.resolve_right hg_pos]
  -- Write `f + g` as the difference of `f⁺ + g⁺` and `f⁻ + g⁻`.
  have h_eq x : f x + g x = ↑((f x).toENNReal + (g x).toENNReal)
      - ↑((-f x).toENNReal + (-g x).toENNReal) := by
    push_cast
    rw [EReal.add_sub_add_comm (.inl (by simp)) (.inr (by simp)),
      EReal.coe_toENNReal_sub_coe_toENNReal_neg, EReal.coe_toENNReal_sub_coe_toENNReal_neg]
  simp_rw [h_eq]
  rw [eintegral_coe_ennreal_sub (by fun_prop) (by fun_prop),
    lintegral_add_left' (by fun_prop), lintegral_add_left' (by fun_prop)]
  · push_cast
    rw [EReal.add_sub_add_comm (.inl (by simp)) (.inr (by simp)), eintegral, eintegral]
  · simp only [eintegral, EIntegrable] at hf_int hg_int h_bot_top h_top_bot
    rw [lintegral_add_left' (by fun_prop), lintegral_add_left' (by fun_prop)]
    simp only [ne_eq, ENNReal.add_eq_top, not_or]
    generalize ∫⁻ x, (f x).toENNReal ∂μ = a at *
    generalize ∫⁻ x, (-f x).toENNReal ∂μ = b at *
    generalize ∫⁻ x, (g x).toENNReal ∂μ = c at *
    generalize ∫⁻ x, (-g x).toENNReal ∂μ = d at *
    induction a <;> induction b <;> induction c <;> induction d <;> simp_all

/-- The integral of a sum is the sum of integrals, provided that the integral of `g` is finite.

See also `eintegral_add` for a more general version. -/
lemma eintegral_add' (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hg_ne_top : ∫ᵉ x, g x ∂μ ≠ ⊤) (hg_ne_bot : ∫ᵉ x, g x ∂μ ≠ ⊥) :
    ∫ᵉ x, f x + g x ∂μ = ∫ᵉ x, f x ∂μ + ∫ᵉ x, g x ∂μ :=
  eintegral_add hf hg (eintegrable_of_eintegral_ne_bot hg_ne_bot) (.inr hg_ne_top)
    (.inr hg_ne_bot)

lemma eintegral_add_ne_bot (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hf_int : ∫ᵉ x, f x ∂μ ≠ ⊥) (hg_int : ∫ᵉ x, g x ∂μ ≠ ⊥) :
    ∫ᵉ x, f x + g x ∂μ ≠ ⊥ := by
  rw [eintegral_add hf hg (eintegrable_of_eintegral_ne_bot hg_int) (.inl hf_int) (.inr hg_int)]
  simp [hf_int, hg_int]

lemma eintegrable_add_of_ne_bot (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hf_int : ∫ᵉ x, f x ∂μ ≠ ⊥) (hg_int : ∫ᵉ x, g x ∂μ ≠ ⊥) :
    EIntegrable (fun x ↦ f x + g x) μ :=
  eintegrable_of_eintegral_ne_bot (eintegral_add_ne_bot hf hg hf_int hg_int)

lemma eintegral_neg (hf : EIntegrable f μ) :
    ∫ᵉ x, -f x ∂μ = - ∫ᵉ x, f x ∂μ := by
  simp only [eintegral, neg_neg]
  rw [EReal.neg_sub (.inl (by simp)) (by simpa [EIntegrable] using hf), add_comm,
    ← sub_eq_add_neg]

lemma eintegral_real_const_mul_of_nonneg {c : ℝ} (hc : 0 ≤ c) (f : α → EReal) :
    ∫ᵉ x, c * f x ∂μ = c * ∫ᵉ x, f x ∂μ := by
  have hc' : (0 : EReal) ≤ c := EReal.coe_nonneg.mpr hc
  have h_pos x : ((c : EReal) * f x).toENNReal = ENNReal.ofReal c * (f x).toENNReal := by
    rw [EReal.toENNReal_mul hc', EReal.toENNReal_of_ne_top (EReal.coe_ne_top c), EReal.toReal_coe]
  have h_neg x : (-((c : EReal) * f x)).toENNReal = ENNReal.ofReal c * (-f x).toENNReal := by
    rw [← mul_neg, EReal.toENNReal_mul hc', EReal.toENNReal_of_ne_top (EReal.coe_ne_top c),
      EReal.toReal_coe]
  simp only [eintegral, h_pos, h_neg, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal, max_eq_left hc]
  rw [EReal.mul_sub_of_nonneg_of_ne_top hc' (EReal.coe_ne_top c)]

lemma eintegral_real_const_mul (c : ℝ) (hf : EIntegrable f μ) :
    ∫ᵉ x, c * f x ∂μ = c * ∫ᵉ x, f x ∂μ := by
  rcases le_total 0 c with hc | hc
  · exact eintegral_real_const_mul_of_nonneg hc f
  have h x : (c : EReal) * f x = ((-c : ℝ) : EReal) * -f x := by
    rw [EReal.coe_neg, neg_mul_neg]
  simp_rw [h]
  rw [eintegral_real_const_mul_of_nonneg (by linarith), eintegral_neg hf, EReal.coe_neg,
    neg_mul_neg]

lemma eintegral_const_mul {c : EReal} (hc_bot : c ≠ ⊥) (hc_top : c ≠ ⊤) (hf : EIntegrable f μ) :
    ∫ᵉ x, c * f x ∂μ = c * ∫ᵉ x, f x ∂μ := by
  lift c to ℝ using ⟨hc_top, hc_bot⟩ with c
  exact eintegral_real_const_mul c hf

/-- The integral of a difference is the difference of integrals, provided that `g` is
`EIntegrable` and that the difference of the integrals is not of the form `⊤ - ⊤` or `⊥ - ⊥`.

See also `eintegral_sub'` for the case where the integral of `g` is finite. -/
lemma eintegral_sub (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hg_int : EIntegrable g μ)
    (h_ne_top : ∫ᵉ x, f x ∂μ ≠ ⊤ ∨ ∫ᵉ x, g x ∂μ ≠ ⊤)
    (h_ne_bot : ∫ᵉ x, f x ∂μ ≠ ⊥ ∨ ∫ᵉ x, g x ∂μ ≠ ⊥) :
    ∫ᵉ x, f x - g x ∂μ = ∫ᵉ x, f x ∂μ - ∫ᵉ x, g x ∂μ := by
  simp_rw [sub_eq_add_neg]
  rw [eintegral_add (g := fun x ↦ -g x) hf hg.neg hg_int.neg, eintegral_neg hg_int]
  · simpa [eintegral_neg hg_int] using h_ne_bot
  · simpa [eintegral_neg hg_int] using h_ne_top

/-- The integral of a difference is the difference of integrals, provided that the integral of
`g` is finite.

See also `eintegral_sub` for a more general version. -/
lemma eintegral_sub' (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hg_ne_top : ∫ᵉ x, g x ∂μ ≠ ⊤) (hg_ne_bot : ∫ᵉ x, g x ∂μ ≠ ⊥) :
    ∫ᵉ x, f x - g x ∂μ = ∫ᵉ x, f x ∂μ - ∫ᵉ x, g x ∂μ :=
  eintegral_sub hf hg (eintegrable_of_eintegral_ne_bot hg_ne_bot) (.inr hg_ne_top)
    (.inr hg_ne_bot)

/-! ### Strict monotonicity -/

/-- The extended integral is strictly monotone with respect to almost-everywhere strict
inequality. -/
lemma eintegral_strict_mono_ae (hμ : μ ≠ 0) (hg : AEMeasurable g μ) (hf : AEMeasurable f μ)
    (hfg : ∀ᵐ x ∂μ, f x < g x) (hfi : ∫ᵉ x, f x ∂μ < ⊤) (hgi : ∫ᵉ x, g x ∂μ ≠ ⊥) :
    ∫ᵉ x, f x ∂μ < ∫ᵉ x, g x ∂μ := by
  rcases eq_or_ne (∫ᵉ x, f x ∂μ) ⊥ with hf_bot | hf_bot
  · rwa [hf_bot, bot_lt_iff_ne_bot]
  -- The integral of `f` is finite. We write `g = (g - f) + f` and show `0 < ∫ᵉ x, g x - f x ∂μ`.
  have h_top : ∀ᵐ x ∂μ, f x ≠ ⊤ :=
    ae_ne_top_of_eintegral_ne_top hf (eintegrable_of_eintegral_ne_bot hf_bot) hfi.ne
  have h_bot : ∀ᵐ x ∂μ, f x ≠ ⊥ := ae_ne_bot_of_eintegral_ne_bot hf hf_bot
  have h_eq : ∀ᵐ x ∂μ, g x = (g x - f x) + f x := by
    filter_upwards [h_top, h_bot] with x h_top h_bot
    lift f x to ℝ using ⟨h_top, h_bot⟩ with r
    rw [EReal.sub_add_cancel]
  have h_pos : 0 < ∫ᵉ x, g x - f x ∂μ := by
    rw [eintegral_eq_lintegral_of_nonneg_ae
        (by filter_upwards [hfg] with x hx using (EReal.sub_pos.mpr hx).le),
      EReal.coe_ennreal_pos, pos_iff_ne_zero, ne_eq, lintegral_eq_zero_iff' (by fun_prop)]
    intro h_zero
    refine hμ (ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp ?_))
    filter_upwards [h_zero, hfg] with x h_zero hx
    exact (EReal.sub_pos.mpr hx).not_ge (EReal.toENNReal_eq_zero_iff.mp h_zero)
  rw [eintegral_congr_ae h_eq, eintegral_add' (by fun_prop) hf hfi.ne hf_bot]
  lift ∫ᵉ x, f x ∂μ to ℝ using ⟨hfi.ne, hf_bot⟩ with r
  generalize ∫ᵉ x, g x - f x ∂μ = s at h_pos ⊢
  induction s with
  | bot => simp at h_pos
  | coe s =>
    norm_cast at h_pos ⊢
    linarith
  | top => simp

lemma eintegral_strict_mono (hμ : μ ≠ 0) (hg : AEMeasurable g μ) (hf : AEMeasurable f μ)
    (hfg : ∀ x, f x < g x) (hfi : ∫ᵉ x, f x ∂μ < ⊤) (hgi : ∫ᵉ x, g x ∂μ ≠ ⊥) :
    ∫ᵉ x, f x ∂μ < ∫ᵉ x, g x ∂μ :=
  eintegral_strict_mono_ae hμ hg hf (ae_of_all μ hfg) hfi hgi

/-! ### Operations on the measure -/

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
  rw [EReal.add_sub_add_comm (by simp) (by simp)]

lemma eintegral_smul_measure {c : ℝ≥0∞} (hc : c ≠ ∞) (f : α → EReal) :
    ∫ᵉ x, f x ∂(c • μ) = c * ∫ᵉ x, f x ∂μ := by
  simp only [eintegral, lintegral_smul_measure, smul_eq_mul, EReal.coe_ennreal_mul]
  rw [EReal.mul_sub_of_nonneg_of_ne_top _ (by simp [hc])]
  norm_cast
  exact zero_le

@[simp]
lemma eintegral_dirac [MeasurableSingletonClass α] (x₀ : α) (f : α → EReal) :
    ∫ᵉ x, f x ∂(Measure.dirac x₀) = f x₀ := by
  simp only [eintegral, lintegral_dirac]
  rcases le_total (f x₀) 0 with (h | h) <;> simp [h]

end MeasureTheory
