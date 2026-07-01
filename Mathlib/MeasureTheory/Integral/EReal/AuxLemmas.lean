/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
module

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

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
* `eintegral_prod`: Fubini's theorem for extended real-valued functions on product measures,
  allowing interchange of integration order.
* `limsup_eintegral_le`: A Fatou-type lemma for the extended integral, relating the limsup of
  integrals to the integral of the limsup.
* `eintegral_liminf_le`: A Fatou-type lemma for the extended integral, relating the liminf of
  integrals to the integral of the liminf.

## Notation

* `∫ᵉ x, f x ∂μ`: The extended integral of `f` with respect to measure `μ`.
* `f⁺` and `f⁻`: Positive and negative parts of a function.

-/

@[expose] public section

open scoped ENNReal

noncomputable
instance : ENorm EReal where
  enorm x := (max x 0).toENNReal + (max (-x) 0).toENNReal

lemma EReal.add_sub_add_comm {a b c d : EReal} (h1 : c ≠ ⊥ ∨ d ≠ ⊤) (h2 : c ≠ ⊤ ∨ d ≠ ⊥) :
    (a + b) - (c + d) = (a - c) + (b - d) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, EReal.neg_add h1 h2, sub_eq_add_neg]
  grind

lemma EReal.mul_sub_of_eq_zero {a b c : EReal} (h : b = 0 ∨ c = 0) :
    a * (b - c) = a * b - a * c := by
  cases h with
  | inl hb => simp [hb]
  | inr hc => simp [hc]

lemma EReal.add_sub_add (a b : EReal) {c d : EReal} (hc : c ≠ ⊥) (hd : d ≠ ⊥) :
    a + b - (c + d) = (a - c) + (b - d) := by
  cases a <;> cases b <;> cases c <;> cases d
  -- 81 goals
  any_goals simp [hc, hd]
  any_goals simp at hc
  any_goals simp at hd
  · norm_cast
    ring
  · norm_cast
  · norm_cast
  · norm_cast

lemma EReal.ne_bot_of_nonneg {a : EReal} (ha : 0 ≤ a) : a ≠ ⊥ := by
  intro h_false
  simp [h_false] at ha

lemma EReal.mul_sub_of_nonneg_of_ne_top {a b c : EReal} (ha : 0 ≤ a) (ha' : a ≠ ⊤) :
    a * (b - c) = a * b - a * c := by
  by_cases ha_zero : a = 0
  · simp [ha_zero]
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha_zero)
  have ha_ne_bot : a ≠ ⊥ := fun h_eq ↦ by simp [h_eq] at ha
  lift a to ℝ using ⟨ha', ha_ne_bot⟩
  cases b <;> cases c
  · simp [EReal.mul_bot_of_pos ha_pos]
  · simp [EReal.mul_bot_of_pos ha_pos]
  · simp [EReal.mul_bot_of_pos ha_pos]
  · simp only [ne_eq, EReal.coe_ne_bot, not_false_eq_true, EReal.sub_bot,
      EReal.mul_top_of_pos ha_pos, EReal.mul_bot_of_pos ha_pos]
    rw [EReal.sub_bot]
    rw [← EReal.coe_mul]
    exact EReal.coe_ne_bot _
  · norm_cast
    ring
  · simp [EReal.mul_bot_of_pos ha_pos, EReal.mul_top_of_pos ha_pos]
  · simp [EReal.mul_top_of_pos ha_pos, EReal.mul_bot_of_pos ha_pos]
  · simp only [ne_eq, EReal.coe_ne_top, not_false_eq_true, EReal.top_sub,
      EReal.mul_top_of_pos ha_pos]
    rw [EReal.top_sub]
    rw [← EReal.coe_mul]
    exact EReal.coe_ne_top _
  · simp [EReal.mul_bot_of_pos ha_pos, EReal.mul_top_of_pos ha_pos]

lemma EReal.sub_lt_sub_of_le_of_lt {x y z t : EReal} (h : x ≤ y) (h' : z < t)
  (hy_top : y ≠ ⊤) (hy_bot : y ≠ ⊥) : x - t < y - z := by
  refine sub_lt_of_lt_add' ?_
  rw [add_sub_assoc', add_comm, add_sub_assoc]
  by_cases hxy : x = y
  · rw [hxy]
    lift y to ℝ using ⟨hy_top, hy_bot⟩
    by_cases htz_top : t - z = ⊤
    · simp_all
    rw [← coe_toReal htz_top <| ne_bot_of_nonneg (sub_pos.mpr h').le]
    norm_cast
    refine lt_add_of_pos_right y ?_
    exact EReal.toReal_pos (sub_pos.mpr h') htz_top
  · rw [← add_zero x]
    refine add_lt_add ?_ ?_
    · grind
    · exact sub_pos.mpr h'

lemma EReal.top_sub_eq_top_or_bot {a : EReal} : ⊤ - a = ⊤ ∨ ⊤ - a = ⊥ := by
  cases a with
  | bot => simp
  | coe a => simp
  | top => simp

section limsup_liminf

open Filter

lemma EReal.coe_ennreal_limsup {α : Type} (F : Filter α) [F.NeBot] (g : α → ℝ≥0∞) :
    (limsup g F).toEReal = limsup (fun x => (g x).toEReal) F := by
  refine Monotone.map_limsup_of_continuousAt ?_ _ ?_
  · intro x y hxy
    simp [hxy]
  · exact continuous_coe_ennreal_ereal.continuousAt

lemma EReal.limsup_coe_ennreal {α : Type} (F : Filter α) [F.NeBot] (g : α → EReal) :
    (limsup g F).toENNReal = limsup (fun x => (g x).toENNReal) F := by
  refine Monotone.map_limsup_of_continuousAt ?_ _ ?_
  · intro x y hxy
    exact EReal.toENNReal_le_toENNReal hxy
  · exact EReal.continuous_toENNReal.continuousAt

lemma EReal.coe_ennreal_liminf {α : Type} (F : Filter α) [F.NeBot] (g : α → ℝ≥0∞) :
    (liminf g F).toEReal = liminf (fun x => (g x).toEReal) F := by
  refine Monotone.map_liminf_of_continuousAt ?_ _ ?_
  · intro x y hxy
    simp [hxy]
  · exact continuous_coe_ennreal_ereal.continuousAt

lemma EReal.liminf_coe_ennreal {α : Type} (F : Filter α) [F.NeBot] (g : α → EReal) :
    (liminf g F).toENNReal = liminf (fun x => (g x).toENNReal) F := by
  refine Monotone.map_liminf_of_continuousAt ?_ _ ?_
  · intro x y hxy
    exact EReal.toENNReal_le_toENNReal hxy
  · exact EReal.continuous_toENNReal.continuousAt

end limsup_liminf


section PosNeg

open MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {f : α → EReal} {μ : Measure α}

noncomputable instance : PosPart (α → EReal) where
  posPart f := fun x ↦ max (f x) 0

noncomputable instance : NegPart (α → EReal) where
  negPart f := fun x ↦ max (- f x) 0

lemma posPartFun_def (f : α → EReal) : f⁺ = fun x ↦ max (f x) 0 := rfl

lemma negPartFun_def (f : α → EReal) : f⁻ = fun x ↦ max (- f x) 0 := rfl

@[simp]
lemma posPartFun_nonneg (f : α → EReal) (x : α) : 0 ≤ f⁺ x := by simp [posPartFun_def]

@[simp]
lemma negPartFun_nonneg (f : α → EReal) (x : α) : 0 ≤ f⁻ x := by simp [negPartFun_def]

lemma posPartFun_sub_negPartFun (f : α → EReal) (x : α) : f⁺ x - f⁻ x = f x := by
  rcases le_total 0 (f x) with h | h <;> simp [posPartFun_def, negPartFun_def, h]

lemma posPartFun_eq_zero_or_negPartFun_eq_zero (f : α → EReal) (x : α) :
    f⁺ x = 0 ∨ f⁻ x = 0 := by
  rcases le_total 0 (f x) with h | h <;> simp [posPartFun_def, negPartFun_def, h]

@[fun_prop]
lemma Measurable.posPartFun (hf : Measurable f) : Measurable (fun x ↦ f⁺ x) := by
  simp only [posPartFun_def]
  fun_prop

@[fun_prop]
lemma Measurable.negPartFun (hf : Measurable f) : Measurable (fun x ↦ f⁻ x) := by
  simp only [negPartFun_def]
  fun_prop

@[fun_prop]
lemma AEMeasurable.posPartFun (hf : AEMeasurable f μ) : AEMeasurable (fun x ↦ f⁺ x) μ := by
  simp only [posPartFun_def]
  fun_prop

@[fun_prop]
lemma AEMeasurable.negPartFun (hf : AEMeasurable f μ) : AEMeasurable (fun x ↦ f⁻ x) μ := by
  simp only [negPartFun_def]
  fun_prop

end PosNeg
