/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Probability.Notation
public import Mathlib.Probability.Notation

/-! # Conditional Lebesgue expectation

We define the conditional expectation of a `ℝ≥0∞`-valued function using the Lebesgue integral.
Given a measure `P : Measure[mΩ₀] Ω` and a sub-σ-algebra `mΩ` of `mΩ₀` (meaning `hm : mΩ ≤ mΩ₀`)
and a function `X : Ω → ℝ≥0∞`, if `P.trim hm` is σ-finite, then the conditional (Lebesgue)
expectation `P⁻[X|mΩ]` of `X` is the `mΩ`-measurable function such that for all
`mΩ`-measurable sets `s`, `∫⁻ ω in s, P⁻[X|mΩ] ω ∂P = ∫⁻ ω in s, X ω ∂P`
(see `setLIntegral_condLExp`). This is unique up to `P`-ae equality (see `ae_eq_condLExp`).

## Main definitions

* `condLExp` : conditional (Lebesgue) expectation of `X` with respect to `mΩ`.
* `setLIntegral_condLExp`: For any `mΩ`-measurable set `s`,
  `∫⁻ ω in s, P⁻[X|mΩ] ω ∂P = ∫⁻ ω in s, X ω ∂P`.
* `ae_eq_condLExp` : the conditional (Lebesgue) expectation is characterized by its (Lebesgue)
  integral on `mΩ`-measurable sets up to `P`-ae equality.

## Notation

For a measure `P : Measure[mΩ₀] Ω`, and another `mΩ : MeasurableSpace Ω`, we define the notation
* `P⁻[X|mΩ] = condLExp mΩ P X`

## Design decisions

`P⁻[X|mΩ]` is assigned the junk value `0` when either `¬ mΩ ≤ mΩ₀` (`mΩ` is not a sub-σ-algebra)
or `h : mΩ ≤ mΩ₀` but `¬ SigmaFinite (P.trim hm)` (the latter always holds when `P` is a
probability measure). When both these hold, in some sense the "user definition" of `P⁻[X|mΩ]`
should be considered "the" measurable function which satisfies `setLIntegral_condLExp`
(which is proven unique up to `P`-ae measurable equality in `ae_eq_condLExp`). The actual definition
is just used to show existence. However for (potential) convenience the actual definition assigns
`P⁻[X|mΩ] := X` in the case when `X` is `mΩ`-measurable (which can be invoked using
`condLExp_eq_self`).

## To do

* Prove the pullout property
* Prove a dominated convergence theorem.

-/

public section

open MeasureTheory ProbabilityTheory Measure

open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ₀ mΩ : MeasurableSpace Ω} {P : Measure[mΩ₀] Ω} {X Y : Ω → ℝ≥0∞}

open Classical in
/-- Conditional (Lebesgue) expectation of a function, with notation `P⁻[X|mΩ]`.

It is defined as `0` if either `¬ mΩ ≤ mΩ₀` or `hm : mΩ ≤ mΩ₀` but `¬ SigmaFinite (P.trim hm)`.

One should typically not use the definition directly.
-/
noncomputable irreducible_def condLExp (mΩ : MeasurableSpace Ω) (P : Measure[mΩ₀] Ω)
    (X : Ω → ℝ≥0∞) : Ω → ℝ≥0∞ :=
  if hm : mΩ ≤ mΩ₀ then
    if SigmaFinite (P.trim hm) then
      if Measurable[mΩ] X then X else
      ∂((P.withDensity X).trim hm)/∂(P.trim hm)
    else 0
  else 0

@[inherit_doc MeasureTheory.condLExp]
scoped macro:max P:term noWs "⁻[" X:term "|" mΩ:term "]" : term =>
  `(MeasureTheory.condLExp $mΩ $P $X)

/-- Unexpander for `μ⁻[f|m]` notation. -/
@[app_unexpander MeasureTheory.condLExp]
meta def condLExpUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $mΩ $P $X) => `($P⁻[$X|$mΩ])
  | _ => throw ()

/-- info: P⁻[X|mΩ] : Ω → ℝ≥0∞ -/
#guard_msgs in
#check P⁻[X|mΩ]
/-- info: P⁻[X|mΩ] sorry : ℝ≥0∞ -/
#guard_msgs in
#check P⁻[X|mΩ] (sorry : Ω)

theorem condLExp_of_not_le (hm_not : ¬mΩ ≤ mΩ₀) : P⁻[X|mΩ] = 0 := by
  rw [condLExp, dif_neg hm_not]

theorem condLExp_of_not_sigmaFinite (hm : mΩ ≤ mΩ₀) (hμm_not : ¬SigmaFinite (P.trim hm)) :
    P⁻[X|mΩ] = 0 := by simp [condLExp, dif_pos hm, hμm_not]

theorem condLExp_eq_self (hm : mΩ ≤ mΩ₀) (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)]
    (hX : Measurable[mΩ] X) : P⁻[X|mΩ] = X := by
  simp [condLExp, hm, hσ, hX]

theorem condLExp_of_not_sub_sigma_measurable (hm : mΩ ≤ mΩ₀) (P : Measure[mΩ₀] Ω)
    [hσ : SigmaFinite (P.trim hm)] {X : Ω → ℝ≥0∞} (hX : ¬Measurable[mΩ] X) :
    P⁻[X|mΩ] = ∂((P.withDensity X).trim hm)/∂(P.trim hm) := by
  simp [condLExp, hm, hσ, hX]

@[fun_prop]
theorem measurable_condLExp (mΩ : MeasurableSpace Ω) (P : Measure[mΩ₀] Ω) (X : Ω → ℝ≥0∞) :
    Measurable[mΩ] P⁻[X|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀
  · by_cases hσ : SigmaFinite (P.trim hm)
    · by_cases hX : Measurable[mΩ] X
      · simp [condLExp_eq_self hm, hX]
      simp [condLExp_of_not_sub_sigma_measurable hm _ hX, measurable_rnDeriv]
    simp [condLExp_of_not_sigmaFinite hm hσ, measurable_zero]
  simp [condLExp_of_not_le hm, measurable_zero]

@[fun_prop]
theorem measurable_condLExp' (mΩ : MeasurableSpace Ω) (P : Measure[mΩ₀] Ω) (X : Ω → ℝ≥0∞) :
    Measurable[mΩ₀] P⁻[X|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀
  · exact (measurable_condLExp _ _ _).mono hm (le_refl _)
  · simp [condLExp_of_not_le hm, measurable_zero]

variable (hm : mΩ ≤ mΩ₀)

/-- The (Lebesgue) integral of the conditional (Lebesgue) expectation `P⁻[X|mΩ]` over an
`mΩ`-measurable set is equal to the integral of `X` on that set. -/
theorem setLIntegral_condLExp (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)]
    (X : Ω → ℝ≥0∞) {s : Set Ω} (hs : MeasurableSet[mΩ] s) :
    ∫⁻ ω in s, P⁻[X|mΩ] ω ∂P = ∫⁻ ω in s, X ω ∂P := by
  by_cases hX : Measurable[mΩ] X
  · simp [condLExp_eq_self hm _ hX]
  have h := AbsolutelyContinuous.trim (withDensity_absolutelyContinuous P X) hm
  have : SFinite ((P.withDensity X).trim hm) := sFinite_of_absolutelyContinuous h
  rw [condLExp_of_not_sub_sigma_measurable hm _ hX, ← lintegral_indicator (hm s hs),
    ← lintegral_trim hm (by measurability), lintegral_indicator hs, setLIntegral_rnDeriv' h hs,
    trim_measurableSet_eq hm hs, withDensity_apply _ (hm s hs)]

theorem setLIntegral_condLExp_trim (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)]
    (X : Ω → ℝ≥0∞) {s : Set Ω} (hs : MeasurableSet[mΩ] s) :
    ∫⁻ ω in s, P⁻[X|mΩ] ω ∂P.trim hm = ∫⁻ ω in s, X ω ∂P := by
  rw [setLIntegral_trim hm (measurable_condLExp _ _ _) hs, setLIntegral_condLExp _ _ _ hs]

theorem lintegral_condLExp (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (X : Ω → ℝ≥0∞) :
    ∫⁻ ω, P⁻[X|mΩ] ω ∂P = ∫⁻ ω, X ω ∂P := by
  simpa [← setLIntegral_univ] using setLIntegral_condLExp _ _ _ .univ

theorem ae_eq_condLExp₀ {P : Measure[mΩ₀] Ω} [hσ : SigmaFinite (P.trim hm)]
    (X : Ω → ℝ≥0∞) (hY : AEMeasurable[mΩ] Y (P.trim hm))
    (hXY : ∀ s, MeasurableSet[mΩ] s → ∫⁻ ω in s, Y ω ∂P = ∫⁻ ω in s, X ω ∂P) :
    Y =ᵐ[P] P⁻[X|mΩ] := by
  apply ae_eq_of_ae_eq_trim
  apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ hY (by fun_prop)
  intro s hs _
  rw [setLIntegral_trim_ae hm hY hs, setLIntegral_condLExp_trim _ _ _ hs]
  exact hXY s hs

/- The conditional (Lebesgue) expectation `P⁻[X|mΩ]` is defined uniquely as an `mΩ`-measurable
function up to `P`-ae equality by its (Lebesgue) integral over all `mΩ`-measurable sets. -/
theorem ae_eq_condLExp (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)]
    (X : Ω → ℝ≥0∞) (hY : Measurable[mΩ] Y)
    (hXY : ∀ s, MeasurableSet[mΩ] s → ∫⁻ ω in s, Y ω ∂P = ∫⁻ ω in s, X ω ∂P) :
    Y =ᵐ[P] P⁻[X|mΩ] := ae_eq_condLExp₀ _ _ hY.aemeasurable hXY

@[simp]
theorem condLExp_const (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (c : ℝ≥0∞) :
    P⁻[fun _ : Ω ↦ c|mΩ] = fun _ ↦ c := condLExp_eq_self _ _ (measurable_const)

@[simp]
theorem condLExp_zero (P : Measure[mΩ₀] Ω) : P⁻[0|mΩ] = 0 := by
  by_cases hm : mΩ ≤ mΩ₀
  swap; · simp [condLExp_of_not_le hm]
  by_cases hσ : SigmaFinite (P.trim hm)
  swap; · simp [condLExp_of_not_sigmaFinite hm hσ]
  exact condLExp_const hm P 0

@[simp]
theorem condLExp_one (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] :
    P⁻[1|mΩ] = 1 := condLExp_const hm P 1

@[gcongr]
theorem condLExp_congr_ae {P : Measure[mΩ₀] Ω}
    {X Y : Ω → ℝ≥0∞} (hXY : X =ᵐ[P] Y) : P⁻[X|mΩ] =ᵐ[P] P⁻[Y|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀
  · by_cases hσ : SigmaFinite (P.trim hm)
    · refine ae_eq_condLExp _ _ _ (measurable_condLExp _ _ _) (fun s hs ↦ ?_)
      rw [setLIntegral_condLExp _ _ _ hs]
      apply setLIntegral_congr_fun_ae (hm s hs)
      filter_upwards [hXY] with _ h _ using h
    simp [condLExp_of_not_sigmaFinite hm hσ]
  simp [condLExp_of_not_le hm]

@[gcongr]
theorem condLExp_congr_ae_trim {P : Measure[mΩ₀] Ω} {X Y : Ω → ℝ≥0∞} (hXY : X =ᵐ[P] Y) :
    P⁻[X|mΩ] =ᵐ[P.trim hm] P⁻[Y|mΩ] := by
  apply ae_eq_trim_of_measurable hm (measurable_condLExp _ _ X) (measurable_condLExp _ _ Y)
  exact condLExp_congr_ae hXY

theorem condLExp_bot' (P : Measure[mΩ₀] Ω) [NeZero P] (X : Ω → ℝ≥0∞) :
    P⁻[X|⊥] = fun _ => (P .univ)⁻¹ • ∫⁻ ω, X ω ∂P := by
  by_cases hP : IsFiniteMeasure P; swap
  · have hσ : ¬SigmaFinite (P.trim bot_le) := by rwa [sigmaFinite_trim_bot_iff]
    rw [not_isFiniteMeasure_iff] at hP
    rw [condLExp_of_not_sigmaFinite bot_le hσ]
    simp [hP, Pi.zero_def]
  obtain ⟨c, h_eq⟩ := eq_const_of_measurable_bot (measurable_condLExp ⊥ P X)
  ext _
  rw [← lintegral_condLExp bot_le]
  simp [h_eq, mul_comm, mul_assoc, ENNReal.mul_inv_cancel
    (NeZero.ne (P .univ)) (measure_ne_top _ _)]

theorem condLExp_bot_ae_eq (P : Measure[mΩ₀] Ω) (X : Ω → ℝ≥0∞) :
    P⁻[X|⊥] =ᵐ[P] fun _ => (P .univ)⁻¹ • ∫⁻ ω, X ω ∂P := by
  rcases eq_zero_or_neZero P with rfl | hP
  · rw [ae_zero]; exact Filter.eventually_bot
  exact ae_of_all P <| congr_fun (condLExp_bot' P X)

theorem condLExp_bot (P : Measure[mΩ₀] Ω) [IsProbabilityMeasure P] (X : Ω → ℝ≥0∞) :
    P⁻[X|⊥] = fun _ => ∫⁻ ω, X ω ∂P :=
  (condLExp_bot' P X).trans (by simp)

theorem condLExp_mono (hXY : X ≤ᵐ[P] Y) :
    P⁻[X|mΩ] ≤ᵐ[P] P⁻[Y|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀
  swap; · simp_rw [condLExp_of_not_le hm, Filter.EventuallyLE.rfl]
  by_cases hσ : SigmaFinite (P.trim hm)
  swap; · simp_rw [condLExp_of_not_sigmaFinite hm hσ, Filter.EventuallyLE.rfl]
  apply ae_le_of_ae_le_trim
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ := P.trim hm) (by fun_prop)
  intro s hs _
  repeat rw [setLIntegral_condLExp_trim hm _ _ hs]
  apply setLIntegral_mono_ae' (hm s hs)
  filter_upwards [hXY] using fun _ h _ ↦ h

theorem condLExp_add_le (X Y : Ω → ℝ≥0∞) :
    P⁻[X|mΩ] + P⁻[Y|mΩ] ≤ᵐ[P] P⁻[X + Y|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀; swap
  · simp_rw [condLExp_of_not_le hm]; filter_upwards; simp
  by_cases hσ : SigmaFinite (P.trim hm); swap
  · simp_rw [condLExp_of_not_sigmaFinite hm hσ]; filter_upwards; simp
  apply ae_le_of_ae_le_trim
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ := P.trim hm) (by fun_prop)
  intro s hs _
  simp only [Pi.add_apply]
  rw [lintegral_add_left (by fun_prop)]
  repeat rw [setLIntegral_condLExp_trim hm _ _ hs]
  grw [le_lintegral_add]
  simp

theorem condLExp_add_left {X : Ω → ℝ≥0∞} (Y : Ω → ℝ≥0∞) (hX : AEMeasurable[mΩ₀] X P) :
    P⁻[X + Y|mΩ] =ᵐ[P] P⁻[X|mΩ] + P⁻[Y|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀
  swap; · simp_rw [condLExp_of_not_le hm]; simp
  by_cases hσ : SigmaFinite (P.trim hm)
  swap; · simp_rw [condLExp_of_not_sigmaFinite hm hσ]; simp
  refine (ae_eq_condLExp _ _ _ (by fun_prop) ?_).symm
  intro s hs
  simp only [Pi.add_apply]
  rw [lintegral_add_left (by measurability)]
  repeat rw [setLIntegral_condLExp hm _ _ hs]
  rw [lintegral_add_left' (by fun_prop)]

theorem condLExp_add_right (X : Ω → ℝ≥0∞) {Y : Ω → ℝ≥0∞} (hY : AEMeasurable[mΩ₀] Y P) :
    P⁻[X + Y|mΩ] =ᵐ[P] P⁻[X|mΩ] + P⁻[Y|mΩ] := by
  rw [add_comm, add_comm P⁻[X|mΩ]]
  exact condLExp_add_left X hY

theorem condLExp_smul (X : Ω → ℝ≥0∞) (hX : AEMeasurable[mΩ₀] X P) (c : ℝ≥0∞) :
    P⁻[c • X|mΩ] =ᵐ[P] c • P⁻[X|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀
  swap; · simp [condLExp_of_not_le hm]
  by_cases hσ : SigmaFinite (P.trim hm)
  swap; · simp [condLExp_of_not_sigmaFinite hm hσ]
  refine (ae_eq_condLExp _ _ _ (by fun_prop) ?_).symm
  intro s hs
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [lintegral_const_mul, lintegral_const_mul'', setLIntegral_condLExp _ _ _ hs]
  all_goals fun_prop

theorem condLExp_smul_le (X : Ω → ℝ≥0∞) {c : ℝ≥0∞} :
    c • P⁻[X|mΩ] ≤ᵐ[P] P⁻[c • X|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀; swap
  · simp_rw [condLExp_of_not_le hm]; filter_upwards; simp
  by_cases hσ : SigmaFinite (P.trim hm); swap
  · simp_rw [condLExp_of_not_sigmaFinite hm hσ]; filter_upwards; simp
  apply ae_le_of_ae_le_trim
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ := P.trim hm) (by fun_prop)
  intro s hs _
  simp [setLIntegral_condLExp_trim _ _ _ hs, lintegral_const_mul _ (measurable_condLExp _ P X),
    lintegral_const_mul_le]

theorem condLExp_smul' (X : Ω → ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    P⁻[c • X|mΩ] =ᵐ[P] c • P⁻[X|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀
  swap; · simp [condLExp_of_not_le hm]
  by_cases hσ : SigmaFinite (P.trim hm)
  swap; · simp [condLExp_of_not_sigmaFinite hm hσ]
  refine (ae_eq_condLExp _ _ _ (by fun_prop) ?_).symm
  intro s hs
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [lintegral_const_mul' _ _ hc, lintegral_const_mul' _ _ hc, setLIntegral_condLExp _ _ _ hs]

section ConditionalProbability

open Set

notation P "⁻⸨ " s "|" mΩ "⸩" => condLExp mΩ P (Set.indicator s 1)

variable {s s₁ s₂ t : Set Ω}

theorem condLProb_le_union (hd : Disjoint s₁ s₂) :
     P⁻⸨s₁| mΩ⸩ + P⁻⸨s₂| mΩ⸩ ≤ᵐ[P] P⁻⸨s₁ ∪ s₂| mΩ⸩ := by
  grw [condLExp_add_le, indicator_union_of_disjoint hd, Pi.add_def]

theorem condLProb_union (hd : Disjoint s₁ s₂) (hs₂ : MeasurableSet[mΩ₀] s₂) :
    P⁻⸨s₁ ∪ s₂| mΩ⸩ =ᵐ[P] P⁻⸨s₁| mΩ⸩ + P⁻⸨s₂| mΩ⸩ := by
  grw [indicator_union_of_disjoint hd, ← condLExp_add_right _ (by measurability), Pi.add_def]

theorem condLProb_union' (hd : Disjoint s₁ s₂) (hs₁ : MeasurableSet[mΩ₀] s₁) :
    P⁻⸨s₁ ∪ s₂| mΩ⸩ =ᵐ[P] P⁻⸨s₁| mΩ⸩ + P⁻⸨s₂| mΩ⸩ := by
  grw [union_comm, condLProb_union hd.symm hs₁, add_comm]

theorem condLProb_le_inter_add_diff : P⁻⸨s ∩ t| mΩ⸩ + P⁻⸨s \ t| mΩ⸩ ≤ᵐ[P] P⁻⸨s| mΩ⸩ := by
  grw [condLProb_le_union disjoint_sdiff_inter.symm]
  filter_upwards using by simp

theorem condLProb_inter_add_diff
    (hs : MeasurableSet[mΩ₀] s) (ht : MeasurableSet[mΩ₀] t) :
    P⁻⸨s ∩ t| mΩ⸩ + P⁻⸨s \ t| mΩ⸩ =ᵐ[P] P⁻⸨s| mΩ⸩ := by
  grw [← condLProb_union disjoint_sdiff_inter.symm (by measurability)]
  simp

theorem condLProb_add_inter (s : Set Ω) (hs : MeasurableSet[mΩ₀] s) (ht : MeasurableSet[mΩ₀] t) :
    P⁻⸨s \ t| mΩ⸩ + P⁻⸨s ∩ t| mΩ⸩ =ᵐ[P] P⁻⸨s| mΩ⸩ := by
  grw [add_comm, condLProb_inter_add_diff hs ht]

theorem condLProb_union_add_inter (s : Set Ω)
    (hs : MeasurableSet[mΩ₀] s) (ht : MeasurableSet[mΩ₀] t) :
    P⁻⸨s ∪ t| mΩ⸩ + P⁻⸨s ∩ t| mΩ⸩ =ᵐ[P] P⁻⸨s| mΩ⸩ + P⁻⸨t| mΩ⸩ := by
  grw [← condLProb_inter_add_diff (by measurability) ht, union_inter_cancel_right,
    union_diff_right, ← condLProb_inter_add_diff hs ht]
  ring_nf
  rfl

-- lemma measure_symmDiff_eq (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
--     μ (s ∆ t) = μ (s \ t) + μ (t \ s) := by
--   simpa only [symmDiff_def, sup_eq_union]
--     using measure_union₀ (ht.diff hs) disjoint_sdiff_sdiff.aedisjoint

-- lemma measure_symmDiff_le (s t u : Set α) :
--     μ (s ∆ u) ≤ μ (s ∆ t) + μ (t ∆ u) :=
--   le_trans (μ.mono <| symmDiff_triangle s t u) (measure_union_le (s ∆ t) (t ∆ u))

-- theorem measure_symmDiff_eq_top (hs : μ s ≠ ∞) (ht : μ t = ∞) : μ (s ∆ t) = ∞ :=
--   measure_mono_top subset_union_right (measure_diff_eq_top ht hs)

theorem condLProb_add_measure_compl (h : MeasurableSet[mΩ₀] s) :
    P⁻⸨s| mΩ⸩ + P⁻⸨sᶜ| mΩ⸩ =ᵐ[P] P⁻⸨univ| mΩ⸩ := by
  grw [← condLProb_union disjoint_compl_right (by measurability)]
  simp

-- theorem measure_biUnion₀ {s : Set β} {f : β → Set α} (hs : s.Countable)
--     (hd : s.Pairwise (AEDisjoint μ on f)) (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) :
--     μ (⋃ b ∈ s, f b) = ∑' p : s, μ (f p) := by
--   haveI := hs.toEncodable
--   rw [biUnion_eq_iUnion]
--   exact measure_iUnion₀ (hd.on_injective Subtype.coe_injective fun x => x.2) fun x => h x x.2

-- theorem measure_biUnion {s : Set β} {f : β → Set α} (hs : s.Countable) (hd : s.PairwiseDisjoint f)
--     (h : ∀ b ∈ s, MeasurableSet (f b)) : μ (⋃ b ∈ s, f b) = ∑' p : s, μ (f p) :=
--   measure_biUnion₀ hs hd.aedisjoint fun b hb => (h b hb).nullMeasurableSet

-- theorem measure_sUnion₀ {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise (AEDisjoint μ))
--     (h : ∀ s ∈ S, NullMeasurableSet s μ) : μ (⋃₀ S) = ∑' s : S, μ s := by
--   rw [sUnion_eq_biUnion, measure_biUnion₀ hs hd h]

-- theorem measure_sUnion {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise Disjoint)
--     (h : ∀ s ∈ S, MeasurableSet s) : μ (⋃₀ S) = ∑' s : S, μ s := by
--   rw [sUnion_eq_biUnion, measure_biUnion hs hd h]

-- set_option backward.isDefEq.respectTransparency false in
-- theorem measure_biUnion_finset₀ {s : Finset ι} {f : ι → Set α}
--     (hd : Set.Pairwise (↑s) (AEDisjoint μ on f)) (hm : ∀ b ∈ s, NullMeasurableSet (f b) μ) :
--     μ (⋃ b ∈ s, f b) = ∑ p ∈ s, μ (f p) := by
--   rw [← Finset.sum_attach, Finset.attach_eq_univ, ← tsum_fintype (L := .unconditional s)]
--   exact measure_biUnion₀ s.countable_toSet hd hm

-- theorem measure_biUnion_finset {s : Finset ι} {f : ι → Set α} (hd : PairwiseDisjoint (↑s) f)
--     (hm : ∀ b ∈ s, MeasurableSet (f b)) : μ (⋃ b ∈ s, f b) = ∑ p ∈ s, μ (f p) :=
--   measure_biUnion_finset₀ hd.aedisjoint fun b hb => (hm b hb).nullMeasurableSet

-- /-- The measure of an a.e. disjoint union (even uncountable) of null-measurable sets is at least
-- the sum of the measures of the sets. -/
-- theorem tsum_meas_le_meas_iUnion_of_disjoint₀ {ι : Type*} {_ : MeasurableSpace α} (μ : Measure α)
--     {As : ι → Set α} (As_mble : ∀ i : ι, NullMeasurableSet (As i) μ)
--     (As_disj : Pairwise (AEDisjoint μ on As)) : (∑' i, μ (As i)) ≤ μ (⋃ i, As i) := by
--   rw [ENNReal.tsum_eq_iSup_sum, iSup_le_iff]
--   intro s
--   simp only [← measure_biUnion_finset₀ (fun _i _hi _j _hj hij => As_disj hij) fun i _ => As_mble i]
--   gcongr
--   exact iUnion_subset fun _ ↦ Subset.rfl

-- /-- The measure of a disjoint union (even uncountable) of measurable sets is at least the sum of
-- the measures of the sets. -/
-- theorem tsum_meas_le_meas_iUnion_of_disjoint {ι : Type*} {_ : MeasurableSpace α} (μ : Measure α)
--     {As : ι → Set α} (As_mble : ∀ i : ι, MeasurableSet (As i))
--     (As_disj : Pairwise (Disjoint on As)) : (∑' i, μ (As i)) ≤ μ (⋃ i, As i) :=
--   tsum_meas_le_meas_iUnion_of_disjoint₀ μ (fun i ↦ (As_mble i).nullMeasurableSet)
--     (fun _ _ h ↦ Disjoint.aedisjoint (As_disj h))

-- /-- If `s` is a countable set, then the measure of its preimage can be found as the sum of measures
-- of the fibers `f ⁻¹' {y}`. -/
-- theorem tsum_measure_preimage_singleton {s : Set β} (hs : s.Countable) {f : α → β}
--     (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) : (∑' b : s, μ (f ⁻¹' {↑b})) = μ (f ⁻¹' s) := by
--   rw [← Set.biUnion_preimage_singleton, measure_biUnion hs (pairwiseDisjoint_fiber f s) hf]

-- lemma measure_preimage_eq_zero_iff_of_countable {s : Set β} {f : α → β} (hs : s.Countable) :
--     μ (f ⁻¹' s) = 0 ↔ ∀ x ∈ s, μ (f ⁻¹' {x}) = 0 := by
  -- rw [← biUnion_preimage_singleton, measure_biUnion_null_iff hs]

/-- If `s` is a `Finset`, then the measure of its preimage can be found as the sum of measures
of the fibers `f ⁻¹' {y}`. -/
-- theorem sum_measure_preimage_singleton (s : Finset β) {f : α → β}
--     (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) : (∑ b ∈ s, μ (f ⁻¹' {b})) = μ (f ⁻¹' ↑s) := by
--   simp only [← measure_biUnion_finset (pairwiseDisjoint_fiber f s) hf,
--     Finset.set_biUnion_preimage_singleton]

-- @[simp] lemma sum_measure_singleton {s : Finset α} [MeasurableSingletonClass α] :
--     ∑ x ∈ s, μ {x} = μ s := by
--   trans ∑ x ∈ s, μ (id ⁻¹' {x})
--   · simp
--   rw [sum_measure_preimage_singleton]
--   · simp
--   · simp

-- theorem measure_diff_null' (h : μ (s₁ ∩ s₂) = 0) : μ (s₁ \ s₂) = μ s₁ :=
--   measure_congr <| diff_ae_eq_self.2 h

-- theorem measure_add_diff (hs : NullMeasurableSet s μ) (t : Set α) :
--     μ s + μ (t \ s) = μ (s ∪ t) := by
--   rw [← measure_union₀' hs disjoint_sdiff_right.aedisjoint, union_diff_self]

-- theorem measure_diff' (s : Set α) (hm : NullMeasurableSet t μ) (h_fin : μ t ≠ ∞) :
--     μ (s \ t) = μ (s ∪ t) - μ t :=
--   ENNReal.eq_sub_of_add_eq h_fin <| by rw [add_comm, measure_add_diff hm, union_comm]
theorem le_condLProb_diff (hs₂ : MeasurableSet[mΩ₀] s₂) :
    P⁻⸨s₁| mΩ⸩ - P⁻⸨s₂| mΩ⸩ ≤ᵐ[P] P⁻⸨s₁ \ s₂| mΩ⸩ := by
  have := condLProb_union (P := P) (mΩ := mΩ) (s₁ := s₁ \ s₂) (s₂ := s₂) (by sorry) hs₂
  filter_upwards [this] with ω hω
  simp at hω
  simp [← hω]
  --grw [tsub_le_iff_left]

theorem condLProb_diff (h : s₂ ⊆ s₁) (hs₁ : MeasurableSet[mΩ₀] s₁) (hs₂ : MeasurableSet[mΩ₀] s₂) :
    P⁻⸨s₁ \ s₂| mΩ⸩ =ᵐ[P] P⁻⸨s₁| mΩ⸩ - P⁻⸨s₂| mΩ⸩ := by
  sorry

-- theorem measure_diff (h : s₂ ⊆ s₁) (h₂ : NullMeasurableSet s₂ μ) (h_fin : μ s₂ ≠ ∞) :
--     μ (s₁ \ s₂) = μ s₁ - μ s₂ := by rw [measure_diff' _ h₂ h_fin, union_eq_self_of_subset_right h]

-- theorem le_measure_diff : μ s₁ - μ s₂ ≤ μ (s₁ \ s₂) :=
--   tsub_le_iff_left.2 <| (measure_le_inter_add_diff μ s₁ s₂).trans <| by
--     gcongr; apply inter_subset_right

-- theorem le_measure_symmDiff : μ s₁ - μ s₂ ≤ μ (s₁ ∆ s₂) :=
--   le_trans le_measure_diff (measure_mono <| by simp [symmDiff_def])

end ConditionalProbability

end MeasureTheory
