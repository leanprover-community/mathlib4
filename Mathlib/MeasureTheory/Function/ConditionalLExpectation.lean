/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
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

open scoped ENNReal Function

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

theorem condLExp_tsum {ι : Type*} [Countable ι] (X : ι → Ω → ℝ≥0∞)
    (hX : ∀ i, AEMeasurable (X i) P) :
    P⁻[∑' i, X i|mΩ] =ᵐ[P] ∑' i, P⁻[X i|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀; swap
  · simp_rw [condLExp_of_not_le hm]; filter_upwards; simp
  by_cases hσ : SigmaFinite (P.trim hm); swap
  · simp_rw [condLExp_of_not_sigmaFinite hm hσ]; filter_upwards; simp
  refine (ae_eq_condLExp _ _ _ (by fun_prop) ?_).symm
  intro s hs
  simp only [ENNReal.tsum_apply]
  repeat rw [lintegral_tsum (by measurability)]
  congr with i
  exact setLIntegral_condLExp hm P (X i) hs

section ConditionalProbability

open Set

noncomputable
def condLProb (mΩ : MeasurableSpace Ω) (P : Measure[mΩ₀] Ω) (s : Set Ω) : Ω → ℝ≥0∞ :=
  P⁻[s.indicator 1| mΩ]

scoped macro:max P:term noWs "⁻⸨" s:term "|" mΩ:term "⸩" : term =>
  `(condLProb $mΩ $P $s)

/-- Unexpander for `P⁻⸨f|m⸩` notation. -/
@[app_unexpander MeasureTheory.condLProb]
meta def condLProbUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $mΩ $P $X) => `($P⁻⸨$X|$mΩ⸩)
  | _ => throw ()

lemma condLProb_def (mΩ : MeasurableSpace Ω) (P : Measure[mΩ₀] Ω) (s : Set Ω) :
  P⁻⸨s|mΩ⸩ = P⁻[s.indicator 1| mΩ] := by rfl

lemma condLProb_of_not_le (hm_not : ¬mΩ ≤ mΩ₀) (s : Set Ω) :
  P⁻⸨s|mΩ⸩ = 0 := by rw [condLProb_def, condLExp_of_not_le hm_not]

lemma condLProb_of_not_sigmaFinite (hm : mΩ ≤ mΩ₀) (hμm_not : ¬SigmaFinite (P.trim hm))
  (s : Set Ω) : P⁻⸨s|mΩ⸩ = 0 := by rw [condLProb_def, condLExp_of_not_sigmaFinite hm hμm_not]

theorem condLProb_bot'₀ [NeZero P] {s : Set Ω} (hs : NullMeasurableSet[mΩ₀] s P) :
    P⁻⸨s|⊥⸩ = fun _ => (P .univ)⁻¹ * P s := by
  grw [condLProb_def, condLExp_bot', lintegral_indicator_one₀ hs, smul_eq_mul]

theorem condLProb_bot_ae_eq₀ {s : Set Ω} (hs : NullMeasurableSet[mΩ₀] s P) :
    P⁻⸨s|⊥⸩ =ᵐ[P] fun _ => (P .univ)⁻¹ * P s := by
  grw [condLProb_def, condLExp_bot_ae_eq, lintegral_indicator_one₀ hs, smul_eq_mul]

theorem condLProb_bot₀ [IsProbabilityMeasure P] {s : Set Ω} (hs : NullMeasurableSet[mΩ₀] s P) :
    P⁻⸨s|⊥⸩ = fun _ => P s := by
  grw [condLProb_def, condLExp_bot, lintegral_indicator_one₀ hs]

theorem condLProb_bot' [NeZero P] {s : Set Ω} (hs : MeasurableSet[mΩ₀] s) :
    P⁻⸨s|⊥⸩ = fun _ => (P .univ)⁻¹ * P s :=
  condLProb_bot'₀ hs.nullMeasurableSet

theorem condLProb_bot_ae_eq {s : Set Ω} (hs : MeasurableSet[mΩ₀] s) :
    P⁻⸨s|⊥⸩ =ᵐ[P] fun _ => (P .univ)⁻¹ * P s :=
  condLProb_bot_ae_eq₀ hs.nullMeasurableSet

theorem condLProb_bot [IsProbabilityMeasure P] {s : Set Ω} (hs : MeasurableSet[mΩ₀] s) :
    P⁻⸨s| ⊥⸩ = fun _ => P s :=
  condLProb_bot₀ hs.nullMeasurableSet

@[gcongr]
theorem condLProb_congr_ae {P : Measure[mΩ₀] Ω} {s t : Set Ω} (hst : s =ᵐ[P] t) :
    P⁻⸨s|mΩ⸩ =ᵐ[P] P⁻⸨t|mΩ⸩ := by
  -- should be a indicator_congr_ae lemma ?
  sorry

variable {s s₁ s₂ t : Set Ω}

theorem condLProb_le_union (hd : Disjoint s₁ s₂) :
     P⁻⸨s₁| mΩ⸩ + P⁻⸨s₂| mΩ⸩ ≤ᵐ[P] P⁻⸨s₁ ∪ s₂| mΩ⸩ := by
  simp only [condLProb_def]
  grw [condLExp_add_le, indicator_union_of_disjoint hd, Pi.add_def]

theorem condLProb_union₀ (hd : Disjoint s₁ s₂) (hs₂ : NullMeasurableSet[mΩ₀] s₂ P) :
    P⁻⸨s₁ ∪ s₂| mΩ⸩ =ᵐ[P] P⁻⸨s₁| mΩ⸩ + P⁻⸨s₂| mΩ⸩ := by
  simp only [condLProb_def]
  grw [indicator_union_of_disjoint hd, ← condLExp_add_right _ (by measurability), Pi.add_def]

theorem condLProb_union'₀ (hd : Disjoint s₁ s₂) (hs₁ : NullMeasurableSet[mΩ₀] s₁ P) :
    P⁻⸨s₁ ∪ s₂| mΩ⸩ =ᵐ[P] P⁻⸨s₁| mΩ⸩ + P⁻⸨s₂| mΩ⸩ := by
  grw [union_comm, condLProb_union₀ hd.symm hs₁, add_comm]

theorem condLProb_union (hd : Disjoint s₁ s₂) (hs₂ : MeasurableSet[mΩ₀] s₂) :
    P⁻⸨s₁ ∪ s₂| mΩ⸩ =ᵐ[P] P⁻⸨s₁| mΩ⸩ + P⁻⸨s₂| mΩ⸩ :=
  condLProb_union₀ hd hs₂.nullMeasurableSet

theorem condLProb_union' (hd : Disjoint s₁ s₂) (hs₁ : MeasurableSet[mΩ₀] s₁) :
    P⁻⸨s₁ ∪ s₂| mΩ⸩ =ᵐ[P] P⁻⸨s₁| mΩ⸩ + P⁻⸨s₂| mΩ⸩ :=
  condLProb_union'₀ hd hs₁.nullMeasurableSet

theorem condLProb_le_inter_add_diff : P⁻⸨s ∩ t| mΩ⸩ + P⁻⸨s \ t| mΩ⸩ ≤ᵐ[P] P⁻⸨s| mΩ⸩ := by
  grw [condLProb_le_union disjoint_sdiff_inter.symm]
  filter_upwards using by simp

theorem condLProb_inter_add_diff₀
    (hs : NullMeasurableSet[mΩ₀] s P) (ht : NullMeasurableSet[mΩ₀] t P) :
    P⁻⸨s ∩ t| mΩ⸩ + P⁻⸨s \ t| mΩ⸩ =ᵐ[P] P⁻⸨s| mΩ⸩ := by
  grw [← condLProb_union₀ disjoint_sdiff_inter.symm (by measurability)]
  simp

theorem condLProb_inter_add_diff
    (hs : MeasurableSet[mΩ₀] s) (ht : MeasurableSet[mΩ₀] t) :
    P⁻⸨s ∩ t| mΩ⸩ + P⁻⸨s \ t| mΩ⸩ =ᵐ[P] P⁻⸨s| mΩ⸩ :=
  condLProb_inter_add_diff₀ hs.nullMeasurableSet ht.nullMeasurableSet

theorem condLProb_add_inter₀ (hs : NullMeasurableSet[mΩ₀] s P)
    (ht : NullMeasurableSet[mΩ₀] t P) :
    P⁻⸨s \ t| mΩ⸩ + P⁻⸨s ∩ t| mΩ⸩ =ᵐ[P] P⁻⸨s| mΩ⸩ := by
  grw [add_comm, condLProb_inter_add_diff₀ hs ht]

theorem condLProb_add_inter (hs : MeasurableSet[mΩ₀] s) (ht : MeasurableSet[mΩ₀] t) :
    P⁻⸨s \ t| mΩ⸩ + P⁻⸨s ∩ t| mΩ⸩ =ᵐ[P] P⁻⸨s| mΩ⸩ :=
  condLProb_add_inter₀ hs.nullMeasurableSet ht.nullMeasurableSet

theorem condLProb_union_add_inter₀
    (hs : NullMeasurableSet[mΩ₀] s P) (ht : NullMeasurableSet[mΩ₀] t P) :
    P⁻⸨s ∪ t| mΩ⸩ + P⁻⸨s ∩ t| mΩ⸩ =ᵐ[P] P⁻⸨s| mΩ⸩ + P⁻⸨t| mΩ⸩ := by
  grw [← condLProb_inter_add_diff₀ (by measurability) ht, union_inter_cancel_right,
    union_diff_right, ← condLProb_inter_add_diff₀ hs ht]
  ring_nf
  rfl

theorem condLProb_union_add_inter (hs : MeasurableSet[mΩ₀] s) (ht : MeasurableSet[mΩ₀] t) :
    P⁻⸨s ∪ t| mΩ⸩ + P⁻⸨s ∩ t| mΩ⸩ =ᵐ[P] P⁻⸨s| mΩ⸩ + P⁻⸨t| mΩ⸩ :=
  condLProb_union_add_inter₀ hs.nullMeasurableSet ht.nullMeasurableSet

@[simp]
theorem condLProb_empty (P : Measure[mΩ₀] Ω) :
    P⁻⸨∅| mΩ⸩ = 0 := by
  simp [condLProb_def, ← Pi.zero_def]

@[simp]
theorem condLProb_univ (P : Measure[mΩ₀] Ω) (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)] :
    P⁻⸨univ| mΩ⸩ = 1 := by
  simp [condLProb_def, indicator_univ, hm]

theorem condLProb_le_one (P : Measure[mΩ₀] Ω) (s : Set Ω) : P⁻⸨s| mΩ⸩ ≤ᵐ[P] 1 := by
  by_cases hm : mΩ ≤ mΩ₀
  swap; · filter_upwards using by simp [condLProb_of_not_le hm]
  by_cases hσ : SigmaFinite (P.trim hm)
  swap; · filter_upwards using by simp [condLProb_of_not_sigmaFinite hm hσ]
  rw [← condLProb_univ P hm]
  apply condLExp_mono
  filter_upwards with _ using by apply indicator_le_indicator_of_subset (by simp) (by positivity)

theorem condLProb_add_condLProb_compl₀ (mΩ : MeasurableSpace Ω) (hs : NullMeasurableSet[mΩ₀] s P) :
    P⁻⸨s| mΩ⸩ + P⁻⸨sᶜ| mΩ⸩ =ᵐ[P] P⁻⸨univ| mΩ⸩ := by
  grw [← condLProb_union₀ disjoint_compl_right (by measurability)]
  simp

theorem condLProb_add_condLProb_compl (mΩ : MeasurableSpace Ω) (hs : MeasurableSet[mΩ₀] s) :
    P⁻⸨s| mΩ⸩ + P⁻⸨sᶜ| mΩ⸩ =ᵐ[P] P⁻⸨univ| mΩ⸩ :=
  condLProb_add_condLProb_compl₀ mΩ hs.nullMeasurableSet

theorem condLProb_compl'₀ (mΩ : MeasurableSpace Ω) (hs : NullMeasurableSet[mΩ₀] s P) :
    P⁻⸨sᶜ| mΩ⸩ =ᵐ[P] P⁻⸨univ| mΩ⸩ - P⁻⸨s| mΩ⸩ := by
  by_cases hm : mΩ ≤ mΩ₀
  swap; · filter_upwards using by simp [condLProb_of_not_le hm]
  by_cases hσ : SigmaFinite (P.trim hm)
  swap; · filter_upwards using by simp [condLProb_of_not_sigmaFinite hm hσ]
  filter_upwards [condLProb_add_condLProb_compl₀ mΩ hs] with _ h'
  apply ENNReal.eq_sub_of_add_eq'
  · simp [condLProb_univ, hm]
  · simp [← Pi.add_apply, h', add_comm]

theorem condLProb_compl' (mΩ : MeasurableSpace Ω) (hs : MeasurableSet[mΩ₀] s) :
    P⁻⸨sᶜ| mΩ⸩ =ᵐ[P] P⁻⸨univ| mΩ⸩ - P⁻⸨s| mΩ⸩ :=
  condLProb_compl'₀ mΩ hs.nullMeasurableSet

theorem condLProb_compl₀ (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hs : NullMeasurableSet[mΩ₀] s P) : P⁻⸨sᶜ| mΩ⸩ =ᵐ[P] 1 - P⁻⸨s| mΩ⸩ := by
  grw [condLProb_compl'₀ _ hs, condLProb_univ P hm]

theorem condLProb_compl (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)] (hs : MeasurableSet[mΩ₀] s) :
    P⁻⸨sᶜ| mΩ⸩ =ᵐ[P] 1 - P⁻⸨s| mΩ⸩ :=
  condLProb_compl₀ hm hs.nullMeasurableSet

-- in PR #34138

variable {α β γ δ : Type*}

lemma Function.support_subsingleton_of_disjoint [Zero β] {s : δ → Set α} (f : α → β)
    (hs : Pairwise (Disjoint on s)) (i : α) [DecidablePred (fun d => i ∈ s d)] (j : δ)
    (hj : i ∈ s j) : Function.support (fun d ↦ if i ∈ s d then f i else 0) ⊆ {j} := by
  intro d
  simp_rw [Set.mem_singleton_iff, Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp]
  rw [← not_imp_not]
  intro hd e
  obtain r := Set.disjoint_iff_inter_eq_empty.mp (hs hd)
  revert r
  change s d ∩ s j ≠ ∅
  rw [← Set.nonempty_iff_ne_empty, Set.nonempty_def]
  exact ⟨i, ⟨e.1, hj⟩⟩

lemma Set.indicator_iUnion_of_disjoint [AddCommMonoid β] [TopologicalSpace β]
    (s : δ → Set α) (hs : Pairwise (Disjoint on s)) (f : α → β) (i : α) :
    (⋃ d, s d).indicator f i = ∑' d, (s d).indicator f i := by
  classical
  simp only [Set.indicator, Set.mem_iUnion]
  by_cases h₀ : ∃ d, i ∈ s d <;> simp only [h₀, ↓reduceIte]
  · obtain ⟨j, hj⟩ := h₀
    rw [← tsum_subtype_eq_of_support_subset (s := {j})]
    · simp only [tsum_fintype, Finset.univ_unique, Set.default_coe_singleton, Finset.sum_singleton,
      left_eq_ite_iff]
      exact fun h ↦ False.elim (h hj)
    · apply (Function.support_subsingleton_of_disjoint f hs i j hj)
  · push_neg at h₀
    simp_rw [if_neg (h₀ _), tsum_zero]

lemma Set.indicator_iUnion_of_disjoint' [AddCommMonoid β] [TopologicalSpace β]
    (s : δ → Set α) (hs : Pairwise (Disjoint on s)) (f : α → β) :
    (⋃ d, s d).indicator f = fun i ↦ ∑' d, (s d).indicator f i := by
  ext i
  simp [Set.indicator_iUnion_of_disjoint, hs]

--

theorem condLProb_iUnion {ι : Type*} [Countable ι] {f : ι → Set Ω}
    (hn : Pairwise (Disjoint on f)) (h : ∀ i, MeasurableSet[mΩ₀] (f i)) :
    P⁻⸨⋃ i, f i| mΩ⸩ =ᵐ[P] ∑' i, P⁻⸨f i| mΩ⸩ := by
  simp only [condLProb_def, Set.indicator_iUnion_of_disjoint' _ hn, ← ENNReal.tsum_apply]
  grw [← condLExp_tsum _ (fun i ↦ AEMeasurable.indicator (by fun_prop) (h i))]

#check measure_iUnion₀
theorem condLProb_iUnion₀ {ι : Type*} [Countable ι] {f : ι → Set Ω}
    (hn : Pairwise (AEDisjoint P on f)) (h : ∀ i, NullMeasurableSet[mΩ₀] (f i) P) :
    P⁻⸨⋃ i, f i| mΩ⸩ =ᵐ[P] ∑' i, P⁻⸨f i| mΩ⸩ := by
  rcases exists_subordinate_pairwise_disjoint h hn with ⟨t, _ht_sub, ht_eq, htm, htd⟩
  have h1 : P⁻⸨⋃ i, f i|mΩ⸩ =ᵐ[P] P⁻⸨⋃ i, t i|mΩ⸩ := by
    exact condLProb_congr_ae (EventuallyEq.countable_iUnion ht_eq)
  have h2 : ∑' i, P⁻⸨f i| mΩ⸩ =ᵐ[P] ∑' i, P⁻⸨t i| mΩ⸩ := by
    have : ∀ᵐ ω ∂P, ∀ i, P⁻⸨f i| mΩ⸩ ω = P⁻⸨t i| mΩ⸩ ω := by
      simpa [ae_all_iff] using fun i ↦ condLProb_congr_ae (ht_eq i)
    filter_upwards [this] with ω hω
    simp only [ENNReal.tsum_apply]
    congr with i
    simp [hω]
  calc
    P⁻⸨⋃ i, f i|mΩ⸩ =ᵐ[P] P⁻⸨⋃ i, t i|mΩ⸩ := by exact h1
                  _ =ᵐ[P] ∑' i, P⁻⸨t i| mΩ⸩ := condLProb_iUnion htd htm
                  _ =ᵐ[P] ∑' i, P⁻⸨f i| mΩ⸩ := by exact h2.symm

-- theorem measure_biUnion₀ {s : Set β} {f : β → Set α} (hs : s.Countable)
--     (hd : s.Pairwise (AEDisjoint μ on f)) (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) :
--     μ (⋃ b ∈ s, f b) = ∑' p : s, μ (f p) := by
--   haveI := hs.toEncodable
--   rw [biUnion_eq_iUnion]
--   exact measure_iUnion₀ (hd.on_injective Subtype.coe_injective fun x => x.2) fun x => h x x.2

-- theorem measure_biUnion {s : Set β} {f : β → Set α} (hs : s.Countable) (hd : s.PairwiseDisjoint f)
--     (h : ∀ b ∈ s, MeasurableSet (f b)) : μ (⋃ b ∈ s, f b) = ∑' p : s, μ (f p) :=
--   measure_biUnion₀ hs hd.aedisjoint fun b hb => (h b hb).nullMeasurableSet

theorem le_condLProb_diff (hs₂ : MeasurableSet[mΩ₀] s₂) :
    P⁻⸨s₁| mΩ⸩ - P⁻⸨s₂| mΩ⸩ ≤ᵐ[P] P⁻⸨s₁ \ s₂| mΩ⸩ := by
  have h : P⁻⸨s₁| mΩ⸩ ≤ᵐ[P] P⁻⸨s₁ ∪ s₂| mΩ⸩ := by
    apply condLExp_mono
    filter_upwards with _
    apply indicator_le_indicator_of_subset subset_union_left (zero_le 1)
  have h' : P⁻⸨s₁ \ s₂| mΩ⸩ + P⁻⸨s₂| mΩ⸩ =ᵐ[P] P⁻⸨s₁ ∪ s₂| mΩ⸩ := by
    grw [← condLProb_union (by grind) hs₂]
    simp
  filter_upwards [h,h'] with ω h h'
  simp only [Pi.add_apply] at h'
  simp [h, h']

theorem condLProb_diff (h : s₂ ⊆ s₁) (hs₂ : MeasurableSet[mΩ₀] s₂) :
    P⁻⸨s₁ \ s₂| mΩ⸩ =ᵐ[P] P⁻⸨s₁| mΩ⸩ - P⁻⸨s₂| mΩ⸩ := by
  have h' : P⁻⸨s₁ \ s₂| mΩ⸩ + P⁻⸨s₂| mΩ⸩ =ᵐ[P] P⁻⸨s₁ ∪ s₂| mΩ⸩ := by
    grw [← condLProb_union (by grind) hs₂]
    simp
  filter_upwards [h', condLProb_le_one P s₁] with ω h1 h2
  apply ENNReal.eq_sub_of_add_eq'
  · exact ne_top_of_le_ne_top (by simp) h2
  simpa [union_eq_left.mpr h] using h1

end ConditionalProbability

end MeasureTheory
