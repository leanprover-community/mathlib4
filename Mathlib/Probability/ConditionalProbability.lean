/-
Copyright (c) 2022 Rishikesh Vaishnav. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rishikesh Vaishnav
-/
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Conditional Probability

This file defines conditional probability and includes basic results relating to it.

Given some measure `μ` defined on a measure space on some type `Ω` and some `s : Set Ω`,
we define the measure of `μ` conditioned on `s` as the restricted measure scaled by
the inverse of the measure of `s`: `cond μ s = (μ s)⁻¹ • μ.restrict s`. The scaling
ensures that this is a probability measure (when `μ` is a finite measure).

From this definition, we derive the "axiomatic" definition of conditional probability
based on application: for any `s t : Set Ω`, we have `μ[t|s] = (μ s)⁻¹ * μ (s ∩ t)`.

## Main Statements

* `cond_cond_eq_cond_inter`: conditioning on one set and then another is equivalent
  to conditioning on their intersection.
* `cond_eq_inv_mul_cond_mul`: Bayes' Theorem, `μ[t|s] = (μ s)⁻¹ * μ[s|t] * (μ t)`.

## Notation

This file uses the notation `μ[|s]` the measure of `μ` conditioned on `s`,
and `μ[t|s]` for the probability of `t` given `s` under `μ` (equivalent to the
application `μ[|s] t`).

These notations are contained in the scope `ProbabilityTheory`.

## Implementation notes

Because we have the alternative measure restriction application principles
`Measure.restrict_apply` and `Measure.restrict_apply'`, which require
measurability of the restricted and restricting sets, respectively,
many of the theorems here will have corresponding alternatives as well.
For the sake of brevity, we've chosen to only go with `Measure.restrict_apply'`
for now, but the alternative theorems can be added if needed.

Use of `@[simp]` generally follows the rule of removing conditions on a measure
when possible.

Hypotheses that are used to "define" a conditional distribution by requiring that
the conditioning set has non-zero measure should be named using the abbreviation
"c" (which stands for "conditionable") rather than "nz". For example `(hci : μ (s ∩ t) ≠ 0)`
(rather than `hnzi`) should be used for a hypothesis ensuring that `μ[|s ∩ t]` is defined.

## Tags

conditional, conditioned, bayes
-/

noncomputable section

open ENNReal MeasureTheory MeasureTheory.Measure MeasurableSpace Set

variable {Ω Ω' α : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {μ : Measure Ω}
  {s t : Set Ω}

namespace ProbabilityTheory

variable (μ) in
/-- The conditional probability measure of measure `μ` on set `s` is `μ` restricted to `s`
and scaled by the inverse of `μ s` (to make it a probability measure):
`(μ s)⁻¹ • μ.restrict s`. -/
def cond (s : Set Ω) : Measure Ω :=
  (μ s)⁻¹ • μ.restrict s

@[inherit_doc ProbabilityTheory.cond]
scoped macro:max μ:term noWs "[|" s:term "]" : term =>
  `(ProbabilityTheory.cond $μ $s)
@[inherit_doc cond]
scoped macro:max μ:term noWs "[" t:term " | " s:term "]" : term =>
  `(ProbabilityTheory.cond $μ $s $t)

/-!
We can't use `notation` or `notation3` as it does not support `noWs`, and so we have to write
our own delaborators.
-/

section delaborators
open Lean PrettyPrinter.Delaborator SubExpr

/-- Unexpander for `μ[|s]` notation. -/
@[app_unexpander ProbabilityTheory.cond]
def condUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $μ $s) => `($μ[|$s])
  | _ => throw ()

/-- info: μ[|s] : Measure Ω -/
#guard_msgs in
#check μ[|s]

/-- Delaborator for `μ[t|s]` notation. -/
@[app_delab DFunLike.coe]
def delabCondApplied : Delab :=
  whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 6 do
    let e ← getExpr
    guard <| e.isAppOfArity' ``DFunLike.coe 6
    guard <| (e.getArg!' 4).isAppOf' ``ProbabilityTheory.cond
    let t ← withAppArg delab
    withAppFn <| withAppArg do
      let μ ← withNaryArg 2 delab
      let s ← withNaryArg 3 delab
      `($μ[$t|$s])

/-- info: μ[t | s] : ℝ≥0∞ -/
#guard_msgs in
#check μ[t | s]
/-- info: μ[t | s] : ℝ≥0∞ -/
#guard_msgs in
#check μ[|s] t

end delaborators

/-- The conditional probability measure of measure `μ` on `{ω | X ω ∈ s}`.

It is `μ` restricted to `{ω | X ω ∈ s}` and scaled by the inverse of `μ {ω | X ω ∈ s}`
(to make it a probability measure): `(μ {ω | X ω ∈ s})⁻¹ • μ.restrict {ω | X ω ∈ s}`. -/
scoped macro:max μ:term noWs "[|" X:term " in " s:term "]" : term => `($μ[|$X ⁻¹' $s])

/-- The conditional probability measure of measure `μ` on set `{ω | X ω = x}`.

It is `μ` restricted to `{ω | X ω = x}` and scaled by the inverse of `μ {ω | X ω = x}`
(to make it a probability measure): `(μ {ω | X ω = x})⁻¹ • μ.restrict {ω | X ω = x}`. -/
scoped macro:max μ:term noWs "[" s:term " | " X:term " in " t:term "]" : term =>
  `($μ[$s | $X ⁻¹' $t])

/-- The conditional probability measure of measure `μ` on `{ω | X ω = x}`.

It is `μ` restricted to `{ω | X ω = x}` and scaled by the inverse of `μ {ω | X ω = x}`
(to make it a probability measure): `(μ {ω | X ω = x})⁻¹ • μ.restrict {ω | X ω = x}`. -/
scoped macro:max μ:term noWs "[|" X:term " ← " x:term "]" : term => `($μ[|$X in {$x:term}])

/-- The conditional probability measure of measure `μ` on set `{ω | X ω = x}`.

It is `μ` restricted to `{ω | X ω = x}` and scaled by the inverse of `μ {ω | X ω = x}`
(to make it a probability measure): `(μ {ω | X ω = x})⁻¹ • μ.restrict {ω | X ω = x}`. -/
scoped macro:max μ:term noWs "[" s:term " | " X:term " ← " x:term "]" : term =>
  `($μ[$s | $X in {$x:term}])

/-- The conditional probability measure of any measure on any set of finite positive measure
is a probability measure. -/
theorem cond_isProbabilityMeasure_of_finite (hcs : μ s ≠ 0) (hs : μ s ≠ ∞) :
    IsProbabilityMeasure μ[|s] :=
  ⟨by
    unfold ProbabilityTheory.cond
    simp only [Measure.coe_smul, Pi.smul_apply, MeasurableSet.univ, Measure.restrict_apply,
      Set.univ_inter, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hcs hs⟩

/-- The conditional probability measure of any finite measure on any set of positive measure
is a probability measure. -/
theorem cond_isProbabilityMeasure [IsFiniteMeasure μ] (hcs : μ s ≠ 0) :
    IsProbabilityMeasure μ[|s] := cond_isProbabilityMeasure_of_finite hcs (measure_ne_top μ s)

instance : IsZeroOrProbabilityMeasure μ[|s] := by
  constructor
  simp only [cond, Measure.coe_smul, Pi.smul_apply, MeasurableSet.univ, Measure.restrict_apply,
    univ_inter, smul_eq_mul, ← ENNReal.div_eq_inv_mul]
  rcases eq_or_ne (μ s) 0 with h | h
  · simp [h]
  rcases eq_or_ne (μ s) ∞ with h' | h'
  · simp [h']
  simp [ENNReal.div_self h h']

variable (μ) in
theorem cond_toMeasurable_eq :
    μ[|(toMeasurable μ s)] = μ[|s] := by
  unfold cond
  by_cases hnt : μ s = ∞
  · simp [hnt]
  · simp [Measure.restrict_toMeasurable hnt]

lemma cond_absolutelyContinuous : μ[|s] ≪ μ :=
  smul_absolutelyContinuous.trans restrict_le_self.absolutelyContinuous

lemma absolutelyContinuous_cond_univ [IsFiniteMeasure μ] : μ ≪ μ[|univ] := by
  rw [cond, restrict_univ]
  refine absolutelyContinuous_smul ?_
  simp [measure_ne_top]

lemma ae_cond_of_forall_mem (hs : MeasurableSet s) {p : Ω → Prop} (h : ∀ x ∈ s, p x) :
    ∀ᵐ x ∂μ[|s], p x := ae_smul_measure (ae_restrict_of_forall_mem hs h) _

lemma ae_cond_mem₀ (hs : NullMeasurableSet s μ) : ∀ᵐ x ∂μ[|s], x ∈ s :=
  ae_smul_measure (ae_restrict_mem₀ hs) _

lemma ae_cond_mem (hs : MeasurableSet s) : ∀ᵐ x ∂μ[|s], x ∈ s :=
  ae_smul_measure (ae_restrict_mem hs) _

section Bayes

variable (μ) in
@[simp] lemma cond_empty : μ[|∅] = 0 := by simp [cond]

variable (μ) in
@[simp] lemma cond_univ [IsProbabilityMeasure μ] : μ[|Set.univ] = μ := by
  simp [cond, measure_univ, Measure.restrict_univ]

@[simp] lemma cond_eq_zero : μ[|s] = 0 ↔ μ s = ∞ ∨ μ s = 0 := by simp [cond]

lemma cond_eq_zero_of_meas_eq_zero (hμs : μ s = 0) : μ[|s] = 0 := by simp [hμs]

/-- The axiomatic definition of conditional probability derived from a measure-theoretic one. -/
theorem cond_apply (hms : MeasurableSet s) (μ : Measure Ω) (t : Set Ω) :
    μ[t|s] = (μ s)⁻¹ * μ (s ∩ t) := by
  rw [cond, Measure.smul_apply, Measure.restrict_apply' hms, Set.inter_comm, smul_eq_mul]

theorem cond_apply' (ht : MeasurableSet t) (μ : Measure Ω) : μ[t|s] = (μ s)⁻¹ * μ (s ∩ t) := by
  rw [cond, Measure.smul_apply, Measure.restrict_apply ht, Set.inter_comm, smul_eq_mul]

@[simp] lemma cond_apply_self (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) : μ[s|s] = 1 := by
  simpa [cond] using ENNReal.inv_mul_cancel hs₀ hs

theorem cond_inter_self (hms : MeasurableSet s) (t : Set Ω) (μ : Measure Ω) :
    μ[s ∩ t|s] = μ[t|s] := by
  rw [cond_apply hms, ← Set.inter_assoc, Set.inter_self, ← cond_apply hms]

theorem inter_pos_of_cond_ne_zero (hms : MeasurableSet s) (hcst : μ[t | s] ≠ 0) :
    0 < μ (s ∩ t) := by
  refine pos_iff_ne_zero.mpr (right_ne_zero_of_mul (a := (μ s)⁻¹) ?_)
  convert hcst
  simp [hms, Set.inter_comm, cond]

lemma cond_pos_of_inter_ne_zero [IsFiniteMeasure μ] (hms : MeasurableSet s) (hci : μ (s ∩ t) ≠ 0) :
    0 < μ[t | s] := by
  rw [cond_apply hms]
  refine ENNReal.mul_pos ?_ hci
  exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)

lemma cond_cond_eq_cond_inter' (hms : MeasurableSet s) (hmt : MeasurableSet t) (hcs : μ s ≠ ∞) :
    μ[|s][|t] = μ[|s ∩ t] := by
  ext u
  obtain hst | hst := eq_or_ne (μ (s ∩ t)) 0
  · have : μ (s ∩ t ∩ u) = 0 := measure_mono_null Set.inter_subset_left hst
    simp [cond_apply, *, ← Set.inter_assoc]
  · have hs : μ s ≠ 0 := (measure_pos_of_superset Set.inter_subset_left hst).ne'
    simp [*, hms.inter hmt, cond_apply, ← Set.inter_assoc, ENNReal.mul_inv, ← mul_assoc,
      mul_comm _ (μ s)⁻¹, ENNReal.inv_mul_cancel]

/-- Conditioning first on `s` and then on `t` results in the same measure as conditioning
on `s ∩ t`. -/
theorem cond_cond_eq_cond_inter (hms : MeasurableSet s) (hmt : MeasurableSet t) (μ : Measure Ω)
    [IsFiniteMeasure μ] : μ[|s][|t] = μ[|s ∩ t] :=
  cond_cond_eq_cond_inter' hms hmt (measure_ne_top μ s)

theorem cond_mul_eq_inter' (hms : MeasurableSet s) (hcs' : μ s ≠ ∞) (t : Set Ω) :
    μ[t|s] * μ s = μ (s ∩ t) := by
  obtain hcs | hcs := eq_or_ne (μ s) 0
  · simp [hcs, measure_inter_null_of_null_left]
  · rw [cond_apply hms, mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hcs hcs', one_mul]

theorem cond_mul_eq_inter (hms : MeasurableSet s) (t : Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ] :
    μ[t|s] * μ s = μ (s ∩ t) := cond_mul_eq_inter' hms (measure_ne_top _ s) t

/-- A version of the law of total probability. -/
theorem cond_add_cond_compl_eq (hms : MeasurableSet s) (μ : Measure Ω) [IsFiniteMeasure μ] :
    μ[t|s] * μ s + μ[t|sᶜ] * μ sᶜ = μ t := by
  rw [cond_mul_eq_inter hms, cond_mul_eq_inter hms.compl, Set.inter_comm _ t,
    Set.inter_comm _ t]
  exact measure_inter_add_diff t hms

/-- **Bayes' Theorem** -/
theorem cond_eq_inv_mul_cond_mul (hms : MeasurableSet s) (hmt : MeasurableSet t) (μ : Measure Ω)
    [IsFiniteMeasure μ] : μ[t|s] = (μ s)⁻¹ * μ[s|t] * μ t := by
  rw [mul_assoc, cond_mul_eq_inter hmt s, Set.inter_comm, cond_apply hms]

end Bayes

lemma comap_cond {i : Ω' → Ω} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ ω ∂μ, ω ∈ range i)
    (hs : MeasurableSet s) : comap i μ[|s] = (comap i μ)[|i in s] := by
  ext t ht
  change μ (range i)ᶜ = 0 at hi'
  rw [cond_apply, comap_apply, cond_apply, comap_apply, comap_apply, image_inter,
    image_preimage_eq_inter_range, inter_right_comm, measure_inter_conull hi',
    measure_inter_conull hi']
  all_goals first
  | exact hi.injective
  | exact hi.measurableSet_image'
  | exact hs
  | exact ht
  | exact hi.measurable hs
  | exact (hi.measurable hs).inter ht

variable [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- The **law of total probability** for a random variable taking finitely many values: a measure
`μ` can be expressed as a linear combination of its conditional measures `μ[|X ← x]` on fibers of a
random variable `X` valued in a fintype. -/
lemma sum_meas_smul_cond_fiber {X : Ω → α} (hX : Measurable X) (μ : Measure Ω) [IsFiniteMeasure μ] :
    ∑ x, μ (X ⁻¹' {x}) • μ[|X ← x] = μ := by
  ext E hE
  calc
    _ = ∑ x, μ (X ⁻¹' {x} ∩ E) := by
      simp only [Measure.coe_finset_sum, Measure.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_comm (μ _), cond_mul_eq_inter (hX (.singleton _))]
    _ = _ := by
      have : ⋃ x ∈ Finset.univ, X ⁻¹' {x} ∩ E = E := by ext; simp
      rw [← measure_biUnion_finset _ fun _ _ ↦ (hX (.singleton _)).inter hE, this]
      aesop (add simp [PairwiseDisjoint, Set.Pairwise, Function.onFun, disjoint_left])

end ProbabilityTheory
