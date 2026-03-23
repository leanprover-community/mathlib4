/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Notation

/-!
# Covariance

We define the covariance of two real-valued random variables.

## Main definitions

* `covariance`: covariance of two real-valued random variables, with notation `cov[X, Y; μ]`.
  `cov[X, Y; μ] = ∫ ω, (X ω - μ[X]) * (Y ω - μ[Y]) ∂μ`.

## Main statements

* `covariance_self`: `cov[X, X; μ] = Var[X; μ]`

## Notation

* `cov[X, Y; μ] = covariance X Y μ`
* `cov[X, Y] = covariance X Y volume`

-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X Y Z : Ω → ℝ} {μ : Measure Ω}

/-- The covariance of two real-valued random variables defined as
the integral of `(X - 𝔼[X])(Y - 𝔼[Y])`. -/
noncomputable def covariance (X Y : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∫ ω, (X ω - μ[X]) * (Y ω - μ[Y]) ∂μ

@[inherit_doc]
scoped notation "cov[" X ", " Y "; " μ "]" => ProbabilityTheory.covariance X Y μ

/-- The covariance of the real-valued random variables `X` and `Y`
according to the volume measure. -/
scoped notation "cov[" X ", " Y "]" => cov[X, Y; MeasureTheory.MeasureSpace.volume]

lemma covariance_eq_sub [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
     cov[X, Y; μ] = μ[X * Y] - μ[X] * μ[Y] := by
   simp_rw [covariance, sub_mul, mul_sub]
   repeat rw [integral_sub]
   · simp_rw [integral_mul_const, integral_const_mul, integral_const, probReal_univ,
       one_smul]
     simp
   · exact hY.const_mul _ |>.integrable (by simp)
   · exact integrable_const _
   · exact hX.integrable_mul hY
   · exact hX.mul_const _ |>.integrable (by simp)
   · exact (hX.integrable_mul hY).sub (hX.mul_const _ |>.integrable (by simp))
   · exact (hY.const_mul _ |>.integrable (by simp)).sub (integrable_const _)

@[simp] lemma covariance_zero_left : cov[0, Y; μ] = 0 := by simp [covariance]

@[simp] lemma covariance_zero_right : cov[X, 0; μ] = 0 := by simp [covariance]

@[simp] lemma covariance_zero_measure : cov[X, Y; (0 : Measure Ω)] = 0 := by simp [covariance]

variable (X Y) in
lemma covariance_comm : cov[X, Y; μ] = cov[Y, X; μ] := by
  simp_rw [covariance]
  congr with x
  ring

@[simp]
lemma covariance_const_left [IsProbabilityMeasure μ] (c : ℝ) : cov[fun _ ↦ c, Y; μ] = 0 := by
  simp [covariance]

@[simp]
lemma covariance_const_right [IsProbabilityMeasure μ] (c : ℝ) : cov[X, fun _ ↦ c; μ] = 0 := by
  simp [covariance]

@[simp]
lemma covariance_add_const_left [IsProbabilityMeasure μ] (hX : Integrable X μ) (c : ℝ) :
    cov[fun ω ↦ X ω + c, Y; μ] = cov[X, Y; μ] := by
  simp_rw [covariance]
  congr with ω
  rw [integral_add hX (by fun_prop)]
  simp

@[simp]
lemma covariance_const_add_left [IsProbabilityMeasure μ] (hX : Integrable X μ) (c : ℝ) :
    cov[fun ω ↦ c + X ω, Y; μ] = cov[X, Y; μ] := by
  simp_rw [add_comm c]
  exact covariance_add_const_left hX c

@[simp]
lemma covariance_add_const_right [IsProbabilityMeasure μ] (hY : Integrable Y μ) (c : ℝ) :
    cov[X, fun ω ↦ Y ω + c; μ] = cov[X, Y; μ] := by
  rw [covariance_comm, covariance_add_const_left hY c, covariance_comm]

@[simp]
lemma covariance_const_add_right [IsProbabilityMeasure μ] (hY : Integrable Y μ) (c : ℝ) :
    cov[X, fun ω ↦ c + Y ω; μ] = cov[X, Y; μ] := by
  simp_rw [add_comm c]
  exact covariance_add_const_right hY c

lemma covariance_add_left [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[X + Y, Z; μ] = cov[X, Z; μ] + cov[Y, Z; μ] := by
  simp_rw [covariance, Pi.add_apply]
  rw [← integral_add]
  · congr with x
    rw [integral_add (hX.integrable (by simp)) (hY.integrable (by simp))]
    ring
  · exact (hX.sub (memLp_const _)).integrable_mul (hZ.sub (memLp_const _))
  · exact (hY.sub (memLp_const _)).integrable_mul (hZ.sub (memLp_const _))

lemma covariance_add_right [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[X, Y + Z; μ] = cov[X, Y; μ] + cov[X, Z; μ] := by
  rw [covariance_comm, covariance_add_left hY hZ hX, covariance_comm X, covariance_comm Z]

lemma covariance_smul_left (c : ℝ) : cov[c • X, Y; μ] = c * cov[X, Y; μ] := by
  simp_rw [covariance, Pi.smul_apply, smul_eq_mul, ← integral_const_mul, ← mul_assoc, mul_sub,
    integral_const_mul]

lemma covariance_smul_right (c : ℝ) : cov[X, c • Y; μ] = c * cov[X, Y; μ] := by
  rw [covariance_comm, covariance_smul_left, covariance_comm]

lemma covariance_const_mul_left (c : ℝ) : cov[fun ω ↦ c * X ω, Y; μ] = c * cov[X, Y; μ] :=
  covariance_smul_left c

lemma covariance_const_mul_right (c : ℝ) : cov[X, fun ω ↦ c * Y ω; μ] = c * cov[X, Y; μ] :=
  covariance_smul_right c

lemma covariance_mul_const_left (c : ℝ) : cov[fun ω ↦ X ω * c, Y; μ] = cov[X, Y; μ] * c := by
  simp [mul_comm, covariance_const_mul_left]

lemma covariance_mul_const_right (c : ℝ) : cov[X, fun ω ↦ Y ω * c; μ] = cov[X, Y; μ] * c := by
  simp [mul_comm, covariance_const_mul_right]

lemma covariance_fun_div_left (c : ℝ) :
    cov[fun ω ↦ X ω / c, Y; μ] = cov[X, Y; μ] / c := by
  simp_rw [← inv_mul_eq_div, covariance_const_mul_left]

lemma covariance_fun_div_right (c : ℝ) :
    cov[X, fun ω ↦ Y ω / c; μ] = cov[X, Y; μ] / c := by
  simp_rw [← inv_mul_eq_div, covariance_const_mul_right]

@[deprecated (since := "2025-11-29")] alias covariance_mul_left := covariance_const_mul_left
@[deprecated (since := "2025-11-29")] alias covariance_mul_right := covariance_const_mul_right

@[simp]
lemma covariance_neg_left : cov[-X, Y; μ] = -cov[X, Y; μ] := by
  calc cov[-X, Y; μ]
  _ = cov[(-1 : ℝ) • X, Y; μ] := by simp
  _ = -cov[X, Y; μ] := by rw [covariance_smul_left]; simp

@[simp]
lemma covariance_fun_neg_left : cov[fun ω ↦ -X ω, Y; μ] = -cov[X, Y; μ] :=
  covariance_neg_left

@[simp]
lemma covariance_neg_right : cov[X, -Y; μ] = -cov[X, Y; μ] := by
  calc cov[X, -Y; μ]
  _ = cov[X, (-1 : ℝ) • Y; μ] := by simp
  _ = -cov[X, Y; μ] := by rw [covariance_smul_right]; simp

@[simp]
lemma covariance_fun_neg_right : cov[X, fun ω ↦ -Y ω; μ] = -cov[X, Y; μ] :=
  covariance_neg_right

lemma covariance_sub_left [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[X - Y, Z; μ] = cov[X, Z; μ] - cov[Y, Z; μ] := by
  simp_rw [sub_eq_add_neg, covariance_add_left hX hY.neg hZ, covariance_neg_left]

lemma covariance_fun_sub_left [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[fun ω ↦ X ω - Y ω, Z; μ] = cov[X, Z; μ] - cov[Y, Z; μ] := covariance_sub_left hX hY hZ

lemma covariance_sub_right [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[X, Y - Z; μ] = cov[X, Y; μ] - cov[X, Z; μ] := by
  simp_rw [sub_eq_add_neg, covariance_add_right hX hY hZ.neg, covariance_neg_right]

lemma covariance_fun_sub_right [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[X, fun ω ↦ Y ω - Z ω; μ] = cov[X, Y; μ] - cov[X, Z; μ] := covariance_sub_right hX hY hZ

@[simp]
lemma covariance_sub_const_left [IsProbabilityMeasure μ] (hX : Integrable X μ) (c : ℝ) :
    cov[fun ω ↦ X ω - c, Y; μ] = cov[X, Y; μ] := by
  simp [sub_eq_add_neg, hX]

@[simp]
lemma covariance_const_sub_left [IsProbabilityMeasure μ] (hX : Integrable X μ) (c : ℝ) :
    cov[fun ω ↦ c - X ω, Y; μ] = -cov[X, Y; μ] := by
  simp [sub_eq_add_neg, hX.neg']

@[simp]
lemma covariance_sub_const_right [IsProbabilityMeasure μ] (hY : Integrable Y μ) (c : ℝ) :
    cov[X, fun ω ↦ Y ω - c; μ] = cov[X, Y; μ] := by
  simp [sub_eq_add_neg, hY]

@[simp]
lemma covariance_const_sub_right [IsProbabilityMeasure μ] (hY : Integrable Y μ) (c : ℝ) :
    cov[X, fun ω ↦ c - Y ω; μ] = -cov[X, Y; μ] := by
  simp [sub_eq_add_neg, hY.neg']

section Sum

variable {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι} [IsFiniteMeasure μ]

lemma covariance_sum_left' (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[∑ i ∈ s, X i, Y; μ] = ∑ i ∈ s, cov[X i, Y; μ] := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi h_ind =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, covariance_add_left, h_ind]
    · exact fun j hj ↦ hX j (by simp [hj])
    · exact hX i (by simp)
    · exact memLp_finset_sum' s (fun j hj ↦ hX j (by simp [hj]))
    · exact hY

lemma covariance_sum_left [Fintype ι] (hX : ∀ i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[∑ i, X i, Y; μ] = ∑ i, cov[X i, Y; μ] :=
  covariance_sum_left' (fun _ _ ↦ hX _) hY

lemma covariance_fun_sum_left' (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[fun ω ↦ ∑ i ∈ s, X i ω, Y; μ] = ∑ i ∈ s, cov[X i, Y; μ] := by
  convert covariance_sum_left' hX hY
  simp

lemma covariance_fun_sum_left [Fintype ι] (hX : ∀ i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[fun ω ↦ ∑ i, X i ω, Y; μ] = ∑ i, cov[X i, Y; μ] := by
  convert covariance_sum_left hX hY
  simp

lemma covariance_sum_right' (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[Y, ∑ i ∈ s, X i; μ] = ∑ i ∈ s, cov[Y, X i; μ] := by
  rw [covariance_comm, covariance_sum_left' hX hY]
  simp_rw [covariance_comm]

lemma covariance_sum_right [Fintype ι] (hX : ∀ i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[Y, ∑ i, X i; μ] = ∑ i, cov[Y, X i; μ] :=
  covariance_sum_right' (fun _ _ ↦ hX _) hY

lemma covariance_fun_sum_right' (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[Y, fun ω ↦ ∑ i ∈ s, X i ω; μ] = ∑ i ∈ s, cov[Y, X i; μ] := by
  convert covariance_sum_right' hX hY
  simp

lemma covariance_fun_sum_right [Fintype ι] (hX : ∀ i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[Y, fun ω ↦ ∑ i, X i ω; μ] = ∑ i, cov[Y, X i; μ] :=
  covariance_fun_sum_right' (fun _ _ ↦ hX _) hY

lemma covariance_sum_sum' {ι' : Type*} {Y : ι' → Ω → ℝ} {t : Finset ι'}
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hY : ∀ i ∈ t, MemLp (Y i) 2 μ) :
    cov[∑ i ∈ s, X i, ∑ j ∈ t, Y j; μ] = ∑ i ∈ s, ∑ j ∈ t, cov[X i, Y j; μ] := by
  rw [covariance_sum_left' hX]
  · exact Finset.sum_congr rfl fun i hi ↦ by rw [covariance_sum_right' hY (hX i hi)]
  · exact memLp_finset_sum' t hY

lemma covariance_sum_sum [Fintype ι] {ι' : Type*} [Fintype ι'] {Y : ι' → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ) :
    cov[∑ i, X i, ∑ j, Y j; μ] = ∑ i, ∑ j, cov[X i, Y j; μ] :=
  covariance_sum_sum' (fun _ _ ↦ hX _) (fun _ _ ↦ hY _)

lemma covariance_fun_sum_fun_sum' {ι' : Type*} {Y : ι' → Ω → ℝ} {t : Finset ι'}
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hY : ∀ i ∈ t, MemLp (Y i) 2 μ) :
    cov[fun ω ↦ ∑ i ∈ s, X i ω, fun ω ↦ ∑ j ∈ t, Y j ω; μ]
      = ∑ i ∈ s, ∑ j ∈ t, cov[X i, Y j; μ] := by
  convert covariance_sum_sum' hX hY
  all_goals simp

lemma covariance_fun_sum_fun_sum [Fintype ι] {ι' : Type*} [Fintype ι'] {Y : ι' → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ) :
    cov[fun ω ↦ ∑ i, X i ω, fun ω ↦ ∑ j, Y j ω; μ] = ∑ i, ∑ j, cov[X i, Y j; μ] :=
  covariance_fun_sum_fun_sum' (fun _ _ ↦ hX _) (fun _ _ ↦ hY _)

end Sum

section Map

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}

lemma covariance_map_equiv (X Y : Ω → ℝ) (Z : Ω' ≃ᵐ Ω) :
    cov[X, Y; μ.map Z] = cov[X ∘ Z, Y ∘ Z; μ] := by
  simp_rw [covariance, integral_map_equiv, Function.comp_apply]

lemma covariance_map {Z : Ω' → Ω} (hX : AEStronglyMeasurable X (μ.map Z))
    (hY : AEStronglyMeasurable Y (μ.map Z)) (hZ : AEMeasurable Z μ) :
    cov[X, Y; μ.map Z] = cov[X ∘ Z, Y ∘ Z; μ] := by
  simp_rw [covariance, Function.comp_apply]
  repeat rw [integral_map]
  any_goals assumption
  exact (hX.sub aestronglyMeasurable_const).mul (hY.sub aestronglyMeasurable_const)

lemma covariance_map_fun {Z : Ω' → Ω} (hX : AEStronglyMeasurable X (μ.map Z))
    (hY : AEStronglyMeasurable Y (μ.map Z)) (hZ : AEMeasurable Z μ) :
    cov[X, Y; μ.map Z] = cov[fun ω ↦ X (Z ω), fun ω ↦ Y (Z ω); μ] :=
  covariance_map hX hY hZ

end Map

lemma IndepFun.covariance_eq_zero (h : X ⟂ᵢ[μ] Y) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
     cov[X, Y; μ] = 0 := by
   by_cases h' : ∀ᵐ ω ∂μ, X ω = 0
   · refine integral_eq_zero_of_ae ?_
     filter_upwards [h'] with ω hω
     simp [hω, integral_eq_zero_of_ae h']
   have := hX.isProbabilityMeasure_of_indepFun X Y (by simp) (by simp) h' h
   rw [covariance_eq_sub hX hY, h.integral_mul_eq_mul_integral
       hX.aestronglyMeasurable hY.aestronglyMeasurable, sub_self]

section Prod

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {X : Ω → ℝ} {Y : Ω' → ℝ}

lemma covariance_fst_snd_prod (hfμ : MemLp X 2 μ) (hgν : MemLp Y 2 ν) :
    cov[fun p ↦ X p.1, fun p ↦ Y p.2; μ.prod ν] = 0 :=
  (indepFun_prod₀ hfμ.aemeasurable hgν.aemeasurable).covariance_eq_zero
    (hfμ.comp_fst ν) (hgν.comp_snd μ)

end Prod

end ProbabilityTheory
