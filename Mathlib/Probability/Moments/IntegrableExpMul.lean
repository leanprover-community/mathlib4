/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Domain of the moment generating function

For `X` a real random variable and `μ` a finite measure, the set
`{t | Integrable (fun ω ↦ exp (t * X ω)) μ}` is an interval containing zero. This is the set of
points for which the moment generating function `mgf X μ t` is well defined.
We prove the integrability of other functions for `t` in the interior of that interval.

## Main results

* `ProbabilityTheory.integrable_exp_mul_of_le`: if `exp (u * X)` is integrable for `0 ≤ u`, then
  it is integrable on `[0, u]`.
* `ProbabilityTheory.integrable_exp_mul_of_ge`: if `exp (u * X)` is integrable for `u ≤ 0`, then
  it is integrable on `[u, 0]`.
* `ProbabilityTheory.integrable_pow_abs_mul_exp_of_mem_interior`: for `v` in the interior of the
  interval in which `exp (t * X)` is integrable, for all `n : ℕ`, `|X| ^ n * exp (v * X)` is
  integrable.

-/


open MeasureTheory Filter Finset Real

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {p : ℕ} {μ : Measure Ω} {t u v : ℝ}

/-- Auxiliary lemma for `integrable_exp_mul_of_le`. -/
lemma integrable_exp_mul_of_le_of_measurable [IsFiniteMeasure μ] (hX : Measurable X)
    (hu : Integrable (fun ω ↦ exp (u * X ω)) μ) (h_nonneg : 0 ≤ t) (htu : t ≤ u) :
    Integrable (fun ω ↦ exp (t * X ω)) μ := by
  by_cases ht : t = 0
  · simp [ht]
  have h_pos : 0 < t := lt_of_le_of_ne' h_nonneg ht
  have hu' : Integrable (1 + {w | 0 ≤ X w}.indicator (fun ω ↦ exp (u * X ω))) μ :=
    (integrable_const _).add (hu.indicator (hX measurableSet_Ici))
  refine hu'.mono ?_ (ae_of_all _ fun ω ↦ ?_)
  · have hX : AEMeasurable X μ := aemeasurable_of_aemeasurable_exp_mul (h_pos.trans_le htu).ne'
      hu.aemeasurable
    exact (measurable_exp.comp_aemeasurable (hX.const_mul _)).aestronglyMeasurable
  · simp only [norm_eq_abs, abs_exp, Pi.add_apply, Pi.one_apply]
    rw [abs_of_nonneg]
    swap; · exact add_nonneg zero_le_one (Set.indicator_nonneg (fun ω _ ↦ by positivity) _)
    rcases le_or_lt 0 (X ω) with h_nonneg | h_neg
    · simp only [Set.mem_setOf_eq, h_nonneg, Set.indicator_of_mem]
      calc rexp (t * X ω) ≤ 1 + rexp (t * X ω) := (le_add_iff_nonneg_left _).mpr zero_le_one
      _ ≤ 1 + exp (u * X ω) := by gcongr
    · simp only [Set.mem_setOf_eq, not_le.mpr h_neg, not_false_eq_true, Set.indicator_of_not_mem,
        add_zero, exp_le_one_iff]
      exact mul_nonpos_of_nonneg_of_nonpos h_pos.le h_neg.le

/-- If `ω ↦ exp (u * X ω)` is integrable at `u ≥ 0`, then it is integrable on `[0, u]`. -/
lemma integrable_exp_mul_of_le [IsFiniteMeasure μ]
    (hu : Integrable (fun ω ↦ exp (u * X ω)) μ) (h_nonneg : 0 ≤ t) (htu : t ≤ u) :
    Integrable (fun ω ↦ exp (t * X ω)) μ := by
  by_cases ht : t = 0
  · simp [ht]
  have hX : AEMeasurable X μ := by
    refine aemeasurable_of_aemeasurable_exp_mul ?_ hu.aemeasurable
    exact ((lt_of_le_of_ne' h_nonneg ht).trans_le htu).ne'
  have h_eq t : (fun ω ↦ exp (t * X ω)) =ᵐ[μ] fun ω ↦ exp (t * hX.mk X ω) := by
    filter_upwards [hX.ae_eq_mk] with ω hω using by rw [hω]
  rw [integrable_congr (h_eq t)]
  rw [integrable_congr (h_eq u)] at hu
  exact integrable_exp_mul_of_le_of_measurable hX.measurable_mk hu h_nonneg htu

/-- If `ω ↦ exp (u * X ω)` is integrable at `u ≤ 0`, then it is integrable on `[u, 0]`. -/
lemma integrable_exp_mul_of_ge [IsFiniteMeasure μ]
    (hu : Integrable (fun ω ↦ exp (u * X ω)) μ) (h_nonpos : t ≤ 0) (htu : u ≤ t) :
    Integrable (fun ω ↦ exp (t * X ω)) μ := by
  suffices Integrable (fun ω ↦ exp (- t * (-X) ω)) μ by simpa using this
  exact integrable_exp_mul_of_le (u := -u) (t := -t)
    (by simpa using hu) (by simp [h_nonpos]) (by simp [htu])

/-- If `ω ↦ exp (u * X ω)` is integrable at `u` and `-u`, then it is integrable on `[-u, u]`. -/
lemma integrable_exp_mul_of_abs_le [IsFiniteMeasure μ]
    (hu_int_pos : Integrable (fun ω ↦ exp (u * X ω)) μ)
    (hu_int_neg : Integrable (fun ω ↦ exp (- u * X ω)) μ)
    (htu : |t| ≤ |u|) :
    Integrable (fun ω ↦ exp (t * X ω)) μ := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht] at htu
    refine integrable_exp_mul_of_le ?_ ht htu
    rcases le_total 0 u with hu | hu
    · rwa [abs_of_nonneg hu]
    · rwa [abs_of_nonpos hu]
  · rw [abs_of_nonpos ht, neg_le] at htu
    refine integrable_exp_mul_of_ge ?_ ht htu
    rcases le_total 0 u with hu | hu
    · rwa [abs_of_nonneg hu]
    · rwa [abs_of_nonpos hu, neg_neg]

lemma integrable_exp_mul_of_le_of_le [IsFiniteMeasure μ] {a b : ℝ}
    (ha : Integrable (fun ω ↦ exp (a * X ω)) μ)
    (hb : Integrable (fun ω ↦ exp (b * X ω)) μ)
    (hat : a ≤ t) (htb : t ≤ b) :
    Integrable (fun ω ↦ exp (t * X ω)) μ := by
  rcases le_total 0 t with ht | ht
  · exact integrable_exp_mul_of_le hb ht htb
  · exact integrable_exp_mul_of_ge ha ht hat

lemma exp_mul_abs_add_le_add : exp (t * |u| + v * u) ≤ rexp ((v + t) * u) + rexp ((v - t) * u) := by
  rcases le_total 0 u with h_nonneg | h_nonpos
  · rw [abs_of_nonneg h_nonneg, ← add_mul, add_comm, le_add_iff_nonneg_right]
    positivity
  · rw [abs_of_nonpos h_nonpos, mul_neg, mul_comm, ← mul_neg, mul_comm, ← add_mul, add_comm,
      ← sub_eq_add_neg, le_add_iff_nonneg_left]
    positivity

lemma exp_mul_abs_le_add : exp (t * |u|) ≤ rexp (t * u) + rexp (-(t * u)) := by
  have h := exp_mul_abs_add_le_add (t := t) (u := u) (v := 0)
  simpa using h

lemma integrable_exp_mul_abs_add (ht_int_pos : Integrable (fun ω ↦ rexp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp ((v - t) * X ω)) μ) :
    Integrable (fun ω ↦ rexp (t * |X ω| + v * X ω)) μ := by
  have h_int_add : Integrable (fun a ↦ rexp ((v + t) * X a) + rexp ((v - t) * X a)) μ :=
    ht_int_pos.add <| by simpa using ht_int_neg
  refine Integrable.mono h_int_add ?_ (ae_of_all _ fun ω ↦ ?_)
  · by_cases ht : t = 0
    · simp only [ht, zero_mul, zero_add]
      simp only [ht, add_zero] at ht_int_pos
      exact ht_int_pos.1
    have hX : AEMeasurable X μ := by
      by_cases hvt : v + t = 0
      · have hvt' : v - t ≠ 0 := by
          rw [sub_ne_zero]
          refine fun h_eq ↦ ht ?_
          simpa [h_eq] using hvt
        exact aemeasurable_of_aemeasurable_exp_mul hvt' ht_int_neg.aemeasurable
      · exact aemeasurable_of_aemeasurable_exp_mul hvt ht_int_pos.aemeasurable
    refine AEMeasurable.aestronglyMeasurable ?_
    exact measurable_exp.comp_aemeasurable ((hX.abs.const_mul _).add (hX.const_mul _))
  · simp only [norm_eq_abs, abs_exp]
    conv_rhs => rw [abs_of_nonneg (by positivity)]
    exact exp_mul_abs_add_le_add

/-- If `ω ↦ rexp (t * X ω)` is integrable at `t` and `-t`, then `ω ↦ rexp (t * |X ω|)` is
integrable. -/
lemma integrable_exp_mul_abs (ht_int_pos : Integrable (fun ω ↦ rexp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp (- t * X ω)) μ) :
    Integrable (fun ω ↦ rexp (t * |X ω|)) μ := by
  have h := integrable_exp_mul_abs_add (t := t) (μ := μ) (X := X) (v := 0) ?_ ?_
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

lemma integrable_exp_abs_mul_abs_add (ht_int_pos : Integrable (fun ω ↦ rexp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp ((v - t) * X ω)) μ) :
    Integrable (fun ω ↦ rexp (|t| * |X ω| + v * X ω)) μ := by
  rcases le_total 0 t with ht_nonneg | ht_nonpos
  · simp_rw [abs_of_nonneg ht_nonneg]
    exact integrable_exp_mul_abs_add ht_int_pos ht_int_neg
  · simp_rw [abs_of_nonpos ht_nonpos]
    exact integrable_exp_mul_abs_add ht_int_neg (by simpa using ht_int_pos)

/-- If `ω ↦ rexp (t * X ω)` is integrable at `t` and `-t`, then `ω ↦ rexp (|t| * |X ω|)` is
integrable. -/
lemma integrable_exp_abs_mul_abs (ht_int_pos : Integrable (fun ω ↦ rexp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp (- t * X ω)) μ) :
    Integrable (fun ω ↦ rexp (|t| * |X ω|)) μ := by
  rcases le_total 0 t with ht_nonneg | ht_nonpos
  · simp_rw [abs_of_nonneg ht_nonneg]
    exact integrable_exp_mul_abs ht_int_pos ht_int_neg
  · simp_rw [abs_of_nonpos ht_nonpos]
    exact integrable_exp_mul_abs ht_int_neg (by simpa using ht_int_pos)

lemma integrable_pow_abs_mul_exp_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun x ↦ rexp ((v + t) * X x)) μ)
    (ht_int_neg : Integrable (fun x ↦ rexp ((v - t) * X x)) μ) (n : ℕ) :
    Integrable (fun ω ↦ |X ω| ^ n * exp (v * X ω)) μ := by
  suffices Integrable (fun ω ↦ (t * |X ω|) ^ n / n.factorial * exp (v * X ω)) μ by
    have h_eq ω : |X ω| ^ n * exp (v * X ω)
        = ((t * |X ω|) ^ n / n.factorial * exp (v * X ω)) * n.factorial / t ^ n := by
      rw [mul_pow]
      field_simp
      ring
    simp_rw [h_eq]
    exact (this.mul_const _).div_const _
  have h_le ω : (|t| * |X ω|) ^ n / n.factorial ≤ exp (|t| * |X ω|) :=
    pow_div_factorial_le_exp _ (by positivity) _
  have h_int := integrable_exp_abs_mul_abs_add ht_int_pos ht_int_neg
  refine Integrable.mono h_int ?_ (ae_of_all _ fun ω ↦ ?_)
  · have hX : AEMeasurable X μ := by
      by_cases hvt : v + t = 0
      · have hvt' : v - t ≠ 0 := by
          rw [sub_ne_zero]
          refine fun h_eq ↦ ht ?_
          simpa [h_eq] using hvt
        exact aemeasurable_of_aemeasurable_exp_mul hvt' ht_int_neg.aemeasurable
      · exact aemeasurable_of_aemeasurable_exp_mul hvt ht_int_pos.aemeasurable
    simp_rw [mul_pow]
    refine AEMeasurable.aestronglyMeasurable ?_
    exact (((hX.abs.pow_const _).const_mul _).div_const _).mul
      (measurable_exp.comp_aemeasurable (hX.const_mul _))
  · simp only [norm_div, norm_pow, norm_mul, norm_eq_abs, abs_abs, norm_natCast, abs_exp,
      Nat.abs_cast]
    rw [exp_add]
    gcongr
    exact h_le _

lemma add_half_inf_sub_mem_Ioo {l u v : ℝ} (hv : v ∈ Set.Ioo l u) :
    v + ((v - l) ⊓ (u - v)) / 2 ∈ Set.Ioo l u := by
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hv.1, hv.2]
  constructor
  · calc l < v := hv.1
    _ ≤ v + ((v - l) ⊓ (u - v)) / 2 := le_add_of_nonneg_right (by positivity)
  · calc v + ((v - l) ⊓ (u - v)) / 2
    _ < v + ((v - l) ⊓ (u - v)) := by gcongr; exact half_lt_self (by positivity)
    _ ≤ v + (u - v) := by gcongr; exact inf_le_right
    _ = u := by abel

lemma sub_half_inf_sub_mem_Ioo {l u v : ℝ} (hv : v ∈ Set.Ioo l u) :
    v - ((v - l) ⊓ (u - v)) / 2 ∈ Set.Ioo l u := by
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hv.1, hv.2]
  constructor
  · calc l = v - (v - l) := by abel
    _ ≤ v - ((v - l) ⊓ (u - v)) := by gcongr; exact inf_le_left
    _ < v - ((v - l) ⊓ (u - v)) / 2 := by gcongr; exact half_lt_self (by positivity)
  · calc v - ((v - l) ⊓ (u - v)) / 2
    _ ≤ v := by
      rw [sub_le_iff_le_add]
      exact le_add_of_nonneg_right (by positivity)
    _ < u := hv.2

lemma integrable_pow_abs_mul_exp_of_mem_interior
    (hv : v ∈ interior {t | Integrable (fun ω ↦ exp (t * X ω)) μ}) (n : ℕ) :
    Integrable (fun ω ↦ |X ω| ^ n * exp (v * X ω)) μ := by
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hv
  obtain ⟨l, u, hvlu, h_subset⟩ := hv
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hvlu.1, hvlu.2]
  refine integrable_pow_abs_mul_exp_of_integrable_exp_mul (t := min (v - l) (u - v) / 2) ?_ ?_ ?_ n
  · positivity
  · exact h_subset (add_half_inf_sub_mem_Ioo hvlu)
  · exact h_subset (sub_half_inf_sub_mem_Ioo hvlu)

/-- If `ω ↦ rexp (t * X ω)` is integrable at `t` and `-t` for `t ≠ 0`, then `ω ↦ |X ω| ^ n` is
integrable for all `n : ℕ`. That is, all moments of `X` are finite. -/
lemma integrable_pow_abs_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun x ↦ rexp (t * X x)) μ)
    (ht_int_neg : Integrable (fun x ↦ rexp (- t * X x)) μ) (n : ℕ) :
    Integrable (fun ω ↦ |X ω| ^ n) μ := by
  have h := integrable_pow_abs_mul_exp_of_integrable_exp_mul (μ := μ) (X := X) ht (v := 0) ?_ ?_ n
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

lemma integrable_pow_mul_exp_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun x ↦ rexp ((v + t) * X x)) μ)
    (ht_int_neg : Integrable (fun x ↦ rexp ((v - t) * X x)) μ) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n * exp (v * X ω)) μ := by
  rw [← integrable_norm_iff]
  · simp_rw [norm_eq_abs, abs_mul, abs_pow, abs_exp]
    exact integrable_pow_abs_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg n
  · have hX : AEMeasurable X μ := by
      by_cases hvt : v + t = 0
      · have hvt' : v - t ≠ 0 := by
          rw [sub_ne_zero]
          refine fun h_eq ↦ ht ?_
          simpa [h_eq] using hvt
        exact aemeasurable_of_aemeasurable_exp_mul hvt' ht_int_neg.aemeasurable
      · exact aemeasurable_of_aemeasurable_exp_mul hvt ht_int_pos.aemeasurable
    exact ((hX.pow_const _).mul
      (measurable_exp.comp_aemeasurable (hX.const_mul _))).aestronglyMeasurable

lemma aemeasurable_of_mem_interior_integrable_exp
    (hv : v ∈ interior {t | Integrable (fun ω ↦ exp (t * X ω)) μ}) :
    AEMeasurable X μ := by
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hv
  obtain ⟨l, u, hvlu, h_subset⟩ := hv
  let t := ((v - l) ⊓ (u - v)) / 2
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hvlu.1, hvlu.2]
  have ht : 0 < t := half_pos h_pos
  by_cases hvt : v + t = 0
  · have hvt' : v - t ≠ 0 := by
      rw [sub_ne_zero]
      refine fun h_eq ↦ ht.ne' ?_
      simpa [h_eq] using hvt
    exact aemeasurable_of_aemeasurable_exp_mul hvt'
      (h_subset (sub_half_inf_sub_mem_Ioo hvlu)).aemeasurable
  · exact aemeasurable_of_aemeasurable_exp_mul hvt
      (h_subset (add_half_inf_sub_mem_Ioo hvlu)).aemeasurable

lemma integrable_pow_mul_exp_of_mem_interior
    (hv : v ∈ interior {t | Integrable (fun ω ↦ exp (t * X ω)) μ}) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n * exp (v * X ω)) μ := by
  rw [← integrable_norm_iff]
  · simp_rw [norm_eq_abs, abs_mul, abs_pow, abs_exp]
    exact integrable_pow_abs_mul_exp_of_mem_interior hv n
  · have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrable_exp hv
    exact ((hX.pow_const _).mul
      (measurable_exp.comp_aemeasurable (hX.const_mul _))).aestronglyMeasurable

/-- If `ω ↦ rexp (t * X ω)` is integrable at `t` and `-t` for `t ≠ 0`, then `ω ↦ X ω ^ n` is
integrable for all `n : ℕ`. -/
lemma integrable_pow_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun x ↦ rexp (t * X x)) μ)
    (ht_int_neg : Integrable (fun x ↦ rexp (- t * X x)) μ) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n) μ := by
  have h := integrable_pow_mul_exp_of_integrable_exp_mul (μ := μ) (X := X) ht (v := 0) ?_ ?_ n
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

end ProbabilityTheory
