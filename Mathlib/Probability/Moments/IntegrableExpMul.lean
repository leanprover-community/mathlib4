/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Domain of the moment generating function

For `X` a real random variable and `μ` a finite measure, the set
`{t | Integrable (fun ω ↦ exp (t * X ω)) μ}` is an interval containing zero. This is the set of
points for which the moment generating function `mgf X μ t` is well defined.
We denote that set by `integrableExpSet X μ`.

We prove the integrability of other functions for `t` in the interior of that interval.

## Main definitions

* `ProbabilityTheory.IntegrableExpSet`: the interval of reals for which `exp (t * X)` is integrable.

## Main results

* `ProbabilityTheory.integrable_exp_mul_of_le_of_le`: if `exp (u * X)` is integrable for `u = a` and
  `u = b` then it is integrable on `[a, b]`.
* `ProbabilityTheory.convex_integrableExpSet`: `integrableExpSet X μ` is a convex set.
* `ProbabilityTheory.integrable_exp_mul_of_nonpos_of_ge`: if `exp (u * X)` is integrable for `u ≤ 0`
  then it is integrable on `[u, 0]`.
* `ProbabilityTheory.integrable_rpow_abs_mul_exp_of_mem_interior`: for `v` in the interior of the
  interval in which `exp (t * X)` is integrable, for all nonnegative `p : ℝ`,
  `|X| ^ p * exp (v * X)` is integrable.
* `ProbabilityTheory.memLp_of_mem_interior_integrableExpSet`: if 0 belongs to the interior of
  `integrableExpSet X μ`, then `X` is in `ℒp` for all finite `p`.

-/


open MeasureTheory Filter Finset Real

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω} {t u v : ℝ}

section Interval

lemma integrable_exp_mul_of_le_of_le {a b : ℝ}
    (ha : Integrable (fun ω ↦ exp (a * X ω)) μ) (hb : Integrable (fun ω ↦ exp (b * X ω)) μ)
    (hat : a ≤ t) (htb : t ≤ b) :
    Integrable (fun ω ↦ exp (t * X ω)) μ := by
  refine Integrable.mono (ha.add hb) ?_ (ae_of_all _ fun ω ↦ ?_)
  · by_cases hab : a = b
    · have ha_eq_t : a = t := le_antisymm hat (hab ▸ htb)
      rw [← ha_eq_t]
      exact ha.1
    · refine AEMeasurable.aestronglyMeasurable ?_
      refine measurable_exp.comp_aemeasurable (AEMeasurable.const_mul ?_ _)
      by_cases ha_zero : a = 0
      · refine aemeasurable_of_aemeasurable_exp_mul ?_ hb.1.aemeasurable
        rw [ha_zero] at hab
        exact Ne.symm hab
      · exact aemeasurable_of_aemeasurable_exp_mul ha_zero ha.1.aemeasurable
  · simp only [norm_eq_abs, abs_exp, Pi.add_apply]
    conv_rhs => rw [abs_of_nonneg (by positivity)]
    rcases le_total 0 (X ω) with h | h
    · calc exp (t * X ω)
      _ ≤ exp (b * X ω) := exp_le_exp.mpr (mul_le_mul_of_nonneg_right htb h)
      _ ≤ exp (a * X ω) + exp (b * X ω) := le_add_of_nonneg_left (exp_nonneg _)
    · calc exp (t * X ω)
      _ ≤ exp (a * X ω) := exp_le_exp.mpr (mul_le_mul_of_nonpos_right hat h)
      _ ≤ exp (a * X ω) + exp (b * X ω) := le_add_of_nonneg_right (exp_nonneg _)

/-- If `ω ↦ exp (u * X ω)` is integrable at `u` and `-u`, then it is integrable on `[-u, u]`. -/
lemma integrable_exp_mul_of_abs_le
    (hu_int_pos : Integrable (fun ω ↦ exp (u * X ω)) μ)
    (hu_int_neg : Integrable (fun ω ↦ exp (- u * X ω)) μ)
    (htu : |t| ≤ |u|) :
    Integrable (fun ω ↦ exp (t * X ω)) μ := by
  refine integrable_exp_mul_of_le_of_le (a := -|u|) (b := |u|) ?_ ?_ ?_ ?_
  · rcases le_total 0 u with hu | hu
    · rwa [abs_of_nonneg hu]
    · simpa [abs_of_nonpos hu]
  · rcases le_total 0 u with hu | hu
    · rwa [abs_of_nonneg hu]
    · rwa [abs_of_nonpos hu]
  · rw [neg_le]
    exact (neg_le_abs t).trans htu
  · exact (le_abs_self t).trans htu

/-- If `ω ↦ exp (u * X ω)` is integrable at `u ≥ 0`, then it is integrable on `[0, u]`. -/
lemma integrable_exp_mul_of_nonneg_of_le [IsFiniteMeasure μ]
    (hu : Integrable (fun ω ↦ exp (u * X ω)) μ) (h_nonneg : 0 ≤ t) (htu : t ≤ u) :
    Integrable (fun ω ↦ exp (t * X ω)) μ :=
  integrable_exp_mul_of_le_of_le (by simp) hu h_nonneg htu

/-- If `ω ↦ exp (u * X ω)` is integrable at `u ≤ 0`, then it is integrable on `[u, 0]`. -/
lemma integrable_exp_mul_of_nonpos_of_ge [IsFiniteMeasure μ]
    (hu : Integrable (fun ω ↦ exp (u * X ω)) μ) (h_nonpos : t ≤ 0) (htu : u ≤ t) :
    Integrable (fun ω ↦ exp (t * X ω)) μ :=
  integrable_exp_mul_of_le_of_le hu (by simp) htu h_nonpos

end Interval

section IntegrableExpSet

/-- The interval of reals `t` for which `exp (t * X)` is integrable. -/
def integrableExpSet (X : Ω → ℝ) (μ : Measure Ω) : Set ℝ :=
  {t | Integrable (fun ω ↦ exp (t * X ω)) μ}

lemma integrable_of_mem_integrableExpSet (h : t ∈ integrableExpSet X μ) :
    Integrable (fun ω ↦ exp (t * X ω)) μ := h

/-- `integrableExpSet X μ` is a convex subset of `ℝ` (it is an interval). -/
lemma convex_integrableExpSet : Convex ℝ (integrableExpSet X μ) := by
  rintro t₁ ht₁ t₂ ht₂ a b ha hb hab
  wlog h_le : t₁ ≤ t₂
  · rw [add_comm] at hab ⊢
    exact this ht₂ ht₁ hb ha hab (not_le.mp h_le).le
  refine integrable_exp_mul_of_le_of_le ht₁ ht₂ ?_ ?_
  · simp only [smul_eq_mul]
    calc t₁
    _ = a * t₁ + b * t₁ := by rw [← add_mul, hab, one_mul]
    _ ≤ a * t₁ + b * t₂ := by gcongr
  · simp only [smul_eq_mul]
    calc a * t₁ + b * t₂
    _ ≤ a * t₂ + b * t₂ := by gcongr
    _ = t₂ := by rw [← add_mul, hab, one_mul]

end IntegrableExpSet

section FiniteMoments

lemma aemeasurable_of_integrable_exp_mul (huv : u ≠ v)
    (hu_int : Integrable (fun ω ↦ exp (u * X ω)) μ)
    (hv_int : Integrable (fun ω ↦ exp (v * X ω)) μ) :
    AEMeasurable X μ := by
  by_cases hu : u = 0
  · have hv : v ≠ 0 := ne_of_ne_of_eq huv.symm hu
    exact aemeasurable_of_aemeasurable_exp_mul hv hv_int.aemeasurable
  · exact aemeasurable_of_aemeasurable_exp_mul hu hu_int.aemeasurable

/-- If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable, then
`ω ↦ exp (t * |X| + v * X)` is integrable. -/
lemma integrable_exp_mul_abs_add (ht_int_pos : Integrable (fun ω ↦ exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp ((v - t) * X ω)) μ) :
    Integrable (fun ω ↦ exp (t * |X ω| + v * X ω)) μ := by
  have h_int_add : Integrable (fun a ↦ exp ((v + t) * X a) + exp ((v - t) * X a)) μ :=
    ht_int_pos.add <| by simpa using ht_int_neg
  refine Integrable.mono h_int_add ?_ (ae_of_all _ fun ω ↦ ?_)
  · by_cases ht : t = 0
    · simp only [ht, zero_mul, zero_add, add_zero] at ht_int_pos ⊢
      exact ht_int_pos.1
    have hX : AEMeasurable X μ := aemeasurable_of_integrable_exp_mul ?_ ht_int_pos ht_int_neg
    swap; · rw [← sub_ne_zero]; simp [ht]
    refine AEMeasurable.aestronglyMeasurable ?_
    exact measurable_exp.comp_aemeasurable ((hX.abs.const_mul _).add (hX.const_mul _))
  · simp only [norm_eq_abs, abs_exp]
    conv_rhs => rw [abs_of_nonneg (by positivity)]
    -- ⊢ exp (t * |X ω| + v * X ω) ≤ exp ((v + t) * X ω) + exp ((v - t) * X ω)
    rcases le_total 0 (X ω) with h_nonneg | h_nonpos
    · rw [abs_of_nonneg h_nonneg, ← add_mul, add_comm, le_add_iff_nonneg_right]
      positivity
    · rw [abs_of_nonpos h_nonpos, mul_neg, mul_comm, ← mul_neg, mul_comm, ← add_mul, add_comm,
        ← sub_eq_add_neg, le_add_iff_nonneg_left]
      positivity

/-- If `ω ↦ exp (t * X ω)` is integrable at `t` and `-t`, then `ω ↦ exp (t * |X ω|)` is
integrable. -/
lemma integrable_exp_mul_abs (ht_int_pos : Integrable (fun ω ↦ exp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp (- t * X ω)) μ) :
    Integrable (fun ω ↦ exp (t * |X ω|)) μ := by
  have h := integrable_exp_mul_abs_add (t := t) (μ := μ) (X := X) (v := 0) ?_ ?_
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

/-- If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable, then
`ω ↦ exp (|t| * |X| + v * X)` is integrable. -/
lemma integrable_exp_abs_mul_abs_add (ht_int_pos : Integrable (fun ω ↦ exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp ((v - t) * X ω)) μ) :
    Integrable (fun ω ↦ exp (|t| * |X ω| + v * X ω)) μ := by
  rcases le_total 0 t with ht_nonneg | ht_nonpos
  · simp_rw [abs_of_nonneg ht_nonneg]
    exact integrable_exp_mul_abs_add ht_int_pos ht_int_neg
  · simp_rw [abs_of_nonpos ht_nonpos]
    exact integrable_exp_mul_abs_add ht_int_neg (by simpa using ht_int_pos)

/-- If `ω ↦ exp (t * X ω)` is integrable at `t` and `-t`, then `ω ↦ exp (|t| * |X ω|)` is
integrable. -/
lemma integrable_exp_abs_mul_abs (ht_int_pos : Integrable (fun ω ↦ exp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp (- t * X ω)) μ) :
    Integrable (fun ω ↦ exp (|t| * |X ω|)) μ := by
  rcases le_total 0 t with ht_nonneg | ht_nonpos
  · simp_rw [abs_of_nonneg ht_nonneg]
    exact integrable_exp_mul_abs ht_int_pos ht_int_neg
  · simp_rw [abs_of_nonpos ht_nonpos]
    exact integrable_exp_mul_abs ht_int_neg (by simpa using ht_int_pos)

/-- Auxiliary lemma for `rpow_abs_le_mul_max_exp`. -/
lemma rpow_abs_le_mul_max_exp_of_pos (x : ℝ) {t p : ℝ} (hp : 0 ≤ p) (ht : 0 < t) :
    |x| ^ p ≤ (p / t) ^ p * max (exp (t * x)) (exp (- t * x)) := by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, rpow_zero, zero_div, neg_mul, one_mul, le_sup_iff, one_le_exp_iff,
      Left.nonneg_neg_iff]
    exact le_total 0 (t * x)
  have h_x_le c (hc : 0 < c) : x ≤ c⁻¹ * exp (c * x) := le_inv_mul_exp x hc
  have h_neg_x_le c (hc : 0 < c) : -x ≤ c⁻¹ * exp (- c * x) := by simpa using le_inv_mul_exp (-x) hc
  have h_abs_le c (hc : 0 < c) : |x| ≤ c⁻¹ * max (exp (c * x)) (exp (- c * x)) := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · rw [neg_le]
      refine (h_neg_x_le c hc).trans ?_
      gcongr
      exact le_max_right _ _
    · refine (h_x_le c hc).trans ?_
      gcongr
      exact le_max_left _ _
  calc |x| ^ p
  _ ≤ ((t / p)⁻¹ * max (exp (t / p * x)) (exp (- t / p * x))) ^ p := by
    refine rpow_le_rpow (abs_nonneg _) ?_ hp
    convert h_abs_le (t / p) (div_pos ht (hp.lt_of_ne' hp_zero)) using 5
    rw [neg_div]
  _ = (p / t) ^ p * max (exp (t * x)) (exp (- t * x)) := by
    rw [mul_rpow (by positivity) (by positivity)]
    congr
    · field_simp
    · rw [rpow_max (by positivity) (by positivity) hp, ← exp_mul, ← exp_mul]
      ring_nf
      congr <;> rw [mul_assoc, mul_inv_cancel₀ hp_zero, mul_one]

lemma rpow_abs_le_mul_max_exp (x : ℝ) {t p : ℝ} (hp : 0 ≤ p) (ht : t ≠ 0) :
    |x| ^ p ≤ (p / |t|) ^ p * max (exp (t * x)) (exp (- t * x)) := by
  rcases lt_or_gt_of_ne ht with ht_neg | ht_pos
  · rw [abs_of_nonpos ht_neg.le, sup_comm]
    convert rpow_abs_le_mul_max_exp_of_pos x hp (t := -t) (by simp [ht_neg])
    simp
  · rw [abs_of_nonneg ht_pos.le]
    exact rpow_abs_le_mul_max_exp_of_pos x hp ht_pos

lemma rpow_abs_le_mul_exp_abs (x : ℝ) {t p : ℝ} (hp : 0 ≤ p) (ht : t ≠ 0) :
    |x| ^ p ≤ (p / |t|) ^ p * exp (|t| * |x|) := by
  refine (rpow_abs_le_mul_max_exp_of_pos x hp (t := |t|) ?_).trans_eq ?_
  · simp [ht]
  · congr
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      simp only [neg_mul, sup_eq_left, exp_le_exp, neg_le_self_iff]
      positivity
    · rw [abs_of_nonpos hx]
      simp only [neg_mul, mul_neg, sup_eq_right, exp_le_exp, le_neg_self_iff]
      exact mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) hx

/-- If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable
then for nonnegative `p : ℝ` and any `x ∈ [0, |t|)`,
`|X| ^ p * exp (v * X + x * |X|)` is integrable. -/
lemma integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul {x : ℝ}
    (h_int_pos : Integrable (fun ω ↦ exp ((v + t) * X ω)) μ)
    (h_int_neg : Integrable (fun ω ↦ exp ((v - t) * X ω)) μ) (h_nonneg : 0 ≤ x) (hx : x < |t|)
    {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun a ↦ |X a| ^ p * exp (v * X a + x * |X a|)) μ := by
  have ht : t ≠ 0 := by
    suffices |t| ≠ 0 by simpa
    exact (h_nonneg.trans_lt hx).ne'
  have hX : AEMeasurable X μ := aemeasurable_of_integrable_exp_mul ?_ h_int_pos h_int_neg
  swap; · rw [← sub_ne_zero]; simp [ht]
  rw [← integrable_norm_iff]
  swap
  · exact AEMeasurable.aestronglyMeasurable <| by fun_prop
  simp only [norm_mul, norm_pow, norm_eq_abs, sq_abs, abs_exp]
  have h_le a : |X a| ^ p * exp (v * X a + x * |X a|)
      ≤ (p / (|t| - x)) ^ p * exp (v * X a + |t| * |X a|) := by
    simp_rw [exp_add, mul_comm (exp (v * X a)), ← mul_assoc]
    gcongr ?_ * _
    have : |t| = |t| - x + x := by simp
    nth_rw 2 [this]
    rw [add_mul, exp_add, ← mul_assoc]
    gcongr ?_ * _
    convert rpow_abs_le_mul_exp_abs (X a) hp (t := |t| - x) _ using 4
    · nth_rw 2 [abs_of_nonneg]
      simp [hx.le]
    · nth_rw 2 [abs_of_nonneg]
      simp [hx.le]
    · rw [sub_ne_zero]
      exact hx.ne'
  refine Integrable.mono (g := fun a ↦ (p / (|t| - x)) ^ p * exp (v * X a + |t| * |X a|))
    ?_ ?_ <| ae_of_all _ fun ω ↦ ?_
  · refine Integrable.const_mul ?_ _
    simp_rw [add_comm (v * X _)]
    exact integrable_exp_abs_mul_abs_add h_int_pos h_int_neg
  · refine AEMeasurable.aestronglyMeasurable ?_
    exact AEMeasurable.mul (by fun_prop) (measurable_exp.comp_aemeasurable (by fun_prop))
  · simp only [sq_abs, norm_mul, norm_pow, norm_eq_abs, abs_exp, norm_div, norm_ofNat]
    simp_rw [abs_rpow_of_nonneg (abs_nonneg _), abs_abs]
    refine (h_le ω).trans_eq ?_
    congr
    symm
    simp only [abs_eq_self, sub_nonneg]
    exact rpow_nonneg (div_nonneg hp (sub_nonneg_of_le hx.le)) _

/-- If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable
then for any `n : ℕ` and any `x ∈ [0, |t|)`,
`|X| ^ n * exp (v * X + x * |X|)` is integrable. -/
lemma integrable_pow_abs_mul_exp_add_of_integrable_exp_mul {x : ℝ}
    (h_int_pos : Integrable (fun ω ↦ exp ((v + t) * X ω)) μ)
    (h_int_neg : Integrable (fun ω ↦ exp ((v - t) * X ω)) μ) (h_nonneg : 0 ≤ x) (hx : x < |t|)
    (n : ℕ) :
    Integrable (fun a ↦ |X a| ^ n * exp (v * X a + x * |X a|)) μ := by
  convert integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul h_int_pos h_int_neg h_nonneg hx
    n.cast_nonneg
  simp

/-- If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable
then for nonnegative `p : ℝ`, `|X| ^ p * exp (v * X)` is integrable. -/
lemma integrable_rpow_abs_mul_exp_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp ((v - t) * X ω)) μ) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω ↦ |X ω| ^ p * exp (v * X ω)) μ := by
  convert integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul ht_int_pos ht_int_neg le_rfl _ hp
    using 4
  · simp
  · simp [ht]

/-- If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable, then for all `n : ℕ`,
`|X| ^ n * exp (v * X)` is integrable. -/
lemma integrable_pow_abs_mul_exp_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp ((v - t) * X ω)) μ) (n : ℕ) :
    Integrable (fun ω ↦ |X ω| ^ n * exp (v * X ω)) μ := by
  convert integrable_rpow_abs_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg
    (by positivity : 0 ≤ (n : ℝ)) with ω
  simp

/-- If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable, then for all nonnegative `p : ℝ`,
`X ^ p * exp (v * X)` is integrable. -/
lemma integrable_rpow_mul_exp_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp ((v - t) * X ω)) μ) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω ↦ X ω ^ p * exp (v * X ω)) μ := by
  have hX : AEMeasurable X μ := aemeasurable_of_integrable_exp_mul ?_ ht_int_pos ht_int_neg
  swap; · rw [← sub_ne_zero]; simp [ht]
  rw [← integrable_norm_iff]
  · simp_rw [norm_eq_abs, abs_mul, abs_exp]
    have h := integrable_rpow_abs_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg hp
    refine h.mono' ?_ ?_
    · exact ((hX.pow_const _).abs.mul
        (measurable_exp.comp_aemeasurable (hX.const_mul _))).aestronglyMeasurable
    · refine ae_of_all _ fun ω ↦ ?_
      simp only [norm_mul, norm_eq_abs, abs_abs, abs_exp]
      gcongr
      exact abs_rpow_le_abs_rpow _ _
  · exact ((hX.pow_const _).mul
      (measurable_exp.comp_aemeasurable (hX.const_mul _))).aestronglyMeasurable

/-- If `exp ((v + t) * X)` and `exp ((v - t) * X)` are integrable, then for all `n : ℕ`,
`X ^ n * exp (v * X)` is integrable. -/
lemma integrable_pow_mul_exp_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp ((v - t) * X ω)) μ) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n * exp (v * X ω)) μ := by
  convert integrable_rpow_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg
    (by positivity : 0 ≤ (n : ℝ)) with ω
  simp

/-- If `ω ↦ exp (t * X ω)` is integrable at `t` and `-t` for `t ≠ 0`, then `ω ↦ |X ω| ^ p` is
integrable for all nonnegative `p : ℝ`. -/
lemma integrable_rpow_abs_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ exp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp (- t * X ω)) μ) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω ↦ |X ω| ^ p) μ := by
  have h := integrable_rpow_abs_mul_exp_of_integrable_exp_mul (μ := μ) (X := X) ht (v := 0) ?_ ?_ hp
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

/-- If `ω ↦ exp (t * X ω)` is integrable at `t` and `-t` for `t ≠ 0`, then `ω ↦ |X ω| ^ n` is
integrable for all `n : ℕ`. That is, all moments of `X` are finite. -/
lemma integrable_pow_abs_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ exp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp (- t * X ω)) μ) (n : ℕ) :
    Integrable (fun ω ↦ |X ω| ^ n) μ := by
  convert integrable_rpow_abs_of_integrable_exp_mul ht ht_int_pos ht_int_neg
    (by positivity : 0 ≤ (n : ℝ)) with ω
  simp

/-- If `ω ↦ exp (t * X ω)` is integrable at `t` and `-t` for `t ≠ 0`, then `ω ↦ X ω ^ p` is
integrable for all nonnegative `p : ℝ`. -/
lemma integrable_rpow_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ exp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp (- t * X ω)) μ) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω ↦ X ω ^ p) μ := by
  have h := integrable_rpow_mul_exp_of_integrable_exp_mul (μ := μ) (X := X) ht (v := 0) ?_ ?_ hp
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

/-- If `ω ↦ exp (t * X ω)` is integrable at `t` and `-t` for `t ≠ 0`, then `ω ↦ X ω ^ n` is
integrable for all `n : ℕ`. -/
lemma integrable_pow_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ exp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ exp (- t * X ω)) μ) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n) μ := by
  convert integrable_rpow_of_integrable_exp_mul ht ht_int_pos ht_int_neg
    (by positivity : 0 ≤ (n : ℝ)) with ω
  simp

section IntegrableExpSet

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

/-- If the interior of the interval `integrableExpSet X μ` is nonempty,
then `X` is a.e. measurable. -/
lemma aemeasurable_of_mem_interior_integrableExpSet (hv : v ∈ interior (integrableExpSet X μ)) :
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

/-- If `v` belongs to the interior of the interval `integrableExpSet X μ`,
then `|X| ^ p * exp (v * X)` is integrable for all nonnegative `p : ℝ`. -/
lemma integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet
    (hv : v ∈ interior (integrableExpSet X μ)) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω ↦ |X ω| ^ p * exp (v * X ω)) μ := by
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hv
  obtain ⟨l, u, hvlu, h_subset⟩ := hv
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hvlu.1, hvlu.2]
  refine integrable_rpow_abs_mul_exp_of_integrable_exp_mul
    (t := min (v - l) (u - v) / 2) ?_ ?_ ?_ hp
  · positivity
  · exact h_subset (add_half_inf_sub_mem_Ioo hvlu)
  · exact h_subset (sub_half_inf_sub_mem_Ioo hvlu)

/-- If `v` belongs to the interior of the interval `integrableExpSet X μ`,
then `|X| ^ n * exp (v * X)` is integrable for all `n : ℕ`. -/
lemma integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet
    (hv : v ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    Integrable (fun ω ↦ |X ω| ^ n * exp (v * X ω)) μ := by
  convert integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet hv
    (by positivity : 0 ≤ (n : ℝ)) with ω
  simp

/-- If `v` belongs to the interior of the interval `integrableExpSet X μ`,
then `X ^ p * exp (v * X)` is integrable for all nonnegative `p : ℝ`. -/
lemma integrable_rpow_mul_exp_of_mem_interior_integrableExpSet
    (hv : v ∈ interior (integrableExpSet X μ)) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω ↦ X ω ^ p * exp (v * X ω)) μ := by
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hv
  obtain ⟨l, u, hvlu, h_subset⟩ := hv
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hvlu.1, hvlu.2]
  refine integrable_rpow_mul_exp_of_integrable_exp_mul
    (t := min (v - l) (u - v) / 2) ?_ ?_ ?_ hp
  · positivity
  · exact h_subset (add_half_inf_sub_mem_Ioo hvlu)
  · exact h_subset (sub_half_inf_sub_mem_Ioo hvlu)

/-- If `v` belongs to the interior of the interval `integrableExpSet X μ`,
then `X ^ n * exp (v * X)` is integrable for all `n : ℕ`. -/
lemma integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (hv : v ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n * exp (v * X ω)) μ := by
  convert integrable_rpow_mul_exp_of_mem_interior_integrableExpSet hv
    (by positivity : 0 ≤ (n : ℝ)) with ω
  simp

/-- If 0 belongs to the interior of the interval `integrableExpSet X μ`,
then `|X| ^ n` is integrable for all nonnegative `p : ℝ`. -/
lemma integrable_rpow_abs_of_mem_interior_integrableExpSet
    (h : 0 ∈ interior (integrableExpSet X μ)) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω ↦ |X ω| ^ p) μ := by
  convert integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet h hp using 1
  simp

/-- If 0 belongs to the interior of the interval `integrableExpSet X μ`,
then `|X| ^ n` is integrable for all `n : ℕ`. -/
lemma integrable_pow_abs_of_mem_interior_integrableExpSet
    (h : 0 ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    Integrable (fun ω ↦ |X ω| ^ n) μ := by
  convert integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet h n
  simp

/-- If 0 belongs to the interior of the interval `integrableExpSet X μ`,
then `X ^ n` is integrable for all nonnegative `p : ℝ`. -/
lemma integrable_rpow_of_mem_interior_integrableExpSet
    (h : 0 ∈ interior (integrableExpSet X μ)) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω ↦ X ω ^ p) μ := by
  convert integrable_rpow_mul_exp_of_mem_interior_integrableExpSet h hp using 1
  simp

/-- If 0 belongs to the interior of the interval `integrableExpSet X μ`,
then `X ^ n` is integrable for all `n : ℕ`. -/
lemma integrable_pow_of_mem_interior_integrableExpSet
    (h : 0 ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n) μ := by
  convert integrable_pow_mul_exp_of_mem_interior_integrableExpSet h n
  simp

/-- If 0 belongs to the interior of `integrableExpSet X μ`, then `X` is in `ℒp` for all
finite `p`. -/
lemma memLp_of_mem_interior_integrableExpSet (h : 0 ∈ interior (integrableExpSet X μ)) (p : ℝ≥0) :
    MemLp X p μ := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet h
  by_cases hp_zero : p = 0
  · simp only [hp_zero, ENNReal.coe_zero, memLp_zero_iff_aestronglyMeasurable]
    exact hX.aestronglyMeasurable
  rw [← integrable_norm_rpow_iff hX.aestronglyMeasurable (mod_cast hp_zero) (by simp)]
  simp only [norm_eq_abs, ENNReal.coe_toReal]
  exact integrable_rpow_abs_of_mem_interior_integrableExpSet h p.2

@[deprecated (since := "2025-02-21")]
alias mem𝓛p_of_mem_interior_integrableExpSet := memLp_of_mem_interior_integrableExpSet

section Complex

open Complex

variable {z : ℂ}

lemma integrable_cexp_mul_of_re_mem_integrableExpSet (hX : AEMeasurable X μ)
    (hz : z.re ∈ integrableExpSet X μ) :
    Integrable (fun ω ↦ cexp (z * X ω)) μ := by
  rw [← integrable_norm_iff]
  · simpa [Complex.norm_eq_abs, Complex.abs_exp] using hz
  · exact AEMeasurable.aestronglyMeasurable (by fun_prop)

lemma integrable_cexp_mul_of_re_mem_interior_integrableExpSet
    (hz : z.re ∈ interior (integrableExpSet X μ)) :
    Integrable (fun ω ↦ cexp (z * X ω)) μ :=
  integrable_cexp_mul_of_re_mem_integrableExpSet
    (aemeasurable_of_mem_interior_integrableExpSet hz) (interior_subset hz)

lemma integrable_rpow_abs_mul_cexp_of_re_mem_interior_integrableExpSet
    (hz : z.re ∈ interior (integrableExpSet X μ)) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω ↦ (|X ω| ^ p : ℝ) * cexp (z * X ω)) μ := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet hz
  rw [← integrable_norm_iff]
  swap; · exact AEMeasurable.aestronglyMeasurable (by fun_prop)
  simpa [abs_rpow_of_nonneg (abs_nonneg _), Complex.abs_exp]
    using integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet hz hp

lemma integrable_pow_abs_mul_cexp_of_re_mem_interior_integrableExpSet
    (hz : z.re ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    Integrable (fun ω ↦ |X ω| ^ n * cexp (z * X ω)) μ := by
  convert integrable_rpow_abs_mul_cexp_of_re_mem_interior_integrableExpSet hz (Nat.cast_nonneg n)
  simp

lemma integrable_rpow_mul_cexp_of_re_mem_interior_integrableExpSet
    (hz : z.re ∈ interior (integrableExpSet X μ)) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω ↦ (X ω ^ p : ℝ) * cexp (z * X ω)) μ := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet hz
  rw [← integrable_norm_iff]
  swap; · exact AEMeasurable.aestronglyMeasurable (by fun_prop)
  simp only [norm_mul, norm_real, Real.norm_eq_abs, Complex.norm_eq_abs, Complex.abs_exp, mul_re,
    ofReal_re, ofReal_im, mul_zero, sub_zero, Complex.abs_ofReal]
  refine (integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet hz hp).mono ?_ ?_
  · exact AEMeasurable.aestronglyMeasurable (by fun_prop)
  refine ae_of_all _ fun ω ↦ ?_
  simp only [norm_mul, Real.norm_eq_abs, Complex.abs_abs, Real.abs_exp]
  gcongr
  exact abs_rpow_le_abs_rpow _ _

lemma integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet
    (hz : z.re ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n * cexp (z * X ω)) μ := by
  convert integrable_rpow_mul_cexp_of_re_mem_interior_integrableExpSet hz (Nat.cast_nonneg n)
  simp

end Complex

end IntegrableExpSet

end FiniteMoments

end ProbabilityTheory
