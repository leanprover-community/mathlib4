/-
Copyright (c) 2023 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Properties of Shannon q-ary entropy and binary entropy functions

The [binary entropy function](https://en.wikipedia.org/wiki/Binary_entropy_function)
`binEntropy p := - p * log p - (1 - p) * log (1 - p)`
is the Shannon entropy of a Bernoulli random variable with success probability `p`.

More generally, the q-ary entropy function is the Shannon entropy of the random variable
with possible outcomes `{1, ..., q}`, where outcome `1` has probability `1 - p`
and all other outcomes are equally likely.

`qaryEntropy (q : ℕ) (p : ℝ) := p * log (q - 1) - p * log p - (1 - p) * log (1 - p)`

This file assumes that entropy is measured in Nats, hence the use of natural logarithms.
Most lemmas are also valid using a logarithm in a different base.

## Main declarations

* `Real.binEntropy`: the binary entropy function
* `Real.qaryEntropy`: the `q`-ary entropy function

## Main results

The functions are also defined outside the interval `Icc 0 1` due to `log x = log |x|`.

* They are continuous everywhere (`binEntropy_continuous` and `qaryEntropy_continuous`).
* They are differentiable everywhere except at points `0` or `1`
  (`hasDerivAt_binEntropy` and `hasDerivAt_qaryEntropy`).
  In addition, due to junk values, `deriv binEntropy p = log (1 - p) - log p`
  holds everywhere (`deriv_binEntropy`).
* they are strictly increasing on `Icc 0 (1 - 1/q))`
  (`qaryEntropy_strictMonoOn`, `binEntropy_strictMonoOn`)
  and strictly decreasing on `Icc (1 - 1/q) 1`
  (`binEntropy_strictAntiOn` and `qaryEntropy_strictAntiOn`).
* they are strictly concave on `Icc 0 1`
  (`strictConcaveOn_qaryEntropy` and `strictConcave_binEntropy`).

## Tags

entropy, Shannon, binary, nit, nepit
-/

namespace Real
variable {q : ℕ} {p : ℝ}

/-! ### Binary entropy -/

/-- The [binary entropy function](https://en.wikipedia.org/wiki/Binary_entropy_function)
`binEntropy p := - p * log p - (1-p) * log (1 - p)`
is the Shannon entropy of a Bernoulli random variable with success probability `p`. -/
@[pp_nodot] noncomputable def binEntropy (p : ℝ) : ℝ := p * log p⁻¹ + (1 - p) * log (1 - p)⁻¹

@[simp] lemma binEntropy_zero : binEntropy 0 = 0 := by simp [binEntropy]
@[simp] lemma binEntropy_one : binEntropy 1 = 0 := by simp [binEntropy]
@[simp] lemma binEntropy_two_inv : binEntropy 2⁻¹ = log 2 := by norm_num [binEntropy]; simp; ring

lemma binEntropy_eq_negMulLog_add_negMulLog_one_sub (p : ℝ) :
    binEntropy p = negMulLog p + negMulLog (1 - p) := by simp [binEntropy, negMulLog, ← neg_mul]

lemma binEntropy_eq_negMulLog_add_negMulLog_one_sub' :
    binEntropy = fun p ↦ negMulLog p + negMulLog (1 - p) :=
  funext binEntropy_eq_negMulLog_add_negMulLog_one_sub

/-- `binEntropy` is symmetric about 1/2. -/
@[simp] lemma binEntropy_one_sub (p : ℝ) : binEntropy (1 - p) = binEntropy p := by
  simp [binEntropy, add_comm]

/-- `binEntropy` is symmetric about 1/2. -/
lemma binEntropy_two_inv_add (p : ℝ) : binEntropy (2⁻¹ + p) = binEntropy (2⁻¹ - p) := by
  rw [← binEntropy_one_sub]; ring_nf

lemma binEntropy_pos (hp₀ : 0 < p) (hp₁ : p < 1) : 0 < binEntropy p := by
  unfold binEntropy
  have : 0 < 1 - p := sub_pos.2 hp₁
  have : 0 < log p⁻¹ := log_pos <| (one_lt_inv₀ hp₀).2 hp₁
  have : 0 < log (1 - p)⁻¹ := log_pos <| (one_lt_inv₀ ‹_›).2 (sub_lt_self _ hp₀)
  positivity

lemma binEntropy_nonneg (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : 0 ≤ binEntropy p := by
  obtain rfl | hp₀ := hp₀.eq_or_lt
  · simp
  obtain rfl | hp₁ := hp₁.eq_or_lt
  · simp
  exact (binEntropy_pos hp₀ hp₁).le

/-- Outside the usual range of `binEntropy`, it is negative. This is due to `log p = log |p|`. -/
lemma binEntropy_neg_of_neg (hp : p < 0) : binEntropy p < 0 := by
  rw [binEntropy, log_inv, log_inv]
  suffices -p * log p < (1 - p) * log (1 - p) by linarith
  by_cases hp' : p < -1
  · have : log p < log (1 - p) := by
      rw [← log_neg_eq_log]
      exact log_lt_log (Left.neg_pos_iff.mpr hp) (by linarith)
    nlinarith [log_pos_of_lt_neg_one hp']
  · have : -p * log p ≤ 0 := by
      wlog h : -1 < p
      · simp only [show p = -1 by linarith, log_neg_eq_log, log_one, le_refl, mul_zero]
      · nlinarith [log_neg_of_lt_zero hp h]
    nlinarith [(log_pos (by linarith) : 0 < log (1 - p))]

/-- Outside the usual range of `binEntropy`, it is negative. This is due to `log p = log |p|`. -/
lemma binEntropy_nonpos_of_nonpos (hp : p ≤ 0) : binEntropy p ≤ 0 := by
  obtain rfl | hp := hp.eq_or_lt
  · simp
  · exact (binEntropy_neg_of_neg hp).le

/-- Outside the usual range of `binEntropy`, it is negative. This is due to `log p = log |p|` -/
lemma binEntropy_neg_of_one_lt (hp : 1 < p) : binEntropy p < 0 := by
  rw [← binEntropy_one_sub]; exact binEntropy_neg_of_neg (sub_neg.2 hp)

/-- Outside the usual range of `binEntropy`, it is negative. This is due to `log p = log |p|` -/
lemma binEntropy_nonpos_of_one_le (hp : 1 ≤ p) : binEntropy p ≤ 0 := by
  rw [← binEntropy_one_sub]; exact binEntropy_nonpos_of_nonpos (sub_nonpos.2 hp)

lemma binEntropy_eq_zero : binEntropy p = 0 ↔ p = 0 ∨ p = 1 := by
  refine ⟨fun h ↦ ?_, by rintro (rfl | rfl) <;> simp⟩
  contrapose! h
  obtain hp₀ | hp₀ := h.1.lt_or_gt
  · exact (binEntropy_neg_of_neg hp₀).ne
  obtain hp₁ | hp₁ := h.2.lt_or_gt.symm
  · exact (binEntropy_neg_of_one_lt hp₁).ne
  · exact (binEntropy_pos hp₀ hp₁).ne'

/-- For probability `p ≠ 0.5`, `binEntropy p < log 2`. -/
lemma binEntropy_lt_log_two : binEntropy p < log 2 ↔ p ≠ 2⁻¹ := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro h rfl
    simp at h
  wlog hp : p < 2⁻¹
  · have hp : 1 - p < 2⁻¹ := by
      rw [sub_lt_comm]; norm_num at *; linarith +splitNe
    rw [← binEntropy_one_sub]
    exact this hp.ne hp
  obtain hp₀ | hp₀ := le_or_gt p 0
  · exact (binEntropy_nonpos_of_nonpos hp₀).trans_lt <| log_pos <| by simp
  have hp₁ : 0 < 1 - p := sub_pos.2 <| hp.trans <| by norm_num
  calc
  _ < log (p * p⁻¹ + (1 - p) * (1 - p)⁻¹) :=
    strictConcaveOn_log_Ioi.2 (inv_pos.2 hp₀) (inv_pos.2 hp₁)
      (by simpa [eq_sub_iff_add_eq, ← two_mul, mul_comm, mul_eq_one_iff_eq_inv₀]) hp₀ hp₁ (by simp)
  _ = log 2 := by rw [mul_inv_cancel₀, mul_inv_cancel₀, one_add_one_eq_two] <;> positivity

lemma binEntropy_le_log_two : binEntropy p ≤ log 2 := by
  obtain rfl | hp := eq_or_ne p 2⁻¹
  · simp
  · exact (binEntropy_lt_log_two.2 hp).le

lemma binEntropy_eq_log_two : binEntropy p = log 2 ↔ p = 2⁻¹ := by
  rw [← binEntropy_le_log_two.not_lt_iff_eq, binEntropy_lt_log_two, not_ne_iff]

/-- Binary entropy is continuous everywhere.
This is due to definition of `Real.log` for negative numbers. -/
@[fun_prop] lemma binEntropy_continuous : Continuous binEntropy := by
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub']; fun_prop

@[fun_prop] lemma differentiableAt_binEntropy (hp₀ : p ≠ 0) (hp₁ : p ≠ 1) :
    DifferentiableAt ℝ binEntropy p := by
  rw [ne_comm, ← sub_ne_zero] at hp₁
  unfold binEntropy
  simp only [log_inv, mul_neg]
  fun_prop (disch := assumption)

lemma differentiableAt_binEntropy_iff_ne_zero_one :
    DifferentiableAt ℝ binEntropy p ↔ p ≠ 0 ∧ p ≠ 1 := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ differentiableAt_binEntropy h.1 h.2⟩
    <;> rintro rfl <;> unfold binEntropy at h
  · rw [DifferentiableAt.fun_add_iff_left] at h
    · simp [log_inv, mul_neg, ← neg_mul, ← negMulLog_def, differentiableAt_negMulLog_iff] at h
    · fun_prop (disch := simp)
  · rw [DifferentiableAt.fun_add_iff_right, differentiableAt_iff_comp_const_sub (b := 1)] at h
    · simp [log_inv, mul_neg, ← neg_mul, ← negMulLog_def, differentiableAt_negMulLog_iff] at h
    · fun_prop (disch := simp)

set_option push_neg.use_distrib true in
/-- Binary entropy has derivative `log (1 - p) - log p`.
It's not differentiable at `0` or `1` but the junk values of `deriv` and `log` coincide there. -/
lemma deriv_binEntropy (p : ℝ) : deriv binEntropy p = log (1 - p) - log p := by
  by_cases hp : p ≠ 0 ∧ p ≠ 1
  · obtain ⟨hp₀, hp₁⟩ := hp
    rw [ne_comm, ← sub_ne_zero] at hp₁
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub', deriv_fun_add, deriv_comp_const_sub,
      deriv_negMulLog hp₀, deriv_negMulLog hp₁]
    · ring
    all_goals fun_prop (disch := assumption)
  -- pathological case where `deriv = 0` since `binEntropy` is not differentiable there
  · rw [deriv_zero_of_not_differentiableAt (differentiableAt_binEntropy_iff_ne_zero_one.not.2 hp)]
    push_neg at hp
    obtain rfl | rfl := hp <;> simp

/-! ### `q`-ary entropy -/

/-- Shannon q-ary Entropy function (measured in Nats, i.e., using natural logs).

It's the Shannon entropy of a random variable with possible outcomes {1, ..., q}
where outcome `1` has probability `1 - p` and all other outcomes are equally likely.

The usual domain of definition is p ∈ [0,1], i.e., input is a probability.

This is a generalization of the binary entropy function `binEntropy`. -/
@[pp_nodot] noncomputable def qaryEntropy (q : ℕ) (p : ℝ) : ℝ := p * log (q - 1 : ℤ) + binEntropy p

@[simp] lemma qaryEntropy_zero (q : ℕ) : qaryEntropy q 0 = 0 := by simp [qaryEntropy]
@[simp] lemma qaryEntropy_one (q : ℕ) : qaryEntropy q 1 = log (q - 1 : ℤ) := by simp [qaryEntropy]
@[simp] lemma qaryEntropy_two : qaryEntropy 2 = binEntropy := by ext; simp [qaryEntropy]

lemma qaryEntropy_pos (hp₀ : 0 < p) (hp₁ : p < 1) : 0 < qaryEntropy q p := by
  unfold qaryEntropy
  have := binEntropy_pos hp₀ hp₁
  positivity

lemma qaryEntropy_nonneg (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : 0 ≤ qaryEntropy q p := by
  obtain rfl | hp₀ := hp₀.eq_or_lt
  · simp
  obtain rfl | hp₁ := hp₁.eq_or_lt
  · simpa [qaryEntropy, -Int.cast_sub] using log_intCast_nonneg _
  exact (qaryEntropy_pos hp₀ hp₁).le

/-- Outside the usual range of `qaryEntropy`, it is negative. This is due to `log p = log |p|`. -/
lemma qaryEntropy_neg_of_neg (hp : p < 0) : qaryEntropy q p < 0 :=
  add_neg_of_nonpos_of_neg (mul_nonpos_of_nonpos_of_nonneg hp.le (log_intCast_nonneg _))
    (binEntropy_neg_of_neg hp)

/-- Outside the usual range of `qaryEntropy`, it is negative. This is due to `log p = log |p|`. -/
lemma qaryEntropy_nonpos_of_nonpos (hp : p ≤ 0) : qaryEntropy q p ≤ 0 :=
  add_nonpos (mul_nonpos_of_nonpos_of_nonneg hp (log_intCast_nonneg _))
    (binEntropy_nonpos_of_nonpos hp)

/-- The q-ary entropy function is continuous everywhere.
This is due to definition of `Real.log` for negative numbers. -/
@[fun_prop] lemma qaryEntropy_continuous : Continuous (qaryEntropy q) := by
  unfold qaryEntropy; fun_prop

@[fun_prop] lemma differentiableAt_qaryEntropy (hp₀ : p ≠ 0) (hp₁ : p ≠ 1) :
    DifferentiableAt ℝ (qaryEntropy q) p := by unfold qaryEntropy; fun_prop (disch := assumption)

lemma deriv_qaryEntropy (hp₀ : p ≠ 0) (hp₁ : p ≠ 1) :
    deriv (qaryEntropy q) p = log (q - 1) + log (1 - p) - log p := by
  unfold qaryEntropy
  rw [deriv_fun_add]
  · simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one, differentiableAt_fun_id,
      deriv_mul_const, deriv_id'', one_mul, deriv_binEntropy, add_sub_assoc]
  all_goals fun_prop (disch := assumption)

/-- Binary entropy has derivative `log (1 - p) - log p`. -/
lemma hasDerivAt_binEntropy (hp₀ : p ≠ 0) (hp₁ : p ≠ 1) :
    HasDerivAt binEntropy (log (1 - p) - log p) p :=
  deriv_binEntropy _ ▸ (differentiableAt_binEntropy hp₀ hp₁).hasDerivAt

lemma hasDerivAt_qaryEntropy (hp₀ : p ≠ 0) (hp₁ : p ≠ 1) :
    HasDerivAt (qaryEntropy q) (log (q - 1) + log (1 - p) - log p) p :=
  deriv_qaryEntropy hp₀ hp₁ ▸ (differentiableAt_qaryEntropy hp₀ hp₁).hasDerivAt

open Filter Topology Set

private lemma tendsto_log_one_sub_sub_log_nhdsGT_atAtop :
    Tendsto (fun p ↦ log (1 - p) - log p) (𝓝[>] 0) atTop := by
  apply Filter.tendsto_atTop_add_left_of_le' (𝓝[>] 0) (log (1/2) : ℝ)
  · have h₁ : (0 : ℝ) < 1 / 2 := by simp
    filter_upwards [Ioc_mem_nhdsGT h₁] with p hx
    gcongr
    linarith [hx.2]
  · apply tendsto_neg_atTop_iff.mpr tendsto_log_nhdsGT_zero

private lemma tendsto_log_one_sub_sub_log_nhdsLT_one_atBot :
    Tendsto (fun p ↦ log (1 - p) - log p) (𝓝[<] 1) atBot := by
  apply Filter.tendsto_atBot_add_right_of_ge' (𝓝[<] 1) (-log (1 - 2⁻¹))
  · have : Tendsto log (𝓝[>] 0) atBot := Real.tendsto_log_nhdsGT_zero
    apply Tendsto.comp (f := (1 - ·)) (g := log) this
    have contF : Continuous ((1 : ℝ) - ·) := continuous_sub_left 1
    have : MapsTo ((1 : ℝ) - ·) (Iio 1) (Ioi 0) := by
      intro p hx
      simp_all only [mem_Iio, mem_Ioi, sub_pos]
    convert ContinuousWithinAt.tendsto_nhdsWithin (x :=(1 : ℝ)) contF.continuousWithinAt this
    exact Eq.symm (sub_eq_zero_of_eq rfl)
  · have h₁ : (1 : ℝ) - (2 : ℝ)⁻¹ < 1 := by norm_num
    filter_upwards [Ico_mem_nhdsLT h₁] with p hx
    gcongr
    exact hx.1

lemma not_continuousAt_deriv_qaryEntropy_one :
    ¬ContinuousAt (deriv (qaryEntropy q)) 1 := by
  have tendstoBot : Tendsto (fun p ↦ log (q - 1) + log (1 - p) - log p) (𝓝[<] 1) atBot := by
    have : (fun p ↦ log (q - 1) + log (1 - p) - log p)
      = (fun p ↦ log (q - 1) + (log (1 - p) - log p)) := by
      ext
      ring
    rw [this]
    apply tendsto_atBot_add_const_left
    exact tendsto_log_one_sub_sub_log_nhdsLT_one_atBot
  apply not_continuousAt_of_tendsto (Filter.Tendsto.congr' _ tendstoBot) nhdsWithin_le_nhds
  · simp only [disjoint_nhds_atBot_iff, not_isBot, not_false_eq_true]
  filter_upwards [Ioo_mem_nhdsLT (show 1 - 2⁻¹ < (1 : ℝ) by norm_num)]
  intros
  apply (deriv_qaryEntropy _ _).symm
  · simp_all only [mem_Ioo, ne_eq]
    linarith [show (1 : ℝ) = 2⁻¹ + 2⁻¹ by norm_num]
  · simp_all only [mem_Ioo, ne_eq]
    linarith [two_inv_lt_one (α := ℝ)]

lemma not_continuousAt_deriv_qaryEntropy_zero :
    ¬ContinuousAt (deriv (qaryEntropy q)) 0 := by
  have tendstoTop : Tendsto (fun p ↦ log (q - 1) + log (1 - p) - log p) (𝓝[>] 0) atTop := by
    have : (fun p ↦ log (q - 1) + log (1 - p) - log p)
        = (fun p ↦ log (q - 1) + (log (1 - p) - log p)) := by ext; ring
    rw [this]
    exact tendsto_atTop_add_const_left _ _ tendsto_log_one_sub_sub_log_nhdsGT_atAtop
  apply not_continuousAt_of_tendsto (Filter.Tendsto.congr' _ tendstoTop) nhdsWithin_le_nhds
  · simp only [disjoint_nhds_atTop_iff, not_isTop, not_false_eq_true]
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2⁻¹ by norm_num)]
  intros
  apply (deriv_qaryEntropy _ _).symm
  · simp_all only [mem_Ioo, ne_eq]
    linarith
  · simp_all only [mem_Ioo, ne_eq]
    linarith [two_inv_lt_one (α := ℝ)]

/-- Second derivative of q-ary entropy. -/
lemma deriv2_qaryEntropy :
    deriv^[2] (qaryEntropy q) p = -1 / (p * (1 - p)) := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp, Function.comp_apply]
  by_cases is_x_where_nondiff : p ≠ 0 ∧ p ≠ 1  -- normal case
  · obtain ⟨xne0, xne1⟩ := is_x_where_nondiff
    suffices ∀ᶠ y in (𝓝 p),
        deriv (fun p ↦ (qaryEntropy q) p) y = log (q - 1) + log (1 - y) - log y by
      refine (Filter.EventuallyEq.deriv_eq this).trans ?_
      rw [deriv_fun_sub ?_ (differentiableAt_log xne0)]
      · rw [deriv.log differentiableAt_fun_id xne0]
        simp only [deriv_id'', one_div]
        · have {q : ℝ} (p : ℝ) : DifferentiableAt ℝ (fun p => q - p) p := by fun_prop
          have d_oneminus (p : ℝ) : deriv (fun (y : ℝ) ↦ 1 - y) p = -1 := by
            rw [deriv_const_sub 1, deriv_id'']
          simp [field, sub_ne_zero_of_ne xne1.symm, this, d_oneminus]
          ring
      · apply DifferentiableAt.add
        simp only [differentiableAt_const]
        exact DifferentiableAt.log (by fun_prop) (sub_ne_zero.mpr xne1.symm)
    filter_upwards [eventually_ne_nhds xne0, eventually_ne_nhds xne1]
      with y xne0 h2 using deriv_qaryEntropy xne0 h2
  -- Pathological case where we use junk value (because function not differentiable)
  · have : p = 0 ∨ p = 1 := Decidable.or_iff_not_not_and_not.mpr is_x_where_nondiff
    rw [deriv_zero_of_not_differentiableAt]
    · simp_all only [ne_eq, not_and, Decidable.not_not]
      cases this <;> simp_all only [
        mul_zero, one_ne_zero, zero_ne_one, sub_zero, mul_one, div_zero, sub_self]
    · intro h
      have contAt := h.continuousAt
      cases this <;> simp_all [
        not_continuousAt_deriv_qaryEntropy_zero, not_continuousAt_deriv_qaryEntropy_one]

lemma deriv2_binEntropy : deriv^[2] binEntropy p = -1 / (p * (1 - p)) :=
  qaryEntropy_two ▸ deriv2_qaryEntropy

/-! ### Strict monotonicity of entropy -/

/-- Qary entropy is strictly increasing in the interval [0, 1 - q⁻¹]. -/
lemma qaryEntropy_strictMonoOn (qLe2 : 2 ≤ q) :
    StrictMonoOn (qaryEntropy q) (Icc 0 (1 - 1/q)) := by
  intro p1 hp1 p2 hp2 p1le2
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (1 - 1/(q : ℝ))) _ _ hp1 hp2 p1le2
  · exact qaryEntropy_continuous.continuousOn
  · intro p hp
    have : 2 ≤ (q : ℝ) := Nat.ofNat_le_cast.mpr qLe2
    have zero_le_qinv : 0 < (q : ℝ)⁻¹ := by positivity
    have : 0 < 1 - p := by
      simp only [sub_pos]
      have p_lt_1_minus_qinv : p < 1 - (q : ℝ)⁻¹ := by
        simp_all only [inv_pos, interior_Icc, mem_Ioo, one_div]
      linarith
    simp only [one_div, interior_Icc, mem_Ioo] at hp
    rw [deriv_qaryEntropy (by linarith)]
    · simp
      rw [← log_mul (by linarith) (by linarith)]
      apply Real.strictMonoOn_log (mem_Ioi.mpr hp.1)
      · simp_all only [mem_Ioi, mul_pos_iff_of_pos_left, show 0 < (q : ℝ) - 1 by linarith]
      · have qpos : 0 < (q : ℝ) := by positivity
        have : q * p < q - 1 := by
          convert (mul_lt_mul_left qpos).2 hp.2 using 1
          simp only [mul_sub, mul_one, isUnit_iff_ne_zero, ne_eq, ne_of_gt qpos, not_false_eq_true,
            IsUnit.mul_inv_cancel]
        linarith
    exact (ne_of_gt (lt_add_neg_iff_lt.mp this : p < 1)).symm

/-- Qary entropy is strictly decreasing in the interval [1 - q⁻¹, 1]. -/
lemma qaryEntropy_strictAntiOn (qLe2 : 2 ≤ q) :
    StrictAntiOn (qaryEntropy q) (Icc (1 - 1/q) 1) := by
  intro p1 hp1 p2 hp2 p1le2
  apply strictAntiOn_of_deriv_neg (convex_Icc (1 - 1/(q : ℝ)) 1) _ _ hp1 hp2 p1le2
  · exact qaryEntropy_continuous.continuousOn
  · intro p hp
    have : 2 ≤ (q : ℝ) := Nat.ofNat_le_cast.mpr qLe2
    have qinv_lt_1 : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    have zero_lt_1_sub_p : 0 < 1 - p := by simp_all only [sub_pos, interior_Icc, mem_Ioo]
    simp only [one_div, interior_Icc, mem_Ioo] at hp
    rw [deriv_qaryEntropy (by linarith)]
    · simp
      rw [← log_mul (by linarith) (by linarith)]
      apply Real.strictMonoOn_log (mem_Ioi.mpr (show 0 < (↑q - 1) * (1 - p) by nlinarith))
      · simp_all only [mem_Ioi]
        linarith
      · have qpos : 0 < (q : ℝ) := by positivity
        ring_nf
        simp only [add_lt_iff_neg_right, neg_add_lt_iff_lt_add, add_zero, gt_iff_lt]
        have : (q : ℝ) - 1 < p * q := by
          have tmp := mul_lt_mul_of_pos_right hp.1 qpos
          simp at tmp
          have : (q : ℝ) ≠ 0 := (ne_of_lt qpos).symm
          have asdfasfd : (1 - (q : ℝ)⁻¹) * ↑q = q - 1 := by calc (1 - (q : ℝ)⁻¹) * ↑q
            _ = q - (q : ℝ)⁻¹ * (q : ℝ) := by ring
            _ = q - 1 := by simp_all only [ne_eq, isUnit_iff_ne_zero,
              not_false_eq_true, IsUnit.inv_mul_cancel]
          rwa [asdfasfd] at tmp
        nlinarith
    exact (ne_of_gt (lt_add_neg_iff_lt.mp zero_lt_1_sub_p : p < 1)).symm

/-- Binary entropy is strictly increasing in interval [0, 1/2]. -/
lemma binEntropy_strictMonoOn : StrictMonoOn binEntropy (Icc 0 2⁻¹) := by
  rw [show Icc (0 : ℝ) 2⁻¹ = Icc 0 (1 - 1/2) by norm_num, ← qaryEntropy_two]
  exact qaryEntropy_strictMonoOn (by rfl)

/-- Binary entropy is strictly decreasing in interval [1/2, 1]. -/
lemma binEntropy_strictAntiOn : StrictAntiOn binEntropy (Icc 2⁻¹ 1) := by
  rw [show (Icc (2⁻¹ : ℝ) 1) = Icc (1/2) 1 by norm_num, ← qaryEntropy_two]
  convert qaryEntropy_strictAntiOn (by rfl) using 1
  norm_num

/-! ### Strict concavity of entropy -/

lemma strictConcaveOn_qaryEntropy : StrictConcaveOn ℝ (Icc 0 1) (qaryEntropy q) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 1) qaryEntropy_continuous.continuousOn
  intro p hp
  rw [deriv2_qaryEntropy]
  · simp_all only [interior_Icc, mem_Ioo]
    apply div_neg_of_neg_of_pos
    · norm_num [show 0 < log 2 by positivity]
    · simp_all only [mul_pos_iff_of_pos_left, sub_pos]

lemma strictConcave_binEntropy : StrictConcaveOn ℝ (Icc 0 1) binEntropy :=
  qaryEntropy_two ▸ strictConcaveOn_qaryEntropy

end Real
