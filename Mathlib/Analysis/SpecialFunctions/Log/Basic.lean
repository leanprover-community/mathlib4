/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.NormedSpace.Real

#align_import analysis.special_functions.log.basic from "leanprover-community/mathlib"@"f23a09ce6d3f367220dc3cecad6b7eb69eb01690"

/-!
# Real logarithm

In this file we define `Real.log` to be the logarithm of a real number. As usual, we extend it from
its domain `(0, +∞)` to a globally defined function. We choose to do it so that `log 0 = 0` and
`log (-x) = log x`.

We prove some basic properties of this function and show that it is continuous.

## Tags

logarithm, continuity
-/

open Set Filter Function

open Topology

noncomputable section

namespace Real

variable {x y : ℝ}

/-- The real logarithm function, equal to the inverse of the exponential for `x > 0`,
to `log |x|` for `x < 0`, and to `0` for `0`. We use this unconventional extension to
`(-∞, 0]` as it gives the formula `log (x * y) = log x + log y` for all nonzero `x` and `y`, and
the derivative of `log` is `1/x` away from `0`. -/
-- @[pp_nodot] -- Porting note: removed
noncomputable def log (x : ℝ) : ℝ :=
  if hx : x = 0 then 0 else expOrderIso.symm ⟨|x|, abs_pos.2 hx⟩
#align real.log Real.log

theorem log_of_ne_zero (hx : x ≠ 0) : log x = expOrderIso.symm ⟨|x|, abs_pos.2 hx⟩ :=
  dif_neg hx
#align real.log_of_ne_zero Real.log_of_ne_zero

theorem log_of_pos (hx : 0 < x) : log x = expOrderIso.symm ⟨x, hx⟩ := by
  rw [log_of_ne_zero hx.ne']
  congr
  exact abs_of_pos hx
#align real.log_of_pos Real.log_of_pos

theorem exp_log_eq_abs (hx : x ≠ 0) : exp (log x) = |x| := by
  rw [log_of_ne_zero hx, ← coe_expOrderIso_apply, OrderIso.apply_symm_apply, Subtype.coe_mk]
#align real.exp_log_eq_abs Real.exp_log_eq_abs

theorem exp_log (hx : 0 < x) : exp (log x) = x := by
  rw [exp_log_eq_abs hx.ne']
  exact abs_of_pos hx
#align real.exp_log Real.exp_log

theorem exp_log_of_neg (hx : x < 0) : exp (log x) = -x := by
  rw [exp_log_eq_abs (ne_of_lt hx)]
  exact abs_of_neg hx
#align real.exp_log_of_neg Real.exp_log_of_neg

theorem le_exp_log (x : ℝ) : x ≤ exp (log x) := by
  by_cases h_zero : x = 0
  · rw [h_zero, log, dif_pos rfl, exp_zero]
    exact zero_le_one
  · rw [exp_log_eq_abs h_zero]
    exact le_abs_self _
#align real.le_exp_log Real.le_exp_log

@[simp]
theorem log_exp (x : ℝ) : log (exp x) = x :=
  exp_injective <| exp_log (exp_pos x)
#align real.log_exp Real.log_exp

theorem surjOn_log : SurjOn log (Ioi 0) univ := fun x _ => ⟨exp x, exp_pos x, log_exp x⟩
#align real.surj_on_log Real.surjOn_log

theorem log_surjective : Surjective log := fun x => ⟨exp x, log_exp x⟩
#align real.log_surjective Real.log_surjective

@[simp]
theorem range_log : range log = univ :=
  log_surjective.range_eq
#align real.range_log Real.range_log

@[simp]
theorem log_zero : log 0 = 0 :=
  dif_pos rfl
#align real.log_zero Real.log_zero

@[simp]
theorem log_one : log 1 = 0 :=
  exp_injective <| by rw [exp_log zero_lt_one, exp_zero]
#align real.log_one Real.log_one

@[simp]
theorem log_abs (x : ℝ) : log |x| = log x := by
  by_cases h : x = 0
  · simp [h]
  · rw [← exp_eq_exp, exp_log_eq_abs h, exp_log_eq_abs (abs_pos.2 h).ne', abs_abs]
#align real.log_abs Real.log_abs

@[simp]
theorem log_neg_eq_log (x : ℝ) : log (-x) = log x := by rw [← log_abs x, ← log_abs (-x), abs_neg]
#align real.log_neg_eq_log Real.log_neg_eq_log

theorem sinh_log {x : ℝ} (hx : 0 < x) : sinh (log x) = (x - x⁻¹) / 2 := by
  rw [sinh_eq, exp_neg, exp_log hx]
#align real.sinh_log Real.sinh_log

theorem cosh_log {x : ℝ} (hx : 0 < x) : cosh (log x) = (x + x⁻¹) / 2 := by
  rw [cosh_eq, exp_neg, exp_log hx]
#align real.cosh_log Real.cosh_log

theorem surjOn_log' : SurjOn log (Iio 0) univ := fun x _ =>
  ⟨-exp x, neg_lt_zero.2 <| exp_pos x, by rw [log_neg_eq_log, log_exp]⟩
#align real.surj_on_log' Real.surjOn_log'

theorem log_mul (hx : x ≠ 0) (hy : y ≠ 0) : log (x * y) = log x + log y :=
  exp_injective <| by
    rw [exp_log_eq_abs (mul_ne_zero hx hy), exp_add, exp_log_eq_abs hx, exp_log_eq_abs hy, abs_mul]
#align real.log_mul Real.log_mul

theorem log_div (hx : x ≠ 0) (hy : y ≠ 0) : log (x / y) = log x - log y :=
  exp_injective <| by
    rw [exp_log_eq_abs (div_ne_zero hx hy), exp_sub, exp_log_eq_abs hx, exp_log_eq_abs hy, abs_div]
#align real.log_div Real.log_div

@[simp]
theorem log_inv (x : ℝ) : log x⁻¹ = -log x := by
  by_cases hx : x = 0; · simp [hx]
  rw [← exp_eq_exp, exp_log_eq_abs (inv_ne_zero hx), exp_neg, exp_log_eq_abs hx, abs_inv]
#align real.log_inv Real.log_inv

theorem log_le_log_iff (h : 0 < x) (h₁ : 0 < y) : log x ≤ log y ↔ x ≤ y := by
  rw [← exp_le_exp, exp_log h, exp_log h₁]
#align real.log_le_log Real.log_le_log_iff

@[gcongr]
lemma log_le_log (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y :=
  (log_le_log_iff hx (hx.trans_le hxy)).2 hxy

@[gcongr]
theorem log_lt_log (hx : 0 < x) (h : x < y) : log x < log y := by
  rwa [← exp_lt_exp, exp_log hx, exp_log (lt_trans hx h)]
#align real.log_lt_log Real.log_lt_log

theorem log_lt_log_iff (hx : 0 < x) (hy : 0 < y) : log x < log y ↔ x < y := by
  rw [← exp_lt_exp, exp_log hx, exp_log hy]
#align real.log_lt_log_iff Real.log_lt_log_iff

theorem log_le_iff_le_exp (hx : 0 < x) : log x ≤ y ↔ x ≤ exp y := by rw [← exp_le_exp, exp_log hx]
#align real.log_le_iff_le_exp Real.log_le_iff_le_exp

theorem log_lt_iff_lt_exp (hx : 0 < x) : log x < y ↔ x < exp y := by rw [← exp_lt_exp, exp_log hx]
#align real.log_lt_iff_lt_exp Real.log_lt_iff_lt_exp

theorem le_log_iff_exp_le (hy : 0 < y) : x ≤ log y ↔ exp x ≤ y := by rw [← exp_le_exp, exp_log hy]
#align real.le_log_iff_exp_le Real.le_log_iff_exp_le

theorem lt_log_iff_exp_lt (hy : 0 < y) : x < log y ↔ exp x < y := by rw [← exp_lt_exp, exp_log hy]
#align real.lt_log_iff_exp_lt Real.lt_log_iff_exp_lt

theorem log_pos_iff (hx : 0 < x) : 0 < log x ↔ 1 < x := by
  rw [← log_one]
  exact log_lt_log_iff zero_lt_one hx
#align real.log_pos_iff Real.log_pos_iff

theorem log_pos (hx : 1 < x) : 0 < log x :=
  (log_pos_iff (lt_trans zero_lt_one hx)).2 hx
#align real.log_pos Real.log_pos

theorem log_pos_of_lt_neg_one (hx : x < -1) : 0 < log x := by
  rw [← neg_neg x, log_neg_eq_log]
  have : 1 < -x := by linarith
  exact log_pos this

theorem log_neg_iff (h : 0 < x) : log x < 0 ↔ x < 1 := by
  rw [← log_one]
  exact log_lt_log_iff h zero_lt_one
#align real.log_neg_iff Real.log_neg_iff

theorem log_neg (h0 : 0 < x) (h1 : x < 1) : log x < 0 :=
  (log_neg_iff h0).2 h1
#align real.log_neg Real.log_neg

theorem log_neg_of_lt_zero (h0 : x < 0) (h1 : -1 < x) : log x < 0 := by
  rw [← neg_neg x, log_neg_eq_log]
  have h0' : 0 < -x := by linarith
  have h1' : -x < 1 := by linarith
  exact log_neg h0' h1'

theorem log_nonneg_iff (hx : 0 < x) : 0 ≤ log x ↔ 1 ≤ x := by rw [← not_lt, log_neg_iff hx, not_lt]
#align real.log_nonneg_iff Real.log_nonneg_iff

theorem log_nonneg (hx : 1 ≤ x) : 0 ≤ log x :=
  (log_nonneg_iff (zero_lt_one.trans_le hx)).2 hx
#align real.log_nonneg Real.log_nonneg

theorem log_nonpos_iff (hx : 0 < x) : log x ≤ 0 ↔ x ≤ 1 := by rw [← not_lt, log_pos_iff hx, not_lt]
#align real.log_nonpos_iff Real.log_nonpos_iff

theorem log_nonpos_iff' (hx : 0 ≤ x) : log x ≤ 0 ↔ x ≤ 1 := by
  rcases hx.eq_or_lt with (rfl | hx)
  · simp [le_refl, zero_le_one]
  exact log_nonpos_iff hx
#align real.log_nonpos_iff' Real.log_nonpos_iff'

theorem log_nonpos (hx : 0 ≤ x) (h'x : x ≤ 1) : log x ≤ 0 :=
  (log_nonpos_iff' hx).2 h'x
#align real.log_nonpos Real.log_nonpos

theorem log_natCast_nonneg (n : ℕ) : 0 ≤ log n := by
  if hn : n = 0 then
    simp [hn]
  else
    have : (1 : ℝ) ≤ n := mod_cast Nat.one_le_of_lt <| Nat.pos_of_ne_zero hn
    exact log_nonneg this

@[deprecated (since := "2024-04-17")]
alias log_nat_cast_nonneg := log_natCast_nonneg

theorem log_neg_natCast_nonneg (n : ℕ) : 0 ≤ log (-n) := by
  rw [← log_neg_eq_log, neg_neg]
  exact log_natCast_nonneg _

@[deprecated (since := "2024-04-17")]
alias log_neg_nat_cast_nonneg := log_neg_natCast_nonneg

theorem log_intCast_nonneg (n : ℤ) : 0 ≤ log n := by
  cases lt_trichotomy 0 n with
  | inl hn =>
      have : (1 : ℝ) ≤ n := mod_cast hn
      exact log_nonneg this
  | inr hn =>
      cases hn with
      | inl hn => simp [hn.symm]
      | inr hn =>
          have : (1 : ℝ) ≤ -n := by rw [← neg_zero, ← lt_neg] at hn; exact mod_cast hn
          rw [← log_neg_eq_log]
          exact log_nonneg this

@[deprecated (since := "2024-04-17")]
alias log_int_cast_nonneg := log_intCast_nonneg

theorem strictMonoOn_log : StrictMonoOn log (Set.Ioi 0) := fun _ hx _ _ hxy => log_lt_log hx hxy
#align real.strict_mono_on_log Real.strictMonoOn_log

theorem strictAntiOn_log : StrictAntiOn log (Set.Iio 0) := by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  rw [← log_abs y, ← log_abs x]
  refine log_lt_log (abs_pos.2 hy.ne) ?_
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]
#align real.strict_anti_on_log Real.strictAntiOn_log

theorem log_injOn_pos : Set.InjOn log (Set.Ioi 0) :=
  strictMonoOn_log.injOn
#align real.log_inj_on_pos Real.log_injOn_pos

theorem log_lt_sub_one_of_pos (hx1 : 0 < x) (hx2 : x ≠ 1) : log x < x - 1 := by
  have h : log x ≠ 0 := by
    rwa [← log_one, log_injOn_pos.ne_iff hx1]
    exact mem_Ioi.mpr zero_lt_one
  linarith [add_one_lt_exp h, exp_log hx1]
#align real.log_lt_sub_one_of_pos Real.log_lt_sub_one_of_pos

theorem eq_one_of_pos_of_log_eq_zero {x : ℝ} (h₁ : 0 < x) (h₂ : log x = 0) : x = 1 :=
  log_injOn_pos (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one) (h₂.trans Real.log_one.symm)
#align real.eq_one_of_pos_of_log_eq_zero Real.eq_one_of_pos_of_log_eq_zero

theorem log_ne_zero_of_pos_of_ne_one {x : ℝ} (hx_pos : 0 < x) (hx : x ≠ 1) : log x ≠ 0 :=
  mt (eq_one_of_pos_of_log_eq_zero hx_pos) hx
#align real.log_ne_zero_of_pos_of_ne_one Real.log_ne_zero_of_pos_of_ne_one

@[simp]
theorem log_eq_zero {x : ℝ} : log x = 0 ↔ x = 0 ∨ x = 1 ∨ x = -1 := by
  constructor
  · intro h
    rcases lt_trichotomy x 0 with (x_lt_zero | rfl | x_gt_zero)
    · refine Or.inr (Or.inr (neg_eq_iff_eq_neg.mp ?_))
      rw [← log_neg_eq_log x] at h
      exact eq_one_of_pos_of_log_eq_zero (neg_pos.mpr x_lt_zero) h
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (eq_one_of_pos_of_log_eq_zero x_gt_zero h))
  · rintro (rfl | rfl | rfl) <;> simp only [log_one, log_zero, log_neg_eq_log]
#align real.log_eq_zero Real.log_eq_zero

theorem log_ne_zero {x : ℝ} : log x ≠ 0 ↔ x ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1 := by
  simpa only [not_or] using log_eq_zero.not
#align real.log_ne_zero Real.log_ne_zero

@[simp]
theorem log_pow (x : ℝ) (n : ℕ) : log (x ^ n) = n * log x := by
  induction' n with n ih
  · simp
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  rw [pow_succ, log_mul (pow_ne_zero _ hx) hx, ih, Nat.cast_succ, add_mul, one_mul]
#align real.log_pow Real.log_pow

@[simp]
theorem log_zpow (x : ℝ) (n : ℤ) : log (x ^ n) = n * log x := by
  induction n
  · rw [Int.ofNat_eq_coe, zpow_natCast, log_pow, Int.cast_natCast]
  rw [zpow_negSucc, log_inv, log_pow, Int.cast_negSucc, Nat.cast_add_one, neg_mul_eq_neg_mul]
#align real.log_zpow Real.log_zpow

theorem log_sqrt {x : ℝ} (hx : 0 ≤ x) : log (√x) = log x / 2 := by
  rw [eq_div_iff, mul_comm, ← Nat.cast_two, ← log_pow, sq_sqrt hx]
  exact two_ne_zero
#align real.log_sqrt Real.log_sqrt

theorem log_le_sub_one_of_pos {x : ℝ} (hx : 0 < x) : log x ≤ x - 1 := by
  rw [le_sub_iff_add_le]
  convert add_one_le_exp (log x)
  rw [exp_log hx]
#align real.log_le_sub_one_of_pos Real.log_le_sub_one_of_pos

/-- Bound for `|log x * x|` in the interval `(0, 1]`. -/
theorem abs_log_mul_self_lt (x : ℝ) (h1 : 0 < x) (h2 : x ≤ 1) : |log x * x| < 1 := by
  have : 0 < 1 / x := by simpa only [one_div, inv_pos] using h1
  replace := log_le_sub_one_of_pos this
  replace : log (1 / x) < 1 / x := by linarith
  rw [log_div one_ne_zero h1.ne', log_one, zero_sub, lt_div_iff h1] at this
  have aux : 0 ≤ -log x * x := by
    refine mul_nonneg ?_ h1.le
    rw [← log_inv]
    apply log_nonneg
    rw [← le_inv h1 zero_lt_one, inv_one]
    exact h2
  rw [← abs_of_nonneg aux, neg_mul, abs_neg] at this
  exact this
#align real.abs_log_mul_self_lt Real.abs_log_mul_self_lt

/-- The real logarithm function tends to `+∞` at `+∞`. -/
theorem tendsto_log_atTop : Tendsto log atTop atTop :=
  tendsto_comp_exp_atTop.1 <| by simpa only [log_exp] using tendsto_id
#align real.tendsto_log_at_top Real.tendsto_log_atTop

theorem tendsto_log_nhdsWithin_zero : Tendsto log (𝓝[≠] 0) atBot := by
  rw [← show _ = log from funext log_abs]
  refine Tendsto.comp (g := log) ?_ tendsto_abs_nhdsWithin_zero
  simpa [← tendsto_comp_exp_atBot] using tendsto_id
#align real.tendsto_log_nhds_within_zero Real.tendsto_log_nhdsWithin_zero

lemma tendsto_log_nhdsWithin_zero_right : Tendsto log (𝓝[>] 0) atBot :=
  tendsto_log_nhdsWithin_zero.mono_left <| nhdsWithin_mono _ fun _ h ↦ ne_of_gt h

theorem continuousOn_log : ContinuousOn log {0}ᶜ := by
  simp (config := { unfoldPartialApp := true }) only [continuousOn_iff_continuous_restrict,
    restrict]
  conv in log _ => rw [log_of_ne_zero (show (x : ℝ) ≠ 0 from x.2)]
  exact expOrderIso.symm.continuous.comp (continuous_subtype_val.norm.subtype_mk _)
#align real.continuous_on_log Real.continuousOn_log

@[continuity]
theorem continuous_log : Continuous fun x : { x : ℝ // x ≠ 0 } => log x :=
  continuousOn_iff_continuous_restrict.1 <| continuousOn_log.mono fun _ => id
#align real.continuous_log Real.continuous_log

@[continuity]
theorem continuous_log' : Continuous fun x : { x : ℝ // 0 < x } => log x :=
  continuousOn_iff_continuous_restrict.1 <| continuousOn_log.mono fun _ hx => ne_of_gt hx
#align real.continuous_log' Real.continuous_log'

theorem continuousAt_log (hx : x ≠ 0) : ContinuousAt log x :=
  (continuousOn_log x hx).continuousAt <| isOpen_compl_singleton.mem_nhds hx
#align real.continuous_at_log Real.continuousAt_log

@[simp]
theorem continuousAt_log_iff : ContinuousAt log x ↔ x ≠ 0 := by
  refine ⟨?_, continuousAt_log⟩
  rintro h rfl
  exact not_tendsto_nhds_of_tendsto_atBot tendsto_log_nhdsWithin_zero _
    (h.tendsto.mono_left inf_le_left)
#align real.continuous_at_log_iff Real.continuousAt_log_iff

theorem log_prod {α : Type*} (s : Finset α) (f : α → ℝ) (hf : ∀ x ∈ s, f x ≠ 0) :
    log (∏ i ∈ s, f i) = ∑ i ∈ s, log (f i) := by
  induction' s using Finset.cons_induction_on with a s ha ih
  · simp
  · rw [Finset.forall_mem_cons] at hf
    simp [ih hf.2, log_mul hf.1 (Finset.prod_ne_zero_iff.2 hf.2)]
#align real.log_prod Real.log_prod

protected theorem _root_.Finsupp.log_prod {α β : Type*} [Zero β] (f : α →₀ β) (g : α → β → ℝ)
    (hg : ∀ a, g a (f a) = 0 → f a = 0) : log (f.prod g) = f.sum fun a b ↦ log (g a b) :=
  log_prod _ _ fun _x hx h₀ ↦ Finsupp.mem_support_iff.1 hx <| hg _ h₀

theorem log_nat_eq_sum_factorization (n : ℕ) :
    log n = n.factorization.sum fun p t => t * log p := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp -- relies on junk values of `log` and `Nat.factorization`
  · simp only [← log_pow, ← Nat.cast_pow]
    rw [← Finsupp.log_prod, ← Nat.cast_finsupp_prod, Nat.factorization_prod_pow_eq_self hn]
    intro p hp
    rw [pow_eq_zero (Nat.cast_eq_zero.1 hp), Nat.factorization_zero_right]
#align real.log_nat_eq_sum_factorization Real.log_nat_eq_sum_factorization

theorem tendsto_pow_log_div_mul_add_atTop (a b : ℝ) (n : ℕ) (ha : a ≠ 0) :
    Tendsto (fun x => log x ^ n / (a * x + b)) atTop (𝓝 0) :=
  ((tendsto_div_pow_mul_exp_add_atTop a b n ha.symm).comp tendsto_log_atTop).congr' <| by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx using by simp [exp_log hx]
#align real.tendsto_pow_log_div_mul_add_at_top Real.tendsto_pow_log_div_mul_add_atTop

theorem isLittleO_pow_log_id_atTop {n : ℕ} : (fun x => log x ^ n) =o[atTop] id := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · simpa using tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x h₁ h₂ using (h₁ h₂).elim
#align real.is_o_pow_log_id_at_top Real.isLittleO_pow_log_id_atTop

theorem isLittleO_log_id_atTop : log =o[atTop] id :=
  isLittleO_pow_log_id_atTop.congr_left fun _ => pow_one _
#align real.is_o_log_id_at_top Real.isLittleO_log_id_atTop

theorem isLittleO_const_log_atTop {c : ℝ} : (fun _ => c) =o[atTop] log := by
  refine Asymptotics.isLittleO_of_tendsto' ?_
    <| Tendsto.div_atTop (a := c) (by simp) tendsto_log_atTop
  filter_upwards [eventually_gt_atTop 1] with x hx
  aesop (add safe forward log_pos)

end Real

section Continuity

open Real

variable {α : Type*}

theorem Filter.Tendsto.log {f : α → ℝ} {l : Filter α} {x : ℝ} (h : Tendsto f l (𝓝 x)) (hx : x ≠ 0) :
    Tendsto (fun x => log (f x)) l (𝓝 (log x)) :=
  (continuousAt_log hx).tendsto.comp h
#align filter.tendsto.log Filter.Tendsto.log

variable [TopologicalSpace α] {f : α → ℝ} {s : Set α} {a : α}

@[fun_prop]
theorem Continuous.log (hf : Continuous f) (h₀ : ∀ x, f x ≠ 0) : Continuous fun x => log (f x) :=
  continuousOn_log.comp_continuous hf h₀
#align continuous.log Continuous.log

@[fun_prop]
nonrec theorem ContinuousAt.log (hf : ContinuousAt f a) (h₀ : f a ≠ 0) :
    ContinuousAt (fun x => log (f x)) a :=
  hf.log h₀
#align continuous_at.log ContinuousAt.log

nonrec theorem ContinuousWithinAt.log (hf : ContinuousWithinAt f s a) (h₀ : f a ≠ 0) :
    ContinuousWithinAt (fun x => log (f x)) s a :=
  hf.log h₀
#align continuous_within_at.log ContinuousWithinAt.log

@[fun_prop]
theorem ContinuousOn.log (hf : ContinuousOn f s) (h₀ : ∀ x ∈ s, f x ≠ 0) :
    ContinuousOn (fun x => log (f x)) s := fun x hx => (hf x hx).log (h₀ x hx)
#align continuous_on.log ContinuousOn.log

end Continuity

section TendstoCompAddSub

open Filter

namespace Real

theorem tendsto_log_comp_add_sub_log (y : ℝ) :
    Tendsto (fun x : ℝ => log (x + y) - log x) atTop (𝓝 0) := by
  have : Tendsto (fun x ↦ 1 + y / x) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
  rw [← comap_exp_nhds_exp, exp_zero, tendsto_comap_iff, ← add_zero (1 : ℝ)]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (-y)] with x hx₀ hxy
  rw [comp_apply, exp_sub, exp_log, exp_log, one_add_div] <;> linarith
#align real.tendsto_log_comp_add_sub_log Real.tendsto_log_comp_add_sub_log

theorem tendsto_log_nat_add_one_sub_log : Tendsto (fun k : ℕ => log (k + 1) - log k) atTop (𝓝 0) :=
  (tendsto_log_comp_add_sub_log 1).comp tendsto_natCast_atTop_atTop
#align real.tendsto_log_nat_add_one_sub_log Real.tendsto_log_nat_add_one_sub_log

end Real

end TendstoCompAddSub

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

variable {e : ℝ} {d : ℕ}

lemma log_nonneg_of_isNat {n : ℕ} (h : NormNum.IsNat e n) : 0 ≤ Real.log (e : ℝ) := by
  rw [NormNum.IsNat.to_eq h rfl]
  exact Real.log_natCast_nonneg _

lemma log_pos_of_isNat {n : ℕ} (h : NormNum.IsNat e n) (w : Nat.blt 1 n = true) :
    0 < Real.log (e : ℝ) := by
  rw [NormNum.IsNat.to_eq h rfl]
  apply Real.log_pos
  simpa using w

lemma log_nonneg_of_isNegNat {n : ℕ} (h : NormNum.IsInt e (.negOfNat n)) :
    0 ≤ Real.log (e : ℝ) := by
  rw [NormNum.IsInt.neg_to_eq h rfl]
  exact Real.log_neg_natCast_nonneg _

lemma log_pos_of_isNegNat {n : ℕ} (h : NormNum.IsInt e (.negOfNat n)) (w : Nat.blt 1 n = true) :
    0 < Real.log (e : ℝ) := by
  rw [NormNum.IsInt.neg_to_eq h rfl]
  rw [Real.log_neg_eq_log]
  apply Real.log_pos
  simpa using w

lemma log_pos_of_isRat {n : ℤ} :
    (NormNum.IsRat e n d) → (decide ((1 : ℚ) < n / d)) → (0 < Real.log (e : ℝ))
  | ⟨inv, eq⟩, h => by
    rw [eq, invOf_eq_inv, ← div_eq_mul_inv]
    have : 1 < (n : ℝ) / d := by exact_mod_cast of_decide_eq_true h
    exact Real.log_pos this

lemma log_pos_of_isRat_neg {n : ℤ} :
    (NormNum.IsRat e n d) → (decide (n / d < (-1 : ℚ))) → (0 < Real.log (e : ℝ))
  | ⟨inv, eq⟩, h => by
    rw [eq, invOf_eq_inv, ← div_eq_mul_inv]
    have : (n : ℝ) / d < -1 := by exact_mod_cast of_decide_eq_true h
    exact Real.log_pos_of_lt_neg_one this

lemma log_nz_of_isRat {n : ℤ} : (NormNum.IsRat e n d) → (decide ((0 : ℚ) < n / d))
    → (decide (n / d < (1 : ℚ))) → (Real.log (e : ℝ) ≠ 0)
  | ⟨inv, eq⟩, h₁, h₂ => by
    rw [eq, invOf_eq_inv, ← div_eq_mul_inv]
    have h₁' : 0 < (n : ℝ) / d := by exact_mod_cast of_decide_eq_true h₁
    have h₂' : (n : ℝ) / d < 1 := by exact_mod_cast of_decide_eq_true h₂
    exact ne_of_lt <| Real.log_neg h₁' h₂'

lemma log_nz_of_isRat_neg {n : ℤ} : (NormNum.IsRat e n d) → (decide (n / d < (0 : ℚ)))
    → (decide ((-1 : ℚ) < n / d)) → (Real.log (e : ℝ) ≠ 0)
  | ⟨inv, eq⟩, h₁, h₂ => by
    rw [eq, invOf_eq_inv, ← div_eq_mul_inv]
    have h₁' : (n : ℝ) / d < 0 := by exact_mod_cast of_decide_eq_true h₁
    have h₂' : -1 < (n : ℝ) / d := by exact_mod_cast of_decide_eq_true h₂
    exact ne_of_lt <| Real.log_neg_of_lt_zero h₁' h₂'

/-- Extension for the `positivity` tactic: `Real.log` of a natural number is always nonnegative. -/
@[positivity Real.log (Nat.cast _)]
def evalLogNatCast : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Real.log (Nat.cast $a)) =>
    assertInstancesCommute
    pure (.nonnegative q(Real.log_natCast_nonneg $a))
  | _, _, _ => throwError "not Real.log"

/-- Extension for the `positivity` tactic: `Real.log` of an integer is always nonnegative. -/
@[positivity Real.log (Int.cast _)]
def evalLogIntCast : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Real.log (Int.cast $a)) =>
    assertInstancesCommute
    pure (.nonnegative q(Real.log_intCast_nonneg $a))
  | _, _, _ => throwError "not Real.log"

/-- Extension for the `positivity` tactic: `Real.log` of a numeric literal. -/
@[positivity Real.log _]
def evalLogNatLit : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Real.log $a) =>
    match ← NormNum.derive a with
    | .isNat (_ : Q(AddMonoidWithOne ℝ)) lit p =>
      assumeInstancesCommute
      have p : Q(NormNum.IsNat $a $lit) := p
      if 1 < lit.natLit! then
        let p' : Q(Nat.blt 1 $lit = true) := (q(Eq.refl true) : Lean.Expr)
        pure (.positive q(log_pos_of_isNat $p $p'))
      else
        pure (.nonnegative q(log_nonneg_of_isNat $p))
    | .isNegNat _ lit p =>
      assumeInstancesCommute
      have p : Q(NormNum.IsInt $a (Int.negOfNat $lit)) := p
      if 1 < lit.natLit! then
        let p' : Q(Nat.blt 1 $lit = true) := (q(Eq.refl true) : Lean.Expr)
        pure (.positive q(log_pos_of_isNegNat $p $p'))
      else
        pure (.nonnegative q(log_nonneg_of_isNegNat $p))
    | .isRat (i : Q(DivisionRing ℝ)) q n d p =>
      assumeInstancesCommute
      have p : Q(by clear! «$i»; exact NormNum.IsRat $a $n $d) := p
      if 0 < q ∧ q < 1 then
        let w₁ : Q(decide ((0 : ℚ) < $n / $d) = true) := (q(Eq.refl true) : Lean.Expr)
        let w₂ : Q(decide ($n / $d < (1 : ℚ)) = true) := (q(Eq.refl true) : Lean.Expr)
        pure (.nonzero q(log_nz_of_isRat $p $w₁ $w₂))
      else if 1 < q then
        let w : Q(decide ((1 : ℚ) < $n / $d) = true) := (q(Eq.refl true) : Lean.Expr)
        pure (.positive q(log_pos_of_isRat $p $w))
      else if -1 < q ∧ q < 0 then
        let w₁ : Q(decide ($n / $d < (0 : ℚ)) = true) := (q(Eq.refl true) : Lean.Expr)
        let w₂ : Q(decide ((-1 : ℚ) < $n / $d) = true) := (q(Eq.refl true) : Lean.Expr)
        pure (.nonzero q(log_nz_of_isRat_neg $p $w₁ $w₂))
      else if q < -1 then
        let w : Q(decide ($n / $d < (-1 : ℚ)) = true) := (q(Eq.refl true) : Lean.Expr)
        pure (.positive q(log_pos_of_isRat_neg $p $w))
      else
        failure
    | _ => failure
  | _, _, _ => throwError "not Real.log"

end Mathlib.Meta.Positivity
