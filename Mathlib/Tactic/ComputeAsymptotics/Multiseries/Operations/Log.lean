/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Operations.Inv
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.LogBasis

/-!
# Logarithm of Multiseries

-/

@[expose] public section

open Filter Asymptotics Topology

namespace ComputeAsymptotics

namespace MultiseriesExpansion

open LazySeries Stream' Seq

/-- Series defining the logarithm function:
```
log (1 + x) = x - x^2/2 + x^3/3 - ...
``` -/
noncomputable def logSeries : LazySeries :=
  ofFn fun n ↦ -(-1 : ℝ)^n / n

theorem logSeries_eq_cons :
    logSeries = Seq.cons 0 (ofFnFrom (fun n ↦ -(-1 : ℝ)^n / n) 1) := by
  simp only [logSeries, ofFn]
  rw [ofFnFrom_eq_cons]
  congr
  norm_num

-- TODO: move
theorem Real.log_hasFPowerSeriesAt : HasFPowerSeriesAt (fun t ↦ Real.log (1 + t))
    (.ofScalars ℝ (fun n ↦ -(-1 : ℝ)^n / n)) 0 := by
  suffices HasFPowerSeriesAt Real.log (.ofScalars ℝ (fun n ↦ -(-1 : ℝ)^n / n)) 1 by
    rw [show (0 : ℝ) = 1 + (-1) by simp]
    conv => arg 1; ext t; rw [show 1 + t = t - (-1) by ring]
    exact HasFPowerSeriesAt.comp_sub this _
  suffices ((FormalMultilinearSeries.ofScalars ℝ (fun n ↦ -(-1 : ℝ)^n / n)) =
      FormalMultilinearSeries.ofScalars ℝ
        (fun n ↦ iteratedDeriv n Real.log 1 / (n.factorial : ℝ))) by
    convert AnalyticAt.hasFPowerSeriesAt _ using 1 <;> try infer_instance
    exact analyticAt_log (by simp)
  ext n
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_eq_mul_left_iff]
  left
  -- clear v
  obtain _ | n := n
  · simp
  rw [Nat.factorial_succ, pow_succ]
  field_simp
  push_cast
  move_mul [((n : ℝ) + 1)]
  simp only [mul_eq_mul_right_iff]
  left
  suffices iteratedDeriv (n + 1) Real.log =
      fun (x : ℝ) ↦ (-1 : ℝ) ^ n * n.factorial * x ^ (-(n : ℤ) - 1) by
    rw [this]
    simp
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp only [Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg]
    rw [iteratedDeriv_succ, ih]
    ext x
    simp only [deriv_const_mul_field', deriv_zpow', Int.cast_sub,
      Int.cast_neg, Int.cast_natCast, Int.cast_one, pow_succ, mul_neg, mul_one, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, neg_mul, Int.reduceNeg]
    ring_nf

theorem logSeries_toFormalMultilinearSeries_eq :
    logSeries.toFormalMultilinearSeries = .ofScalars ℝ (fun n ↦ -(-1 : ℝ)^n / n) := by
  simp only [toFormalMultilinearSeries, FormalMultilinearSeries.ofScalars_series_eq_iff]
  suffices logSeries.coeff = (fun (n : ℕ) ↦ -(-1 : ℝ)^n / n) by
    rw [this]
  ext n
  simp [LazySeries.coeff, logSeries]

theorem logSeries_convergent : logSeries.Convergent := by
  apply convergent_of_HasFPowerSeriesAt
  convert Real.log_hasFPowerSeriesAt
  rw [logSeries_toFormalMultilinearSeries_eq]

theorem logSeries_toFun : logSeries.toFun =ᶠ[𝓝 0] (fun t ↦ Real.log (1 + t)) := by
  apply toFun_of_HasFPowerSeriesAt
  convert Real.log_hasFPowerSeriesAt
  rw [logSeries_toFormalMultilinearSeries_eq]

mutual

/-- `Multiseries`-part of `MultiseriesExpansion.log`. -/
noncomputable def Multiseries.log {basis_hd basis_tl}
    (logBasis : LogBasis (basis_hd :: basis_tl))
    (ms : Multiseries basis_hd basis_tl) :
    Multiseries basis_hd basis_tl :=
  match ms.destruct with
  | none => .nil
  | some (exp, coef, tl) =>
    match basis_tl with
    | [] => (Multiseries.const _ _ (Real.log coef.toReal)) +
        (tl.mulConst coef.toReal⁻¹).powser logSeries -- here exp = 0 by assumption
    | List.cons _ _ =>
      match logBasis with
      | .cons _ _ _ logBasis_tl log_hd =>
        (.cons 0 (log logBasis_tl coef + log_hd.mulConst exp) .nil) +
          (tl.mulMonomial coef.inv (-exp)).powser logSeries

/-- If `ms` approximates `f` and the last exponent of the leading term of `ms` is 0,
then `ms.log logBasis` approximates `Real.log ∘ f`. -/
noncomputable def log {basis : Basis}
    (logBasis : LogBasis basis)
    (ms : MultiseriesExpansion basis) :
    MultiseriesExpansion basis :=
  match basis with
  | [] => Real.log ms
  | List.cons basis_hd basis_tl => mk (Multiseries.log logBasis ms.seq) (Real.log ∘ ms.toFun)

end

@[simp]
theorem log_seq {basis_hd basis_tl} {logBasis : LogBasis (basis_hd :: basis_tl)}
    {ms : MultiseriesExpansion (basis_hd :: basis_tl)} :
    (ms.log logBasis).seq = Multiseries.log logBasis ms.seq := by
  simp [log]

@[simp]
theorem log_toFun {basis_hd basis_tl} {logBasis : LogBasis (basis_hd :: basis_tl)}
    {ms : MultiseriesExpansion (basis_hd :: basis_tl)} :
    (ms.log logBasis).toFun = Real.log ∘ ms.toFun := by
  simp [log]

mutual

theorem Multiseries.log_Sorted {basis_hd basis_tl}
    {logBasis : LogBasis (basis_hd :: basis_tl)}
    {ms : Multiseries basis_hd basis_tl}
    (h_logBasis : logBasis.WellFormed)
    (h_last : ∀ x, ms.exps.getLast? = .some x → x = 0)
    (h_wo : ms.Sorted) :
    (ms.log logBasis).Sorted := by
  cases ms with
  | nil => simp [Multiseries.log]
  | cons exp coef tl =>
  cases basis_tl with
  | nil =>
    have h_exp : exp = 0 := by
      simp at h_last
      simpa [leadingTerm] using h_last
    obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := Sorted_cons h_wo
    simp only [Multiseries.log, Multiseries.destruct_cons]
    apply Multiseries.add_Sorted Multiseries.const_Sorted
    apply Multiseries.powser_Sorted
    · apply Multiseries.mulConst_Sorted h_tl_wo
    · simp only [Multiseries.mulConst_leadingExp]
      generalize tl.leadingExp = x at h_comp
      cases x
      · exact WithBot.bot_lt_coe 0
      · simp only [WithBot.coe_lt_coe] at h_comp
        norm_cast
        linarith
  | cons basis_tl_hd basis_tl_tl =>
    obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := Sorted_cons h_wo
    obtain ⟨_, _, _, _, logBasis_tl, log_hd, h_wo, h_approx⟩ := logBasis
    unfold Multiseries.log
    simp only [Multiseries.destruct_cons]
    apply Multiseries.add_Sorted
    · apply Sorted.cons
      · apply add_Sorted
        · apply log_Sorted (basis := basis_tl_hd :: basis_tl_tl)
            (LogBasis.tail_WellFormed h_logBasis) _ h_coef_wo
          intro x h
          specialize h_last x
          simpa [-exps_eq_Seq_exps, List.getLast?_cons, h] using h_last
        · apply mulConst_Sorted
          exact h_logBasis.left
      · simp
      · exact Multiseries.Sorted.nil
    · apply Multiseries.powser_Sorted
      · apply Multiseries.mulMonomial_Sorted h_tl_wo
        exact inv_Sorted h_coef_wo
      · -- copypaste from above
        simp only [Multiseries.mulMonomial_leadingExp]
        generalize tl.leadingExp = x at h_comp
        cases x
        · exact WithBot.bot_lt_coe 0
        · simp only [WithBot.coe_lt_coe] at h_comp
          norm_cast
          linarith
termination_by 2 *basis_tl.length + 1

theorem log_Sorted {basis : Basis}
    {logBasis : LogBasis basis}
    {ms : MultiseriesExpansion basis}
    (h_logBasis : logBasis.WellFormed)
    (h_last : ∀ x, ms.exps.getLast? = .some x → x = 0)
    (h_wo : ms.Sorted) :
    (ms.log logBasis).Sorted := by
  cases basis with
  | nil => apply Sorted.const
  | cons basis_hd basis_tl =>
    simp only [Sorted_iff_Seq_Sorted, log_seq]
    exact Multiseries.log_Sorted h_logBasis (by simpa [exps] using h_last) (by simpa using h_wo)
termination_by 2 * basis.length
decreasing_by grind

end

theorem log_Approximates {basis : Basis}
    {logBasis : LogBasis basis}
    {ms : MultiseriesExpansion basis}
    (h_basis : WellFormedBasis basis)
    (h_logBasis : logBasis.WellFormed)
    (h_wo : ms.Sorted)
    (h_approx : ms.Approximates)
    (h_trimmed : ms.Trimmed)
    (h_pos : 0 < ms.realCoef)
    (h_last : ∀ x, ms.exps.getLast? = .some x → x = 0) :
    (ms.log logBasis).Approximates := by
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · simp
  cases ms with
  | nil f =>
    simp only [log, mk_seq, Multiseries.log, Multiseries.destruct_nil, mk_toFun,
      Approximates_nil_iff]
    simp at h_approx
    apply h_approx.mono
    intro x hx
    simp at hx ⊢
    grind
  | cons exp coef tl f =>
  obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := Sorted_cons h_wo
  obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := Trimmed_cons h_trimmed
  obtain ⟨h_coef, h_maj, h_tl⟩ := Approximates_cons h_approx
  have h_f_pos : ∀ᶠ t in atTop, 0 < f t :=
    eventually_pos_of_coef_pos h_pos h_wo h_approx h_trimmed h_basis
  cases basis_tl with
  | nil =>
    simp only [log, mk_seq, Multiseries.log, Multiseries.destruct_cons, mk_toFun]
    have h_exp : exp = 0 := by
      simp at h_last
      simpa [leadingTerm] using h_last
    subst h_exp
    simp only [WithBot.coe_zero] at h_comp
    let ms := (MultiseriesExpansion.const [basis_hd] (Real.log coef.toReal)) + (powser logSeries
      (MultiseriesExpansion.mulConst coef.toReal⁻¹ (mk tl (f - basis_hd ^ 0 * coef.toFun))))
    have h : ms.Approximates := by
      simp only [pow_zero, const_toFun, one_mul, ms]
      apply add_Approximates
      · apply const_Approximates h_basis
      · apply powser_Approximates logSeries_convergent h_basis
        · simp [h_comp]
        · apply mulConst_Sorted
          simpa
        apply mulConst_Approximates
        convert h_tl using 4
        simp
    convert replaceFun_Approximates _ h
    · ext g
      simp [ms_eq_ms_iff_mk_eq_mk, ms]
    simp only [pow_zero, const_toFun, one_mul, add_toFun, const_toFun', powser_toFun,
      mulConst_toFun, mk_toFun, ms]
    have h_tendsto_zero : Tendsto (coef.toReal⁻¹ • (f - fun x ↦ coef.toReal)) atTop (𝓝 0) := by
      convert tl_mulMonomial_coef_inv_neg_exp_toFun_tendsto_zero h_basis h_wo h_approx h_trimmed
      ext t
      simp [inv, toReal, ofReal]
      field
    set g := coef.toReal⁻¹ • (f - fun x ↦ coef.toReal)
    apply logSeries_toFun.comp_tendsto at h_tendsto_zero
    grw [h_tendsto_zero]
    apply h_f_pos.mono
    intro t h_f_pos
    simp only [Pi.add_apply, Function.comp_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, g]
    simp at h_pos
    rw [← Real.log_mul (by positivity)]
    · congr
      ring_nf
      field
    · ring_nf
      rw [mul_inv_cancel₀ (by positivity)]
      simp only [sub_self, zero_add, ne_eq, mul_eq_zero, inv_eq_zero, not_or]
      constructor <;> positivity
  | cons basis_tl_hd basis_tl_tl =>
    cases logBasis with | cons _ _ _ logBasis_tl log_hd =>
    obtain ⟨h_log_hd_wo, h_log_hd_approx, h_log_hd_trimmed, h_log_hd_fun, h_logBasis_tl⟩ :=
      h_logBasis
    unfold log
    simp only [mk_seq, Multiseries.log, Multiseries.destruct_cons, mk_toFun]
    let ms := (mk (.cons 0 ((log logBasis_tl coef) + (mulConst exp log_hd)) .nil)
      (Real.log ∘ coef.toFun + exp • log_hd.toFun)) +
      ((mk tl (f - basis_hd ^ exp * coef.toFun)).mulMonomial coef.inv (-exp)).powser logSeries
    have h : ms.Approximates := by
      have h_coef_last : ∀ (x : ℝ), coef.exps.getLast? = some x → x = 0 := by
        simp
        simp [List.getLast?_cons] at h_last
        grind
      simp only [ms]
      apply add_Approximates
      · apply Approximates.cons
        · apply add_Approximates
          · apply log_Approximates h_basis.tail h_logBasis_tl h_coef_wo
              h_coef h_coef_trimmed
            · simpa using h_pos
            · exact h_coef_last
          · apply mulConst_Approximates
            exact h_log_hd_approx
        · apply add_Majorated' _ _ (by rfl) (by rfl)
          · have := log_Approximates (ms := coef) h_basis.tail
              h_logBasis_tl h_coef_wo h_coef h_coef_trimmed h_pos h_coef_last
            rw [← log_toFun (logBasis := logBasis_tl)]
            apply MultiseriesExpansion.Approximates_coef_Majorated_head this h_basis
          · apply smul_Majorated
            rw [h_log_hd_fun]
            simp only [Majorated]
            intro exp' h_exp'
            change (Real.log ∘ basis_hd) =o[atTop] ((fun t ↦ t ^ exp') ∘ basis_hd)
            apply Asymptotics.IsLittleO.comp_tendsto (l := atTop)
            swap
            · apply h_basis.right
              simp
            exact isLittleO_log_rpow_atTop h_exp'
        · simp [h_log_hd_fun]
      · apply powser_Approximates logSeries_convergent h_basis
        · simp only [leadingExp_def, mulMonomial_seq, mk_seq, Multiseries.mulMonomial_leadingExp]
          generalize tl.leadingExp = x at h_comp
          cases x
          · exact WithBot.bot_lt_coe 0
          · simp only [WithBot.coe_lt_coe] at h_comp
            norm_cast
            linarith
        · simp only [Sorted_iff_Seq_Sorted, mulMonomial_seq, mk_seq] at h_tl_wo ⊢
          apply Multiseries.mulMonomial_Sorted h_tl_wo
          apply inv_Sorted h_coef_wo
        apply mulMonomial_Approximates h_basis h_tl
        exact inv_Approximates h_basis.tail h_coef_wo h_coef h_coef_trimmed
    convert replaceFun_Approximates _ h
    · ext g
      simp [ms_eq_ms_iff_mk_eq_mk, ms]
    have h_tendsto_zero := tl_mulMonomial_coef_inv_neg_exp_toFun_tendsto_zero h_basis h_wo h_approx
      h_trimmed
    simp only [mulMonomial_toFun, mk_toFun, inv_toFun, h_log_hd_fun, add_toFun, powser_toFun,
      ms] at h_tendsto_zero ⊢
    set g := (f - basis_hd ^ exp * coef.toFun) * basis_hd ^ (-exp) * coef.toFun⁻¹
    have hg_gt : ∀ᶠ t in atTop, -1/2 ≤ g t := by
      apply Filter.Tendsto.eventually_const_le (by norm_num) h_tendsto_zero
    apply logSeries_toFun.comp_tendsto at h_tendsto_zero
    grw [h_tendsto_zero]
    have h_coef_pos : ∀ᶠ t in atTop, 0 < coef.toFun t :=
      eventually_pos_of_coef_pos (by simpa using h_pos) h_coef_wo h_coef h_coef_trimmed h_basis.tail
    have h_basis_hd_pos : ∀ᶠ t in atTop, 0 < basis_hd t := basis_head_eventually_pos h_basis
    apply (h_f_pos.and (h_coef_pos.and (h_basis_hd_pos.and hg_gt))).mono
    intro t ⟨h_f_pos, h_coef_pos, h_basis_hd_pos, hg_gt⟩
    simp only [Pi.add_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Real.log_rpow (by positivity), ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by linarith)]
    congr
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.inv_apply, g]
    rw [Real.rpow_neg h_basis_hd_pos.le]
    field

end MultiseriesExpansion

end ComputeAsymptotics
