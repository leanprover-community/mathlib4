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

set_option linter.flexible false
set_option linter.style.longLine false
set_option linter.style.multiGoal false

@[expose] public section

open Filter Asymptotics Topology

namespace ComputeAsymptotics

namespace PreMS

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

theorem logSeries_analytic : logSeries.Analytic := by
  apply analytic_of_HasFPowerSeriesAt
  convert Real.log_hasFPowerSeriesAt
  rw [logSeries_toFormalMultilinearSeries_eq]

theorem logSeries_toFun : logSeries.toFun =ᶠ[𝓝 0] (fun t ↦ Real.log (1 + t)) := by
  apply toFun_of_HasFPowerSeriesAt
  convert Real.log_hasFPowerSeriesAt
  rw [logSeries_toFormalMultilinearSeries_eq]

mutual

noncomputable def SeqMS.log {basis_hd basis_tl}
    (logBasis : LogBasis (basis_hd :: basis_tl))
    (ms : SeqMS basis_hd basis_tl) :
    SeqMS basis_hd basis_tl :=
  match ms.destruct with
  | none => .nil
  | some (exp, coef, tl) =>
    match basis_tl with
    | [] => (SeqMS.const _ _ (Real.log coef.toReal)) +
        (tl.mulConst coef.toReal⁻¹).apply logSeries -- here exp = 0 by assumption
    | List.cons _ _ =>
      match logBasis with
      | .cons _ _ _ logBasis_tl log_hd =>
        let logC := log logBasis_tl coef
        (.cons 0 (logC + log_hd.mulConst exp) .nil) +
          (tl.mulMonomial coef.inv (-exp)).apply logSeries

/-- If `ms` approximates `f` and the last exponent of the leading term of `ms` is 0,
then `ms.log logBasis` approximates `Real.log ∘ f`. -/
noncomputable def log {basis : Basis}
    (logBasis : LogBasis basis)
    (ms : PreMS basis) :
    PreMS basis :=
  match basis with
  | [] => Real.log ms
  | List.cons basis_hd basis_tl => mk (SeqMS.log logBasis ms.seq) (Real.log ∘ ms.toFun)

end

@[simp]
theorem log_seq {basis_hd basis_tl} {logBasis : LogBasis (basis_hd :: basis_tl)}
    {ms : PreMS (basis_hd :: basis_tl)} :
    (ms.log logBasis).seq = SeqMS.log logBasis ms.seq := by
  simp [log]

@[simp]
theorem log_toFun {basis_hd basis_tl} {logBasis : LogBasis (basis_hd :: basis_tl)}
    {ms : PreMS (basis_hd :: basis_tl)} :
    (ms.log logBasis).toFun = Real.log ∘ ms.toFun := by
  simp [log]

mutual

theorem SeqMS.log_WellOrdered {basis_hd basis_tl}
    {logBasis : LogBasis (basis_hd :: basis_tl)}
    {ms : SeqMS basis_hd basis_tl}
    (h_logBasis : logBasis.WellFormed)
    (h_last : ∀ x, ms.exps.getLast? = .some x → x = 0)
    (h_wo : ms.WellOrdered) :
    (ms.log logBasis).WellOrdered := by
  cases ms with
  | nil => simp [SeqMS.log]
  | cons exp coef tl =>
  cases basis_tl with
  | nil =>
    have h_exp : exp = 0 := by
      simp at h_last
      simpa [leadingTerm] using h_last
    obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
    simp [SeqMS.log, SeqMS.destruct_cons]
    apply SeqMS.add_WellOrdered SeqMS.const_WellOrdered
    apply SeqMS.apply_WellOrdered
    · apply SeqMS.mulConst_WellOrdered h_tl_wo
    · simp only [SeqMS.mulConst_leadingExp]
      generalize tl.leadingExp = x at h_comp
      cases x
      · exact WithBot.bot_lt_coe 0
      · simp only [WithBot.coe_lt_coe] at h_comp
        norm_cast
        linarith
  | cons basis_tl_hd basis_tl_tl =>
    obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
    obtain ⟨_, _, _, _, logBasis_tl, log_hd, h_wo, h_approx⟩ := logBasis
    unfold SeqMS.log
    simp only [SeqMS.destruct_cons]
    apply SeqMS.add_WellOrdered
    · apply WellOrdered.cons
      · apply add_WellOrdered
        · apply log_WellOrdered (basis := basis_tl_hd :: basis_tl_tl) (LogBasis.tail_WellFormed h_logBasis) _ h_coef_wo
          intro x h
          specialize h_last x
          simpa [-exps_eq_Seq_exps, List.getLast?_cons, h] using h_last
        · apply mulConst_WellOrdered
          exact h_logBasis.left
      · simp
      · exact SeqMS.WellOrdered.nil
    · apply SeqMS.apply_WellOrdered
      · apply SeqMS.mulMonomial_WellOrdered h_tl_wo
        exact inv_WellOrdered h_coef_wo
      · -- copypaste from above
        simp only [SeqMS.mulMonomial_leadingExp]
        generalize tl.leadingExp = x at h_comp
        cases x
        · exact WithBot.bot_lt_coe 0
        · simp only [WithBot.coe_lt_coe] at h_comp
          norm_cast
          linarith
termination_by 2 *basis_tl.length + 1

theorem log_WellOrdered {basis : Basis}
    {logBasis : LogBasis basis}
    {ms : PreMS basis}
    (h_logBasis : logBasis.WellFormed)
    (h_last : ∀ x, ms.exps.getLast? = .some x → x = 0)
    (h_wo : ms.WellOrdered) :
    (ms.log logBasis).WellOrdered := by
  cases basis with
  | nil => apply WellOrdered.const
  | cons basis_hd basis_tl =>
    simp
    exact SeqMS.log_WellOrdered h_logBasis (by simpa [exps] using h_last) (by simpa using h_wo)
termination_by 2 * basis.length
decreasing_by grind

end

theorem log_Approximates {basis : Basis}
    {logBasis : LogBasis basis}
    {ms : PreMS basis}
    (h_basis : WellFormedBasis basis)
    (h_logBasis : logBasis.WellFormed)
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates)
    (h_trimmed : ms.Trimmed)
    (h_pos : 0 < ms.realCoef)
    (h_last : ∀ x, ms.exps.getLast? = .some x → x = 0) :
    (ms.log logBasis).Approximates := by
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · simp
  cases ms with
  | nil f =>
    simp [log, SeqMS.log]
    simp at h_approx
    apply h_approx.mono
    intro x hx
    simp at hx ⊢
    grind
  | cons exp coef tl f =>
  obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
  obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := Trimmed_cons h_trimmed
  obtain ⟨h_coef, h_maj, h_tl⟩ := Approximates_cons h_approx
  have h_f_pos : ∀ᶠ t in atTop, 0 < f t :=
    eventually_pos_of_coef_pos h_pos h_wo h_approx h_trimmed h_basis
  cases basis_tl with
  | nil =>
    simp [log, SeqMS.log, SeqMS.destruct_cons]
    have h_exp : exp = 0 := by
      simp at h_last
      simpa [leadingTerm] using h_last
    subst h_exp
    simp at h_comp
    let ms := (PreMS.const [basis_hd] (Real.log coef.toReal)) + (PreMS.apply logSeries
      (PreMS.mulConst coef.toReal⁻¹ (mk tl (f - basis_hd ^ 0 * coef.toFun))))
    have h : ms.Approximates := by
      simp [ms]
      apply add_Approximates
      · apply const_Approximates h_basis
      · apply apply_Approximates logSeries_analytic h_basis
        · simp [h_comp]
        · apply mulConst_WellOrdered
          simpa
        apply mulConst_Approximates
        convert h_tl using 4
        simp
    convert replaceFun_Approximates _ h
    · ext g
      simp [ms_eq_ms_iff_mk_eq_mk, ms]
    simp [ms]
    have h_tendsto_zero : Tendsto (coef.toReal⁻¹ • (f - fun x ↦ coef.toReal)) atTop (𝓝 0) := by
      convert tl_mulMonomial_coef_inv_neg_exp_toFun_tendsto_zero h_basis h_wo h_approx h_trimmed
      ext t
      simp [inv, toReal]
      field
    set g := coef.toReal⁻¹ • (f - fun x ↦ coef.toReal)
    apply logSeries_toFun.comp_tendsto at h_tendsto_zero
    grw [h_tendsto_zero]
    apply h_f_pos.mono
    intro t h_f_pos
    simp [g]
    simp at h_pos
    rw [← Real.log_mul (by positivity)]
    · congr
      ring_nf
      field
    · ring_nf
      rw [mul_inv_cancel₀ (by positivity)]
      simp
      constructor <;> positivity
  | cons basis_tl_hd basis_tl_tl =>
    cases logBasis with | cons _ _ _ logBasis_tl log_hd =>
    obtain ⟨h_log_hd_wo, h_log_hd_approx, h_log_hd_trimmed, h_log_hd_fun, h_logBasis_tl⟩ := h_logBasis
    unfold log
    simp [SeqMS.log]
    let ms := (mk (.cons 0 ((log logBasis_tl coef) + (mulConst exp log_hd)) .nil) (Real.log ∘ coef.toFun + exp • log_hd.toFun)) +
      ((mk tl (f - basis_hd ^ exp * coef.toFun)).mulMonomial coef.inv (-exp)).apply logSeries
    have h : ms.Approximates := by
      have h_coef_last : ∀ (x : ℝ), coef.exps.getLast? = some x → x = 0 := by
        simp
        simp [List.getLast?_cons] at h_last
        grind
      simp [ms]
      apply add_Approximates
      · apply Approximates.cons
        · apply add_Approximates
          apply log_Approximates h_basis.tail h_logBasis_tl h_coef_wo
            h_coef h_coef_trimmed
          · simpa using h_pos
          · exact h_coef_last
          · apply mulConst_Approximates
            exact h_log_hd_approx
        · apply add_majorated' _ _ (by rfl) (by rfl)
          · have := log_Approximates (ms := coef) h_basis.tail
              h_logBasis_tl h_coef_wo h_coef h_coef_trimmed h_pos h_coef_last
            rw [← log_toFun (logBasis := logBasis_tl)]
            apply PreMS.Approximates_coef_majorated_head this h_basis
          · apply smul_majorated
            rw [h_log_hd_fun]
            simp only [majorated]
            intro exp' h_exp'
            change (Real.log ∘ basis_hd) =o[atTop] ((fun t ↦ t ^ exp') ∘ basis_hd)
            apply Asymptotics.IsLittleO.comp_tendsto (l := atTop)
            swap
            · apply h_basis.right
              simp
            exact isLittleO_log_rpow_atTop h_exp'
        · simp [h_log_hd_fun]
      · apply apply_Approximates logSeries_analytic h_basis
        · simp
          generalize tl.leadingExp = x at h_comp
          cases x
          · exact WithBot.bot_lt_coe 0
          · simp only [WithBot.coe_lt_coe] at h_comp
            norm_cast
            linarith
        · simp at h_tl_wo ⊢
          apply SeqMS.mulMonomial_WellOrdered h_tl_wo
          apply inv_WellOrdered h_coef_wo
        apply mulMonomial_Approximates h_basis h_tl
        exact inv_Approximates h_basis.tail h_coef_wo h_coef h_coef_trimmed
    convert replaceFun_Approximates _ h
    · ext g
      simp [ms_eq_ms_iff_mk_eq_mk, ms]
    have h_tendsto_zero := tl_mulMonomial_coef_inv_neg_exp_toFun_tendsto_zero h_basis h_wo h_approx h_trimmed
    simp [ms, h_log_hd_fun] at h_tendsto_zero ⊢
    set g := (f - basis_hd ^ exp * coef.toFun) * basis_hd ^ (-exp) * coef.toFun⁻¹
    have hg_gt : ∀ᶠ t in atTop, -1/2 ≤ g t := by
      apply Filter.Tendsto.eventually_const_le (by norm_num) h_tendsto_zero
    apply logSeries_toFun.comp_tendsto at h_tendsto_zero
    grw [h_tendsto_zero]
    have h_coef_pos : ∀ᶠ t in atTop, 0 < coef.toFun t := by
      apply eventually_pos_of_coef_pos (by simpa using h_pos) h_coef_wo h_coef h_coef_trimmed h_basis.tail
    have h_basis_hd_pos : ∀ᶠ t in atTop, 0 < basis_hd t := basis_head_eventually_pos h_basis
    apply (h_f_pos.and (h_coef_pos.and (h_basis_hd_pos.and hg_gt))).mono
    intro t ⟨h_f_pos, h_coef_pos, h_basis_hd_pos, hg_gt⟩
    simp
    rw [← Real.log_rpow (by positivity), ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by linarith)]
    congr
    simp [g]
    rw [Real.rpow_neg h_basis_hd_pos.le]
    field


    -- apply Approximates_of_EventuallyEq
    --     (f := fun t ↦ (Real.log (fC t) + Real.log (basis_hd t) * exp) +
    --       Real.log (1 + basis_hd t ^ (-exp) * (fC t)⁻¹ * (f t - (basis_hd t) ^ exp * fC t)))
    -- · apply Eventually.mono (h_f_pos.and (h_fC_pos.and (h_basis_hd_pos)))
    --   intro x ⟨h_f, h_fC, h_basis_hd⟩
    --   simp only [Function.comp_apply]
    --   rw [mul_comm, ← Real.log_rpow, ← Real.log_mul, ← Real.log_mul]
    --   rotate_left
    --   · positivity
    --   · rw [mul_sub]
    --     ring_nf
    --     move_mul [← basis_hd x ^ exp]
    --     rw [← Real.rpow_add h_basis_hd]
    --     simp only [add_neg_cancel, Real.rpow_zero, one_mul, ne_eq]
    --     rw [mul_inv_cancel₀ h_fC.ne']
    --     simp only [sub_self, zero_add, mul_eq_zero, inv_eq_zero, not_or]
    --     constructorm* _ ∧ _ <;> positivity
    --   · positivity
    --   · positivity
    --   · assumption
    --   congr
    --   rw [mul_add]
    --   move_mul [← (fC x)⁻¹]
    --   simp only [mul_one, inv_mul_cancel₀ h_fC.ne', one_mul, ← Real.rpow_add h_basis_hd,
    --     add_neg_cancel, Real.rpow_zero]
    --   ring
    -- apply add_Approximates
    -- · apply Approximates.cons (fC := fun t ↦ Real.log (fC t) + Real.log (basis_hd t) * exp)
    --   · apply add_Approximates
    --     · apply log_Approximates h_basis.tail (LogBasis.tail_WellFormed h_logBasis) h_coef_wo
    --         h_coef h_coef_trimmed
    --       · rwa [leadingTerm_cons_coef] at h_pos
    --       intro x h
    --       specialize h_last x
    --       unfold leadingTerm at h_last
    --       simp only [head_cons] at h_last
    --       simpa [List.getLast?_cons, h] using h_last
    --     · apply mulConst_Approximates'
    --       simp only [LogBasis.WellFormed] at h_logBasis
    --       exact h_logBasis.right.left
    --   · rw [show (0 : ℝ) = 0 ⊔ 0 by simp]
    --     apply add_majorated
    --     · unfold leadingTerm at h_pos h_last
    --       simp only [head_cons] at h_pos h_last
    --       replace h_last : ∀ (x : ℝ), coef.leadingTerm.exps.getLast? = some x → x = 0 := by
    --         intro x h
    --         apply h_last
    --         rw [← h]
    --         simp only [List.getLast?_cons]
    --         apply Option.eq_of_mem_of_mem (by simp [h]) h
    --       have := log_Approximates (ms := coef) (f := fC) h_basis.tail
    --         (LogBasis.tail_WellFormed h_logBasis) h_coef_wo h_coef h_coef_trimmed h_pos
    --         h_last
    --       exact PreMS.Approximates_coef_majorated_head this h_basis
    --     · apply mul_const_majorated
    --       simp only [majorated]
    --       intro exp' h_exp'
    --       change (Real.log ∘ basis_hd) =o[atTop] ((fun t ↦ t ^ exp') ∘ basis_hd)
    --       apply Asymptotics.IsLittleO.comp_tendsto (l := atTop)
    --       swap
    --       · apply h_basis.right
    --         simp
    --       exact isLittleO_log_rpow_atTop h_exp'
    --   · apply Approximates.nil
    --     simp only [Real.rpow_zero, one_mul, sub_self]
    --     rfl
    -- · have h_tendsto_zero : Tendsto (fun t ↦ (f t - basis_hd t ^ exp * fC t) * basis_hd t ^ (-exp) *
    --       (fC t)⁻¹) atTop (𝓝 0) := by
    --     apply Tendsto.congr' (f₁ := fun t ↦ fC⁻¹ t * basis_hd t ^ (-exp) * f t - 1)
    --     · apply Eventually.mono (h_fC_pos.and h_basis_hd_pos)
    --       intro t ⟨h_fC, h_basis_hd⟩
    --       simp only [Pi.inv_apply]
    --       ring_nf
    --       simp [mul_inv_cancel₀ h_fC.ne', ← Real.rpow_add h_basis_hd]
    --     rw [show (0 : ℝ) = 1 - 1 by simp]
    --     apply Tendsto.sub_const
    --     apply Tendsto.congr' (f₁ := f / (fun k ↦ fC k * basis_hd k ^ (exp)))
    --     · simp only [EventuallyEq]
    --       apply h_basis_hd_pos.mono
    --       intro t h_basis_hd_pos
    --       simp only [Pi.div_apply, Pi.inv_apply, Real.rpow_neg h_basis_hd_pos.le]
    --       ring
    --     rw [← isEquivalent_iff_tendsto_one]
    --     conv_rhs => ext t; rw [mul_comm]
    --     apply IsEquivalent_coef h_coef h_coef_wo h_coef_trimmed h_coef_ne_zero h_tl h_comp h_basis
    --     apply (h_fC_pos.and h_basis_hd_pos).mono
    --     intro t ⟨h_fC_pos, h_basis_hd_pos⟩
    --     simp only [ne_eq, mul_eq_zero, not_or]
    --     constructor
    --     · exact h_fC_pos.ne'
    --     · rw [Real.rpow_eq_zero_iff_of_nonneg]
    --       · push_neg
    --         intro h
    --         simp [h] at h_basis_hd_pos
    --       · exact h_basis_hd_pos.le
    --   apply Approximates_of_EventuallyEq
    --     (f := logSeries.toFun ∘ fun t ↦ (f t - basis_hd t ^ exp * fC t) * basis_hd t ^ (-exp) *
    --       (fC t)⁻¹)
    --   · apply Eventually.mono (Filter.EventuallyEq.comp_tendsto logSeries_toFun h_tendsto_zero)
    --     intro t ht
    --     simp at ht
    --     simp [ht]
    --     field_simp
    --   apply apply_Approximates logSeries_analytic h_basis
    --   · simp only [mulMonomial_leadingExp]
    --     generalize tl.leadingExp = x at h_comp
    --     cases x
    --     · exact WithBot.bot_lt_coe 0
    --     · simp only [WithBot.coe_lt_coe] at h_comp
    --       norm_cast
    --       linarith
    --   · apply mulMonomial_WellOrdered h_tl_wo
    --     apply inv_WellOrdered h_coef_wo
    --   apply mulMonomial_Approximates h_basis h_tl
    --   exact inv_Approximates h_basis.tail h_coef_wo h_coef h_coef_trimmed

end PreMS

end ComputeAsymptotics
