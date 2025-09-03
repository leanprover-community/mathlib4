/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic.Tendsto.Multiseries.Operations.Inv
import Mathlib.Tactic.Tendsto.Multiseries.LogBasis

/-!
# Logarithm of Multiseries

-/

open Filter Asymptotics Topology

namespace TendstoTactic

namespace PreMS

open LazySeries Stream' Seq

-- log (1 + x) = x - x^2/2 + x^3/3 - ...

noncomputable def logSeries : LazySeries :=
  ofFn fun n ↦ -(-1 : ℝ)^n / n

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
  ext n v
  simp
  left
  clear v
  cases' n with n
  · simp
  rw [Nat.factorial_succ, pow_succ]
  field_simp
  move_mul [((n : ℝ) + 1)]
  simp
  left
  suffices iteratedDeriv (n + 1) Real.log =
      fun (x : ℝ) ↦ (-1 : ℝ) ^ n * n.factorial * x ^ (-(n : ℤ) - 1) by
    rw [this]
    simp
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp
    rw [iteratedDeriv_succ, ih]
    ext x
    simp [Nat.factorial_succ, pow_succ]
    ring_nf

theorem logSeries_toFormalMultilinearSeries_eq :
    logSeries.toFormalMultilinearSeries = .ofScalars ℝ (fun n ↦ -(-1 : ℝ)^n / n) := by
  simp [toFormalMultilinearSeries]
  suffices logSeries.coeff = (fun (n : ℕ) ↦ -(-1 : ℝ)^n / n) by
    rw [this]
  ext n
  simp [LazySeries.coeff, logSeries]

theorem logSeries_analytic : logSeries.analytic := by
  apply analytic_of_HasFPowerSeriesAt
  convert Real.log_hasFPowerSeriesAt
  rw [logSeries_toFormalMultilinearSeries_eq]

theorem logSeries_toFun : logSeries.toFun =ᶠ[𝓝 0] (fun t ↦ Real.log (1 + t)) := by
  apply toFun_of_HasFPowerSeriesAt
  convert Real.log_hasFPowerSeriesAt
  rw [logSeries_toFormalMultilinearSeries_eq]

-- log (C b^e + F) = log C + e log b + log(1 + C^-1 b^-e F)
-- here we assume that the last exponent is 0
noncomputable def log {basis : Basis}
    (logBasis : LogBasis basis)
    (ms : PreMS basis) :
    PreMS basis :=
  match basis with
  | [] => Real.log ms
  | List.cons _ basis_tl =>
    match destruct ms with
    | none => .nil
    | some ((exp, coef), tl) =>
      match basis_tl with
      | [] => PreMS.add (PreMS.const _ (Real.log coef)) <|
          logSeries.apply (PreMS.mulConst tl coef⁻¹) -- here exp = 0 by assumption
      | List.cons _ _ =>
        let logC := log logBasis.tail coef
        match logBasis with
        | .cons _ _ _ _ log_hd =>
          PreMS.add ((.cons (0, logC.add <| log_hd.mulConst exp) .nil)) <|
            logSeries.apply (mulMonomial tl coef.inv (-exp))

theorem log_WellOrdered {basis : Basis}
    {logBasis : LogBasis basis}
    {ms : PreMS basis}
    (h_logBasis : logBasis.WellFormed)
    (h_last : ∀ x, ms.leadingTerm.exps.getLast? = .some x → x = 0)
    (h_wo : ms.WellOrdered)
    :
    (ms.log logBasis).WellOrdered := by
  cases' basis with basis_hd basis_tl
  · apply WellOrdered.const
  cases basis_tl with
  | nil =>
    cases' ms with exp coef tl
    · simpa [log]
    have h_exp : exp = 0 := by
      simpa [leadingTerm] using h_last
    obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
    simp [log]
    apply add_WellOrdered const_WellOrdered
    apply apply_WellOrdered
    · apply mulConst_WellOrdered h_tl_wo
    · simp
      generalize tl.leadingExp = x at h_comp
      cases x
      · exact WithBot.bot_lt_coe 0
      · simp at h_comp
        norm_cast
        linarith
  | cons basis_tl_hd basis_tl_tl =>
    cases' ms with exp coef tl
    · simpa [log]
    obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
    cases' logBasis with _ _ _ _ logBasis_tl log_hd h_wo h_approx
    unfold log
    simp
    apply add_WellOrdered
    · apply WellOrdered.cons
      · apply add_WellOrdered
        · apply log_WellOrdered (LogBasis.tail_WellFormed h_logBasis) _ h_coef_wo
          intro x h
          specialize h_last x
          unfold leadingTerm at h_last
          simpa [List.getLast?_cons, h] using h_last
        · apply mulConst_WellOrdered
          exact h_logBasis.left
      · simp [leadingExp]
        exact WithBot.bot_lt_coe 0
      · exact WellOrdered.nil
    · apply apply_WellOrdered
      · apply mulMonomial_WellOrdered h_tl_wo
        exact inv_WellOrdered h_coef_wo
      · -- copypaste from above
        simp
        generalize tl.leadingExp = x at h_comp
        cases x
        · exact WithBot.bot_lt_coe 0
        · simp at h_comp
          norm_cast
          linarith

theorem log_Approximates {basis : Basis} {f : ℝ → ℝ}
    {logBasis : LogBasis basis}
    {ms : PreMS basis}
    (h_basis : WellFormedBasis basis)
    (h_logBasis : logBasis.WellFormed)
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates f)
    (h_trimmed : ms.Trimmed)
    (h_pos : 0 < ms.leadingTerm.coef)
    (h_last : ∀ x, ms.leadingTerm.exps.getLast? = .some x → x = 0)
    :
    (ms.log logBasis).Approximates (Real.log ∘ f) := by
  cases' basis with basis_hd basis_tl
  · simp [Approximates] at h_approx
    apply Approximates_of_EventuallyEq (f := Real.log ∘ (fun _ ↦ ms))
    · apply EventuallyEq.fun_comp h_approx.symm
    change (log logBasis ms).Approximates (fun x ↦ Real.log ms)
    simp [log, Approximates]
  cases basis_tl with
  | nil =>
    cases' ms with exp coef tl
    · simp [log]
      apply Approximates_nil at h_approx
      apply Approximates.nil
      trans Real.log ∘ (fun _ ↦ 0)
      · apply Filter.EventuallyEq.fun_comp h_approx
      apply EventuallyEq.of_eq
      ext
      simp
    · simp [log]
      have h_exp : exp = 0 := by
        simpa [leadingTerm] using h_last
      subst h_exp
      obtain ⟨fC, h_coef, h_maj, h_tl⟩ := Approximates_cons h_approx
      obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
      simp [Approximates] at h_coef
      -- f = basis_hd t ^ exp * coef + (f t - basis_hd t ^ exp * coef)
      --   = basis_hd t ^ exp * coef * (1 + basis_hd t ^ (-exp) * coef⁻¹ *
      --                                       (f t - basis_hd t ^ exp * coef))
      -- log f = log coef + exp * log basis_hd + log (1 + basis_hd t ^ (-exp) * coef⁻¹ *
      --                                       (f t - basis_hd t ^ exp * coef))
      -- here exp = 0, so
      -- log f = log coef + log (1 + coef⁻¹ * (f t - coef))
      have h_tendsto_zero : Tendsto (fun t ↦ f t - coef) atTop (𝓝 0) := by
        apply neg_leadingExp_tendsto_zero h_comp
        apply Approximates_of_EventuallyEq _ h_tl
        apply Eventually.mono h_coef
        intro x hx
        simpa using hx
      apply Approximates_of_EventuallyEq
          (f := fun t ↦ Real.log coef + Real.log (1 + (f t - coef) * coef⁻¹))
      · simp [leadingTerm] at h_pos
        rw [NormedAddCommGroup.tendsto_nhds_zero] at h_tendsto_zero
        specialize h_tendsto_zero (coef * 2⁻¹) (by positivity)
        calc
          _ =ᶠ[atTop] (fun t ↦ Real.log (coef * (1 + (f t - coef) * coef⁻¹))) := by
            apply Eventually.mono h_tendsto_zero
            intro x hx
            simp
            rw [Real.log_mul h_pos.ne']
            intro h
            field_simp at h
            simp [h, abs_of_pos h_pos] at hx
            apply one_lt_of_lt_mul_left₀ at hx
            · norm_num at hx
            · exact h_pos.le
          _ = _ := by
            ext x
            simp
            congr
            field_simp
      apply add_Approximates
      · exact const_Approximates h_basis
      apply Approximates_of_EventuallyEq (f := logSeries.toFun ∘ fun t ↦ (f t - coef) * coef⁻¹)
      · have := Filter.EventuallyEq.comp_tendsto logSeries_toFun
          (by simpa using h_tendsto_zero.mul_const coef⁻¹)
        apply Eventually.mono this
        simp
      apply apply_Approximates logSeries_analytic h_basis
      · exact mulConst_WellOrdered h_tl_wo
      · simp
        generalize tl.leadingExp = x at h_comp
        cases x
        · exact WithBot.bot_lt_coe 0
        · simp at h_comp
          norm_cast
      apply mulConst_Approximates'
      apply Approximates_of_EventuallyEq _ h_tl
      simp
      apply Eventually.mono h_coef
      intro x hx
      simpa using hx
  | cons basis_tl_hd basis_tl_tl =>
    cases' ms with exp coef tl
    · simp [log]
      apply Approximates_nil at h_approx
      apply Approximates.nil
      trans Real.log ∘ (fun _ ↦ 0)
      · apply Filter.EventuallyEq.fun_comp h_approx
      apply EventuallyEq.of_eq
      ext
      simp
    obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
    obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := Trimmed_cons h_trimmed
    obtain ⟨fC, h_coef, h_maj, h_tl⟩ := Approximates_cons h_approx
    cases' logBasis with _ _ _ _ logBasis_tl log_hd h_wo h_log_approx
    unfold log
    simp
    have h_f_pos : ∀ᶠ t in atTop, 0 < f t :=
      eventually_pos_of_coef_pos h_pos h_wo h_approx h_trimmed h_basis
    have h_fC_pos : ∀ᶠ t in atTop, 0 < fC t := by
      unfold leadingTerm at h_pos
      simp at h_pos
      apply eventually_pos_of_coef_pos h_pos h_coef_wo h_coef h_coef_trimmed h_basis.tail
    have h_basis_hd_pos : ∀ᶠ t in atTop, 0 < basis_hd t := basis_head_eventually_pos h_basis
    apply Approximates_of_EventuallyEq
        (f := fun t ↦ (Real.log (fC t) + Real.log (basis_hd t) * exp) +
          Real.log (1 + basis_hd t ^ (-exp) * (fC t)⁻¹ * (f t - (basis_hd t) ^ exp * fC t)))
    · apply Eventually.mono (h_f_pos.and (h_fC_pos.and (h_basis_hd_pos)))
      intro x ⟨h_f, h_fC, h_basis_hd⟩
      simp
      rw [mul_comm, ← Real.log_rpow, ← Real.log_mul, ← Real.log_mul]
      rotate_left
      · positivity
      · rw [mul_sub]
        ring_nf
        move_mul [← basis_hd x ^ exp]
        rw [← Real.rpow_add h_basis_hd]
        simp
        rw [mul_inv_cancel₀ h_fC.ne']
        simp
        constructorm* _ ∧ _ <;> positivity
      · positivity
      · positivity
      · assumption
      congr
      rw [mul_add]
      move_mul [← (fC x)⁻¹]
      simp [inv_mul_cancel₀ h_fC.ne', ← Real.rpow_add h_basis_hd]
      ring
    apply add_Approximates
    · apply Approximates.cons (fC := fun t ↦ Real.log (fC t) + Real.log (basis_hd t) * exp)
      · apply add_Approximates
        · apply log_Approximates h_basis.tail (LogBasis.tail_WellFormed h_logBasis) h_coef_wo
            h_coef h_coef_trimmed
          · rwa [leadingTerm_cons_coef] at h_pos
          intro x h
          specialize h_last x
          unfold leadingTerm at h_last
          simp at h_last
          simpa [List.getLast?_cons, h] using h_last
        · apply mulConst_Approximates'
          simp [LogBasis.WellFormed] at h_logBasis
          exact h_logBasis.right.left
      · rw [show (0 : ℝ) = 0 ⊔ 0 by simp]
        apply add_majorated
        · have := PreMS.Approximates_coef_majorated_head h_coef h_basis
          unfold leadingTerm at h_pos h_last
          simp at h_pos h_last
          replace h_last : ∀ (x : ℝ), coef.leadingTerm.exps.getLast? = some x → x = 0 := by
            intro x h
            apply h_last
            rw [← h]
            rw [List.getLast?_eq_getLast _ (leadingTerm_ne_nil),
              List.getLast?_eq_getLast _ (by simp)]
            simp
            rw [List.getLast_cons]
          have := log_Approximates (ms := coef) (f := fC) h_basis.tail
            (LogBasis.tail_WellFormed h_logBasis) h_coef_wo h_coef h_coef_trimmed h_pos
            h_last
          exact PreMS.Approximates_coef_majorated_head this h_basis
        · apply mul_const_majorated
          simp [majorated]
          intro exp' h_exp'
          change (Real.log ∘ basis_hd) =o[atTop] ((fun t ↦ t ^ exp') ∘ basis_hd)
          apply Asymptotics.IsLittleO.comp_tendsto (l := atTop)
          swap
          · apply h_basis.right
            simp
          exact isLittleO_log_rpow_atTop h_exp'
      · apply Approximates.nil
        simp
        rfl
    · have h_tendsto_zero : Tendsto (fun t ↦ (fC t)⁻¹ * basis_hd t ^ (-exp) *
          (f t - basis_hd t ^ exp * fC t)) atTop (𝓝 0) := by
        apply Tendsto.congr' (f₁ := fun t ↦ fC⁻¹ t * basis_hd t ^ (-exp) * f t - 1)
        · apply Eventually.mono (h_fC_pos.and h_basis_hd_pos)
          intro t ⟨h_fC, h_basis_hd⟩
          simp [mul_sub]
          ring_nf
          simp [mul_inv_cancel₀ h_fC.ne', ← Real.rpow_add h_basis_hd]
        rw [show (0 : ℝ) = 1 - 1 by simp]
        apply Tendsto.sub_const
        apply Tendsto.congr' (f₁ := f / (fun k ↦ fC k * basis_hd k ^ (exp)))
        · simp only [EventuallyEq]
          apply h_basis_hd_pos.mono
          intro t h_basis_hd_pos
          simp [Real.rpow_neg h_basis_hd_pos.le]
          ring
        rw [← isEquivalent_iff_tendsto_one]
        conv => rhs; ext t; rw [mul_comm]
        apply IsEquivalent_coef h_coef h_coef_wo h_coef_trimmed h_coef_ne_zero h_tl h_comp h_basis
        apply (h_fC_pos.and h_basis_hd_pos).mono
        intro t ⟨h_fC_pos, h_basis_hd_pos⟩
        simp
        constructor
        · exact h_fC_pos.ne'
        · rw [Real.rpow_eq_zero_iff_of_nonneg]
          · push_neg
            intro h
            simp [h] at h_basis_hd_pos
          · exact h_basis_hd_pos.le
      apply Approximates_of_EventuallyEq
        (f := logSeries.toFun ∘ fun t ↦ (fC t)⁻¹ * basis_hd t ^ (-exp) *
          (f t - basis_hd t ^ exp * fC t))
      · have := Filter.EventuallyEq.comp_tendsto logSeries_toFun h_tendsto_zero
        apply Eventually.mono this
        intro t ht
        simp at ht
        simp [ht]
        congr 3
        ring
      apply apply_Approximates logSeries_analytic h_basis
      · apply mulMonomial_WellOrdered h_tl_wo
        exact inv_WellOrdered h_coef_wo
      · simp
        generalize tl.leadingExp = x at h_comp
        cases x
        · exact WithBot.bot_lt_coe 0
        · simp at h_comp
          norm_cast
          linarith
      apply mulMonomial_Approximates h_basis h_tl
      exact inv_Approximates h_basis.tail h_coef_wo h_coef h_coef_trimmed

end PreMS

end TendstoTactic
