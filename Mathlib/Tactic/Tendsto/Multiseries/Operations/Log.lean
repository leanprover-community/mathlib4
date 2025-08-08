/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.Tendsto.Multiseries.Operations.Inv
import Mathlib.Tactic.Tendsto.Multiseries.Trimming
import Mathlib.Tactic.Tendsto.Multiseries.LeadingTerm
import Mathlib.Tactic.Tendsto.Multiseries.LogBasis

/-!
# Logarithm of Multiseries

-/

set_option linter.style.longLine false

open Filter Asymptotics Topology

namespace TendstoTactic

namespace PreMS

open LazySeries Stream' Seq

-- log (1 + x) = x - x^2/2 + x^3/3 - ...

noncomputable def logSeriesFrom (n : ℕ) : LazySeries :=
  let g : ℕ → Option (ℝ × ℕ) := fun n =>
    some (-(-1)^n / n, n + 1)
  Seq.corec g n

noncomputable def logSeries : LazySeries :=
  Seq.cons 0 (logSeriesFrom 1)

-- example : logSeries.get? 0 = .some 0 := by simp [logSeries]
-- example : logSeries.get? 1 = .some 1 := by
--   simp [logSeries]
--   rw [Seq.corec_cons (by rfl)]
--   simp
-- example : logSeries.get? 2 = .some (-1/2) := by
--   simp [logSeries]
--   rw [Seq.corec_cons (by rfl), Seq.corec_cons (by rfl)]
--   simp
-- example : logSeries.get? 3 = .some (1/3) := by
--   simp [logSeries]
--   rw [Seq.corec_cons (by rfl), Seq.corec_cons (by rfl), Seq.corec_cons (by rfl)]
--   simp
--   norm_num

theorem logSeriesFrom_eq_cons {n : ℕ} :
    logSeriesFrom n = Seq.cons (-(-1 : ℝ)^n/n) (logSeriesFrom (n + 1)) := by
  unfold logSeriesFrom
  nth_rw 1 [corec_cons]
  rfl

-- example : Real.log 0 = 0 := by exact?

-- log (C b^e + F) = log C + e log b + log(1 + C^-1 b^-e F)

noncomputable def log {basis : Basis}
    (logBasis : LogBasis basis)
    (ms : PreMS basis)
    :
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
        | .cons _ _ _ _ log_hd _ _ =>
          PreMS.add ((.cons (0, logC.add <| log_hd.mulConst exp) .nil)) <|
            logSeries.apply (mulMonomial tl coef.inv (-exp))

theorem logSeries_analytic : logSeries.analytic := by
  sorry

theorem logSeries_toFun : logSeries.toFun = (fun t ↦ Real.log (1 + t)) := by
  sorry

theorem log_WellOrdered {basis : Basis}
    (logBasis : LogBasis basis)
    (ms : PreMS basis)
    (h_last : ∀ x, ms.leadingTerm.exps.getLast? = .some x → x = 0)
    (h_wo : ms.WellOrdered)
    :
    (ms.log logBasis).WellOrdered := by
  sorry
  -- cases' basis with basis_hd basis_tl
  -- · apply WellOrdered.const
  -- cases basis_tl with
  -- | nil =>
  --   cases' ms with exp coef tl
  --   · simpa [log]
  --   have h_exp : exp = 0 := by
  --     simpa [leadingTerm] using h_last
  --   obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
  --   simp [log]
  --   apply add_WellOrdered const_WellOrdered
  --   apply apply_WellOrdered
  --   · apply mulConst_WellOrdered h_tl_wo
  --   · simp
  --     generalize tl.leadingExp = x at h_comp
  --     cases x
  --     · exact WithBot.bot_lt_coe 0
  --     · simp at h_comp
  --       norm_cast
  --       linarith
  -- | cons basis_tl_hd basis_tl_tl =>
  --   cases' ms with exp coef tl
  --   · simpa [log]
  --   obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
  --   cases' logBasis with _ _ _ _ logBasis_tl log_hd h_wo h_approx
  --   simp [log]
  --   apply add_WellOrdered
  --   · apply WellOrdered.cons
  --     · apply add_WellOrdered
  --       · apply log_WellOrdered _ _ _ h_coef_wo
  --         intro x h
  --         specialize h_last x
  --         unfold leadingTerm at h_last
  --         simpa [List.getLast?_cons, h] using h_last
  --       · exact mulConst_WellOrdered h_wo
  --     · simp [leadingExp]
  --       exact WithBot.bot_lt_coe 0
  --     · exact WellOrdered.nil
  --   · apply apply_WellOrdered
  --     · apply mulMonomial_WellOrdered h_tl_wo
  --       exact inv_WellOrdered h_coef_wo
  --     · -- copypaste from above
  --       simp
  --       generalize tl.leadingExp = x at h_comp
  --       cases x
  --       · exact WithBot.bot_lt_coe 0
  --       · simp at h_comp
  --         norm_cast
  --         linarith

theorem log_Approximates {basis : Basis} {f : ℝ → ℝ}
    (logBasis : LogBasis basis)
    (ms : PreMS basis)
    (h_basis : WellFormedBasis basis)
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates f)
    (h_trimmed : ms.Trimmed)
    (h_pos : 0 < ms.leadingTerm.coef)
    (h_last : ∀ x, ms.leadingTerm.exps.getLast? = .some x → x = 0)
    :
    (ms.log logBasis).Approximates (Real.log ∘ f) := by
  sorry
  -- cases' basis with basis_hd basis_tl
  -- · simp [Approximates] at h_approx
  --   apply Approximates_of_EventuallyEq (f := Real.log ∘ (fun _ ↦ ms))
  --   · apply EventuallyEq.fun_comp h_approx.symm
  --   change (log logBasis ms).Approximates (fun x ↦ Real.log ms)
  --   simp [log, Approximates]
  -- cases basis_tl with
  -- | nil =>
  --   cases' ms with exp coef tl
  --   · simp [log]
  --     apply Approximates_nil at h_approx
  --     apply Approximates.nil
  --     trans Real.log ∘ (fun _ ↦ 0)
  --     · apply Filter.EventuallyEq.fun_comp h_approx
  --     apply EventuallyEq.of_eq
  --     ext
  --     simp
  --   · simp [log]
  --     have h_exp : exp = 0 := by
  --       simpa [leadingTerm] using h_last
  --     subst h_exp
  --     obtain ⟨fC, h_coef, h_maj, h_tl⟩ := Approximates_cons h_approx
  --     obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
  --     simp [Approximates] at h_coef
  --     -- f = basis_hd t ^ exp * coef + (f t - basis_hd t ^ exp * coef)
  --     --   = basis_hd t ^ exp * coef * (1 + basis_hd t ^ (-exp) * coef⁻¹ * (f t - basis_hd t ^ exp * coef))
  --     -- log f = log coef + exp * log basis_hd + log (1 + basis_hd t ^ (-exp) * coef⁻¹ * (f t - basis_hd t ^ exp * coef))
  --     -- here exp = 0, so
  --     -- log f = log coef + log (1 + coef⁻¹ * (f t - coef))
  --     apply Approximates_of_EventuallyEq
  --         (f := fun t ↦ Real.log coef + Real.log (1 + (f t - coef) * coef⁻¹))
  --     · calc
  --         _ =ᶠ[atTop] (fun t ↦ Real.log (coef * (1 + (f t - coef) * coef⁻¹))) := by
  --           sorry
  --         _ =ᶠ[atTop] _ := by
  --           sorry
  --     apply add_Approximates
  --     · exact const_Approximates h_basis
  --     apply Approximates_of_EventuallyEq (f := logSeries.toFun ∘ (fun t ↦ (f t - coef) * coef⁻¹))
  --     · sorry
  --     apply apply_Approximates logSeries_analytic h_basis
  --     · exact mulConst_WellOrdered h_tl_wo
  --     · simp
  --       generalize tl.leadingExp = x at h_comp
  --       cases x
  --       · exact WithBot.bot_lt_coe 0
  --       · simp at h_comp
  --         norm_cast
  --     apply mulConst_Approximates
  --     apply Approximates_of_EventuallyEq _ h_tl
  --     sorry
  -- | cons basis_tl_hd basis_tl_tl =>
  --   cases' ms with exp coef tl
  --   · simp [log]
  --     apply Approximates_nil at h_approx
  --     apply Approximates.nil
  --     trans Real.log ∘ (fun _ ↦ 0)
  --     · apply Filter.EventuallyEq.fun_comp h_approx
  --     apply EventuallyEq.of_eq
  --     ext
  --     simp
  --   obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
  --   obtain ⟨h_coef_trimmed, _⟩ := Trimmed_cons h_trimmed
  --   obtain ⟨fC, h_coef, h_maj, h_tl⟩ := Approximates_cons h_approx
  --   cases' logBasis with _ _ _ _ logBasis_tl log_hd h_wo h_log_approx
  --   simp [log]
  --   apply Approximates_of_EventuallyEq (f := fun t ↦ (Real.log (fC t) + Real.log (basis_hd t) * exp) + Real.log (1 + basis_hd t ^ (-exp) * (fC t)⁻¹ * (f t - (basis_hd t) ^ exp * fC t)))
  --   · sorry
  --   apply add_Approximates
  --   · apply Approximates.cons (fC := fun t ↦ Real.log (fC t) + Real.log (basis_hd t) * exp)
  --     · apply add_Approximates
  --       · apply log_Approximates _ _ h_basis.tail h_coef_wo h_coef h_coef_trimmed
  --         · rwa [leadingTerm_cons_coef] at h_pos
  --         intro x h
  --         specialize h_last x
  --         unfold leadingTerm at h_last
  --         simp at h_last
  --         simpa [List.getLast?_cons, h] using h_last
  --       · exact mulConst_Approximates h_log_approx
  --     · sorry
  --       -- apply basis_tail_majorated_head h_basis
  --     · apply Approximates.nil
  --       sorry
  --   · apply Approximates_of_EventuallyEq
  --       (f := logSeries.toFun ∘ (fun t ↦ (fC t)⁻¹ * basis_hd t ^ (-exp) * (f t - basis_hd t ^ exp * fC t)))
  --     · sorry
  --     apply apply_Approximates logSeries_analytic h_basis
  --     · apply mulMonomial_WellOrdered h_tl_wo
  --       exact inv_WellOrdered h_coef_wo
  --     · simp
  --       generalize tl.leadingExp = x at h_comp
  --       cases x
  --       · exact WithBot.bot_lt_coe 0
  --       · simp at h_comp
  --         norm_cast
  --         linarith
  --     apply mulMonomial_Approximates h_basis h_tl
  --     exact inv_Approximates h_basis.tail h_coef_wo h_coef h_coef_trimmed

end PreMS

end TendstoTactic
