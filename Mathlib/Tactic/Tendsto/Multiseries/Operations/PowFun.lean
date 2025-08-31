import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Tendsto.Multiseries.LeadingTerm

namespace TendstoTactic.PreMS

open Filter

theorem exp_Approximates_pow_of_pos
    {basis1 basis2 : Basis} {ms1 : PreMS basis1} {ms2 : PreMS basis2}
    {f g : ℝ → ℝ}
    (h_basis1 : WellFormedBasis basis1)
    (h_wo1 : ms1.WellOrdered) (h_approx1 : ms1.Approximates f) (h_trimmed1 : ms1.Trimmed)
    (h_pos1: 0 < ms1.leadingTerm.coef)
    (h_approx2 : ms2.Approximates (Real.exp ∘ ((Real.log ∘ f) * g))) :
    ms2.Approximates (fun x ↦ (f x) ^ (g x)) := by
  apply Approximates_of_EventuallyEq _ h_approx2
  have hf_pos : ∀ᶠ t in atTop, 0 < f t :=
    eventually_pos_of_coef_pos h_pos1 h_wo1 h_approx1 h_trimmed1 h_basis1
  apply hf_pos.mono
  intro x hx
  simp [Real.rpow_def_of_pos hx]

end TendstoTactic.PreMS
