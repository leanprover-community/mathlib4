/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic.Tendsto.Multiseries.Operations.Inv

/-!
# Trigonometric functions

TODO
-/

namespace TendstoTactic.PreMS

open LazySeries Stream' Seq
open scoped Nat

-- cos (x) = 1 - x^2/2! + x^4/4! - x^6/6! + ...
-- sin (x) = x - x^3/3! + x^5/5! - x^7/7! + ...

noncomputable def cosSeries : LazySeries :=
  ofFn fun n ↦ if n % 2 = 0 then (-1 : ℝ) ^ (n / 2) * (n ! : ℝ)⁻¹ else 0

noncomputable def sinSeries : LazySeries :=
  ofFn fun n ↦ if n % 2 = 1 then (-1 : ℝ) ^ ((n - 1) / 2) * (n ! : ℝ)⁻¹ else 0

theorem cosSeries_get {n : ℕ} : cosSeries.get? n =
    some (if n % 2 = 0 then (-1 : ℝ) ^ (n / 2) * (n ! : ℝ)⁻¹ else 0) := by
  simp [cosSeries]

theorem sinSeries_get {n : ℕ} : sinSeries.get? n =
    some (if n % 2 = 1 then (-1 : ℝ) ^ ((n - 1) / 2) * (n ! : ℝ)⁻¹ else 0) := by
  simp [sinSeries]

theorem cosSeries_analytic : cosSeries.analytic := by
  sorry

theorem cosSeries_toFun : cosSeries.toFun = Real.cos := by
  sorry

theorem sinSeries_analytic : sinSeries.analytic := by
  sorry

theorem sinSeries_toFun : sinSeries.toFun = Real.sin := by
  sorry

mutual

noncomputable def cos {basis : Basis} (ms : PreMS basis) : PreMS basis :=
  match basis with
  | [] => Real.cos ms
  | List.cons _ _ =>
    match destruct ms with
    | .none => PreMS.one _
    | .some ((exp, coef), tl) =>
      if exp < 0 then
        cosSeries.apply ms
      else
        PreMS.sub
          ((cosSeries.apply tl).mulMonomial coef.cos 0)
          ((sinSeries.apply tl).mulMonomial coef.sin 0)

noncomputable def sin {basis : Basis} (ms : PreMS basis) : PreMS basis :=
  match basis with
  | [] => Real.sin ms
  | List.cons _ _ =>
    match destruct ms with
    | .none => .nil
    | .some ((exp, coef), tl) =>
      if exp < 0 then
        sinSeries.apply ms
      else
        PreMS.add
          ((cosSeries.apply tl).mulMonomial coef.sin 0)
          ((sinSeries.apply tl).mulMonomial coef.cos 0)

end

mutual

  theorem sin_WellOrdered {basis : Basis} {ms : PreMS basis}
      (h : ms.WellOrdered)
      (h_nonpos : ¬ Term.FirstIsPos ms.leadingTerm.exps) :
      (ms.sin).WellOrdered := by
    cases' basis with basis_hd basis_tl
    · apply WellOrdered.const
    cases' ms with exp coef tl
    · simpa [sin] using WellOrdered.nil
    simp [sin]
    split_ifs with h_if
    · apply apply_WellOrdered h
      simpa
    have h_exp : exp = 0 := by
      unfold leadingTerm at h_nonpos
      simp at h_nonpos
      contrapose! h_nonpos
      constructor
      simp at h_if
      exact lt_of_le_of_ne h_if h_nonpos.symm
    subst h_exp
    clear h_if
    obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h
    apply add_WellOrdered
    · apply mulMonomial_WellOrdered
      · exact apply_WellOrdered h_tl_wo h_comp
      · apply sin_WellOrdered h_coef_wo
        contrapose! h_nonpos
        exact Term.FirstIsPos_of_tail rfl h_nonpos
    · apply mulMonomial_WellOrdered
      · exact apply_WellOrdered h_tl_wo h_comp
      · apply cos_WellOrdered h_coef_wo
        contrapose! h_nonpos
        exact Term.FirstIsPos_of_tail rfl h_nonpos

  theorem cos_WellOrdered {basis : Basis} {ms : PreMS basis}
      (h : ms.WellOrdered)
      (h_nonpos : ¬ Term.FirstIsPos ms.leadingTerm.exps) :
      (ms.cos).WellOrdered := by
    cases' basis with basis_hd basis_tl
    · apply WellOrdered.const
    cases' ms with exp coef tl
    · simpa [cos] using one_WellOrdered
    simp [cos]
    split_ifs with h_if
    · apply apply_WellOrdered h
      simpa
    have h_exp : exp = 0 := by
      unfold leadingTerm at h_nonpos
      simp at h_nonpos
      contrapose! h_nonpos
      constructor
      simp at h_if
      exact lt_of_le_of_ne h_if h_nonpos.symm
    subst h_exp
    clear h_if
    obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h
    apply sub_WellOrdered
    · apply mulMonomial_WellOrdered
      · exact apply_WellOrdered h_tl_wo h_comp
      · apply cos_WellOrdered h_coef_wo
        contrapose! h_nonpos
        exact Term.FirstIsPos_of_tail rfl h_nonpos
    · apply mulMonomial_WellOrdered
      · exact apply_WellOrdered h_tl_wo h_comp
      · apply sin_WellOrdered h_coef_wo
        contrapose! h_nonpos
        exact Term.FirstIsPos_of_tail rfl h_nonpos

end

mutual

  theorem sin_Approximates {f : ℝ → ℝ} {basis : Basis} {ms : PreMS basis}
      (h_basis : WellFormedBasis basis)
      (h_wo : ms.WellOrdered)
      (h_approx : ms.Approximates f)
      (h_nonpos : ¬ Term.FirstIsPos ms.leadingTerm.exps) :
      ms.sin.Approximates (Real.sin ∘ f) := by
    cases' basis with basis_hd basis_tl
    · simp [sin, Approximates] at h_approx ⊢
      apply h_approx.mono
      simp +contextual
    cases' ms with exp coef tl
    · simp [sin]
      apply Approximates_nil at h_approx
      apply Approximates_of_EventuallyEq (f := fun _ ↦ 0)
      · apply h_approx.mono
        simp +contextual
      apply Approximates.nil
      rfl
    simp [sin]
    split_ifs with h_if
    · rw [← sinSeries_toFun]
      exact apply_Approximates sinSeries_analytic h_basis h_wo (by simpa) h_approx
    have h_exp : exp = 0 := by
      unfold leadingTerm at h_nonpos
      simp at h_nonpos
      contrapose! h_nonpos
      constructor
      simp at h_if
      exact lt_of_le_of_ne h_if h_nonpos.symm
    subst h_exp
    clear h_if
    obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
    obtain ⟨fC, h_coef, h_majorated, h_tl⟩ := Approximates_cons h_approx
    simp at h_tl
    convert_to (((cosSeries.apply tl).mulMonomial coef.sin 0).add ((sinSeries.apply tl).mulMonomial coef.cos 0)).Approximates
      (fun t ↦ Real.cos (f t - fC t) * Real.sin (fC t) + Real.sin (f t - fC t) * Real.cos (fC t))
    · ext t
      rw [add_comm, ← Real.sin_add]
      simp
    apply add_Approximates
    · sorry
      -- apply mulMonomial_Approximates h_basis
      -- · rw [← expSeries_toFun]
      --   exact apply_Approximates expSeries_analytic h_basis h_tl_wo h_comp h_tl
      -- apply exp_Approximates h_basis.tail h_coef_wo h_coef
      -- contrapose! h_nonpos
      -- exact Term.FirstIsPos_of_tail rfl h_nonpos
    · sorry

  theorem cos_Approximates {f : ℝ → ℝ} {basis : Basis} {ms : PreMS basis}
      (h_basis : WellFormedBasis basis)
      (h_wo : ms.WellOrdered)
      (h_approx : ms.Approximates f)
      (h_nonpos : ¬ Term.FirstIsPos ms.leadingTerm.exps) :
      ms.cos.Approximates (Real.cos ∘ f) := by
    cases' basis with basis_hd basis_tl
    · simp [cos, Approximates] at h_approx ⊢
      apply h_approx.mono
      simp +contextual
    cases' ms with exp coef tl
    · simp [cos]
      apply Approximates_nil at h_approx
      apply Approximates_of_EventuallyEq (f := fun _ ↦ 1)
      · apply h_approx.mono
        simp +contextual
      exact one_Approximates h_basis
    simp [cos]
    split_ifs with h_if
    · rw [← cosSeries_toFun]
      exact apply_Approximates cosSeries_analytic h_basis h_wo (by simpa) h_approx
    have h_exp : exp = 0 := by
      unfold leadingTerm at h_nonpos
      simp at h_nonpos
      contrapose! h_nonpos
      constructor
      simp at h_if
      exact lt_of_le_of_ne h_if h_nonpos.symm
    subst h_exp
    clear h_if
    obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
    obtain ⟨fC, h_coef, h_majorated, h_tl⟩ := Approximates_cons h_approx
    simp at h_tl
    sorry
    -- convert_to ((sinSeries.apply tl).mulMonomial coef.sin 0).Approximates
    --     (fun t ↦ (Real.exp ∘ fC) t * basis_hd t ^ (0 : ℝ) * (Real.exp ∘ (fun s ↦ f s - fC s)) t)
    -- · ext t
    --   simp [← Real.exp_add]
    -- apply mulMonomial_Approximates h_basis
    -- · rw [← expSeries_toFun]
    --   exact apply_Approximates expSeries_analytic h_basis h_tl_wo h_comp h_tl
    -- apply exp_Approximates h_basis.tail h_coef_wo h_coef
    -- contrapose! h_nonpos
    -- exact Term.FirstIsPos_of_tail rfl h_nonpos

end

end TendstoTactic.PreMS
