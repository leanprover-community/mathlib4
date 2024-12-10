/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.Tendsto.Multiseries.Operations.Inv

import Mathlib.Tactic.Tendsto.Multiseries.Operations.ForPow
import Mathlib.Tactic.Tendsto.Multiseries.Trimming
import Mathlib.Tactic.Tendsto.Multiseries.LeadingTerm

set_option linter.style.longLine false

/-!
# Powers for multiseries

-/

open Filter Asymptotics

namespace TendstoTactic

namespace PreMS

open LazySeries Stream' Seq
open ForPow

noncomputable def powSeriesFrom (a : ℝ) (acc : ℝ) (n : ℕ) : LazySeries :=
  let g : (ℝ × ℕ) → Option (ℝ × (ℝ × ℕ)) := fun (acc, m) =>
    some (acc, (acc * (a - m) / (m + 1), m + 1))
  Seq.corec g (acc, n)

noncomputable def powSeries (a : ℝ) : LazySeries :=
  powSeriesFrom a 1 0

theorem powSeriesFrom_eq_cons {a : ℝ} {acc : ℝ} {n : ℕ} :
    powSeriesFrom a acc n = Seq.cons acc (powSeriesFrom a (acc * (a - n) / (n + 1)) (n + 1)) := by
  unfold powSeriesFrom
  nth_rw 1 [corec_cons]
  rfl

theorem powSeriesFrom_get {a acc : ℝ} {n m : ℕ} : (powSeriesFrom a acc n).get? m =
    .some (acc * (decreasing_factorial (a - n) m) * n.factorial / (n + m).factorial) := by
  simp [powSeriesFrom]
  induction m generalizing acc n with
  | zero =>
    simp [powSeriesFrom]
    rw [corec_cons]
    pick_goal 2
    · exact Eq.refl _
    simp [decreasing_factorial]
    field_simp
  | succ m ih =>
    rw [corec_cons]
    pick_goal 2
    · exact Eq.refl _
    simp
    rw [ih]
    simp [div_eq_mul_inv]
    move_mul [acc]
    congr 2
    swap
    · congr 3
      ring
    simp [Nat.factorial_succ]
    rw [← mul_assoc]
    congr 1
    move_mul [((n : ℝ) + 1)⁻¹]
    rw [mul_inv_cancel_right₀ (by linarith)]
    symm
    convert decreasing_factorial_sub_one using 3
    ring

theorem powSeries_get {a : ℝ} {n : ℕ} : (powSeries a).get? n = .some (binomialCoef a n) := by
  simp [powSeries, powSeriesFrom_get]
  rfl

theorem powSeries_eq_binomialSeries {a : ℝ} : (powSeries a).toFormalMultilinearSeries = binomialSeries a := by
  ext n f
  simp [binomialSeries, toFormalMultilinearSeries_coeff, powSeries_get]
  rw [mul_comm]
  congr
  exact Eq.symm List.prod_ofFn

theorem powSeries_analytic {a : ℝ} : analytic (powSeries a) := by
  simp [analytic, powSeries_eq_binomialSeries]
  have := @binomialSeries_radius_ge_one a
  apply lt_of_lt_of_le _ this
  simp

theorem powSeries_toFun_eq {t : ℝ} {a : ℝ} (ht : ‖t‖ < 1) : (powSeries a).toFun t = (1 + t)^a := by
  simp [toFun, powSeries_eq_binomialSeries]
  exact binomialSum_eq_rpow ht

noncomputable def pow {basis : Basis} (ms : PreMS basis) (a : ℝ) : PreMS basis :=
  match basis with
  | [] => ms^a
  | List.cons _ _ =>
    match destruct ms with
    | none =>
      if a = 0 then
        one _
      else
        .nil
    | some ((exp, coef), tl) => mulMonomial
      ((powSeries a).apply (mulMonomial tl coef.inv (-exp))) (coef.pow a) (exp * a)

theorem powSeries_zero_eq : powSeries 0 = Seq.cons 1 zeros := by
  simp [powSeries, powSeriesFrom]
  rw [corec_cons]
  pick_goal 2
  · simp
    constructor <;> exact Eq.refl _
  congr 1
  let motive : LazySeries → LazySeries → Prop := fun a b =>
    b = zeros ∧
    ∃ n, a = Seq.corec (fun (p : ℝ × ℕ) ↦ some (p.1, -(p.1 * ↑p.2) / (↑p.2 + 1), p.2 + 1)) (0, n)
  apply Eq.coind motive
  · simp [motive]
    use 1
  · intro a b ih
    simp only [motive] at ih ⊢
    obtain ⟨hb, n, ha⟩ := ih
    subst ha hb
    left
    use 0, ?_, zeros
    constructor
    · rw [corec_cons]
      · exact Eq.refl _
      · rfl
    constructor
    · conv => lhs; rw [zeros_eq_cons]
    constructor
    · rfl
    use n + 1
    simp

theorem pow_WellOrdered {basis : Basis} {ms : PreMS basis} {a : ℝ}
    (h_wo : ms.WellOrdered) : (ms.pow a).WellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    cases' ms with exp coef tl
    · simp [pow]
      split_ifs
      · apply one_WellOrdered
      · apply WellOrdered.nil
    · obtain ⟨h_coef, h_comp, h_tl⟩ := WellOrdered_cons h_wo
      simp [pow]
      apply mulMonomial_WellOrdered
      · apply apply_WellOrdered
        · apply mulMonomial_WellOrdered
          · exact h_tl
          · apply inv_WellOrdered
            exact h_coef
        · simp
          generalize leadingExp tl = w at *
          cases w with
          | bot => simp [Ne.bot_lt']
          | coe => simpa [← WithBot.coe_add] using h_comp
      · apply pow_WellOrdered
        exact h_coef

theorem pow_zero_Approximates {basis : Basis} {F : ℝ → ℝ} {ms : PreMS basis}
    (h_basis : WellFormedBasis basis) (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates F) (h_trimmed : ms.Trimmed)  :
    (ms.pow 0).Approximates 1 := by
  cases basis with
  | nil =>
    unfold pow
    simp only [Approximates] at *
    eta_expand
    simp
  | cons basis_hd basis_tl =>
    cases' ms with exp coef tl
    · apply Approximates_nil at h_approx
      simp [pow]
      exact one_Approximates h_basis
    · apply Trimmed_cons at h_trimmed
      obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := h_trimmed
      obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
      obtain ⟨C, h_coef, _, h_tl⟩ := Approximates_cons h_approx
      simp [pow, powSeries_zero_eq]
      apply Approximates.cons (C := 1)
      · conv => rhs; rw [← mul_one 1]
        apply mul_Approximates (h_basis.tail)
        · exact pow_zero_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed
        · exact one_Approximates (h_basis.tail)
      · apply const_majorated
        apply basis_tendsto_top h_basis
        simp
      · simp
        rw [show (fun t ↦ 0) = fun t ↦ 1 * (basis_hd t)^(0 : ℝ) * 0 by simp]
        apply mulMonomial_Approximates h_basis
        swap
        · exact pow_zero_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed
        conv => arg 2; ext t; rw [← zero_mul (C⁻¹ t * basis_hd t ^ (-exp) * (F t - basis_hd t ^ exp * C t))]
        apply mul_Approximates h_basis
        pick_goal 2
        · apply mulMonomial_Approximates h_basis h_tl
          apply inv_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed
        apply zeros_apply_Approximates h_basis
        · apply mulMonomial_WellOrdered h_tl_wo
          exact inv_WellOrdered h_coef_wo
        · apply mulMonomial_Approximates h_basis h_tl
          apply inv_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed
        simp
        generalize tl.leadingExp = e at h_comp
        cases e
        · simp [Ne.bot_lt]
        · simpa [← WithBot.coe_add] using h_comp

theorem pow_Approximates {basis : Basis} {F : ℝ → ℝ} {ms : PreMS basis} {a : ℝ}
    (h_basis : WellFormedBasis basis) (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates F) (h_trimmed : ms.Trimmed) (h_pos : 0 < ms.leadingTerm.coef) :
    (ms.pow a).Approximates (F^a) := by
  by_cases ha : a = 0
  · rw [ha]
    eta_expand
    simp
    apply pow_zero_Approximates h_basis h_wo h_approx h_trimmed
  cases basis with
  | nil =>
    unfold pow
    simp only [Approximates] at *
    eta_expand
    simp
    apply EventuallyEq.pow_const h_approx
  | cons basis_hd basis_tl =>
    have hF_pos : ∀ᶠ t in atTop, 0 < F t := eventually_pos_of_coef_pos h_pos h_wo h_approx h_trimmed h_basis
    cases' ms with exp coef tl
    · apply Approximates_nil at h_approx
      simp [pow]
      split_ifs
      apply Approximates.nil
      conv =>
        rhs
        ext
        simp
        rw [← Real.zero_rpow ha]
      eta_expand
      simp
      apply EventuallyEq.pow_const h_approx
    · apply Trimmed_cons at h_trimmed
      obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := h_trimmed
      obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
      obtain ⟨C, h_coef, _, h_tl⟩ := Approximates_cons h_approx
      have h_basis_hd_pos : ∀ᶠ t in atTop, 0 < basis_hd t :=
        basis_head_eventually_pos h_basis
      have hC_pos : ∀ᶠ t in atTop, 0 < C t := by
        have hC_equiv : C ~[atTop] F / (fun t ↦ (basis_hd t)^exp) := by
          have hF_equiv := IsEquivalent_coef h_coef h_coef_wo h_coef_trimmed h_coef_ne_zero h_tl h_comp h_basis
          have : C =ᶠ[atTop] (fun t ↦ (basis_hd t)^exp * C t) / (fun t ↦ (basis_hd t)^exp) := by
            simp only [EventuallyEq]
            apply Eventually.mono h_basis_hd_pos
            intro t ht
            simp
            rw [mul_div_cancel_left₀]
            apply ne_of_gt
            apply Real.rpow_pos_of_pos ht
          apply Asymptotics.IsEquivalent.congr_left _ this.symm
          apply IsEquivalent.div hF_equiv.symm
          rfl
        apply eventually_pos_of_IsEquivallent hC_equiv
        apply Eventually.mono <| hF_pos.and h_basis_hd_pos
        intro t ⟨hF_pos, h_basis_hd_pos⟩
        simp
        apply div_pos hF_pos
        apply Real.rpow_pos_of_pos h_basis_hd_pos
      simp [pow]
      apply Approximates_of_EventuallyEq (F := fun t ↦ (C t)^a * (basis_hd t)^(exp * a) *
        (fun t ↦ (C t)^(-a) * (basis_hd t)^(-exp * a) * (F t)^a) t)
      · simp only [EventuallyEq]
        apply Eventually.mono <| hC_pos.and h_basis_hd_pos
        intro t ⟨hC_pos, h_basis_hd_pos⟩
        simp
        ring_nf
        move_mul [←  C t ^ (-a)]
        rw [← Real.rpow_add hC_pos]
        simp [← Real.rpow_add h_basis_hd_pos]
      apply mulMonomial_Approximates h_basis
      swap
      · apply pow_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed
        rwa [leadingTerm_cons_coef] at h_pos
      have : (tl.mulMonomial coef.inv (-exp)).Approximates (fun t ↦ C⁻¹ t *
          (basis_hd t)^(-exp) * (F t - basis_hd t ^ exp * C t))
          (basis := basis_hd :: basis_tl) := by
        apply mulMonomial_Approximates h_basis
        · exact h_tl
        · exact inv_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed
      apply Approximates_of_EventuallyEq
        (F' := (fun t ↦ -1 + C⁻¹ t * basis_hd t ^ (-exp) * F t)) at this
      swap
      · simp only [EventuallyEq]
        apply Eventually.mono <| hC_pos.and h_basis_hd_pos
        intro t ⟨hC_pos, h_basis_hd_pos⟩
        simp
        ring_nf
        simp [mul_inv_cancel₀ hC_pos.ne.symm]
        simp [← Real.rpow_add h_basis_hd_pos]
      apply Approximates_of_EventuallyEq
        (F := (fun t ↦ (1 + t)^a) ∘ (fun t ↦ -1 + C⁻¹ t * basis_hd t ^ (-exp) * F t))
      · simp only [EventuallyEq]
        apply Eventually.mono <| hF_pos.and (hC_pos.and h_basis_hd_pos)
        intro t ⟨hF_pos, hC_pos, h_basis_hd_pos⟩
        simp
        rw [Real.mul_rpow _ hF_pos.le, Real.mul_rpow, Real.inv_rpow hC_pos.le, Real.rpow_neg hC_pos.le, ← Real.rpow_mul h_basis_hd_pos.le, neg_mul]
        · apply inv_nonneg_of_nonneg
          linarith
        · apply Real.rpow_nonneg
          linarith
        · apply mul_nonneg
          · apply inv_nonneg_of_nonneg
            linarith
          · apply Real.rpow_nonneg
            linarith
      apply Approximates_of_EventuallyEq (F := (powSeries a).toFun ∘
          (fun t ↦ -1 + C⁻¹ t * basis_hd t ^ (-exp) * F t))
      · have : Tendsto (fun t ↦ -1 + C⁻¹ t * basis_hd t ^ (-exp) * F t) atTop (nhds 0) := by
          rw [show (0 : ℝ) = -1 + 1 by simp]
          apply Tendsto.const_add
          apply Tendsto.congr' (f₁ := F / (fun k ↦ C k * basis_hd k ^ (exp)))
          · simp only [EventuallyEq]
            apply Eventually.mono <| h_basis_hd_pos
            intro t h_basis_hd_pos
            simp [Real.rpow_neg h_basis_hd_pos.le]
            ring
          rw [← isEquivalent_iff_tendsto_one]
          conv => rhs; ext; rw [mul_comm]
          apply IsEquivalent_coef h_coef h_coef_wo h_coef_trimmed h_coef_ne_zero h_tl h_comp h_basis
          apply Eventually.mono <| hC_pos.and h_basis_hd_pos
          intro t ⟨hC_pos, h_basis_hd_pos⟩
          simp
          constructor
          · exact hC_pos.ne.symm
          · rw [Real.rpow_eq_zero_iff_of_nonneg]
            · push_neg
              intro h
              simp [h] at h_basis_hd_pos
            · exact h_basis_hd_pos.le
        have : ∀ᶠ t in atTop, ‖-1 + C⁻¹ t * basis_hd t ^ (-exp) * F t‖ < 1 := by
          apply NormedAddCommGroup.tendsto_nhds_zero.mp this
          simp
        simp only [EventuallyEq]
        apply Eventually.mono this
        intro t this
        simp
        rw [powSeries_toFun_eq]
        · simp
        · simpa using this
      apply apply_Approximates powSeries_analytic h_basis
      · apply mulMonomial_WellOrdered h_tl_wo
        exact inv_WellOrdered h_coef_wo
      · simp
        generalize leadingExp tl = w at h_comp
        cases w with
        | bot => simp [Ne.bot_lt']
        | coe => simpa [← WithBot.coe_add] using h_comp
      · exact this

-- theorem zpow_Approximates {basis : Basis} {F : ℝ → ℝ} {ms : PreMS basis} {a : ℤ}
--     (h_basis : WellFormedBasis basis) (h_wo : ms.WellOrdered)
--     (h_approx : ms.Approximates F) (h_trimmed : ms.Trimmed) :
--     (ms.pow a).Approximates (F^a) := by
--   by_cases ha : a = 0
--   · rw [ha]
--     eta_expand
--     simp
--     apply pow_zero_Approximates h_basis h_wo h_approx h_trimmed
--   cases basis with
--   | nil =>
--     unfold pow
--     simp only [Approximates] at *
--     eta_expand
--     simp
--     apply EventuallyEq.pow_const h_approx
--   | cons basis_hd basis_tl =>
--     -- have hF_pos : ∀ᶠ t in atTop, 0 < F t := eventually_pos_of_coef_pos h_pos h_wo h_approx h_trimmed h_basis
--     cases' ms with exp coef tl
--     · apply Approximates_nil at h_approx
--       simp [pow]
--       split_ifs
--       apply Approximates.nil
--       conv =>
--         rhs
--         ext
--         simp
--         rw [← zero_zpow _ ha]
--       eta_expand
--       simp
--       apply EventuallyEq.pow_const h_approx
--     · apply Trimmed_cons at h_trimmed
--       obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := h_trimmed
--       obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
--       obtain ⟨C, h_coef, _, h_tl⟩ := Approximates_cons h_approx
--       have h_basis_hd_pos : ∀ᶠ t in atTop, 0 < basis_hd t :=
--         basis_head_eventually_pos h_basis
--       -- have hC_pos : ∀ᶠ t in atTop, 0 < C t := by
--       --   have hC_equiv : C ~[atTop] F / (fun t ↦ (basis_hd t)^exp) := by
--       --     have hF_equiv := IsEquivalent_coef h_coef h_coef_wo h_coef_trimmed h_coef_ne_zero h_tl h_comp h_basis
--       --     have : C =ᶠ[atTop] (fun t ↦ (basis_hd t)^exp * C t) / (fun t ↦ (basis_hd t)^exp) := by
--       --       simp only [EventuallyEq]
--       --       apply Eventually.mono h_basis_hd_pos
--       --       intro t ht
--       --       simp
--       --       rw [mul_div_cancel_left₀]
--       --       apply ne_of_gt
--       --       apply Real.rpow_pos_of_pos ht
--       --     apply Asymptotics.IsEquivalent.congr_left _ this.symm
--       --     apply IsEquivalent.div hF_equiv.symm
--       --     rfl
--       --   apply eventually_pos_of_IsEquivallent hC_equiv
--       --   apply Eventually.mono <| hF_pos.and h_basis_hd_pos
--       --   intro t ⟨hF_pos, h_basis_hd_pos⟩
--       --   simp
--       --   apply div_pos hF_pos
--       --   apply Real.rpow_pos_of_pos h_basis_hd_pos
--       simp [pow]
--       apply Approximates_of_EventuallyEq (F := fun t ↦ (C t)^a * (basis_hd t)^(exp * a) *
--         (fun t ↦ (C t)^(-a) * (basis_hd t)^(-exp * a) * (F t)^a) t)
--       · apply Eq.eventuallyEq
--         ext t
--         simp
--         ring_nf
--         move_mul [← (C t ^ a)⁻¹]
--         rw [inv_mul_cancel₀]
--         swap
--         · sorry
--         focus
--         simp
--         rw [← Real.rpow_add hC_pos]
--         simp [← Real.rpow_add h_basis_hd_pos]
--       apply mulMonomial_Approximates h_basis
--       swap
--       · apply pow_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed
--         rwa [leadingTerm_cons_coef] at h_pos
--       have : (tl.mulMonomial coef.inv (-exp)).Approximates (fun t ↦ C⁻¹ t *
--           (basis_hd t)^(-exp) * (F t - basis_hd t ^ exp * C t))
--           (basis := basis_hd :: basis_tl) := by
--         apply mulMonomial_Approximates h_basis
--         · exact h_tl
--         · exact inv_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed
--       apply Approximates_of_EventuallyEq
--         (F' := (fun t ↦ -1 + C⁻¹ t * basis_hd t ^ (-exp) * F t)) at this
--       swap
--       · simp only [EventuallyEq]
--         apply Eventually.mono <| hC_pos.and h_basis_hd_pos
--         intro t ⟨hC_pos, h_basis_hd_pos⟩
--         simp
--         ring_nf
--         simp [mul_inv_cancel₀ hC_pos.ne.symm]
--         simp [← Real.rpow_add h_basis_hd_pos]
--       apply Approximates_of_EventuallyEq
--         (F := (fun t ↦ (1 + t)^a) ∘ (fun t ↦ -1 + C⁻¹ t * basis_hd t ^ (-exp) * F t))
--       · simp only [EventuallyEq]
--         apply Eventually.mono <| hF_pos.and (hC_pos.and h_basis_hd_pos)
--         intro t ⟨hF_pos, hC_pos, h_basis_hd_pos⟩
--         simp
--         rw [Real.mul_rpow _ hF_pos.le, Real.mul_rpow, Real.inv_rpow hC_pos.le, Real.rpow_neg hC_pos.le, ← Real.rpow_mul h_basis_hd_pos.le, neg_mul]
--         · apply inv_nonneg_of_nonneg
--           linarith
--         · apply Real.rpow_nonneg
--           linarith
--         · apply mul_nonneg
--           · apply inv_nonneg_of_nonneg
--             linarith
--           · apply Real.rpow_nonneg
--             linarith
--       apply Approximates_of_EventuallyEq (F := (powSeries a).toFun ∘
--           (fun t ↦ -1 + C⁻¹ t * basis_hd t ^ (-exp) * F t))
--       · have : Tendsto (fun t ↦ -1 + C⁻¹ t * basis_hd t ^ (-exp) * F t) atTop (nhds 0) := by
--           rw [show (0 : ℝ) = -1 + 1 by simp]
--           apply Tendsto.const_add
--           apply Tendsto.congr' (f₁ := F / (fun k ↦ C k * basis_hd k ^ (exp)))
--           · simp only [EventuallyEq]
--             apply Eventually.mono <| h_basis_hd_pos
--             intro t h_basis_hd_pos
--             simp [Real.rpow_neg h_basis_hd_pos.le]
--             ring
--           rw [← isEquivalent_iff_tendsto_one]
--           conv => rhs; ext; rw [mul_comm]
--           apply IsEquivalent_coef h_coef h_coef_wo h_coef_trimmed h_coef_ne_zero h_tl h_comp h_basis
--           apply Eventually.mono <| hC_pos.and h_basis_hd_pos
--           intro t ⟨hC_pos, h_basis_hd_pos⟩
--           simp
--           constructor
--           · exact hC_pos.ne.symm
--           · rw [Real.rpow_eq_zero_iff_of_nonneg]
--             · push_neg
--               intro h
--               simp [h] at h_basis_hd_pos
--             · exact h_basis_hd_pos.le
--         have : ∀ᶠ t in atTop, ‖-1 + C⁻¹ t * basis_hd t ^ (-exp) * F t‖ < 1 := by
--           apply NormedAddCommGroup.tendsto_nhds_zero.mp this
--           simp
--         simp only [EventuallyEq]
--         apply Eventually.mono this
--         intro t this
--         simp
--         rw [powSeries_toFun_eq]
--         · simp
--         · simpa using this
--       apply apply_Approximates powSeries_analytic h_basis
--       · apply mulMonomial_WellOrdered h_tl_wo
--         exact inv_WellOrdered h_coef_wo
--       · simp
--         generalize leadingExp tl = w at h_comp
--         cases w with
--         | bot => simp [Ne.bot_lt']
--         | coe => simpa [← WithBot.coe_add] using h_comp
--       · exact this


end PreMS

end TendstoTactic
