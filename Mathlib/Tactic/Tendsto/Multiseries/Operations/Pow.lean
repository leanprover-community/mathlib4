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
    .some (acc * ((descPochhammer ℤ m).smeval (a - n)) * n.factorial / (n + m).factorial) := by
  simp [powSeriesFrom]
  induction m generalizing acc n with
  | zero =>
    simp [powSeriesFrom]
    rw [corec_cons]
    pick_goal 2
    · exact Eq.refl _
    simp
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
    simp [show a - n = a - (n + 1) + 1 by ring, descPochhammer_succ_left, Polynomial.smeval_X_mul,
      Polynomial.smeval_comp]

theorem powSeries_get {a : ℝ} {n : ℕ} : (powSeries a).get? n = .some (Ring.choose a n) := by
  field_simp [powSeries, powSeriesFrom_get, Ring.choose_eq_div]

theorem powSeries_eq_binomialSeries {a : ℝ} : (powSeries a).toFormalMultilinearSeries = binomialSeries ℝ a := by
  ext n f
  simp [binomialSeries, toFormalMultilinearSeries_coeff, powSeries_get]
  rw [mul_comm]
  congr
  exact Eq.symm List.prod_ofFn

theorem powSeries_analytic {a : ℝ} : analytic (powSeries a) := by
  simp [analytic, powSeries_eq_binomialSeries]
  have : 1 ≤ (binomialSeries ℝ a).radius := by apply binomialSeries_radius_ge_one
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
  apply eq_of_bisim' motive
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

theorem neg_zpow {basis : Basis} {ms : PreMS basis} {a : ℤ} :
    ms.neg.pow a = (ms.pow a).mulConst ((-1)^a) := by
  cases basis with
  | nil => simp [neg, pow, mulConst, ← mul_zpow]
  | cons basis_hd basis_tl =>
    cases' ms with exp coef tl
    · conv => lhs; simp [pow]
      split_ifs with ha <;> simp [pow, ha, one]
    simp [pow]
    rw [neg_zpow, mulMonomial_mulConst_left]
    congr 3
    rw [neg_inv_comm, mulMonomial_neg_left, mulMonomial_neg_right, neg_neg]

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

theorem pow_zero_Approximates {basis : Basis} {f : ℝ → ℝ} {ms : PreMS basis}
    (h_basis : WellFormedBasis basis) (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates f) (h_trimmed : ms.Trimmed)  :
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
      obtain ⟨fC, h_coef, _, h_tl⟩ := Approximates_cons h_approx
      simp [pow, powSeries_zero_eq]
      apply Approximates.cons (fC := 1)
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
        conv => arg 2; ext t; rw [← zero_mul (fC⁻¹ t * basis_hd t ^ (-exp) * (f t - basis_hd t ^ exp * fC t))]
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

theorem pow_Approximates {basis : Basis} {f : ℝ → ℝ} {ms : PreMS basis} {a : ℝ}
    (h_basis : WellFormedBasis basis) (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates f) (h_trimmed : ms.Trimmed) (h_pos : 0 < ms.leadingTerm.coef) :
    (ms.pow a).Approximates (f^a) := by
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
    have hF_pos : ∀ᶠ t in atTop, 0 < f t := eventually_pos_of_coef_pos h_pos h_wo h_approx h_trimmed h_basis
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
      obtain ⟨fC, h_coef, _, h_tl⟩ := Approximates_cons h_approx
      have h_basis_hd_pos : ∀ᶠ t in atTop, 0 < basis_hd t :=
        basis_head_eventually_pos h_basis
      have hC_pos : ∀ᶠ t in atTop, 0 < fC t := by
        have hC_equiv : fC ~[atTop] f / (fun t ↦ (basis_hd t)^exp) := by
          have hF_equiv := IsEquivalent_coef h_coef h_coef_wo h_coef_trimmed h_coef_ne_zero h_tl h_comp h_basis
          have : fC =ᶠ[atTop] (fun t ↦ (basis_hd t)^exp * fC t) / (fun t ↦ (basis_hd t)^exp) := by
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
      apply Approximates_of_EventuallyEq (f := fun t ↦ (fC t)^a * (basis_hd t)^(exp * a) *
        (fun t ↦ (fC t)^(-a) * (basis_hd t)^(-exp * a) * (f t)^a) t)
      · simp only [EventuallyEq]
        apply Eventually.mono <| hC_pos.and h_basis_hd_pos
        intro t ⟨hC_pos, h_basis_hd_pos⟩
        simp
        ring_nf
        move_mul [←  fC t ^ (-a)]
        rw [← Real.rpow_add hC_pos]
        simp [← Real.rpow_add h_basis_hd_pos]
      apply mulMonomial_Approximates h_basis
      swap
      · apply pow_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed
        rwa [leadingTerm_cons_coef] at h_pos
      have : (tl.mulMonomial coef.inv (-exp)).Approximates (fun t ↦ fC⁻¹ t *
          (basis_hd t)^(-exp) * (f t - basis_hd t ^ exp * fC t))
          (basis := basis_hd :: basis_tl) := by
        apply mulMonomial_Approximates h_basis
        · exact h_tl
        · exact inv_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed
      apply Approximates_of_EventuallyEq
        (f' := (fun t ↦ -1 + fC⁻¹ t * basis_hd t ^ (-exp) * f t)) at this
      swap
      · simp only [EventuallyEq]
        apply Eventually.mono <| hC_pos.and h_basis_hd_pos
        intro t ⟨hC_pos, h_basis_hd_pos⟩
        simp
        ring_nf
        simp [mul_inv_cancel₀ hC_pos.ne.symm]
        simp [← Real.rpow_add h_basis_hd_pos]
      apply Approximates_of_EventuallyEq
        (f := (fun t ↦ (1 + t)^a) ∘ (fun t ↦ -1 + fC⁻¹ t * basis_hd t ^ (-exp) * f t))
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
      apply Approximates_of_EventuallyEq (f := (powSeries a).toFun ∘
          (fun t ↦ -1 + fC⁻¹ t * basis_hd t ^ (-exp) * f t))
      · have : Tendsto (fun t ↦ -1 + fC⁻¹ t * basis_hd t ^ (-exp) * f t) atTop (nhds 0) := by
          rw [show (0 : ℝ) = -1 + 1 by simp]
          apply Tendsto.const_add
          apply Tendsto.congr' (f₁ := f / (fun k ↦ fC k * basis_hd k ^ (exp)))
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
        have : ∀ᶠ t in atTop, ‖-1 + fC⁻¹ t * basis_hd t ^ (-exp) * f t‖ < 1 := by
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

theorem zpow_Approximates {basis : Basis} {f : ℝ → ℝ} {ms : PreMS basis} {a : ℤ}
    (h_basis : WellFormedBasis basis) (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates f) (h_trimmed : ms.Trimmed) :
    (ms.pow a).Approximates (f^a) := by
  rcases lt_trichotomy 0 ms.leadingTerm.coef with (h_leading | h_leading | h_leading)
  · convert_to (ms.pow a).Approximates (f ^ (a : ℝ))
    · ext
      simp
    apply pow_Approximates <;> assumption
  · have : ms = zero _ := by apply zero_of_leadingTerm_zero_coef h_trimmed h_leading.symm
    subst this
    cases basis with
    | nil =>
      simp [zero, pow, Approximates]
      simp [zero, Approximates] at h_approx
      by_cases ha : a = 0
      · simp [ha]
        rfl
      · replace ha : a ≠ 0 := by simpa
        apply h_approx.mono
        simp [zero_zpow a ha]
        intro x hx
        rw [hx, zero_zpow a ha]
    | cons basis_hd basis_tl =>
      simp [zero, pow]
      simp [zero] at h_approx
      apply Approximates_nil at h_approx
      split_ifs with ha
      · subst ha
        exact const_Approximates h_basis
      · apply Approximates.nil
        replace ha : a ≠ 0 := by simpa
        apply h_approx.mono
        simp [zero_zpow a ha]
        intro x hx
        rw [hx, zero_zpow a ha]
  · have : (ms.neg.pow a).Approximates ((-f)^a) := by
      rw [show (-f)^a = (-f)^(a : ℝ) by ext; simp]
      apply pow_Approximates h_basis (neg_WellOrdered h_wo) (neg_Approximates h_approx)
      · exact neg_Trimmed h_trimmed
      · simpa [neg_leadingTerm]
    rw [show (-f)^a = fun t ↦ (f t)^a * (-1)^a by ext; simp [← mul_zpow]] at this
    rw [neg_zpow] at this
    have h_eq : ms.pow a = ((ms.pow a).mulConst ((-1)^a)).mulConst ((-1)^a) := by
      simp [← mul_zpow]
    rw [h_eq, show f ^ a = fun x ↦ (f x) ^ a * (-1)^a * (-1)^a by ext; simp [mul_assoc, ← mul_zpow]]
    apply mulConst_Approximates this

end PreMS

end TendstoTactic
