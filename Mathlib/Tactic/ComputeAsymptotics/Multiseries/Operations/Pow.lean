/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.Calculus.FormalMultilinearSeries
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Operations.Inv
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Trimming
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.LeadingTerm

/-!
# Powers of multiseries

-/

set_option linter.style.multiGoal false

@[expose] public section

open Filter Asymptotics Topology

namespace ComputeAsymptotics

namespace PreMS

open LazySeries Stream'

/-- Binomial series starting from `acc` and `n`:
```
[acc * (a - n) / (n + 1), acc * (a - n) * (a - n + 1) / ((n + 1) * (n + 2)), ...]
```
-/
noncomputable def powSeriesFrom (a : ℝ) (acc : ℝ) (n : ℕ) : LazySeries :=
  let g : (ℝ × ℕ) → Option (ℝ × (ℝ × ℕ)) := fun (acc, m) =>
    some (acc, (acc * (a - m) / (m + 1), m + 1))
  Seq.corec g (acc, n)

/-- Binomial series:
```
[1, a, a * (a - 1) / 2, a * (a - 1) * (a - 2) / 6, ...]
```
-/
noncomputable def powSeries (a : ℝ) : LazySeries :=
  powSeriesFrom a 1 0

theorem powSeriesFrom_eq_cons {a : ℝ} {acc : ℝ} {n : ℕ} :
    powSeriesFrom a acc n = Seq.cons acc (powSeriesFrom a (acc * (a - n) / (n + 1)) (n + 1)) := by
  unfold powSeriesFrom
  nth_rw 1 [Seq.corec_cons]
  rfl

theorem powSeries_eq_cons {a : ℝ} :
    powSeries a = Seq.cons 1 (powSeriesFrom a a 1) := by
  simp only [powSeries]
  rw [powSeriesFrom_eq_cons]
  congr
  norm_num

theorem powSeriesFrom_get {a acc : ℝ} {n m : ℕ} : (powSeriesFrom a acc n).get? m =
    .some (acc * ((descPochhammer ℤ m).smeval (a - n)) * n.factorial / (n + m).factorial) := by
  simp only [powSeriesFrom]
  induction m generalizing acc n with
  | zero =>
    simp only [descPochhammer_zero, Polynomial.smeval_one, pow_zero, one_smul, mul_one, add_zero]
    rw [Seq.corec_cons]
    pick_goal 2
    · rfl
    simp only [Seq.get?_cons_zero, Option.some.injEq]
    field_simp
  | succ m ih =>
    rw [Seq.corec_cons]
    pick_goal 2
    · exact Eq.refl _
    simp only [Seq.get?_cons_succ]
    rw [ih]
    simp only [div_eq_mul_inv, Nat.cast_add, Nat.cast_one, Option.some.injEq]
    move_mul [acc]
    congr 2
    swap
    · congr 3
      ring
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [← mul_assoc]
    congr 1
    move_mul [((n : ℝ) + 1)⁻¹]
    rw [mul_inv_cancel_right₀ (by linarith)]
    simp [show a - n = a - (n + 1) + 1 by ring, descPochhammer_succ_left, Polynomial.smeval_X_mul,
      Polynomial.smeval_comp]

theorem powSeries_get {a : ℝ} {n : ℕ} : (powSeries a).get? n = .some (Ring.choose a n) := by
  simp [powSeries, powSeriesFrom_get, Ring.descPochhammer_eq_factorial_smul_choose]
  field

theorem powSeries_eq_binomialSeries {a : ℝ} :
    (powSeries a).toFormalMultilinearSeries = binomialSeries ℝ a := by
  ext n
  simp [binomialSeries, toFormalMultilinearSeries_coeff, powSeries_get]

theorem powSeries_analytic {a : ℝ} : Analytic (powSeries a) := by
  simp only [Analytic, powSeries_eq_binomialSeries]
  have : 1 ≤ (binomialSeries ℝ a).radius := by apply binomialSeries_radius_ge_one
  apply lt_of_lt_of_le _ this
  simp

theorem powSeries_toFun_eq {t : ℝ} {a : ℝ} (ht : ‖t‖ < 1) : (powSeries a).toFun t = (1 + t)^a := by
  simp only [toFun, powSeries_eq_binomialSeries]
  rw [← HasFPowerSeriesOnBall.sum Real.one_add_rpow_hasFPowerSeriesOnBall_zero]
  · simp
  · simpa [← ENNReal.ofReal_one, Metric.emetric_ball]

/-- If `ms` approximates `f` that eventually positive and `a` is a real number,
then `ms.pow a` approximates `f^a`. -/
noncomputable def pow {basis : Basis} (ms : PreMS basis) (a : ℝ) : PreMS basis :=
  match basis with
  | [] => Real.rpow ms a
  | List.cons _ _ =>
    match destruct ms with
    | none =>
      if a = 0 then
        one _
      else
        .nil
    | some (exp, coef, tl) => mulMonomial
      ((powSeries a).apply (mulMonomial tl coef.inv (-exp))) (coef.pow a) (exp * a)

theorem powSeries_zero_eq : powSeries 0 = Seq.cons 1 zeros := by
  simp only [powSeries, powSeriesFrom, zero_sub, mul_neg]
  rw [Seq.corec_cons]
  pick_goal 2
  · simp only [CharP.cast_eq_zero, mul_zero, neg_zero, zero_add, div_one, Option.some.injEq,
    Prod.mk.injEq]
    constructor <;> exact Eq.refl _
  congr 1
  let motive : LazySeries → LazySeries → Prop := fun a b =>
    b = zeros ∧
    ∃ n, a = Seq.corec (fun (p : ℝ × ℕ) ↦ some (p.1, -(p.1 * ↑p.2) / (↑p.2 + 1), p.2 + 1)) (0, n)
  apply Seq.eq_of_bisim' motive
  · simp only [true_and, motive]
    use 1
  · intro a b ih
    simp only [motive] at ih ⊢
    obtain ⟨hb, n, ha⟩ := ih
    subst ha hb
    right
    use 0, ?_, zeros
    constructor
    · rw [Seq.corec_cons]
      · rfl
    constructor
    · conv_lhs => rw [zeros_eq_cons]
    constructor
    · rfl
    use n + 1
    simp

theorem neg_zpow {basis : Basis} {ms : PreMS basis} {a : ℤ} :
    ms.neg.pow a = (ms.pow a).mulConst ((-1)^a) := by
  cases basis with
  | nil => simp [neg, pow, mulConst, ← mul_zpow]
  | cons basis_hd basis_tl =>
    cases ms with
    | nil =>
      conv_lhs => simp [pow]
      split_ifs with ha <;> simp [pow, ha, one]
    | cons exp coef tl =>
      simp only [pow, neg_cons, destruct_cons]
      rw [neg_zpow, mulMonomial_mulConst_right]
      congr 3
      rw [neg_inv_comm, mulMonomial_neg_left, mulMonomial_neg_right, neg_neg]

theorem pow_WellOrdered {basis : Basis} {ms : PreMS basis} {a : ℝ}
    (h_wo : ms.WellOrdered) : (ms.pow a).WellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    cases ms with
    | nil =>
      simp only [pow, destruct_nil]
      split_ifs
      · apply one_WellOrdered
      · apply WellOrdered.nil
    | cons exp coef tl =>
      obtain ⟨h_coef, h_comp, h_tl⟩ := WellOrdered_cons h_wo
      simp only [pow, destruct_cons]
      apply mulMonomial_WellOrdered
      · apply apply_WellOrdered
        · apply mulMonomial_WellOrdered
          · exact h_tl
          · apply inv_WellOrdered
            exact h_coef
        · simp only [mulMonomial_leadingExp]
          generalize leadingExp tl = w at *
          cases w with
          | bot => simp [Ne.bot_lt']
          | coe => simpa [← WithBot.coe_add] using h_comp
      · apply pow_WellOrdered
        exact h_coef

theorem pow_zero_Approximates {basis : Basis} {f : ℝ → ℝ} {ms : PreMS basis}
    (h_basis : WellFormedBasis basis) (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates f) (h_trimmed : ms.Trimmed) :
    (ms.pow 0).Approximates 1 := by
  cases basis with
  | nil =>
    unfold pow
    simp only [Approximates_const_iff] at *
    eta_expand
    simp
  | cons basis_hd basis_tl =>
    cases ms with
    | nil =>
      apply Approximates_nil at h_approx
      simp only [pow, destruct_nil, ↓reduceIte]
      exact one_Approximates h_basis
    | cons exp coef tl =>
      apply Trimmed_cons at h_trimmed
      obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := h_trimmed
      obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
      obtain ⟨fC, h_coef, _, h_tl⟩ := Approximates_cons h_approx
      simp only [pow, destruct_cons, powSeries_zero_eq, apply_cons, mul_zero, mulMonomial_cons,
        add_zero]
      apply Approximates.cons (fC := 1)
      · conv_rhs => rw [← mul_one 1]
        apply mul_Approximates (h_basis.tail)
        · exact one_Approximates (h_basis.tail)
        · exact pow_zero_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed
      · apply const_majorated
        apply basis_tendsto_top h_basis
        simp
      · simp only [Pi.one_apply, Real.rpow_zero, mul_one, sub_self]
        rw [show (fun t ↦ 0) = fun t ↦ 0 * (basis_hd t)^(0 : ℝ) * 1 by simp]
        apply mulMonomial_Approximates h_basis
        swap
        · exact pow_zero_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed
        conv =>
          arg 2; ext t
          rw [← mul_zero ((f t - basis_hd t ^ exp * fC t) * basis_hd t ^ (-exp) * fC⁻¹ t)]
        apply mul_Approximates h_basis
        · apply mulMonomial_Approximates h_basis h_tl
          apply inv_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed
        apply zeros_apply_Approximates h_basis
        · apply mulMonomial_WellOrdered h_tl_wo
          apply inv_WellOrdered h_coef_wo
        · apply mulMonomial_Approximates h_basis h_tl
          apply inv_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed
        simp only [mulMonomial_leadingExp]
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
    simp only [Pi.pow_apply, Real.rpow_zero]
    apply pow_zero_Approximates h_basis h_wo h_approx h_trimmed
  cases basis with
  | nil =>
    unfold pow
    simp only [Approximates_const_iff] at *
    grw [h_approx]
    rfl
  | cons basis_hd basis_tl =>
    have hF_pos : ∀ᶠ t in atTop, 0 < f t :=
      eventually_pos_of_coef_pos h_pos h_wo h_approx h_trimmed h_basis
    cases ms with
    | nil =>
      apply Approximates_nil at h_approx
      simp only [pow, destruct_nil]
      split_ifs
      apply Approximates.nil
      grw [h_approx]
      apply EventuallyEq.of_eq
      ext t
      exact Real.zero_rpow ha
    | cons exp coef tl =>
      apply Trimmed_cons at h_trimmed
      obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := h_trimmed
      obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
      obtain ⟨fC, h_coef, _, h_tl⟩ := Approximates_cons h_approx
      have h_basis_hd_pos : ∀ᶠ t in atTop, 0 < basis_hd t :=
        basis_head_eventually_pos h_basis
      have hC_pos : ∀ᶠ t in atTop, 0 < fC t := by
        have hC_equiv : fC ~[atTop] f / (fun t ↦ (basis_hd t)^exp) := by
          have hF_equiv :=
            IsEquivalent_coef h_coef h_coef_wo h_coef_trimmed h_coef_ne_zero h_tl h_comp h_basis
          have : fC =ᶠ[atTop] (fun t ↦ (basis_hd t)^exp * fC t) / (fun t ↦ (basis_hd t)^exp) := by
            simp only [EventuallyEq]
            apply h_basis_hd_pos.mono
            intro t ht
            simp only [Pi.div_apply]
            rw [mul_div_cancel_left₀]
            apply ne_of_gt
            apply Real.rpow_pos_of_pos ht
          apply Asymptotics.IsEquivalent.congr_left _ this.symm
          apply IsEquivalent.div hF_equiv.symm
          rfl
        apply eventually_pos_of_IsEquivallent hC_equiv
        apply (hF_pos.and h_basis_hd_pos).mono
        intro t ⟨hF_pos, h_basis_hd_pos⟩
        simp only [Pi.div_apply, gt_iff_lt]
        apply div_pos hF_pos
        apply Real.rpow_pos_of_pos h_basis_hd_pos
      simp only [pow, destruct_cons]
      apply Approximates_of_EventuallyEq (f := fun t ↦
        (fun t ↦ (fC t)^(-a) * (basis_hd t)^(-exp * a) * (f t)^a) t * (basis_hd t)^(exp * a) *
        (fC t)^a)
      · apply (hC_pos.and h_basis_hd_pos).mono
        intro t ⟨hC_pos, h_basis_hd_pos⟩
        simp only [neg_mul, Pi.pow_apply]
        simp [Real.rpow_neg_eq_inv_rpow, Real.inv_rpow hC_pos.le, Real.inv_rpow h_basis_hd_pos.le]
        field
      apply mulMonomial_Approximates h_basis
      swap
      · apply pow_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed
        rwa [leadingTerm_cons_coef] at h_pos
      have : (tl.mulMonomial coef.inv (-exp)).Approximates (fun t ↦
          (f t - basis_hd t ^ exp * fC t) * (basis_hd t)^(-exp) * fC⁻¹ t) := by
        apply mulMonomial_Approximates h_basis
        · exact h_tl
        · exact inv_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed
      apply Approximates_of_EventuallyEq
        (f' := (fun t ↦ -1 + fC⁻¹ t * basis_hd t ^ (-exp) * f t)) at this
      swap
      · apply (hC_pos.and h_basis_hd_pos).mono
        intro t ⟨hC_pos, h_basis_hd_pos⟩
        simp [Real.rpow_neg_eq_inv_rpow, Real.inv_rpow h_basis_hd_pos.le]
        field
      apply Approximates_of_EventuallyEq
        (f := (fun t ↦ (1 + t)^a) ∘ (fun t ↦ -1 + fC⁻¹ t * basis_hd t ^ (-exp) * f t))
      · simp only [EventuallyEq]
        apply (hF_pos.and (hC_pos.and h_basis_hd_pos)).mono
        intro t ⟨hF_pos, hC_pos, h_basis_hd_pos⟩
        simp only [Pi.inv_apply, Function.comp_apply, add_neg_cancel_left, neg_mul]
        rw [Real.mul_rpow _ hF_pos.le, Real.mul_rpow, Real.inv_rpow hC_pos.le,
          Real.rpow_neg hC_pos.le, ← Real.rpow_mul h_basis_hd_pos.le, neg_mul]
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
      · have : Tendsto (fun t ↦ -1 + fC⁻¹ t * basis_hd t ^ (-exp) * f t) atTop (𝓝 0) := by
          rw [show (0 : ℝ) = -1 + 1 by simp]
          apply Tendsto.const_add
          apply Tendsto.congr' (f₁ := f / (fun k ↦ fC k * basis_hd k ^ (exp)))
          · simp only [EventuallyEq]
            apply h_basis_hd_pos.mono
            intro t h_basis_hd_pos
            simp only [Pi.div_apply, Pi.inv_apply, Real.rpow_neg h_basis_hd_pos.le]
            ring
          rw [← isEquivalent_iff_tendsto_one]
          conv_rhs => ext; rw [mul_comm]
          apply IsEquivalent_coef h_coef h_coef_wo h_coef_trimmed h_coef_ne_zero h_tl h_comp h_basis
          apply (hC_pos.and h_basis_hd_pos).mono
          intro t ⟨hC_pos, h_basis_hd_pos⟩
          simp only [ne_eq, mul_eq_zero, not_or]
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
        apply this.mono
        intro t this
        simp only [Pi.inv_apply, Function.comp_apply, add_neg_cancel_left]
        rw [powSeries_toFun_eq]
        · simp
        · simpa using this
      apply apply_Approximates powSeries_analytic h_basis
      · simp only [mulMonomial_leadingExp]
        generalize leadingExp tl = w at h_comp
        cases w with
        | bot => simp [Ne.bot_lt']
        | coe => simpa [← WithBot.coe_add] using h_comp
      · apply mulMonomial_WellOrdered h_tl_wo
        apply inv_WellOrdered h_coef_wo
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
      simp only [Approximates_const_iff, pow, zero]
      simp only [Approximates_const_iff, zero] at h_approx
      by_cases ha : a = 0
      · simp [ha]
        rfl
      · replace ha : a ≠ 0 := by simpa
        grw [h_approx]
        simp
        rfl
    | cons basis_hd basis_tl =>
      simp only [pow, zero, destruct_nil, Int.cast_eq_zero]
      simp only [zero] at h_approx
      apply Approximates_nil at h_approx
      split_ifs with ha
      · subst ha
        exact const_Approximates h_basis
      · apply Approximates.nil
        replace ha : a ≠ 0 := by simpa
        apply h_approx.mono
        simp only [Pi.zero_apply, Pi.pow_apply]
        intro x hx
        rw [hx, zero_zpow a ha]
  · have h_neg_approx : (ms.neg.pow a).Approximates ((-f)^a) := by
      rw [show (-f)^a = (-f)^(a : ℝ) by ext; simp]
      apply pow_Approximates h_basis (neg_WellOrdered h_wo) (neg_Approximates h_approx)
      · exact neg_Trimmed h_trimmed
      · simpa [neg_leadingTerm]
    rw [show (-f)^a = (-1 : ℝ)^a • fun t ↦ (f t)^a by ext; simp [← mul_zpow]] at h_neg_approx
    rw [neg_zpow] at h_neg_approx
    have h_eq : ms.pow a = ((ms.pow a).mulConst ((-1)^a)).mulConst ((-1)^a) := by
      simp [← mul_zpow]
    rw [h_eq, show f ^ a = (-1 : ℝ)^a • (-1 : ℝ)^a • fun x ↦ (f x) ^ a by
      ext; rw [smul_smul, ← zpow_add₀ (by simp), Even.neg_one_zpow (by simp)]; simp]
    apply mulConst_Approximates h_neg_approx

end PreMS

end ComputeAsymptotics
