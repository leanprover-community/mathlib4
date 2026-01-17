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

set_option linter.flexible false
set_option linter.style.longLine false
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
  simp only [LazySeries.toFun, powSeries_eq_binomialSeries]
  rw [← HasFPowerSeriesOnBall.sum Real.one_add_rpow_hasFPowerSeriesOnBall_zero]
  · simp
  · simpa [← ENNReal.ofReal_one, Metric.emetric_ball]

theorem powSeries_toFun_eq' (a : ℝ) : (powSeries a).toFun =ᶠ[𝓝 0] (fun t ↦ (1 + t)^a) := by
  apply Filter.eventuallyEq_of_mem (s := Metric.ball 0 1)
  · apply Metric.ball_mem_nhds
    simp
  intro t h
  rw [powSeries_toFun_eq]
  simpa using h

mutual

/-- If `ms` approximates `f` that eventually positive and `a` is a real number,
then `ms.pow a` approximates `f^a`. -/
noncomputable def SeqMS.pow {basis_hd basis_tl} (ms : SeqMS basis_hd basis_tl) (a : ℝ) :
    SeqMS basis_hd basis_tl :=
  match ms.destruct with
  | none =>
    if a = 0 then
      SeqMS.one
    else
      .nil
  | some (exp, coef, tl) =>
    (((tl.mulMonomial coef.inv (-exp))).apply (powSeries a)).mulMonomial
      (coef.pow a) (exp * a)

/-- If `ms` approximates `f` that eventually positive and `a` is a real number,
then `ms.pow a` approximates `f^a`. -/
noncomputable def pow {basis : Basis} (ms : PreMS basis) (a : ℝ) : PreMS basis :=
  match basis with
  | [] => ms.toReal ^ a
  | List.cons _ _ => mk (SeqMS.pow ms.seq a) (ms.toFun ^ a)

end

noncomputable def npow {basis : Basis} (ms : PreMS basis) (a : ℕ) : PreMS basis :=
  match basis with
  | [] => ms.toReal ^ a
  | List.cons _ _ => (ms.pow a).replaceFun (ms.toFun ^ a)

noncomputable def zpow {basis : Basis} (ms : PreMS basis) (a : ℤ) : PreMS basis :=
  match basis with
  | [] => ms.toReal ^ a
  | List.cons _ _ => (ms.pow a).replaceFun (ms.toFun ^ a)

@[simp]
theorem pow_toFun {basis : Basis} {ms : PreMS basis} {a : ℝ} :
    (ms.pow a).toFun = ms.toFun ^ a := by
  cases basis with
  | nil => simp [pow, toReal]; rfl
  | cons basis_hd basis_tl => simp [pow]

@[simp]
theorem pow_seq {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} {a : ℝ} :
    (ms.pow a).seq = SeqMS.pow ms.seq a := by
  cases ms with
  | nil => simp [pow]
  | cons exp coef tl => simp [pow]

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

theorem powSeries_zero_toFun_eq : (powSeries 0).toFun = 1 := by
  simp [powSeries_zero_eq]
  ext t
  rw [LazySeries.toFun_cons]
  · simp [zeros_toFun]
  · apply cons_analytic zeros_analytic
  · simp [tail_radius_eq]

mutual

theorem SeqMS.neg_zpow {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl} {a : ℤ} :
    ms.neg.pow a = (ms.pow a).mulConst ((-1)^a) := by
  cases ms with
  | nil =>
    conv_lhs => simp [SeqMS.pow]
    split_ifs with ha <;> simp [SeqMS.pow, ha, SeqMS.one]
  | cons exp coef tl =>
    simp only [SeqMS.pow, SeqMS.neg_cons, SeqMS.destruct_cons]
    rw [neg_zpow, SeqMS.mulMonomial_mulConst_right]
    congr 3
    rw [neg_inv_comm, SeqMS.mulMonomial_neg_left, SeqMS.mulMonomial_neg_right, SeqMS.neg_neg]

theorem neg_zpow {basis : Basis} {ms : PreMS basis} {a : ℤ} :
    ms.neg.pow a = (ms.pow a).mulConst ((-1)^a) := by
  cases basis with
  | nil => simp [neg, pow, mulConst, ← mul_zpow, ofReal, toReal]
  | cons basis_hd basis_tl =>
    simp [ms_eq_ms_iff_mk_eq_mk]
    constructor
    · exact SeqMS.neg_zpow
    · ext t
      simp
      rw [neg_eq_neg_one_mul, mul_zpow]

end

mutual

theorem SeqMS.pow_WellOrdered {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl} {a : ℝ}
    (h_wo : ms.WellOrdered) : (ms.pow a).WellOrdered := by
  cases ms with
  | nil =>
    simp only [SeqMS.pow, SeqMS.destruct_nil]
    split_ifs
    · apply SeqMS.one_WellOrdered
    · apply WellOrdered.nil
  | cons exp coef tl =>
    obtain ⟨h_coef, h_comp, h_tl⟩ := WellOrdered_cons h_wo
    simp only [SeqMS.pow, SeqMS.destruct_cons]
    apply SeqMS.mulMonomial_WellOrdered
    · apply SeqMS.apply_WellOrdered
      · apply SeqMS.mulMonomial_WellOrdered
        · exact h_tl
        · apply inv_WellOrdered
          exact h_coef
      · simp only [SeqMS.mulMonomial_leadingExp]
        generalize tl.leadingExp = w at *
        cases w with
        | bot => simp [Ne.bot_lt']
        | coe => simpa [← WithBot.coe_add] using h_comp
    · apply pow_WellOrdered
      exact h_coef

theorem pow_WellOrdered {basis : Basis} {ms : PreMS basis} {a : ℝ}
    (h_wo : ms.WellOrdered) : (ms.pow a).WellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simp at *
    apply SeqMS.pow_WellOrdered h_wo

end

theorem pow_zero_Approximates {basis : Basis} {ms : PreMS basis}
    (h_basis : WellFormedBasis basis) (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates) (h_trimmed : ms.Trimmed) :
    (ms.pow 0).Approximates := by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
    cases ms with
    | nil f =>
      apply Approximates_nil at h_approx
      simp [pow, SeqMS.pow]
      convert one_Approximates h_basis
      simp [one, SeqMS.one]
      rfl
    | cons exp coef tl f =>
      apply Trimmed_cons at h_trimmed
      obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := h_trimmed
      obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
      obtain ⟨h_coef, _, h_tl⟩ := Approximates_cons h_approx
      simp [pow, SeqMS.pow]
      let ms := (((mk tl (f - basis_hd ^ exp * coef.toFun)).mulMonomial coef.inv (-exp)).apply (powSeries 0)).mulMonomial (coef.pow 0) 0
      have h : ms.Approximates := by
        simp [ms]
        apply mulMonomial_Approximates h_basis
        · apply apply_Approximates powSeries_analytic h_basis
          · simp
            generalize tl.leadingExp = w at h_comp
            cases w with
            | bot => simp [Ne.bot_lt']
            | coe => simpa [← WithBot.coe_add] using h_comp
          · simp
            apply SeqMS.mulMonomial_WellOrdered h_tl_wo
            apply inv_WellOrdered h_coef_wo
          · apply mulMonomial_Approximates h_basis h_tl
            apply inv_Approximates h_basis.tail h_coef_wo h_coef h_coef_trimmed
        · apply pow_zero_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed
      convert replaceFun_Approximates _ h
      simp [ms, powSeries_zero_toFun_eq]

theorem pow_Approximates {basis : Basis} {ms : PreMS basis} {a : ℝ}
    (h_basis : WellFormedBasis basis) (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates) (h_trimmed : ms.Trimmed) (h_pos : 0 < ms.leadingTerm.coef) :
    (ms.pow a).Approximates := by
  by_cases ha : a = 0
  · rw [ha]
    apply pow_zero_Approximates h_basis h_wo h_approx h_trimmed
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
    cases ms with
    | nil f =>
      apply Approximates_nil at h_approx
      simp [pow, SeqMS.pow]
      split_ifs
      apply Approximates.nil
      grw [h_approx]
      apply EventuallyEq.of_eq
      ext t
      exact Real.zero_rpow ha
    | cons exp coef tl f =>
      have hF_pos : ∀ᶠ t in atTop, 0 < f t :=
        eventually_pos_of_coef_pos h_pos h_wo h_approx h_trimmed h_basis
      obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := Trimmed_cons h_trimmed
      obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
      obtain ⟨h_coef, _, h_tl⟩ := Approximates_cons h_approx
      simp [pow, SeqMS.pow]
      let ms := (((mk tl (f - basis_hd ^ exp * coef.toFun)).mulMonomial coef.inv (-exp)).apply (powSeries a)).mulMonomial (coef.pow a) (exp * a)
      have h : ms.Approximates := by
        simp [ms]
        apply mulMonomial_Approximates h_basis
        · apply apply_Approximates powSeries_analytic h_basis
          · simp
            generalize tl.leadingExp = w at h_comp
            cases w with
            | bot => simp [Ne.bot_lt']
            | coe => simpa [← WithBot.coe_add] using h_comp
          · simp
            apply SeqMS.mulMonomial_WellOrdered h_tl_wo
            apply inv_WellOrdered h_coef_wo
          · apply mulMonomial_Approximates h_basis h_tl
            apply inv_Approximates h_basis.tail h_coef_wo h_coef h_coef_trimmed
        · apply pow_Approximates (h_basis.tail) h_coef_wo h_coef h_coef_trimmed h_pos
      convert replaceFun_Approximates _ h
      have h_tendsto_zero := tl_mulMonomial_coef_inv_neg_exp_toFun_tendsto_zero h_basis h_wo h_approx h_trimmed
      simp [ms] at h_tendsto_zero ⊢
      set g := (f - basis_hd ^ exp * coef.toFun) * basis_hd ^ (-exp) * coef.toFun⁻¹
      have h_basis_hd_pos : ∀ᶠ t in atTop, 0 < basis_hd t :=
        basis_head_eventually_pos h_basis
      have hC_pos : ∀ᶠ t in atTop, 0 < coef.toFun t := by
        have hC_equiv : coef.toFun ~[atTop] f / (fun t ↦ (basis_hd t)^exp) := by
          have hF_equiv := IsEquivalent_coef h_approx h_wo h_coef_trimmed h_coef_ne_zero h_basis
          have : coef.toFun =ᶠ[atTop] (fun t ↦ (basis_hd t)^exp * coef.toFun t) / (fun t ↦ (basis_hd t)^exp) := by
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
      have hg_gt : ∀ᶠ t in atTop, -1/2 ≤ g t := by
        apply Filter.Tendsto.eventually_const_le (by norm_num) h_tendsto_zero
      apply (powSeries_toFun_eq' a).comp_tendsto at h_tendsto_zero
      grw [h_tendsto_zero]
      apply (hC_pos.and (h_basis_hd_pos.and hg_gt)).mono
      intro t ⟨hC_pos, h_basis_hd_pos, hg_gt⟩
      simp [g]
      have : 0 ≤ 1 + (f t - basis_hd t ^ exp * coef.toFun t) * (basis_hd t ^ exp)⁻¹ * (coef.toFun t)⁻¹ := by
        convert_to 0 ≤ 1 + g t
        · simp [g, Real.rpow_neg h_basis_hd_pos.le]
        linarith
      rw [Real.rpow_neg h_basis_hd_pos.le, Real.rpow_mul h_basis_hd_pos.le, ← Real.mul_rpow, ← Real.mul_rpow]
      · congr
        field
      · positivity
      · linarith
      · exact this
      · positivity

theorem npow_eq_pow {basis : Basis} {ms : PreMS basis} {a : ℕ} :
    (ms.npow a) = ms.pow a := by
  cases basis with
  | nil => simp [npow, pow, toReal]
  | cons basis_hd basis_tl =>
    simp [npow, pow]
    ext t
    simp

theorem zpow_eq_pow {basis : Basis} {ms : PreMS basis} {a : ℤ} :
    (ms.zpow a) = ms.pow a := by
  cases basis with
  | nil => simp [zpow, pow, toReal]
  | cons basis_hd basis_tl =>
    simp [zpow, pow]
    ext t
    simp

@[simp]
theorem npow_toFun {basis : Basis} {ms : PreMS basis} {a : ℕ} :
    (ms.npow a).toFun = ms.toFun ^ a := by
  ext t
  simp [npow_eq_pow]

@[simp]
theorem zpow_toFun {basis : Basis} {ms : PreMS basis} {a : ℤ} :
    (ms.zpow a).toFun = ms.toFun ^ a := by
  ext t
  simp [zpow_eq_pow]

theorem npow_WellOrdered {basis : Basis} {ms : PreMS basis} {a : ℕ}
    (h_wo : ms.WellOrdered) : (ms.npow a).WellOrdered := by
  rw [npow_eq_pow]
  apply pow_WellOrdered h_wo

theorem zpow_WellOrdered {basis : Basis} {ms : PreMS basis} {a : ℤ}
    (h_wo : ms.WellOrdered) : (ms.zpow a).WellOrdered := by
  rw [zpow_eq_pow]
  apply pow_WellOrdered h_wo

theorem zpow_Approximates {basis : Basis} {ms : PreMS basis} {a : ℤ}
    (h_basis : WellFormedBasis basis) (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates) (h_trimmed : ms.Trimmed) :
    (ms.zpow a).Approximates := by
  rw [zpow_eq_pow]
  rcases lt_trichotomy 0 ms.realCoef with (h_leading | h_leading | h_leading)
  · apply pow_Approximates <;> assumption
  · have : IsZero ms := by apply IsZero_of_leadingTerm_zero_coef h_trimmed h_leading.symm
    cases basis with
    | nil => simp
    | cons basis_hd basis_tl =>
      have h_fun := IsZero_Approximates_zero this h_approx
      simp at this
      simp [pow, this, SeqMS.pow]
      split_ifs with ha
      · subst ha
        convert one_Approximates h_basis
        simp
      · apply Approximates.nil
        replace ha : a ≠ 0 := by simpa
        grw [h_fun]
        apply EventuallyEq.of_eq
        ext t
        simp [zero_zpow a ha]
  · have h_neg_approx : (ms.neg.pow a).Approximates := by
      apply pow_Approximates h_basis (neg_WellOrdered h_wo) (neg_Approximates h_approx)
      · exact neg_Trimmed h_trimmed
      · simpa [neg_leadingTerm]
    rw [neg_zpow] at h_neg_approx
    have h_eq : ms.pow a = ((ms.pow a).mulConst ((-1)^a)).mulConst ((-1)^a) := by
      simp [← mul_zpow]
    rw [h_eq]
    apply mulConst_Approximates h_neg_approx

theorem npow_Approximates {basis : Basis} {ms : PreMS basis} {a : ℕ}
    (h_basis : WellFormedBasis basis) (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates) (h_trimmed : ms.Trimmed) :
    (ms.npow a).Approximates := by
  rw [npow_eq_pow, show (a : ℝ) = (a : ℤ) by simp, ← zpow_eq_pow]
  apply zpow_Approximates h_basis h_wo h_approx h_trimmed

end PreMS

end ComputeAsymptotics
