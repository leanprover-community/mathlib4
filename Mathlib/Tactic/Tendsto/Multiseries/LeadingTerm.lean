/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.Tendsto.Multiseries.Term
import Mathlib.Tactic.Tendsto.Multiseries.Trimming

/-!
Here we find the limit of series by reducing the problem to computing limits for its leading
term.
-/

set_option linter.style.longLine false

open Filter Asymptotics Topology

namespace TendstoTactic

namespace PreMS

open Stream' Seq

/-- `ms.leadingTerm` is its leading monomial. -/
def leadingTerm {basis : Basis} (ms : PreMS basis) : Term :=
  match basis with
  | [] => ⟨ms, []⟩
  | List.cons _ _ =>
    match head ms with
    | none => ⟨0, List.replicate basis.length 0⟩
    | some (exp, coef) =>
      let pre := coef.leadingTerm
      ⟨pre.coef, exp :: pre.exps⟩

/-- `Term.coef ms.coef.leadingTerm` is equal to `Term.coef ms.leadingTerm`. -/
theorem leadingTerm_cons_coef {basis_hd} {basis_tl} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)} :
    (@leadingTerm (basis_hd :: basis_tl) (cons (exp, coef) tl)).coef = coef.leadingTerm.coef := by
  conv => lhs; simp [leadingTerm]

theorem leadingTerm_length {basis : Basis} {ms : PreMS basis} :
    ms.leadingTerm.exps.length = basis.length :=
  match basis with
  | [] => by simp [leadingTerm]
  | List.cons basis_hd basis_tl => by
    cases ms <;> simp [leadingTerm, leadingTerm_length]

theorem leadingTerm_ne_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    : ms.leadingTerm.exps ≠ [] := by
  cases' ms with exp coef tl <;> simp [leadingTerm]

theorem leadingTerm_cons_toFun {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} (t : ℝ) :
    (leadingTerm (basis := basis_hd :: basis_tl) (Seq.cons (exp, coef) tl)).toFun
      (basis_hd :: basis_tl) t =
    (basis_hd t)^exp * (leadingTerm coef).toFun basis_tl t := by
  simp [leadingTerm, Term.toFun]
  conv =>
    congr <;> rw [Term.fold_eq_mul]
    lhs
    rw [mul_comm] -- why do I need these rws? Why ring_nf can't solve the goal?
  rw [← mul_assoc]

theorem zero_of_leadingTerm_zero_coef {basis : Basis} {ms : PreMS basis} (h_trimmed : ms.Trimmed)
    (h : ms.leadingTerm.coef = 0) : ms = zero basis := by
  cases basis with
  | nil =>
    simp [leadingTerm] at h
    exact h
  | cons basis_hd basis_tl =>
    cases' ms with exp coef tl
    · rfl
    simp [leadingTerm] at h
    replace h_trimmed := Trimmed_cons h_trimmed
    have : coef = zero _ := zero_of_leadingTerm_zero_coef h_trimmed.left h
    simp [this] at h_trimmed

/-- If `ms` is not zero, then eventually `ms.leadingTerm.toFun` is non-zero. -/
theorem leadingTerm_eventually_ne_zero {basis : Basis} {ms : PreMS basis}
    (h_trimmed : ms.Trimmed) (h_ne_zero : ms ≠ zero _)
    (h_basis : WellFormedBasis basis) :
    ∀ᶠ t in atTop, ms.leadingTerm.toFun basis t ≠ 0 := by
  cases basis with
  | nil =>
    unfold leadingTerm
    simp [Term.toFun]
    use default
    intros
    intro h
    simp [h, zero] at h_ne_zero
  | cons basis_hd basis_tl =>
    cases' ms with exp coef tl
    · absurd h_ne_zero
      constructor
    · obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := Trimmed_cons h_trimmed
      let coef_ih := coef.leadingTerm_eventually_ne_zero h_coef_trimmed h_coef_ne_zero
        (h_basis.tail)
      apply (coef_ih.and (basis_head_eventually_pos h_basis)).mono
      rintro t ⟨coef_ih, h_basis_hd_pos⟩
      simp [leadingTerm, Term.toFun, -ne_eq]
      simp only [Term.toFun] at coef_ih
      conv =>
        rw [Term.fold_eq_mul]
        lhs
        lhs
        rw [mul_comm]
      rw [mul_assoc]
      rw [Term.fold_eq_mul] at coef_ih
      apply mul_ne_zero
      · exact (Real.rpow_pos_of_pos h_basis_hd_pos _).ne.symm
      · exact coef_ih

mutual
  /-- If function `f` is approximated by `cons (exp, coef) tl` and `coef` approximates `fC`, then
  `f` is asymptotically equivalent to `fC * basis_hd ^ exp`. -/
  theorem IsEquivalent_coef {basis_hd fC f : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
      {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
      (h_coef : coef.Approximates fC)
      (h_coef_wo : coef.WellOrdered)
      (h_coef_trimmed : coef.Trimmed)
      (h_coef_ne_zero : coef ≠ zero _)
      (h_tl : tl.Approximates (fun t ↦ f t - (basis_hd t)^exp * fC t))
      (h_comp : leadingExp tl < ↑exp)
      (h_basis : WellFormedBasis (basis_hd :: basis_tl)) :
      f ~[atTop] fun t ↦ (basis_hd t)^exp * (fC t) := by
    have coef_ih := coef.IsEquivalent_leadingTerm (f := fC) h_coef_wo h_coef h_coef_trimmed
      (h_basis.tail)
    simp [IsEquivalent]
    eta_expand
    simp only [Pi.sub_apply]
    cases' tl with tl_exp tl_coef tl_tl
    · apply Approximates_nil at h_tl
      apply EventuallyEq.trans_isLittleO h_tl
      apply Asymptotics.isLittleO_zero -- should be simp lemma
    · obtain ⟨tl_C, _, h_tl_maj, _⟩ := Approximates_cons h_tl
      simp at h_comp
      let exp' := (exp + tl_exp) / 2
      specialize h_tl_maj exp' (by simp only [exp']; linarith)
      apply IsLittleO.trans h_tl_maj
      apply (isLittleO_iff_tendsto' _).mpr
      · simp_rw [← div_div]
        conv in _ / _ =>
          rw [div_eq_mul_inv, div_mul_comm, div_mul]
        apply (isLittleO_iff_tendsto' _).mp
        · have : (fun t ↦ basis_hd t ^ exp / basis_hd t ^ exp') =ᶠ[atTop]
              fun t ↦ (basis_hd t)^(exp - exp') := by
            apply (basis_head_eventually_pos h_basis).mono
            intro t h
            simp only
            rw [← Real.rpow_sub h]
          apply IsLittleO.trans_eventuallyEq _ this.symm
          have := IsEquivalent.inv coef_ih
          apply IsEquivalent.trans_isLittleO this
          apply EventuallyEq.trans_isLittleO (Term.inv_toFun ((h_basis.tail)))
          apply Term.tail_fun_IsLittleO_head
          · rw [Term.inv_length, leadingTerm_length]
          · exact h_basis
          · simp only [exp']
            linarith
        · apply (basis_head_eventually_pos h_basis).mono
          intro t h1 h2
          absurd h2
          apply div_ne_zero <;> exact (Real.rpow_pos_of_pos h1 _).ne.symm
      · have h_C_ne_zero : ∀ᶠ t in atTop, fC t ≠ 0 := by
          obtain ⟨φ, h_φ, h_C⟩ := Asymptotics.IsEquivalent.exists_eq_mul coef_ih
          have h_φ_pos : ∀ᶠ t in atTop, 0 < φ t := by
            apply eventually_gt_of_tendsto_gt (by simp) h_φ
          apply EventuallyEq.rw (p := fun _ b => b ≠ 0) h_C.symm
          apply (h_φ_pos.and (leadingTerm_eventually_ne_zero
            h_coef_trimmed h_coef_ne_zero ((h_basis.tail)))).mono
          rintro t ⟨h_φ_pos, h⟩
          exact mul_ne_zero h_φ_pos.ne.symm h
        apply (h_C_ne_zero.and (basis_head_eventually_pos h_basis)).mono
        rintro t ⟨h_C_ne_zero, h_basis_pos⟩
        intro h
        absurd h
        apply mul_ne_zero _ h_C_ne_zero
        exact (Real.rpow_pos_of_pos h_basis_pos _).ne.symm

  /-- If `f` is approximated by trimmed multiseries `ms`, then it is asymptotically equivalent to
  `ms.leadingTerm.toFun`. -/
  theorem IsEquivalent_leadingTerm {basis : Basis} {ms : PreMS basis} {f : ℝ → ℝ}
      (h_wo : ms.WellOrdered)
      (h_approx : ms.Approximates f) (h_trimmed : ms.Trimmed)
      (h_basis : WellFormedBasis basis) :
      f ~[atTop] ms.leadingTerm.toFun basis := by
    cases basis with
    | nil =>
      simp [Approximates] at h_approx
      simp [leadingTerm]
      apply EventuallyEq.isEquivalent (by assumption)
    | cons basis_hd basis_tl =>
      cases' ms with exp coef tl
      · have hF := Approximates_nil h_approx
        unfold leadingTerm
        simp [Term.zero_coef_toFun]
        apply EventuallyEq.isEquivalent (by assumption)
      · obtain ⟨fC, h_coef, _, h_tl⟩ := Approximates_cons h_approx
        obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := Trimmed_cons h_trimmed
        obtain ⟨h_coef_wo, h_comp, _⟩ := WellOrdered_cons h_wo
        have coef_ih := coef.IsEquivalent_leadingTerm (f := fC) h_coef_wo h_coef h_coef_trimmed
          (h_basis.tail)
        have : f ~[atTop] fun t ↦ (basis_hd t)^exp * (fC t) :=
          IsEquivalent_coef h_coef h_coef_wo h_coef_trimmed h_coef_ne_zero h_tl h_comp h_basis
        apply IsEquivalent.trans this
        eta_expand
        simp_rw [leadingTerm_cons_toFun]
        apply IsEquivalent.mul IsEquivalent.refl
        exact coef_ih
end

-- TODO: to another file
-- TODO: generalize
lemma eventually_pos_of_IsEquivallent {l : Filter ℝ} {f g : ℝ → ℝ} (h : f ~[l] g)
    (hg : ∀ᶠ t in l, 0 < g t) : ∀ᶠ x in l, 0 < f x := by
  obtain ⟨φ, hφ_tendsto, h_eq⟩ := Asymptotics.IsEquivalent.exists_eq_mul h
  have hφ : ∀ᶠ x in l, 1/2 < φ x := by
    apply eventually_gt_of_tendsto_gt _ hφ_tendsto
    linarith
  apply ((h_eq.and hφ).and hg).mono
  intro x ⟨⟨h_eq, hφ⟩, hg⟩
  rw [h_eq]
  simp
  nlinarith

/-- If `f` is approximated by `ms`, and `ms.leadingTerm.coef > 0`, then
`f` is eventually positive. -/
theorem eventually_pos_of_coef_pos {basis : Basis} {ms : PreMS basis} {f : ℝ → ℝ}
    (h_pos : 0 < ms.leadingTerm.coef) (h_wo : ms.WellOrdered) (h_approx : ms.Approximates f)
    (h_trimmed : ms.Trimmed) (h_basis : WellFormedBasis basis):
    ∀ᶠ t in atTop, 0 < f t := by
  apply eventually_pos_of_IsEquivallent (IsEquivalent_leadingTerm h_wo h_approx h_trimmed h_basis)
  exact Term.toFun_pos h_basis h_pos

/-- If `f` is approximated by `ms`, and `ms` is not zero, then
`f` is eventually non-zero. -/
theorem eventually_ne_zero_of_not_zero {basis : Basis} {ms : PreMS basis} {f : ℝ → ℝ}
    (h_ne_zero : ms ≠ zero _) (h_wo : ms.WellOrdered) (h_approx : ms.Approximates f)
    (h_trimmed : ms.Trimmed) (h_basis : WellFormedBasis basis):
    ∀ᶠ t in atTop, f t ≠ 0 := by
  have := IsEquivalent_leadingTerm h_wo h_approx h_trimmed h_basis
  obtain ⟨φ, hφ_tendsto, h_eq⟩ := Asymptotics.IsEquivalent.exists_eq_mul this
  have hφ : ∀ᶠ t in atTop, 1/2 < φ t := by
    apply eventually_gt_of_tendsto_gt _ hφ_tendsto
    linarith
  have h_leadingTerm := leadingTerm_eventually_ne_zero h_trimmed h_ne_zero h_basis
  simp only [EventuallyEq] at h_eq
  apply ((h_eq.and hφ).and h_leadingTerm).mono
  intro t ⟨⟨h_eq, hφ⟩, h_leadingTerm⟩
  rw [h_eq]
  simp
  constructor
  · linarith
  · exact h_leadingTerm

theorem compare_of_leadingTerms {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms1 ms2 : PreMS (basis_hd :: basis_tl)} {f1 f2 : ℝ → ℝ}
    (h_wo1 : ms1.WellOrdered) (h_wo2 : ms2.WellOrdered)
    (h_approx1 : ms1.Approximates f1) (h_approx2 : ms2.Approximates f2)
    (h_trimmed1 : ms1.Trimmed) (h_trimmed2 : ms2.Trimmed)
    (h_basis : WellFormedBasis (basis_hd :: basis_tl))
    (h2 : ms2 ≠ .nil)
    (h_lt : ms1.leadingTerm < ms2.leadingTerm) :
    f1 =o[atTop] f2 := by
  apply Asymptotics.IsEquivalent.trans_isLittleO
    (IsEquivalent_leadingTerm h_wo1 h_approx1 h_trimmed1 h_basis)
  apply Asymptotics.IsLittleO.trans_isEquivalent _
    (IsEquivalent_leadingTerm h_wo2 h_approx2 h_trimmed2 h_basis).symm
  rw [Term.lt_iff] at h_lt
  cases' ms1 with exp1 coef1 tl1
  · convert Asymptotics.isLittleO_zero _ _ using 1
    ext t
    rw [Term.zero_coef_toFun]
    · simp
    unfold leadingTerm
    simp
  cases' ms2 with exp2 coef2 tl2
  · contradiction
  have _ : IsAsymm ℝ (· < ·) := inferInstance
  obtain ⟨h_coef_wo1, h_comp1, h_tl_wo1⟩ := WellOrdered_cons h_wo1
  obtain ⟨h_coef_wo2, h_comp2, h_tl_wo2⟩ := WellOrdered_cons h_wo2
  obtain ⟨fC1, h_coef1, _, h_tl1⟩ := Approximates_cons h_approx1
  obtain ⟨fC2, h_coef2, _, h_tl2⟩ := Approximates_cons h_approx2
  obtain ⟨h_coef_trimmed1, h_coef_ne_zero1⟩ := Trimmed_cons h_trimmed1
  obtain ⟨h_coef_trimmed2, h_coef_ne_zero2⟩ := Trimmed_cons h_trimmed2
  clear h2
  unfold leadingTerm at h_lt
  simp at h_lt
  simp [LT.lt] at h_lt
  cases h_lt with
  | cons h =>
    unfold leadingTerm
    simp
    unfold Term.toFun
    simp
    conv => lhs; ext x; rw [Term.fold_eq_mul, mul_comm _ (basis_hd x ^ exp1), mul_assoc, mul_comm]
    conv => rhs; ext x; rw [Term.fold_eq_mul, mul_comm _ (basis_hd x ^ exp1), mul_assoc, mul_comm]
    apply Asymptotics.IsLittleO.mul_isBigO
    swap
    · apply isBigO_refl
    convert_to (Term.toFun ⟨coef1.leadingTerm.coef, coef1.leadingTerm.exps⟩ basis_tl) =o[atTop]
        Term.toFun ⟨coef2.leadingTerm.coef, coef2.leadingTerm.exps⟩ basis_tl
    · unfold Term.toFun
      ext x
      conv => rhs; rw [Term.fold_eq_mul]
    · unfold Term.toFun
      ext x
      conv => rhs; rw [Term.fold_eq_mul]
    cases' basis_tl with basis_tl_hd basis_tl_tl
    · cases h
    apply Asymptotics.IsEquivalent.trans_isLittleO
      (IsEquivalent_leadingTerm h_coef_wo1 h_coef1 h_coef_trimmed1 h_basis.tail).symm
    apply Asymptotics.IsLittleO.trans_isEquivalent _
      (IsEquivalent_leadingTerm h_coef_wo2 h_coef2 h_coef_trimmed2 h_basis.tail)
    apply compare_of_leadingTerms h_coef_wo1 h_coef_wo2 h_coef1 h_coef2 h_coef_trimmed1
      h_coef_trimmed2 h_basis.tail h_coef_ne_zero2
    simp [LT.lt]
    constructor
    · right
      exact h
    constructor
    · intro h'
      rw [h'] at h
      apply asymm h h
    · apply asymm h
  | rel h =>
    change exp1 < exp2 at h
    apply Asymptotics.isLittleO_of_tendsto'
    · refine (Term.toFun_ne_zero (t := leadingTerm (basis := basis_hd :: basis_tl) (Seq.cons (exp2, coef2) tl2)) h_basis ?_).mono ?_
      · intro h'
        apply zero_of_leadingTerm_zero_coef h_trimmed2 at h'
        simp [zero] at h'
      intro x h1 h2
      contradiction
    simp_rw [div_eq_mul_inv]
    apply Filter.Tendsto.congr' (f₁ := fun x ↦
      (leadingTerm (basis := basis_hd :: basis_tl) (Seq.cons (exp1, coef1) tl1)).toFun (basis_hd :: basis_tl) x *
        ((leadingTerm (basis := basis_hd :: basis_tl) (Seq.cons (exp2, coef2) tl2)).inv.toFun (basis_hd :: basis_tl) x))
    · apply ((leadingTerm (basis := basis_hd :: basis_tl) (Seq.cons (exp2, coef2) tl2)).inv_toFun h_basis).mono
      intro x hx
      simp at hx ⊢
      left
      rw [hx]
    apply Filter.Tendsto.congr' (f₁ :=
        ((leadingTerm (basis := basis_hd :: basis_tl) (Seq.cons (exp1, coef1) tl1)).mul
        (leadingTerm (basis := basis_hd :: basis_tl) (Seq.cons (exp2, coef2) tl2)).inv).toFun (basis_hd :: basis_tl))
    · refine (Term.mul_toFun
        (t1 := leadingTerm (basis := basis_hd :: basis_tl) (Seq.cons (exp1, coef1) tl1))
        (t2 := (leadingTerm (basis := basis_hd :: basis_tl) (Seq.cons (exp2, coef2) tl2)).inv)
        h_basis
        ?_).mono ?_
      · rw [leadingTerm_length, Term.inv_length, leadingTerm_length]
      intro x hx
      simpa using hx
    apply Term.tendsto_zero _ _ _ h_basis
    · simp [leadingTerm_length]
    · simpa

--------------------------------

-- TODO: remove assumptions here using `zero_of_leadingTerm_zero_coef`
theorem tendsto_zero_of_zero_coef {basis : Basis} {ms : PreMS basis} {f : ℝ → ℝ}
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates f)
    (h_trimmed : ms.Trimmed)
    (h_basis : WellFormedBasis basis)
    {t_coef : ℝ} {t_exps : List ℝ}
    (h_eq : ms.leadingTerm = ⟨t_coef, t_exps⟩)
    (h_coef : t_coef = 0) :
    Tendsto f atTop (𝓝 0) := by
  apply (IsEquivalent.tendsto_nhds_iff
    (IsEquivalent_leadingTerm h_wo h_approx h_trimmed h_basis)).mpr
  rw [h_eq]
  apply Term.tendsto_zero_of_coef_zero _ h_coef

theorem tendsto_const_of_AllZero {basis : Basis} {ms : PreMS basis} {f : ℝ → ℝ}
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates f)
    (h_trimmed : ms.Trimmed)
    (h_basis : WellFormedBasis basis)
    {t_coef : ℝ} {t_exps : List ℝ}
    (h_eq : ms.leadingTerm = ⟨t_coef, t_exps⟩)
    (h_exps : Term.AllZero t_exps) :
    Tendsto f atTop (𝓝 t_coef) := by
  apply (IsEquivalent.tendsto_nhds_iff
    (IsEquivalent_leadingTerm h_wo h_approx h_trimmed h_basis)).mpr
  rw [h_eq]
  apply Term.tendsto_const_of_AllZero _ h_exps
  · convert leadingTerm_length (ms := ms)
    simp [h_eq]

theorem tendsto_zero_of_FirstIsNeg {basis : Basis} {ms : PreMS basis} {f : ℝ → ℝ}
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates f)
    {t_coef : ℝ} {t_exps : List ℝ}
    (h_eq : ms.leadingTerm = ⟨t_coef, t_exps⟩)
    (h_exps : Term.FirstIsNeg t_exps) :
    Tendsto f atTop (𝓝 0) := by
  cases' basis with basis_hd basis_tl
  · simp [leadingTerm] at h_eq
    simp [h_eq.right, Term.FirstIsNeg] at h_exps
  cases' ms with exp coef tl
  · apply Approximates_nil at h_approx
    apply Tendsto.congr' h_approx.symm
    apply tendsto_const_nhds
  · obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
    obtain ⟨fC, h_coef_approx, h_maj, h_tl_approx⟩ := Approximates_cons h_approx
    simp [leadingTerm] at h_eq
    simp [← h_eq.right, Term.FirstIsNeg] at h_exps
    cases' h_exps with h_neg h_zero
    · exact majorated_tendsto_zero_of_neg h_neg h_maj
    have hC : Tendsto fC atTop (𝓝 0) := by
      apply tendsto_zero_of_FirstIsNeg (t_coef := t_coef) h_coef_wo h_coef_approx _ h_zero.right
      rw [← h_eq.left]
    have h_tl : Tendsto (f - fC) atTop (𝓝 0) := by
      have h : Tendsto (fun t ↦ f t - basis_hd t ^ exp * fC t) atTop (𝓝 0) := by
        apply neg_leadingExp_tendsto_zero _ h_tl_approx
        convert h_comp
        simp [h_zero.left]
      apply Tendsto.congr' _ h
      simp [h_zero.left]
      rfl
    simpa using Tendsto.add h_tl hC

theorem tendsto_top_of_FirstIsPos {basis : Basis} {ms : PreMS basis} {f : ℝ → ℝ}
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates f)
    (h_trimmed : ms.Trimmed)
    (h_basis : WellFormedBasis basis)
    {t_coef : ℝ} {t_exps : List ℝ}
    (h_eq : ms.leadingTerm = ⟨t_coef, t_exps⟩)
    (h_exps : Term.FirstIsPos t_exps)
    (h_coef : 0 < t_coef) :
    Tendsto f atTop atTop := by
  apply (IsEquivalent.tendsto_atTop_iff
    (IsEquivalent_leadingTerm h_wo h_approx h_trimmed h_basis)).mpr
  apply Term.tendsto_top_of_FirstIsPos h_basis leadingTerm_length
  all_goals simpa [h_eq]

theorem tendsto_bot_of_FirstIsPos {basis : Basis} {ms : PreMS basis} {f : ℝ → ℝ}
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates f)
    (h_trimmed : ms.Trimmed)
    (h_basis : WellFormedBasis basis)
    {t_coef : ℝ} {t_exps : List ℝ}
    (h_eq : ms.leadingTerm = ⟨t_coef, t_exps⟩)
    (h_exps : Term.FirstIsPos t_exps)
    (h_coef : t_coef < 0) :
    Tendsto f atTop atBot := by
  apply (IsEquivalent.tendsto_atBot_iff
    (IsEquivalent_leadingTerm h_wo h_approx h_trimmed h_basis)).mpr
  apply Term.tendsto_bot_of_FirstIsPos h_basis leadingTerm_length
  all_goals simpa [h_eq]

------------------------------------------------------------------

lemma extendBasisEnd_zero_last_exp_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {b : ℝ → ℝ}
    {ms : PreMS (basis_hd :: basis_tl)} :
    (ms.extendBasisEnd b).leadingTerm.exps.getLast (leadingTerm_ne_nil) = 0 := by
  cases' ms with exp coef tl
  · simp [extendBasisEnd, leadingTerm, PreMS.const]
  cases' basis_tl with basis_tl_hd basis_tl_tl
  · simp [extendBasisEnd, leadingTerm, PreMS.const]
  have ih := extendBasisEnd_zero_last_exp_cons (ms := coef) (b := b)
  simp [extendBasisEnd, leadingTerm]
  cases' coef with coef_exp coef_coef coef_tl
  · simp
  simp
  simp [extendBasisEnd, leadingTerm] at ih
  exact ih

theorem extendBasisEnd_zero_last_exp {basis : Basis} {b : ℝ → ℝ} {ms : PreMS basis} :
    ∀ a, (ms.extendBasisEnd b).leadingTerm.exps.getLast? = .some a → a = 0 := by
  intro a h
  cases' basis with basis_hd basis_tl
  · simp [extendBasisEnd, leadingTerm, PreMS.const] at h
    rw [h]
  · simp [List.getLast?_eq_getLast _ leadingTerm_ne_nil, extendBasisEnd_zero_last_exp_cons] at h
    rw [h]

end PreMS

end TendstoTactic
