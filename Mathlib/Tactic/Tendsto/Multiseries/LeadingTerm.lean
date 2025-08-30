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

lemma Term.IsLittleO_of_lt_exps {basis : Basis} {t1 t2 : Term}
    (h_basis : WellFormedBasis basis)
    (h1 : t1.exps.length = basis.length)
    (h2 : t2.exps.length = basis.length)
    (h_coef2 : t2.coef ≠ 0)
    (h_lt : t1.exps < t2.exps) :
    t1.toFun basis =o[atTop] t2.toFun basis := by
  obtain ⟨coef1, exps1⟩ := t1
  obtain ⟨coef2, exps2⟩ := t2
  simp at h1 h2 h_lt h_coef2
  cases' basis with basis_hd basis_tl
  · simp at h1 h2
    simp [h1, h2] at h_lt
  cases' exps1 with exp1 exps1_tl
  · simp at h1
  cases' exps2 with exp2 exps2_tl
  · simp at h2
  cases h_lt with
  | cons h =>
    unfold Term.toFun
    simp
    conv => lhs; ext x; rw [Term.fold_eq_mul, mul_comm _ (basis_hd x ^ exp1), mul_assoc, mul_comm]
    conv => rhs; ext x; rw [Term.fold_eq_mul, mul_comm _ (basis_hd x ^ exp1), mul_assoc, mul_comm]
    apply Asymptotics.IsLittleO.mul_isBigO
    swap
    · apply isBigO_refl
    convert_to (Term.toFun ⟨coef1, exps1_tl⟩ basis_tl) =o[atTop]
        Term.toFun ⟨coef2, exps2_tl⟩ basis_tl
    · unfold Term.toFun
      ext x
      conv => rhs; rw [Term.fold_eq_mul]
    · unfold Term.toFun
      ext x
      conv => rhs; rw [Term.fold_eq_mul]
    exact Term.IsLittleO_of_lt_exps h_basis.tail (by simpa using h1) (by simpa using h2)
      (by simpa) h
  | rel h =>
    apply Asymptotics.isLittleO_of_tendsto'
    · apply (Term.toFun_ne_zero (t := ⟨coef2, exp2 :: exps2_tl⟩) h_basis (by simpa)).mono
      intro x h1 h2
      contradiction
    simp_rw [div_eq_mul_inv]
    apply Filter.Tendsto.congr' (f₁ := fun x ↦
      (Term.toFun ⟨coef1, exp1 :: exps1_tl⟩ (basis_hd :: basis_tl)) x *
        (Term.toFun (Term.inv ⟨coef2, exp2 :: exps2_tl⟩) (basis_hd :: basis_tl)) x)
    · apply ((Term.inv_toFun (t := ⟨coef2, exp2 :: exps2_tl⟩) h_basis)).mono
      intro x hx
      simp at hx ⊢
      left
      rw [hx]
    simp at h1 h2
    apply Filter.Tendsto.congr' (f₁ :=
      ((Term.mk coef1 (exp1 :: exps1_tl)).mul
      (Term.mk coef2 (exp2 :: exps2_tl)).inv).toFun (basis_hd :: basis_tl))
    · refine (Term.mul_toFun
        (t1 := Term.mk coef1 (exp1 :: exps1_tl))
        (t2 := Term.inv ⟨coef2, exp2 :: exps2_tl⟩)
        h_basis
        ?_).mono ?_
      · simp [Term.inv_length,h1, h2]
      intro x hx
      simpa using hx
    apply Term.tendsto_zero _ _ _ h_basis
    · simp [h1, h2]
    · simpa

theorem Term.IsLittleO_of_lt_exps_left {left right : Basis} {t1 t2 : Term}
    (h_basis : WellFormedBasis (left ++ right))
    (h1 : t1.exps.length = left.length + right.length)
    (h2 : t2.exps.length = right.length)
    (h_coef2 : t2.coef ≠ 0)
    (h_lt : t1.exps < List.replicate left.length 0 ++ t2.exps) :
    t1.toFun (left ++ right) =o[atTop] t2.toFun right := by
  obtain ⟨coef2, exps2⟩ := t2
  let t2' : Term := ⟨coef2, List.replicate left.length 0 ++ exps2⟩
  have : t2'.toFun (left ++ right) = Term.toFun ⟨coef2, exps2⟩ right := Term.zeros_append_toFun _ h2
  rw [← this]
  apply Term.IsLittleO_of_lt_exps h_basis <;> simpa

theorem Term.IsLittleO_of_lt_exps_right {left right : Basis} {t1 t2 : Term}
    (h_basis : WellFormedBasis (left ++ right))
    (h1 : t1.exps.length = left.length + right.length)
    (h2 : t2.exps.length = right.length)
    (h_coef1 : t1.coef ≠ 0)
    (h_lt : List.replicate left.length 0 ++ t2.exps < t1.exps) :
    t2.toFun right =o[atTop] t1.toFun (left ++ right) := by
  obtain ⟨coef2, exps2⟩ := t2
  let t2' : Term := ⟨coef2, List.replicate left.length 0 ++ exps2⟩
  have : t2'.toFun (left ++ right) = Term.toFun ⟨coef2, exps2⟩ right := Term.zeros_append_toFun _ h2
  rw [← this]
  apply Term.IsLittleO_of_lt_exps h_basis <;> simpa

theorem IsLittleO_of_lt_leadingTerm_left {left right : Basis}
    {ms1 : PreMS (left ++ right)} {ms2 : PreMS right} {f1 f2 : ℝ → ℝ}
    (h_wo1 : ms1.WellOrdered) (h_wo2 : ms2.WellOrdered)
    (h_approx1 : ms1.Approximates f1) (h_approx2 : ms2.Approximates f2)
    (h_trimmed1 : ms1.Trimmed) (h_trimmed2 : ms2.Trimmed)
    (h_basis : WellFormedBasis (left ++ right))
    (h2 : ms2 ≠ zero _)
    (h_lt : ms1.leadingTerm.exps < List.replicate left.length 0 ++ ms2.leadingTerm.exps) :
    f1 =o[atTop] f2 := by
  apply Asymptotics.IsEquivalent.trans_isLittleO
    (IsEquivalent_leadingTerm h_wo1 h_approx1 h_trimmed1 h_basis)
  apply Asymptotics.IsLittleO.trans_isEquivalent _
    (IsEquivalent_leadingTerm h_wo2 h_approx2 h_trimmed2 h_basis.of_append_right).symm
  apply Term.IsLittleO_of_lt_exps_left h_basis _ _ _ h_lt
  · simp [leadingTerm_length]
  · simp [leadingTerm_length]
  · contrapose! h2
    exact zero_of_leadingTerm_zero_coef h_trimmed2 h2

theorem IsLittleO_of_lt_leadingTerm_right {left right : Basis}
    {ms1 : PreMS (left ++ right)} {ms2 : PreMS right} {f1 f2 : ℝ → ℝ}
    (h_wo1 : ms1.WellOrdered) (h_wo2 : ms2.WellOrdered)
    (h_approx1 : ms1.Approximates f1) (h_approx2 : ms2.Approximates f2)
    (h_trimmed1 : ms1.Trimmed) (h_trimmed2 : ms2.Trimmed)
    (h_basis : WellFormedBasis (left ++ right))
    (h1 : ms1 ≠ zero _)
    (h_lt : List.replicate left.length 0 ++ ms2.leadingTerm.exps < ms1.leadingTerm.exps) :
    f2 =o[atTop] f1 := by
  apply Asymptotics.IsEquivalent.trans_isLittleO
    (IsEquivalent_leadingTerm h_wo2 h_approx2 h_trimmed2 h_basis.of_append_right)
  apply Asymptotics.IsLittleO.trans_isEquivalent _
    (IsEquivalent_leadingTerm h_wo1 h_approx1 h_trimmed1 h_basis).symm
  apply Term.IsLittleO_of_lt_exps_right h_basis _ _ _ h_lt
  · simp [leadingTerm_length]
  · simp [leadingTerm_length]
  · contrapose! h1
    exact zero_of_leadingTerm_zero_coef h_trimmed1 h1


theorem IsLittleO_of_lt_leadingTerm {basis : Basis}
    {ms1 ms2 : PreMS basis} {f1 f2 : ℝ → ℝ}
    (h_wo1 : ms1.WellOrdered) (h_wo2 : ms2.WellOrdered)
    (h_approx1 : ms1.Approximates f1) (h_approx2 : ms2.Approximates f2)
    (h_trimmed1 : ms1.Trimmed) (h_trimmed2 : ms2.Trimmed)
    (h_basis : WellFormedBasis basis)
    (h2 : ms2 ≠ zero _)
    (h_lt : ms1.leadingTerm.exps < ms2.leadingTerm.exps) :
    f1 =o[atTop] f2 :=
  IsLittleO_of_lt_leadingTerm_left (left := []) h_wo1 h_wo2 h_approx1 h_approx2 h_trimmed1
    h_trimmed2 h_basis h2 h_lt

theorem IsEquivalent_of_leadingTerm_zeros_append {left right : Basis}
    {ms1 : PreMS (left ++ right)} {ms2 : PreMS right} {f1 f2 : ℝ → ℝ}
    (h_wo1 : ms1.WellOrdered) (h_wo2 : ms2.WellOrdered)
    (h_approx1 : ms1.Approximates f1) (h_approx2 : ms2.Approximates f2)
    (h_trimmed1 : ms1.Trimmed) (h_trimmed2 : ms2.Trimmed)
    (h_basis : WellFormedBasis (left ++ right))
    (h_coef : ms1.leadingTerm.coef = ms2.leadingTerm.coef)
    (h_exps : List.replicate left.length 0 ++ ms2.leadingTerm.exps = ms1.leadingTerm.exps) :
    f1 ~[atTop] f2 := by
  apply Asymptotics.IsEquivalent.trans
    (IsEquivalent_leadingTerm h_wo1 h_approx1 h_trimmed1 h_basis)
  apply Asymptotics.IsEquivalent.trans _
    (IsEquivalent_leadingTerm h_wo2 h_approx2 h_trimmed2 h_basis.of_append_right).symm
  convert Asymptotics.IsEquivalent.refl using 1
  let t2' : Term := ⟨ms2.leadingTerm.coef, List.replicate left.length 0 ++ ms2.leadingTerm.exps⟩
  have : t2'.toFun (left ++ right) = Term.toFun ms2.leadingTerm right := by
    apply Term.zeros_append_toFun
    simp [leadingTerm_length]
  rw [← this]
  congr!
  simp [t2']
  conv => rhs; change ⟨ms1.leadingTerm.coef, ms1.leadingTerm.exps⟩
  congr 1
  rw [h_coef]

theorem IsEquivalent_of_leadingTerm_zeros_append_mul_coef {left right : Basis}
    {ms1 : PreMS (left ++ right)} {ms2 : PreMS right} {f1 f2 : ℝ → ℝ}
    (h_wo1 : ms1.WellOrdered) (h_wo2 : ms2.WellOrdered)
    (h_approx1 : ms1.Approximates f1) (h_approx2 : ms2.Approximates f2)
    (h_trimmed1 : ms1.Trimmed) (h_trimmed2 : ms2.Trimmed)
    (h_basis : WellFormedBasis (left ++ right))
    (h_coef : ms1.leadingTerm.coef / ms2.leadingTerm.coef ≠ 0)
    (h_exps : List.replicate left.length 0 ++ ms2.leadingTerm.exps = ms1.leadingTerm.exps) :
    f1 ~[atTop] (ms1.leadingTerm.coef / ms2.leadingTerm.coef) • f2 := by
  apply Asymptotics.IsEquivalent.trans
    (IsEquivalent_leadingTerm h_wo1 h_approx1 h_trimmed1 h_basis)
  trans (ms1.leadingTerm.coef / ms2.leadingTerm.coef) • (ms2.leadingTerm.toFun right)
  swap
  · have h_eq := (IsEquivalent_leadingTerm h_wo2 h_approx2 h_trimmed2 h_basis.of_append_right).symm
    have : (fun (_ : ℝ) ↦ ms1.leadingTerm.coef / ms2.leadingTerm.coef) ~[atTop]
        (fun _ ↦ ms1.leadingTerm.coef / ms2.leadingTerm.coef) := by
      rfl
    convert Asymptotics.IsEquivalent.smul this h_eq using 1
  convert Asymptotics.IsEquivalent.refl using 1
  let t2' : Term := ⟨ms2.leadingTerm.coef, List.replicate left.length 0 ++ ms2.leadingTerm.exps⟩
  have : t2'.toFun (left ++ right) = Term.toFun ms2.leadingTerm right := by
    apply Term.zeros_append_toFun
    simp [leadingTerm_length]
  rw [← this, ← Term.smul_toFun]
  congr!
  simp [t2']
  rw [mul_div_cancel₀]
  contrapose! h_coef
  simp [h_coef]

theorem FirstIsPos_ne_zero {basis : Basis} {ms : PreMS basis}
    (h_pos : Term.FirstIsPos ms.leadingTerm.exps) :
    ms ≠ zero _ := by
  intro h
  cases' basis with basis_hd basis_tl
  · simp [leadingTerm] at h_pos
    cases h_pos
  · apply Term.not_FirstIsPos_of_AllZero _ h_pos
    simp [h, zero, leadingTerm]
    exact Term.AllZero_of_replicate

theorem const_leadingTerm_eq {basis : Basis} {c : ℝ} :
    (PreMS.const basis c).leadingTerm = ⟨c, List.replicate basis.length 0⟩ := by
  cases' basis with basis_hd basis_tl
  · simp [const, leadingTerm]
  · simp [const, leadingTerm, const_leadingTerm_eq, List.replicate_succ]

theorem monomial_rpow_leadingTerm_eq {basis : Basis} {n : ℕ} (h : n < basis.length) (r : ℝ) :
    (PreMS.monomial_rpow basis n r).leadingTerm =
    ⟨1, List.replicate n 0 ++ r :: List.replicate (basis.length - n - 1) 0⟩ := by
  cases' basis with basis_hd basis_tl
  · simp at h
  cases' n with n
  · simp [monomial_rpow, leadingTerm, one, const_leadingTerm_eq]
  · simp [monomial_rpow, leadingTerm, monomial_rpow_leadingTerm_eq (by simpa using h) r,
      List.replicate_succ]

theorem monomial_leadingTerm_eq {basis : Basis} {n : ℕ} (h : n < basis.length) :
    (PreMS.monomial basis n).leadingTerm =
      ⟨1, List.replicate n 0 ++ 1 :: List.replicate (basis.length - n - 1) 0⟩ :=
  monomial_rpow_leadingTerm_eq h 1

theorem extendBasisEnd_leadingTerm_eq {basis : Basis} {b : ℝ → ℝ} {ms : PreMS basis} :
    (ms.extendBasisEnd b).leadingTerm = ⟨ms.leadingTerm.coef, ms.leadingTerm.exps ++ [0]⟩ := by
  cases' basis with basis_hd basis_tl
  · simp [extendBasisEnd, leadingTerm, const]
  cases' ms with exp coef tl
  · simp [extendBasisEnd, leadingTerm, List.replicate_succ']
  simp [extendBasisEnd, leadingTerm, extendBasisEnd_leadingTerm_eq]

lemma log_basis_getLast_IsLittleO_aux {basis : Basis}
    {ms : PreMS basis}
    (h_pos : Term.FirstIsPos ms.leadingTerm.exps) :
    basis ≠ [] := by
  contrapose! h_pos
  subst h_pos
  exact id

theorem log_basis_getLast_IsLittleO {basis : Basis} (h_basis : WellFormedBasis basis)
    {ms : PreMS basis} {f : ℝ → ℝ} (h_wo : ms.WellOrdered) (h_approx : ms.Approximates f)
    (h_trimmed : ms.Trimmed) (h_pos : Term.FirstIsPos ms.leadingTerm.exps) :
    (Real.log ∘ (basis.getLast (log_basis_getLast_IsLittleO_aux h_pos))) =o[atTop] f := by
  cases' basis with basis_hd basis_tl
  · simp [leadingTerm] at h_pos
    cases h_pos
  have h_basis' := insertLastLog_WellFormedBasis h_basis
  let ms' : PreMS (basis_hd :: basis_tl ++ [Real.log ∘ (basis_hd :: basis_tl).getLast (by simp)]) :=
    ms.extendBasisEnd (Real.log ∘ (basis_hd :: basis_tl).getLast (by simp))
  have h_wo' : ms'.WellOrdered := PreMS.extendBasisEnd_WellOrdered h_wo
  have h_approx' : ms'.Approximates f := PreMS.extendBasisEnd_Approximates h_basis' h_approx
  have h_trimmed' : ms'.Trimmed := extendBasisEnd_Trimmed h_trimmed
  let ms_log :
      PreMS (basis_hd :: basis_tl ++ [Real.log ∘ (basis_hd :: basis_tl).getLast (by simp)]) :=
    PreMS.monomial _ (basis_tl.length + 1)
  have h_log_wo : ms_log.WellOrdered := monomial_WellOrdered
  have h_log_approx : ms_log.Approximates (Real.log ∘
      ((basis_hd :: basis_tl).getLast (log_basis_getLast_IsLittleO_aux h_pos))) := by
    convert monomial_Approximates (n := ⟨basis_tl.length + 1, by simp⟩) h_basis'
    simp
  have h_log_trimmed : ms_log.Trimmed := monomial_Trimmed (by simp)
  apply IsLittleO_of_lt_leadingTerm h_log_wo h_wo' h_log_approx h_approx' h_log_trimmed
    h_trimmed' h_basis'
  · exact extendBasisEnd_ne_zero (FirstIsPos_ne_zero h_pos)
  simp only [ms_log, ms']
  rw [monomial_leadingTerm_eq (by simp)]
  simp [extendBasisEnd_leadingTerm_eq]
  have h_len : ms.leadingTerm.exps.length = basis_tl.length + 1 := by
    simp [leadingTerm_length]
  clear * - h_pos h_len
  generalize ms.leadingTerm.exps = exps at *
  generalize basis_tl.length + 1 = n at *
  induction n generalizing exps with
  | zero =>
    simp at h_len
    simp [h_len] at h_pos
    cases h_pos
  | succ n ih =>
    cases' exps with exp exps_tl <;> simp at h_len
    rcases h_pos with h_pos | ⟨rfl, h_pos⟩
    · exact List.Lex.rel h_pos
    apply List.Lex.cons
    apply ih _ h_pos h_len

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
