/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Tactic.Tendsto.Multiseries.Term
import Mathlib.Tactic.Tendsto.Multiseries.Trimming

/-!
Here we find the limit of series by reducing the problem to computing limits for its leading
term.
-/

open Filter Asymptotics

namespace TendstoTactic

namespace PreMS

open Stream' Seq

def leadingTerm {basis : Basis} (ms : PreMS basis) : MS.Term :=
  match basis with
  | [] => ⟨ms, []⟩
  | List.cons _ _ =>
    match destruct ms with
    | none => ⟨0, List.range basis.length |>.map fun _ => 0⟩
    | some ((exp, coef), _) =>
      let pre := coef.leadingTerm
      ⟨pre.coef, exp :: pre.exps⟩

theorem leadingTerm_length {basis : Basis} {ms : PreMS basis} :
    ms.leadingTerm.exps.length = basis.length :=
  match basis with
  | [] => by simp [leadingTerm]
  | List.cons basis_hd basis_tl => by
    cases ms <;> simp [leadingTerm, leadingTerm_length]

theorem leadingTerm_cons_toFun {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} (x : ℝ) :
    (leadingTerm (basis := basis_hd :: basis_tl) (Seq.cons (exp, coef) tl)).toFun
      (basis_hd :: basis_tl) x =
    (basis_hd x)^exp * (leadingTerm coef).toFun basis_tl x := by
  simp [leadingTerm, MS.Term.toFun]
  conv =>
    congr <;> rw [MS.Term.fun_mul]
    lhs
    rw [mul_comm] -- why do I need these rws? Why ring_nf can't solve the goal?
  rw [← mul_assoc]

theorem leadingTerm_eventually_ne_zero {basis : Basis} {ms : PreMS basis}
    (h_trimmed : ms.Trimmed) (h_ne_zero : ¬ ms.FlatZero)
    (h_basis : MS.WellOrderedBasis basis) :
    ∀ᶠ x in atTop, ms.leadingTerm.toFun basis x ≠ 0 := by
  cases basis with
  | nil =>
    unfold leadingTerm
    simp [MS.Term.toFun]
    use default
    intros
    intro
    absurd h_ne_zero
    constructor
    assumption
  | cons basis_hd basis_tl =>
    cases' ms with exp coef tl
    · absurd h_ne_zero
      constructor
    · obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := Trimmed_cons h_trimmed
      let coef_ih := coef.leadingTerm_eventually_ne_zero h_coef_trimmed h_coef_ne_zero
        (MS.WellOrderedBasis_tail h_basis)
      apply Eventually.mono <| coef_ih.and (MS.basis_head_eventually_pos h_basis)
      rintro x ⟨coef_ih, h_basis_hd_pos⟩
      simp [leadingTerm, MS.Term.toFun, -ne_eq]
      simp only [MS.Term.toFun] at coef_ih
      conv =>
        rw [MS.Term.fun_mul]
        lhs
        lhs
        rw [mul_comm]
      rw [mul_assoc]
      rw [MS.Term.fun_mul] at coef_ih
      apply mul_ne_zero
      · exact (Real.rpow_pos_of_pos h_basis_hd_pos _).ne.symm
      · exact coef_ih

-- TODO: rewrite without mutual
mutual
  theorem IsEquivalent_coef {basis_hd C F : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
      {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
      (h_coef : coef.Approximates C)
      (h_coef_wo : coef.WellOrdered)
      (h_coef_trimmed : coef.Trimmed)
      (h_coef_ne_zero : ¬coef.FlatZero)
      (h_tl : tl.Approximates (fun x ↦ F x - (basis_hd x)^exp * C x))
      (h_comp : leadingExp tl < ↑exp)
      (h_basis : MS.WellOrderedBasis (basis_hd :: basis_tl)) :
      F ~[atTop] fun x ↦ (basis_hd x)^exp * (C x) := by
    have coef_ih := coef.IsEquivalent_leadingTerm (F := C) h_coef_wo h_coef h_coef_trimmed
      (MS.WellOrderedBasis_tail h_basis)
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
        · have : (fun x ↦ basis_hd x ^ exp / basis_hd x ^ exp') =ᶠ[atTop]
              fun x ↦ (basis_hd x)^(exp - exp') := by
            apply Eventually.mono <| MS.basis_head_eventually_pos h_basis
            intro x h
            simp only
            rw [← Real.rpow_sub h]
          apply IsLittleO.trans_eventuallyEq _ this.symm
          have := IsEquivalent.inv coef_ih
          apply IsEquivalent.trans_isLittleO this
          apply EventuallyEq.trans_isLittleO (MS.Term.fun_inv ((MS.WellOrderedBasis_tail h_basis)))
          apply MS.Term.tail_fun_IsLittleO_head
          · rw [MS.Term.inv_length, PreMS.leadingTerm_length]
          · exact h_basis
          · simp only [exp']
            linarith
        · apply Eventually.mono <| MS.basis_head_eventually_pos h_basis
          intro x h1 h2
          absurd h2
          apply div_ne_zero <;> exact (Real.rpow_pos_of_pos h1 _).ne.symm
      · have h_C_ne_zero : ∀ᶠ x in atTop, C x ≠ 0 := by
          obtain ⟨φ, h_φ, h_C⟩ := Asymptotics.IsEquivalent.exists_eq_mul coef_ih
          have h_φ_pos : ∀ᶠ x in atTop, 0 < φ x := by
            apply eventually_gt_of_tendsto_gt (by simp) h_φ
          apply EventuallyEq.rw (p := fun _ b => b ≠ 0) h_C.symm
          apply Eventually.mono <| h_φ_pos.and (leadingTerm_eventually_ne_zero
            h_coef_trimmed h_coef_ne_zero ((MS.WellOrderedBasis_tail h_basis)))
          rintro x ⟨h_φ_pos, h⟩
          exact mul_ne_zero h_φ_pos.ne.symm h
        apply Eventually.mono <| h_C_ne_zero.and
          (MS.basis_head_eventually_pos h_basis)
        rintro x ⟨h_C_ne_zero, h_basis_pos⟩
        intro h
        absurd h
        apply mul_ne_zero _ h_C_ne_zero
        exact (Real.rpow_pos_of_pos h_basis_pos _).ne.symm

  theorem IsEquivalent_leadingTerm {basis : Basis} {ms : PreMS basis} {F : ℝ → ℝ}
      (h_wo : ms.WellOrdered)
      (h_approx : ms.Approximates F) (h_trimmed : ms.Trimmed)
      (h_basis : MS.WellOrderedBasis basis)
      : F ~[atTop] ms.leadingTerm.toFun basis := by
    cases basis with
    | nil =>
      simp [Approximates] at h_approx
      simp [leadingTerm]
      apply EventuallyEq.isEquivalent (by assumption)
    | cons basis_hd basis_tl =>
      cases' ms with exp coef tl
      · have hF := Approximates_nil h_approx
        unfold leadingTerm
        simp [MS.Term.zero_coef_fun]
        apply EventuallyEq.isEquivalent (by assumption)
      · obtain ⟨C, h_coef, _, h_tl⟩ := Approximates_cons h_approx
        obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := Trimmed_cons h_trimmed
        obtain ⟨h_coef_wo, h_comp, _⟩ := WellOrdered_cons h_wo
        have coef_ih := coef.IsEquivalent_leadingTerm (F := C) h_coef_wo h_coef h_coef_trimmed
          (MS.WellOrderedBasis_tail h_basis)
        have : F ~[atTop] fun x ↦ (basis_hd x)^exp * (C x) :=
          PreMS.IsEquivalent_coef h_coef h_coef_wo h_coef_trimmed h_coef_ne_zero h_tl h_comp h_basis
        apply IsEquivalent.trans this
        eta_expand
        simp_rw [PreMS.leadingTerm_cons_toFun]
        apply IsEquivalent.mul IsEquivalent.refl
        exact coef_ih
end

theorem eventually_ne_zero_of_not_FlatZero {basis : Basis} {ms : PreMS basis} {F : ℝ → ℝ}
    (h_ne_zero : ¬ ms.FlatZero) (h_wo : ms.WellOrdered) (h_approx : ms.Approximates F)
    (h_trimmed : ms.Trimmed) (h_basis : MS.WellOrderedBasis basis):
    ∀ᶠ x in atTop, F x ≠ 0 := by
  have := IsEquivalent_leadingTerm h_wo h_approx h_trimmed h_basis
  obtain ⟨φ, ⟨hφ_tendsto, h_eq⟩⟩ := Asymptotics.IsEquivalent.exists_eq_mul this
  have hφ : ∀ᶠ x in atTop, 1/2 < φ x := by
    apply eventually_gt_of_tendsto_gt _ hφ_tendsto
    linarith
  have h_leadingTerm := leadingTerm_eventually_ne_zero h_trimmed h_ne_zero h_basis
  simp only [EventuallyEq] at h_eq
  apply Eventually.mono <| (h_eq.and hφ).and h_leadingTerm
  intro x ⟨⟨h_eq, hφ⟩, h_leadingTerm⟩
  rw [h_eq]
  simp
  constructor
  · linarith
  · exact h_leadingTerm

end PreMS

def MS.leadingTerm (ms : MS) : MS.Term :=
  PreMS.leadingTerm ms.val

theorem MS.leadingTerm_length {ms : MS} : ms.leadingTerm.exps.length = ms.basis.length := by
  apply PreMS.leadingTerm_length

theorem MS.IsEquivalent_leadingTerm (ms : MS) (h_basis : MS.WellOrderedBasis ms.basis)
    (h_trimmed : ms.Trimmed) : ms.F ~[atTop] ms.leadingTerm.toFun ms.basis := by
  apply PreMS.IsEquivalent_leadingTerm ms.h_wo ms.h_approx h_trimmed h_basis

noncomputable def MS.findLimitTrimmed (ms : MS) (h_basis : MS.WellOrderedBasis ms.basis)
    (h_trimmed : ms.Trimmed) :
    FindLimitResult ms.F :=
  let r := ms.leadingTerm.findLimit (basis := ms.basis) (by apply MS.leadingTerm_length) h_basis
  match r with
  | .top p => .top (by {
      exact (IsEquivalent.tendsto_atTop_iff
        (MS.IsEquivalent_leadingTerm ms h_basis h_trimmed)).mpr p
    })
  | .bot p => .bot (by {
      exact (IsEquivalent.tendsto_atBot_iff
        (MS.IsEquivalent_leadingTerm ms h_basis h_trimmed)).mpr p
    })
  | .fin c p => .fin c (by {
      exact IsEquivalent.tendsto_nhds (MS.IsEquivalent_leadingTerm ms h_basis h_trimmed).symm p
    })

-- def MS.findLimit (ms : MS) (h_basis : MS.WellOrderedBasis ms.basis) :
--     TendstoM <| FindLimitResult ms.F := do
--   let trimmed ← MS.trim ms
--   let r ← MS.findLimitTrimmed trimmed.result (trimmed.h_eq_basis ▸ h_basis) trimmed.h_trimmed
--   return (trimmed.h_eq_F ▸ r)

end TendstoTactic
