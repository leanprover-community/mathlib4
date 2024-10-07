import Mathlib.Tactic.Tendsto.Multiseries.Term
import Mathlib.Tactic.Tendsto.Multiseries.Trimming


/-!
Here we find the limit of series by reducing the problem to computing limits for series' leading
term.
-/

set_option linter.unusedVariables false
set_option linter.style.longLine false

open Filter Asymptotics

namespace TendstoTactic

namespace PreMS

def leadingTerm {basis : Basis} (ms : PreMS basis) : MS.Term :=
  match basis with
  | [] => ⟨ms, []⟩
  | _ :: _ =>
    ms.casesOn'
    (nil := ⟨0, List.range basis.length |>.map fun _ => 0⟩)
    (cons := fun (deg, coef) _ =>
      let pre := coef.leadingTerm
      ⟨pre.coef, deg :: pre.degs⟩
    )

theorem leadingTerm_length {basis : Basis} (ms : PreMS basis) :
    ms.leadingTerm.degs.length = basis.length :=
  match basis with
  | [] => by simp [leadingTerm]
  | basis_hd :: basis_tl => by
    apply ms.casesOn
    · simp [leadingTerm, CoList.casesOn', CoList.casesOn_nil]
    · simp [leadingTerm, CoList.casesOn', CoList.casesOn_cons]
      exact leadingTerm_length

theorem leadingTerm_cons_toFun {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} (x : ℝ) :
    (leadingTerm (basis := basis_hd :: basis_tl) (CoList.cons (deg, coef) tl)).toFun
      (basis_hd :: basis_tl) x =
    (basis_hd x)^deg * (leadingTerm coef).toFun basis_tl x := by
  simp [leadingTerm, MS.Term.toFun, CoList.casesOn', CoList.casesOn_cons]
  conv =>
    congr <;> rw [MS.Term.fun_mul]
    lhs
    rw [mul_comm] -- why do I need these rws? Why ring_nf can't solve the goal?
  rw [← mul_assoc]

-- somehow I avoided it
-- lemma PreMS.leadingTerm_coef_ne_zero {basis : Basis} {ms : PreMS}
--     (h_depth : ms.hasDepth basis.length) (h_wo : ms.wellOrdered) (h_trimmed : ms.isTrimmed)
--     (h_basis : MS.wellOrderedBasis basis) :
--     (ms.leadingTerm h_depth).coef ≠ 0 := by
--   induction ms using PreMS.rec' generalizing basis with
--   | nil =>
--     simp [isTrimmed] at h_trimmed
--   | const c =>
--     simp [isTrimmed] at h_trimmed
--     unfold leadingTerm
--     simpa
--   | cons deg coef tl coef_ih _ =>
--     cases basis with
--     | nil => simp [hasDepth] at h_depth
--     | cons basis_hd basis_tl =>
--       simp [leadingTerm]
--       simp [wellOrdered] at h_wo
--       simp [isTrimmed] at h_trimmed
--       simp [MS.wellOrderedBasis] at h_basis
--       exact coef_ih _ h_wo.left h_trimmed h_basis.right.left

theorem leadingTerm_eventually_ne_zero {basis : Basis} {ms : PreMS basis}
    (h_wo : ms.wellOrdered) (h_trimmed : ms.isTrimmed) (h_ne_zero : ¬ ms.isFlatZero)
    (h_basis : MS.wellOrderedBasis basis) :
    ∀ᶠ x in atTop, ms.leadingTerm.toFun basis x ≠ 0 :=
  match basis with
  | [] => by
    unfold leadingTerm
    simp [MS.Term.toFun]
    use default
    intros
    intro
    absurd h_ne_zero
    constructor
    assumption
  | basis_hd :: basis_tl => by
    revert h_wo h_ne_zero h_trimmed
    apply ms.casesOn
    · intro _ _ h_ne_zero
      absurd h_ne_zero
      constructor
    · intro (deg, coef) tl h_wo h_trimmed _
      replace h_wo := wellOrdered_cons h_wo
      obtain ⟨h_coef_wo, _, _⟩ := h_wo
      obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := isTrimmed_cons h_trimmed
      simp [MS.wellOrderedBasis] at h_basis
      let coef_ih := coef.leadingTerm_eventually_ne_zero h_coef_wo h_coef_trimmed h_coef_ne_zero
        h_basis.right.left
      apply Eventually.mono <| coef_ih.and (MS.basis_head_eventually_pos h_basis)
      rintro x ⟨coef_ih, h_basis_hd_pos⟩
      simp only [leadingTerm, MS.Term.toFun, List.zip_cons_cons, List.foldl_cons, CoList.casesOn',
        CoList.casesOn_cons]
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
  theorem IsEquivalent_coef {basis_hd C F : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
      {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
      (h_coef : coef.isApproximation C basis_tl)
      (h_coef_wo : coef.wellOrdered)
      (h_coef_trimmed : coef.isTrimmed)
      (h_coef_ne_zero : ¬coef.isFlatZero)
      (h_tl : tl.isApproximation (fun x ↦ F x - (basis_hd x)^deg * C x))
      (h_comp_wo : leadingExp tl < ↑deg)
      (h_basis : MS.wellOrderedBasis (basis_hd :: basis_tl)) :
      F ~[atTop] fun x ↦ (basis_hd x)^deg * (C x) := by
    have coef_ih := coef.IsEquivalent_leadingTerm (F := C) h_coef_wo h_coef h_coef_trimmed
      h_basis.right.left
    simp [IsEquivalent]
    eta_expand
    simp only [Pi.sub_apply]
    revert h_tl h_comp_wo
    apply tl.casesOn
    · intro h_tl h_comp_wo
      replace h_tl := isApproximation_nil h_tl
      apply EventuallyEq.trans_isLittleO h_tl
      apply Asymptotics.isLittleO_zero -- should be simp lemma
    · intro (tl_deg, tl_coef) tl_tl h_tl h_comp_wo
      replace h_tl := isApproximation_cons h_tl
      obtain ⟨tl_C, h_tl_coef, h_tl_comp, h_tl_tl⟩ := h_tl
      simp [leadingExp] at h_comp_wo
      let deg' := (deg + tl_deg) / 2
      specialize h_tl_comp deg' (by simp only [deg']; linarith)
      apply IsLittleO.trans h_tl_comp
      apply (isLittleO_iff_tendsto' _).mpr
      · simp_rw [← div_div]
        conv in _ / _ =>
          rw [div_eq_mul_inv, div_mul_comm, div_mul]
        apply (isLittleO_iff_tendsto' _).mp
        · have : (fun x ↦ basis_hd x ^ deg / basis_hd x ^ deg') =ᶠ[atTop]
              fun x ↦ (basis_hd x)^(deg - deg') := by
            apply Eventually.mono <| MS.basis_head_eventually_pos h_basis
            intro x h
            simp only
            rw [← Real.rpow_sub h]
          apply IsLittleO.trans_eventuallyEq _ this.symm
          have := IsEquivalent.inv coef_ih
          apply IsEquivalent.trans_isLittleO this
          apply EventuallyEq.trans_isLittleO (MS.Term.fun_inv h_basis.right.left)
          apply MS.Term.tail_fun_IsLittleO_head
          · rw [MS.Term.inv_length, PreMS.leadingTerm_length]
          · simp [MS.wellOrderedBasis]
            tauto
          · simp only [deg']
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
          apply Eventually.mono <| h_φ_pos.and (leadingTerm_eventually_ne_zero h_coef_wo
            h_coef_trimmed h_coef_ne_zero h_basis.right.left)
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
      (h_wo : ms.wellOrdered)
      (h_approx : ms.isApproximation F basis) (h_trimmed : ms.isTrimmed)
      (h_basis : MS.wellOrderedBasis basis)
      : F ~[atTop] ms.leadingTerm.toFun basis :=
    match basis with
    | [] => by
      simp [isApproximation] at h_approx
      simp [leadingTerm]
      apply EventuallyEq.isEquivalent (by assumption)
    | basis_hd :: basis_tl => by
      revert h_wo h_approx h_trimmed
      apply ms.casesOn
      · intro h_wo h_approx h_trimmed
        have hF := isApproximation_nil h_approx
        unfold leadingTerm
        simp [MS.Term.zero_coef_fun]
        apply EventuallyEq.isEquivalent (by assumption)
      · intro (deg, coef) tl h_wo h_approx h_trimmed
        obtain ⟨C, h_coef, h_comp, h_tl⟩ := isApproximation_cons h_approx
        obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := isTrimmed_cons h_trimmed
        obtain ⟨h_coef_wo, h_comp_wo, h_tl_wo⟩ := wellOrdered_cons h_wo
        simp [MS.wellOrderedBasis] at h_basis
        have coef_ih := coef.IsEquivalent_leadingTerm (F := C) h_coef_wo h_coef h_coef_trimmed
          h_basis.right.left
        have : F ~[atTop] fun x ↦ (basis_hd x)^deg * (C x) :=
          PreMS.IsEquivalent_coef h_coef h_coef_wo h_coef_trimmed h_coef_ne_zero h_tl h_comp_wo h_basis
        apply IsEquivalent.trans this
        eta_expand
        simp_rw [PreMS.leadingTerm_cons_toFun]
        apply IsEquivalent.mul IsEquivalent.refl
        exact coef_ih
end

theorem eventually_ne_zero_of_not_isFlatZero {basis : Basis} {ms : PreMS basis} {F : ℝ → ℝ}
    (h_ne_zero : ¬ ms.isFlatZero) (h_wo : ms.wellOrdered) (h_approx : ms.isApproximation F _)
    (h_trimmed : ms.isTrimmed) (h_basis : MS.wellOrderedBasis basis):
    ∀ᶠ x in atTop, F x ≠ 0 := by
  have := IsEquivalent_leadingTerm h_wo h_approx h_trimmed h_basis
  obtain ⟨φ, ⟨hφ_tendsto, h_eq⟩⟩ := Asymptotics.IsEquivalent.exists_eq_mul this
  have hφ : ∀ᶠ x in atTop, 1/2 < φ x := by
    apply eventually_gt_of_tendsto_gt _ hφ_tendsto
    linarith
  have h_leadingTerm := leadingTerm_eventually_ne_zero h_wo h_trimmed h_ne_zero h_basis
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

theorem MS.leadingTerm_length {ms : MS} : ms.leadingTerm.degs.length = ms.basis.length := by
  apply PreMS.leadingTerm_length

theorem MS.IsEquivalent_leadingTerm (ms : MS) (h_basis : MS.wellOrderedBasis ms.basis)
    (h_trimmed : ms.isTrimmed) : ms.F ~[atTop] ms.leadingTerm.toFun ms.basis := by
  apply PreMS.IsEquivalent_leadingTerm ms.h_wo ms.h_approx h_trimmed h_basis

def MS.findLimitTrimmed (ms : MS) (h_basis : MS.wellOrderedBasis ms.basis)
    (h_trimmed : ms.isTrimmed) :
    TendstoM <| FindLimitResult ms.F := do
  let r ← ms.leadingTerm.findLimit (basis := ms.basis) (by apply MS.leadingTerm_length) h_basis
  match r with
  | .top p => return .top (by {
      exact (IsEquivalent.tendsto_atTop_iff (MS.IsEquivalent_leadingTerm ms h_basis h_trimmed)).mpr p
    })
  | .bot p => return .bot (by {
      exact (IsEquivalent.tendsto_atBot_iff (MS.IsEquivalent_leadingTerm ms h_basis h_trimmed)).mpr p
    })
  | .fin c p => return .fin c (by {
      exact IsEquivalent.tendsto_nhds (MS.IsEquivalent_leadingTerm ms h_basis h_trimmed).symm p
    })

def MS.findLimit (ms : MS) (h_basis : MS.wellOrderedBasis ms.basis) :
    TendstoM <| FindLimitResult ms.F := do
  let trimmed ← MS.trim ms
  let r ← MS.findLimitTrimmed trimmed.result (trimmed.h_eq_basis ▸ h_basis) trimmed.h_trimmed
  return (trimmed.h_eq_F ▸ r)

end TendstoTactic
