import Mathlib.Tactic.Tendsto.Multiseries.Term
import Mathlib.Tactic.Tendsto.Multiseries.Trimming

open Filter Asymptotics

namespace TendstoTactic


def PreMS.leadingTerm {n : ℕ} (ms : PreMS) (h_depth : ms.hasDepth n) : MS.Term :=
  match ms with
  | .const c => ⟨c, []⟩
  | .nil => ⟨0, List.range n |>.map fun _ => 0⟩
  | .cons deg coef tl =>
    match n with
    | .zero => default -- unreachable
    | .succ m =>
      let pre := coef.leadingTerm (by cases h_depth; assumption)
      ⟨pre.coef, deg :: pre.degs⟩

def MS.leadingTerm (ms : MS) : MS.Term :=
  PreMS.leadingTerm ms.val ms.h_depth

theorem PreMS.leadingTerm_length {n : ℕ} {ms : PreMS} (h_depth : ms.hasDepth n) :
    (ms.leadingTerm h_depth).degs.length = n := by
  induction ms using PreMS.rec' generalizing n with
  | const _ =>
    cases h_depth
    rfl
  | nil =>
    unfold leadingTerm
    simp
  | cons deg coef tl coef_ih _ =>
    cases n with
    | zero => cases h_depth
    | succ m =>
      simp [PreMS.leadingTerm]
      apply coef_ih


theorem MS.leadingTerm_length {ms : MS} : ms.leadingTerm.degs.length = ms.basis.length := by
  apply PreMS.leadingTerm_length

-- lemma lol {n : ℕ} (hn : 0 < n) : (MS.baseFun hn).isTrimmed := by
--   sorry

-- example : (MS.baseFun (n := 3) (by decide)).leadingTerm (by exact lol (by decide)) = ⟨1, [1, 0, 0]⟩ := by
--   rfl

theorem PreMS.leadingTerm_cons_toFun {deg : ℝ} {coef : PreMS} {tl : Thunk PreMS} {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h_depth : (PreMS.cons deg coef tl).hasDepth (basis_hd :: basis_tl).length) (x : ℝ) :
    ((PreMS.cons deg coef tl).leadingTerm h_depth).toFun (basis_hd :: basis_tl) x = (basis_hd x)^deg *
    (coef.leadingTerm (by cases h_depth; assumption)).toFun basis_tl x := by
  simp [leadingTerm, MS.Term.toFun]
  conv =>
    congr <;> rw [MS.Term.fun_mul]
    lhs
    rw [mul_comm] -- why do I need these rws? Why ring_nf can't solve the goal?
  rw [← mul_assoc]

-- somehow I avoided it
-- lemma PreMS.leadingTerm_coef_ne_zero {basis : Basis} {ms : PreMS} (h_depth : ms.hasDepth basis.length)
--     (h_wo : ms.wellOrdered) (h_trimmed : ms.isTrimmed) (h_basis : MS.wellOrderedBasis basis) :
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

theorem PreMS.leadingTerm_eventually_ne_zero {basis : Basis} {ms : PreMS} (h_depth : ms.hasDepth basis.length)
    (h_wo : ms.wellOrdered) (h_trimmed : ms.isTrimmed) (h_ne_zero : ¬ ms.isFlatZero) (h_basis : MS.wellOrderedBasis basis) :
    ∀ᶠ x in atTop, (ms.leadingTerm h_depth).toFun basis x ≠ 0 := by
  induction ms using PreMS.rec' generalizing basis with
  | nil =>
    simp [isFlatZero] at h_ne_zero
  | const c =>
    -- simp [isFlatZero] at h_ne_zero -- somehow it's not needed
    unfold leadingTerm
    simp [MS.Term.toFun]
    use default
    intros
    assumption
  | cons deg coef tl coef_ih _ =>
    cases basis with
    | nil => cases h_depth
    | cons basis_hd basis_tl =>
      cases h_depth with | cons _ _ _ _ h_depth_coef h_depth_tl =>
      simp [wellOrdered] at h_wo
      simp [isTrimmed] at h_trimmed
      specialize coef_ih h_depth_coef h_wo.left h_trimmed.left h_trimmed.right h_basis.right.left
      apply Eventually.mono <| coef_ih.and (MS.basis_head_eventually_pos h_basis)
      rintro x ⟨coef_ih, h_basis_hd_pos⟩
      simp only [leadingTerm, MS.Term.toFun, List.zip_cons_cons, List.foldl_cons]
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

theorem PreMS.IsEquivalent_leadingTerm {val : PreMS} {basis : Basis} {F : ℝ → ℝ}
    (h_depth : val.hasDepth basis.length) (h_wo : val.wellOrdered)
    (h_approx : val.isApproximation F basis) (h_trimmed : val.isTrimmed)
    (h_basis : MS.wellOrderedBasis basis)
    : F ~[atTop] (val.leadingTerm h_depth).toFun basis := by
  induction val using PreMS.rec' generalizing F basis with
  | nil =>
    cases h_approx
    unfold leadingTerm
    simp [MS.Term.zero_coef_fun]
    apply EventuallyEq.isEquivalent (by assumption)
  | const c =>
    cases h_approx
    simp [leadingTerm]
    apply EventuallyEq.isEquivalent (by assumption)
  | cons deg coef tl coef_ih tl_ih =>
    cases h_approx
    rename_i C basis_hd basis_tl h_coef h h_tl
    have : F ~[atTop] fun x ↦ (basis_hd x)^deg * (C x) := by
      simp [IsEquivalent]
      eta_expand
      simp only [Pi.sub_apply]
      simp [wellOrdered] at h_wo
      generalize tl.get = tlg at *
      cases h_tl with
      | nil _ _ h_nil =>
        apply EventuallyEq.trans_isLittleO h_nil
        apply Asymptotics.isLittleO_zero -- should be simp lemma
      | cons tl_deg tl_coef tl_tl _ C' _ _ h_tl_coef h_tl_tl h_tl =>
        simp [wellOrdered] at h_wo
        let deg' := (deg + tl_deg) / 2
        specialize h_tl deg' (by simp only [deg']; linarith)
        apply IsLittleO.trans h_tl
        cases h_depth with | cons _ _ _ _ h_depth_coef h_depth_tl =>
        simp [isTrimmed] at h_trimmed
        simp [MS.wellOrderedBasis] at h_basis
        specialize coef_ih h_depth_coef h_wo.left h_coef h_trimmed.left h_basis.right.left
        apply (isLittleO_iff_tendsto' _).mpr
        · simp_rw [← div_div]
          conv in _ / _ =>
            rw [div_eq_mul_inv, div_mul_comm, div_mul]
          apply (isLittleO_iff_tendsto' _).mp
          · have : (fun x ↦ basis_hd x ^ deg / basis_hd x ^ deg') =ᶠ[atTop] fun x ↦ (basis_hd x)^(deg - deg') := by
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
            apply Eventually.mono <| h_φ_pos.and (leadingTerm_eventually_ne_zero h_depth_coef h_wo.left h_trimmed.left h_trimmed.right h_basis.right.left)
            rintro x ⟨h_φ_pos, h⟩
            exact mul_ne_zero h_φ_pos.ne.symm h
          apply Eventually.mono <| h_C_ne_zero.and
            (MS.basis_head_eventually_pos h_basis)
          rintro x ⟨h_C_ne_zero, h_basis_pos⟩
          intro h
          absurd h
          apply mul_ne_zero _ h_C_ne_zero
          exact (Real.rpow_pos_of_pos h_basis_pos _).ne.symm
    apply IsEquivalent.trans this
    eta_expand
    simp_rw [PreMS.leadingTerm_cons_toFun]
    apply IsEquivalent.mul IsEquivalent.refl
    apply coef_ih
    · simp [wellOrdered] at h_wo; exact h_wo.left
    · exact h_coef
    · simp [isTrimmed] at h_trimmed; exact h_trimmed.left
    · simp [MS.wellOrderedBasis] at h_basis; exact h_basis.right.left

theorem MS.IsEquivalent_leadingTerm (ms : MS) (h_basis : MS.wellOrderedBasis ms.basis)
    (h_trimmed : ms.isTrimmed) : ms.F ~[atTop] ms.leadingTerm.toFun ms.basis := by
  apply PreMS.IsEquivalent_leadingTerm _ ms.h_wo ms.h_approx h_trimmed h_basis

def MS.findLimitTrimmed (ms : MS) (h_basis : MS.wellOrderedBasis ms.basis) (h_trimmed : ms.isTrimmed) :
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

noncomputable def MS.findLimit (ms : MS) (h_basis : MS.wellOrderedBasis ms.basis) :
    TendstoM <| FindLimitResult ms.F := do
  let trimmed ← Trimming.MS.trim ms
  let r ← MS.findLimitTrimmed trimmed.result (trimmed.h_eq_basis ▸ h_basis) trimmed.h_trimmed
  return (trimmed.h_eq_F ▸ r)

end TendstoTactic
