import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.Tendsto.Multiseries.BasicNew
import Mathlib.Tactic.Tendsto.Multiseries.Operations.Mul
import Mathlib.Tactic.Tendsto.Multiseries.TrimmingNew

set_option linter.unusedVariables false
set_option linter.style.longLine false

open Filter Asymptotics

namespace TendstoTactic

namespace PreMS

abbrev LazySeries := CoList ℝ

namespace LazySeries

noncomputable def toFormalMultilinearSeries (s : LazySeries) : FormalMultilinearSeries ℝ ℝ ℝ :=
  fun n =>
  match s.get n with
  | .none => 0
  | .some c => c • ContinuousMultilinearMap.mkPiAlgebraFin ℝ n ℝ

noncomputable def toFun (s : LazySeries) : ℝ → ℝ :=
  s.toFormalMultilinearSeries.sum

#check FormalMultilinearSeries.zero_apply

theorem toFun_nil : toFun CoList.nil = 0 := by
  simp [toFun]
  unfold toFormalMultilinearSeries
  simp
  unfold FormalMultilinearSeries.sum
  simp
  rfl

theorem toFun_cons {s_hd : ℝ} {s_tl : LazySeries} :
    toFun (.cons s_hd s_tl) = fun x ↦ s_hd + ((toFun s_tl) x) * x := by
  sorry


theorem toFun_tendsto_head {s_hd : ℝ} {s_tl : LazySeries}
    (h_analytic : AnalyticAt ℝ (toFun (.cons s_hd s_tl)) 0) :
    Tendsto (toFun (.cons s_hd s_tl)) (nhds 0) (nhds s_hd) := by
  have : (toFun (.cons s_hd s_tl)) 0 = s_hd := by
    simp [toFun, FormalMultilinearSeries.sum]
    rw [tsum_eq_zero_add']
    · simp
      unfold toFormalMultilinearSeries
      simp [FormalMultilinearSeries.coeff]
    · simp
      exact summable_zero
  conv =>
    arg 3
    rw [← this]
  apply ContinuousAt.tendsto
  apply AnalyticAt.continuousAt h_analytic

theorem toFun_IsBigO_one {s : LazySeries} (h_analytic : AnalyticAt ℝ (toFun s) 0) {F : ℝ → ℝ}
    (hF : Tendsto F atTop (nhds 0)) : ((toFun s) ∘ F) =O[atTop] (1 : ℝ → ℝ) := by
  revert h_analytic
  apply s.casesOn
  · simp [toFun_nil]
    intro
    apply isBigO_zero
  · intro s_hd s_tl h_analytic
    apply isBigO_const_of_tendsto (y := s_hd) _ (by exact ne_zero_of_eq_one rfl)
    apply Tendsto.comp _ hF
    apply toFun_tendsto_head h_analytic

theorem tail_analytic {s_hd : ℝ} {s_tl : LazySeries}
    (h_analytic : AnalyticAt ℝ (toFun (.cons s_hd s_tl)) 0) :
    AnalyticAt ℝ (toFun s_tl) 0 := by
  sorry

-- theorem

noncomputable def apply (s : LazySeries) {basis : Basis}
    (ms : PreMS basis) : PreMS basis :=
  match basis with
  | [] => default -- We can not substitute constant (and PreMS with nonnegative
                  -- leading exponent) to series
  | basis_hd :: basis_tl =>
    let T := PreMS (basis_hd :: basis_tl) × LazySeries
    let g : T → CoList.OutType (PreMS (basis_hd :: basis_tl)) T := fun (cur_power, cur_s) =>
      cur_s.casesOn'
      (nil := .nil)
      (cons := fun c cs =>
        .cons (mulConst cur_power c) (cur_power.mul ms, cs)
      )
    let terms := CoList.corec g (PreMS.one _, s) -- [c0, c1 * ms, c2, * ms^2, ...]
    merge1 terms

#check AnalyticAt

@[simp]
theorem apply_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    apply .nil ms = CoList.nil := by
  sorry

@[simp]
theorem apply_cons {s_hd : ℝ} {s_tl : LazySeries}
    {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    (apply (.cons s_hd s_tl) ms) = .cons (0, PreMS.const s_hd _) ((apply s_tl ms).mul ms) := by
  -- simp [apply]
  -- conv =>
  --   lhs
  --   rw [CoList.corec_cons _ _ (by rfl)]
  --   simp
  sorry

@[simp]
theorem apply_cons_leadingExp {s_hd : ℝ} {s_tl : LazySeries} {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    (apply (.cons s_hd s_tl) ms).leadingExp = 0 := by
  simp [leadingExp]

theorem apply_leadingExp_le_zero {s : LazySeries} {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    (apply s ms).leadingExp ≤ 0 := by
  apply s.casesOn <;> simp [leadingExp]

theorem apply_isApproximation {s : LazySeries} (h_analytic : AnalyticAt ℝ s.toFun 0) {basis : Basis}
    {ms : PreMS basis}
    (h_basis : MS.wellOrderedBasis basis) (h_wo : ms.wellOrdered)
    (h_neg : ms.hasNegativeLeading) (h_trimmed : ms.isTrimmed) {F : ℝ → ℝ}
    (h_approx : ms.isApproximation F basis) : (apply s ms).isApproximation (s.toFun ∘ F) basis := by
  have hF_tendsto_zero : Tendsto F atTop (nhds 0) := by
    apply hasNegativeLeading_tendsto_zero h_neg h_approx
  cases basis with
  | nil => cases h_neg
  | cons basis_hd basis_tl =>
    simp [hasNegativeLeading] at h_neg
    let motive : (F : ℝ → ℝ) → (ms : PreMS (basis_hd :: basis_tl)) → Prop := fun F' ms' =>
      ∃ (s : LazySeries), (AnalyticAt ℝ s.toFun 0) ∧
        ∃ X Y fX fY, F' =ᶠ[atTop] fX + fY * s.toFun ∘ F ∧ ms' = PreMS.add X ((s.apply ms).mul Y) ∧
        X.wellOrdered ∧ X.isApproximation fX (basis_hd :: basis_tl) ∧
        Y.wellOrdered ∧ Y.isApproximation fY (basis_hd :: basis_tl)
    apply isApproximation.coind motive
    · intro f ms' ih
      simp [motive] at ih
      obtain ⟨s, h_analytic, ⟨X, Y, fX, fY, hf_eq, h_ms_eq, hX_wo, hX_approx, hY_wo, hY_approx⟩⟩ := ih
      revert h_ms_eq hX_wo hX_approx
      apply X.casesOn
      · intro h_ms_eq _ hX_approx
        replace hX_approx := isApproximation_nil hX_approx
        revert h_ms_eq hY_wo hY_approx
        apply Y.casesOn
        · intro _ hY_approx h_ms_eq
          replace hY_approx := isApproximation_nil hY_approx
          left
          constructor
          · simpa using h_ms_eq
          · trans; exact hf_eq
            conv =>
              rhs
              ext x
              rw [← zero_add 0]
            apply EventuallyEq.add
            · exact hX_approx
            · simp only [Filter.EventuallyEq] at hY_approx ⊢
              apply Filter.Eventually.mono hY_approx
              intro x h
              simp [h]
        · intro (Y_deg, Y_coef) Y_tl hY_wo hY_approx h_ms_eq
          have hY_approx' := isApproximation_cons hY_approx
          obtain ⟨YC, hY_coef, hY_comp, hY_tl⟩ := hY_approx'
          have hY_wo' := wellOrdered_cons hY_wo
          obtain ⟨hY_coef_wo, hY_comp_wo, hY_tl_wo⟩ := hY_wo'
          revert h_ms_eq hf_eq h_analytic
          apply s.casesOn
          · intro h_analytic hf_eq h_ms_eq
            left
            constructor
            · simpa [apply_nil] using h_ms_eq
            · trans; exact hf_eq
              simpa [toFun_nil]
          · intro s_hd s_tl h_analytic hf_eq h_ms_eq
            right
            simp [-apply_cons] at h_ms_eq -- TODO: rewrite
            rw [apply_cons] at h_ms_eq
            simp only [mul_cons_cons, mul_assoc', zero_add] at h_ms_eq
            use Y_deg
            use (const s_hd basis_tl).mul Y_coef
            use (mulMonomial Y_tl (const s_hd basis_tl) 0).add ((apply s_tl ms).mul (ms.mul (CoList.cons (Y_deg, Y_coef) Y_tl)))
            use fun x ↦ s_hd * (YC x)
            constructor
            · exact h_ms_eq
            · constructor
              · apply mul_isApproximation (MS.wellOrderedBasis_tail h_basis)
                · apply const_isApproximation_const
                  simp [MS.wellOrderedBasis] at h_basis
                  exact h_basis.right.left
                · exact hY_coef
              · constructor
                · intro deg h_deg
                  apply EventuallyEq.trans_isLittleO (f₂ := fY * toFun (CoList.cons s_hd s_tl) ∘ F)
                  · trans; exact hf_eq
                    apply eventuallyEq_iff_sub.mpr
                    simpa
                  conv =>
                    rhs; ext x; rw [show basis_hd x ^ deg = basis_hd x ^ deg * 1 by ring] -- mul_one is blocked :(
                  apply IsLittleO.mul_isBigO
                  · exact hY_comp deg (by assumption)
                  apply isBigO_const_of_tendsto (y := s_hd) _ (by simp)
                  apply Tendsto.comp _ hF_tendsto_zero
                  apply toFun_tendsto_head h_analytic
                · simp only [motive]
                  use s_tl
                  constructor
                  · apply tail_analytic h_analytic
                  use mulMonomial Y_tl (const s_hd basis_tl) 0
                  use ms.mul (CoList.cons (Y_deg, Y_coef) Y_tl)
                  use (fun x ↦ s_hd * (fY x - basis_hd x ^ Y_deg * YC x))
                  use F * fY
                  constructor
                  · simp only [EventuallyEq] at hf_eq hX_approx ⊢
                    apply Eventually.mono <| hf_eq.and hX_approx
                    intro x ⟨hf_eq, hX_approx⟩
                    simp [hf_eq, hX_approx, toFun_cons]
                    ring_nf!
                  constructor
                  · rfl
                  constructor
                  · apply mulMonomial_wellOrdered hY_tl_wo
                    exact const_wellOrdered
                  constructor
                  · simp [MS.wellOrderedBasis] at h_basis
                    have := mulMonomial_isApproximation h_basis (m_coef := const s_hd basis_tl) (m_deg := 0) hY_tl
                      (const_isApproximation_const h_basis.right.left)
                    simpa using this
                  constructor
                  · apply mul_wellOrdered h_wo hY_wo
                  apply mul_isApproximation h_basis
                  · exact h_approx
                  · exact hY_approx
      · intro (X_deg, X_coef) X_tl h_ms_eq hX_wo hX_approx
        right
        have hX_approx' := isApproximation_cons hX_approx
        obtain ⟨XC, hX_coef, hX_comp, hX_tl⟩ := hX_approx'
        have hX_wo' := wellOrdered_cons hX_wo
        obtain ⟨hX_coef_wo, hX_comp_wo, hX_tl_wo⟩ := hX_wo'
        revert h_ms_eq hY_wo hY_approx
        apply Y.casesOn
        · intro _ hY_approx h_ms_eq
          replace hY_approx := isApproximation_nil hY_approx
          replace hf_eq : f =ᶠ[atTop] fX := by
            trans
            · exact hf_eq
            conv =>
              rhs
              ext x
              rw [← add_zero (fX x)]
            apply EventuallyEq.add
            · rfl
            conv => rhs; ext x; rw [← zero_mul ((s.toFun ∘ F) x)]
            apply EventuallyEq.mul
            · exact hY_approx
            · rfl
          simp at h_ms_eq -- #1 (i've copypasted it to below)
          use X_deg
          use X_coef
          use X_tl
          use XC
          constructor
          · exact h_ms_eq
          constructor
          · exact hX_coef
          constructor
          · intro deg h_deg
            apply Filter.EventuallyEq.trans_isLittleO hf_eq (hX_comp deg h_deg)
          · simp [motive]
            use s
            constructor
            · exact h_analytic
            use X_tl
            use .nil
            use fun x ↦ fX x - basis_hd x ^ X_deg * XC x
            use 0
            constructor
            · simp
              apply eventuallyEq_iff_sub.mpr
              eta_expand
              simp
              apply eventuallyEq_iff_sub.mp hf_eq
            constructor
            · simp
            constructor
            · exact hX_tl_wo
            constructor
            · exact hX_tl
            constructor
            · apply wellOrdered.nil
            · apply isApproximation.nil
              rfl
        · intro (Y_deg, Y_coef) Y_tl hY_wo hY_approx h_ms_eq
          have hY_approx' := isApproximation_cons hY_approx
          obtain ⟨YC, hY_coef, hY_comp, hY_tl⟩ := hY_approx'
          have hY_wo' := wellOrdered_cons hY_wo
          obtain ⟨hY_coef_wo, hY_comp_wo, hY_tl_wo⟩ := hY_wo'
          revert h_ms_eq hf_eq h_analytic
          apply s.casesOn
          · intro h_analytic hf_eq h_ms_eq
            replace hf_eq : f =ᶠ[atTop] fX := by
              trans
              · exact hf_eq
              conv =>
                rhs
                ext x
                rw [← add_zero (fX x)]
              apply EventuallyEq.add
              · rfl
              conv => rhs; ext x; rw [← mul_zero (fY x)]
              apply EventuallyEq.mul
              · rfl
              · simp [toFun_nil]
                rfl
            simp [apply_nil] at h_ms_eq -- copypaste from #1
            use X_deg
            use X_coef
            use X_tl
            use XC
            constructor
            · exact h_ms_eq
            constructor
            · exact hX_coef
            constructor
            · intro deg h_deg
              apply Filter.EventuallyEq.trans_isLittleO hf_eq (hX_comp deg h_deg)
            · simp [motive]
              use .nil
              constructor
              · exact h_analytic
              use X_tl
              use .nil
              use fun x ↦ fX x - basis_hd x ^ X_deg * XC x
              use 0
              constructor
              · simp
                apply eventuallyEq_iff_sub.mpr
                eta_expand
                simp
                apply eventuallyEq_iff_sub.mp hf_eq
              constructor
              · simp
              constructor
              · exact hX_tl_wo
              constructor
              · exact hX_tl
              constructor
              · exact wellOrdered.nil
              · apply isApproximation.nil
                rfl
          · intro s_hd s_tl h_analytic hf_eq h_ms_eq
            simp only [apply_cons, zero_add, mul_assoc, mul_cons_cons] at h_ms_eq
            have h_out : ms'.out = ?_ := by simp only [h_ms_eq]; exact add_out_eq
            simp [add_out] at h_out
            split_ifs at h_out with h1 h2
            · replace h_ms_eq := CoList.out_eq_cons h_out
              clear h_out
              use X_deg
              use X_coef
              use ?_
              use XC
              constructor
              · exact h_ms_eq
              constructor
              · exact hX_coef
              constructor
              · intro deg h_deg
                apply EventuallyEq.trans_isLittleO hf_eq
                apply IsLittleO.add
                · exact hX_comp deg h_deg
                conv =>
                  rhs; ext x; rw [show basis_hd x ^ deg = basis_hd x ^ deg * 1 by ring] -- mul_one is blocked :(
                apply IsLittleO.mul_isBigO
                · apply hY_comp deg
                  linarith
                apply toFun_IsBigO_one h_analytic hF_tendsto_zero
              simp [motive]
              use .cons s_hd s_tl
              constructor
              · exact h_analytic
              focus
              replace h_ms_eq : ms' = CoList.cons (X_deg, X_coef)
                  (add X_tl
                  ((apply (CoList.cons s_hd s_tl) ms).mul (CoList.cons (Y_deg, Y_coef) Y_tl))) := by
                rw [h_ms_eq]
                congr
                simp only [apply_cons, mul_cons, mulMonomial_cons,
                  zero_add, mul_assoc']
                rw [cons_add]
                · simp
                  conv => lhs; arg 2; arg 2; simp [leadingExp]
                  conv => rhs; arg 1; rw [← zero_add Y_deg]
                  rw [WithBot.coe_add, ← add_assoc]
                  apply WithBot.add_lt_add_right (by simp)
                  conv => rhs; arg 1; rw [← zero_add 0]
                  rw [WithBot.coe_add]
                  apply WithBot.add_lt_add_of_le_of_lt (by simp)
                  · apply apply_leadingExp_le_zero
                  · exact h_neg
              use X_tl
              use .cons (Y_deg, Y_coef) Y_tl
              use fun x ↦ fX x - basis_hd x ^ X_deg * XC x
              use fY
              constructor
              · apply eventuallyEq_iff_sub.mpr
                eta_expand
                simp
                ring_nf!
                conv =>
                  lhs; ext x; rw [show f x + (-fX x - fY x * toFun (CoList.cons s_hd s_tl) (F x)) =
                    f x - (fX x + fY x * toFun (CoList.cons s_hd s_tl) (F x)) by ring_nf]
                apply eventuallyEq_iff_sub.mp
                exact hf_eq
              constructor
              · simp
                rw [cons_add]
                · simp
                  conv => lhs; arg 2; arg 2; simp [leadingExp]
                  conv => rhs; arg 1; rw [← zero_add Y_deg]
                  rw [WithBot.coe_add, ← add_assoc]
                  apply WithBot.add_lt_add_right (by simp)
                  conv => rhs; arg 1; rw [← zero_add 0]
                  rw [WithBot.coe_add]
                  apply WithBot.add_lt_add_of_le_of_lt (by simp)
                  · apply apply_leadingExp_le_zero
                  · exact h_neg
              constructor
              · exact hX_tl_wo
              constructor
              · exact hX_tl
              constructor
              · exact hY_wo
              · exact hY_approx
            · replace h_ms_eq := CoList.out_eq_cons h_out
              clear h_out
              simp only [← add_assoc] at h_ms_eq
              use Y_deg
              use (const s_hd basis_tl).mul Y_coef
              use ?_
              use fun x ↦ s_hd * YC x
              constructor
              · exact h_ms_eq
              constructor
              · apply mul_isApproximation (MS.wellOrderedBasis_tail h_basis)
                · simp [MS.wellOrderedBasis] at h_basis
                  apply const_isApproximation_const h_basis.right.left
                · exact hY_coef
              constructor
              · intro deg h_deg
                apply EventuallyEq.trans_isLittleO hf_eq
                apply IsLittleO.add
                · apply hX_comp deg
                  linarith
                conv =>
                  rhs; ext x; rw [show basis_hd x ^ deg = basis_hd x ^ deg * 1 by ring] -- mul_one is blocked :(
                apply IsLittleO.mul_isBigO
                · apply hY_comp deg h_deg
                apply toFun_IsBigO_one h_analytic hF_tendsto_zero
              simp [motive]
              use s_tl
              constructor
              · apply tail_analytic h_analytic
              use add (CoList.cons (X_deg, X_coef) X_tl) (mulMonomial Y_tl (const s_hd basis_tl) 0)
              use ms.mul (CoList.cons (Y_deg, Y_coef) Y_tl)
              use fun x ↦ fX x + s_hd * (fY x - basis_hd x ^ Y_deg * YC x)
              use F * fY
              constructor
              · apply eventuallyEq_iff_sub.mpr
                eta_expand
                simp
                ring_nf!
                conv =>
                  lhs; ext x; rw [show f x - s_hd * fY x + (-fX x - fY x * F x * toFun s_tl (F x)) =
                    f x - (s_hd * fY x + fX x + fY x * F x * toFun s_tl (F x)) by ring_nf]
                apply eventuallyEq_iff_sub.mp
                trans
                · exact hf_eq
                apply eventuallyEq_iff_sub.mpr
                eta_expand
                simp [toFun_cons]
                ring_nf!
                rfl
              constructor
              · simp [add_assoc']
              constructor
              · apply add_wellOrdered
                · exact hX_wo
                apply mulMonomial_wellOrdered
                · exact hY_tl_wo
                · exact const_wellOrdered
              constructor
              · apply add_isApproximation
                · exact hX_approx
                · conv =>
                    arg 1
                    ext x
                    rw [show s_hd = (fun x ↦ s_hd * (basis_hd x)^(0 : ℝ)) x by simp]
                  apply mulMonomial_isApproximation h_basis
                  · exact hY_tl
                  · apply const_isApproximation_const
                    simp [MS.wellOrderedBasis] at h_basis
                    exact h_basis.right.left
              constructor
              · apply mul_wellOrdered
                · exact h_wo
                · exact hY_wo
              · apply mul_isApproximation h_basis
                · exact h_approx
                · exact hY_approx
            · have h : X_deg = Y_deg := by linarith
              clear h1 h2
              replace h_ms_eq := CoList.out_eq_cons h_out
              clear h_out
              simp only [← add_assoc] at h_ms_eq
              use X_deg
              use X_coef.add ((const s_hd basis_tl).mul Y_coef)
              use ?_
              use fun x ↦ XC x + s_hd * YC x
              constructor
              · exact h_ms_eq
              constructor
              · apply add_isApproximation
                · exact hX_coef
                · apply mul_isApproximation (MS.wellOrderedBasis_tail h_basis)
                  · apply const_isApproximation_const
                    simp [MS.wellOrderedBasis] at h_basis
                    exact h_basis.right.left
                  · exact hY_coef
              constructor
              · intro deg h_deg
                apply EventuallyEq.trans_isLittleO hf_eq
                apply IsLittleO.add
                · exact hX_comp deg h_deg
                conv =>
                  rhs; ext x; rw [show basis_hd x ^ deg = basis_hd x ^ deg * 1 by ring] -- mul_one is blocked :(
                apply IsLittleO.mul_isBigO
                · exact hY_comp deg (h ▸ h_deg)
                apply toFun_IsBigO_one h_analytic hF_tendsto_zero
              simp [motive]
              use s_tl
              constructor
              · exact tail_analytic h_analytic
              use add X_tl (mulMonomial Y_tl (const s_hd basis_tl) 0)
              use ms.mul (CoList.cons (Y_deg, Y_coef) Y_tl)
              use fun x ↦ (fX x - basis_hd x ^ X_deg * XC x) + s_hd * (fY x - basis_hd x ^ Y_deg * YC x)
              use F * fY
              constructor
              · apply eventuallyEq_iff_sub.mpr
                eta_expand
                simp
                rw [h]
                ring_nf!
                conv =>
                  lhs; ext x; rw [show f x - s_hd * fY x + (-fX x - fY x * F x * toFun s_tl (F x)) =
                    f x - (s_hd * fY x + fX x + fY x * F x * toFun s_tl (F x)) by ring_nf]
                apply eventuallyEq_iff_sub.mp
                trans
                · exact hf_eq
                apply eventuallyEq_iff_sub.mpr
                eta_expand
                simp [toFun_cons]
                ring_nf!
                rfl
              constructor
              · simp [add_assoc']
              constructor
              · apply add_wellOrdered
                · exact hX_tl_wo
                · apply mulMonomial_wellOrdered
                  · exact hY_tl_wo
                  · exact const_wellOrdered
              constructor
              · apply add_isApproximation
                · exact hX_tl
                · conv =>
                    arg 1
                    ext x
                    rw [show s_hd = (fun x ↦ s_hd * (basis_hd x)^(0 : ℝ)) x by simp]
                  apply mulMonomial_isApproximation h_basis
                  · exact hY_tl
                  · apply const_isApproximation_const
                    simp [MS.wellOrderedBasis] at h_basis
                    exact h_basis.right.left
              constructor
              · apply mul_wellOrdered
                · exact h_wo
                · exact hY_wo
              · apply mul_isApproximation h_basis
                · exact h_approx
                · exact hY_approx
    · simp [motive]
      use s
      constructor
      · exact h_analytic
      use .nil
      use one _
      use 0
      use 1
      simp
      constructor
      · apply wellOrdered.nil
      constructor
      · apply isApproximation.nil
        apply Filter.EventuallyEq.refl
      constructor
      · apply const_wellOrdered
      · apply one_isApproximation_one h_basis

end LazySeries

end PreMS

end TendstoTactic
