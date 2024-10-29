import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.Tendsto.Multiseries.Basic
import Mathlib.Tactic.Tendsto.Multiseries.Operations.Mul
import Mathlib.Tactic.Tendsto.Multiseries.Trimming

set_option linter.unusedVariables false
set_option linter.style.longLine false

open Filter Asymptotics Stream' Seq

namespace TendstoTactic

namespace PreMS

abbrev LazySeries := Seq ℝ

namespace LazySeries

noncomputable def apply_aux {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (ms : PreMS (basis_hd :: basis_tl)) : PreMS (basis_hd :: basis_tl) × LazySeries →
    Option ((PreMS (basis_hd :: basis_tl)) × (PreMS (basis_hd :: basis_tl) × LazySeries)) := fun (cur_power, cur_s) =>
      match destruct cur_s with
      | none => none
      | some (c, cs) => .some ((mulConst cur_power c), (cur_power.mul ms, cs))

noncomputable def apply (s : LazySeries) {basis : Basis}
    (ms : PreMS basis) : PreMS basis :=
  match basis with
  | [] => default -- We can not substitute constant (and PreMS with nonnegative
                  -- leading exponent) to series
  | List.cons basis_hd basis_tl =>
    let terms := Seq.corec (apply_aux ms) (PreMS.one _, s) -- [c0, c1 * ms, c2, * ms^2, ...]
    merge1 terms

-- theorems

noncomputable def coeff (s : LazySeries) (n : ℕ) :=
  match s.get? n with
  | .none => 0
  | .some c => c • ContinuousMultilinearMap.mkPiAlgebraFin ℝ n ℝ

noncomputable def toFormalMultilinearSeries (s : LazySeries) : FormalMultilinearSeries ℝ ℝ ℝ :=
  s.coeff

theorem toFormalMultilinearSeries_coeff {s : LazySeries} {n : ℕ} : s.toFormalMultilinearSeries.coeff n = (s.get? n).getD 0 := by
  unfold FormalMultilinearSeries.coeff
  simp only [toFormalMultilinearSeries, coeff]
  generalize Seq.get? s n = t at *
  cases t with
  | none => simp
  | some x =>
    simp
    rw [List.prod_eq_one] -- cringe
    · simp
    · simp [List.forall_mem_ofFn_iff]

theorem toFormalMultilinearSeries_norm {s : LazySeries} {n : ℕ} : ‖(s.toFormalMultilinearSeries) n‖ = |(s.get? n).getD 0| := by
  simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef, Real.norm_eq_abs]
  congr
  exact toFormalMultilinearSeries_coeff

def analytic (s : LazySeries) : Prop := 0 < s.toFormalMultilinearSeries.radius

open ENNReal in
theorem tail_radius_eq {s_hd : ℝ} {s_tl : LazySeries} :
    (toFormalMultilinearSeries (.cons s_hd s_tl)).radius = s_tl.toFormalMultilinearSeries.radius := by
  apply le_antisymm
  · refine le_of_forall_nnreal_lt (fun r hr ↦ ?_)
    obtain ⟨C, ⟨hC, h_bound⟩⟩ := FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius _ hr
    by_cases hr_pos : r = 0
    · rw [hr_pos]
      simp
    replace hr_pos : 0 < r := lt_of_le_of_ne' (zero_le _) hr_pos
    apply FormalMultilinearSeries.le_radius_of_bound (C := C / r)
    intro n
    specialize h_bound (n + 1)
    simp [toFormalMultilinearSeries_coeff] at h_bound ⊢
    simp [toFormalMultilinearSeries_coeff, pow_succ, ← mul_assoc] at h_bound ⊢
    rwa [le_div_iff₀]
    simpa
  · refine le_of_forall_nnreal_lt (fun r hr ↦ ?_)
    obtain ⟨C, ⟨hC, h_bound⟩⟩ := FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius _ hr
    by_cases hr_pos : r = 0
    · rw [hr_pos]
      simp
    replace hr_pos : 0 < r := lt_of_le_of_ne' (zero_le _) hr_pos
    apply FormalMultilinearSeries.le_radius_of_bound (C := (C * r) ⊔ |s_hd|)
    intro n
    cases n with
    | zero =>
      simp [toFormalMultilinearSeries_coeff]
    | succ m =>
      specialize h_bound m
      simp [toFormalMultilinearSeries_coeff] at h_bound ⊢
      left
      simp [toFormalMultilinearSeries_coeff, pow_succ, ← mul_assoc] at h_bound ⊢
      rw [← div_le_iff₀, mul_div_assoc, ← NNReal.coe_div, div_self hr_pos.ne.symm] <;> simpa

theorem tail_analytic {s_hd : ℝ} {s_tl : LazySeries}
    (h_analytic : analytic (.cons s_hd s_tl)) :
    analytic s_tl := by
  simp [analytic] at *
  rwa [← tail_radius_eq]

noncomputable def toFun (s : LazySeries) : ℝ → ℝ :=
  s.toFormalMultilinearSeries.sum

theorem toFun_nil : toFun Seq.nil = 0 := by
  simp [toFun]
  unfold toFormalMultilinearSeries coeff
  simp
  unfold FormalMultilinearSeries.sum
  simp
  rfl

theorem toFun_cons {s_hd : ℝ} {s_tl : LazySeries} {x : ℝ}
    (h : analytic (Seq.cons s_hd s_tl))
    (hx : x ∈ EMetric.ball 0 (toFormalMultilinearSeries (Seq.cons s_hd s_tl)).radius):
    toFun (.cons s_hd s_tl) x = s_hd + ((toFun s_tl) x) * x := by
  have h_tl := tail_analytic h
  have h_hsum := FormalMultilinearSeries.hasFPowerSeriesOnBall _ h
  replace h_hsum := HasFPowerSeriesOnBall.hasSum h_hsum hx
  have h_hsum_tl := FormalMultilinearSeries.hasFPowerSeriesOnBall _ h_tl
  replace h_hsum_tl := HasFPowerSeriesOnBall.hasSum h_hsum_tl (tail_radius_eq ▸ hx)
  simp at h_hsum h_hsum_tl
  simp_rw [toFormalMultilinearSeries_coeff] at h_hsum h_hsum_tl
  unfold toFun
  generalize (toFormalMultilinearSeries (Seq.cons s_hd s_tl)).sum x = a at *
  generalize (toFormalMultilinearSeries s_tl).sum x = b at *
  apply HasSum.unique h_hsum
  replace h_hsum_tl := HasSum.mul_right x h_hsum_tl
  ring_nf at h_hsum_tl
  conv at h_hsum_tl =>
    arg 1
    ext i
    rw [← pow_succ']
    rw [show Seq.get? s_tl i = Seq.get? (.cons s_hd s_tl) (i + 1) by simp]
  have := HasSum.zero_add (f := (fun n ↦ x ^ n * (Seq.get? (Seq.cons s_hd s_tl) n).getD 0)) h_hsum_tl
  simpa using this

theorem toFun_tendsto_head {s_hd : ℝ} {s_tl : LazySeries}
    (h_analytic : analytic (.cons s_hd s_tl)) :
    Tendsto (toFun (.cons s_hd s_tl)) (nhds 0) (nhds s_hd) := by
  have : (toFun (.cons s_hd s_tl)) 0 = s_hd := by
    simp [toFun, FormalMultilinearSeries.sum]
    rw [tsum_eq_zero_add']
    · simp
      unfold toFormalMultilinearSeries
      simp [FormalMultilinearSeries.coeff, coeff]
    · simp
      exact summable_zero
  conv =>
    arg 3
    rw [← this]
  apply ContinuousAt.tendsto
  have h_hsum := FormalMultilinearSeries.hasFPowerSeriesOnBall _ h_analytic
  replace h_hsum := HasFPowerSeriesOnBall.hasFPowerSeriesAt h_hsum
  exact HasFPowerSeriesAt.continuousAt h_hsum

theorem toFun_IsBigO_one {s : LazySeries} (h_analytic : s.analytic) {F : ℝ → ℝ}
    (hF : Tendsto F atTop (nhds 0)) : ((toFun s) ∘ F) =O[atTop] (1 : ℝ → ℝ) := by
  revert h_analytic
  apply s.recOn
  · simp [toFun_nil]
    intro
    apply isBigO_zero
  · intro s_hd s_tl h_analytic
    apply isBigO_const_of_tendsto (y := s_hd) _ (by exact ne_zero_of_eq_one rfl)
    apply Tendsto.comp _ hF
    apply toFun_tendsto_head h_analytic

@[simp]
theorem apply_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    apply .nil ms = Seq.nil := by
  simp [apply, apply_aux, Seq.corec_nil]

@[simp]
theorem apply_cons {s_hd : ℝ} {s_tl : LazySeries}
    {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    (apply (.cons s_hd s_tl) ms) = .cons (0, PreMS.const s_hd _) ((apply s_tl ms).mul ms) := by
  simp [apply]
  conv =>
    lhs
    rw [Seq.corec_cons (by rfl)]
    simp [one]
    arg 1
    arg 1
    unfold const
  rw [merge1_cons_head_cons]
  simp [Seq.cons_eq_cons, one, ← merge1_mul_comm_right]
  congr 1
  let motive : Seq (PreMS (basis_hd :: basis_tl)) → Seq (PreMS (basis_hd :: basis_tl)) → Prop := fun x y =>
    ∃ (X : PreMS (basis_hd :: basis_tl)), ∃ s,
      x = Seq.corec (apply_aux ms) (X.mul ms, s) ∧
      y = Seq.map (fun x ↦ x.mul ms) (Seq.corec (apply_aux ms) (X, s))
  apply Seq.Eq.coind motive
  · intro x y ih
    simp [motive] at ih
    obtain ⟨X, s, hx, hy⟩ := ih
    subst hx hy
    apply s.recOn
    · right
      unfold apply_aux
      simp [Seq.corec_nil]
    · intro s_hd s_tl
      left
      use ?_, ?_, ?_
      constructor
      · unfold apply_aux
        simp
        rw [Seq.corec_cons]
        pick_goal 2
        · simp
          constructor
          · exact Eq.refl _
          · exact Eq.refl _
        congr
        · exact Eq.refl _
        · exact Eq.refl _
      constructor
      · unfold apply_aux
        rw [Seq.corec_cons]
        pick_goal 2
        · simp
          constructor
          · exact Eq.refl _
          · exact Eq.refl _
        simp
        congr
        · rw [mul_mulConst]
        · exact Eq.refl _
      simp only [motive]
      use ?_, s_tl
      constructor
      · unfold apply_aux
        simp
        congr 2
        exact Eq.refl _
      · unfold apply_aux
        simp
  · simp [motive]
    use const 1 (basis_hd :: basis_tl), s_tl

@[simp]
theorem apply_cons_leadingExp {s_hd : ℝ} {s_tl : LazySeries} {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    (apply (.cons s_hd s_tl) ms).leadingExp = 0 := by
  simp [leadingExp]

theorem apply_leadingExp_le_zero {s : LazySeries} {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    (apply s ms).leadingExp ≤ 0 := by
  apply s.recOn <;> simp [leadingExp]

theorem apply_wellOrdered {s : LazySeries} {basis : Basis}
    {ms : PreMS basis}
    (h_wo : ms.wellOrdered) (h_neg : ms.hasNegativeLeading) :
    (apply s ms).wellOrdered := by
  cases basis with
  | nil =>
    simp [apply, default]
    exact zero_wellOrdered
  | cons basis_hd basis_tl =>
    by_cases h_ms_ne_nil : ms = .nil
    · rw [h_ms_ne_nil]
      apply s.recOn
      · simp
        exact wellOrdered.nil
      · intro s_hd s_tl
        simp
        apply wellOrdered.cons_nil
        exact const_wellOrdered
    simp [apply]
    apply merge1_wellOrdered
    · let motive : Seq (PreMS (basis_hd :: basis_tl)) → Prop := fun a =>
        ∃ X s, a = Seq.corec (apply_aux ms) (X, s) ∧ X.wellOrdered
      apply Seq.All.coind motive
      · intro hd tl ih
        simp only [motive] at ih ⊢
        obtain ⟨X, s, h_eq⟩ := ih
        revert h_eq
        apply s.recOn
        · intro h_eq
          rw [Seq.corec_nil] at h_eq
          · simp at h_eq
          simp [apply_aux]
        intro s_hd s_tl h_eq
        rw [Seq.corec_cons] at h_eq
        pick_goal 2
        · simp only [apply_aux, Seq.recOn_cons]
          exact Eq.refl _
        simp [Seq.cons_eq_cons] at h_eq
        obtain ⟨⟨h_hd, h_tl⟩, hX_wo⟩ := h_eq
        constructor
        · rw [h_hd]
          exact mulConst_wellOrdered hX_wo
        use ?_, ?_
        constructor
        · exact h_tl
        · exact mul_wellOrdered hX_wo h_wo
      · simp only [motive]
        use one _, s
        simp
        exact const_wellOrdered
    · simp [hasNegativeLeading] at h_neg
      let motive : Seq (PreMS (basis_hd :: basis_tl)) → Prop := fun a =>
        ∃ X s, a = Seq.corec (apply_aux ms) (X, s) ∧ X ≠ .nil
      apply Seq.Sorted.coind (r := (fun x1 x2 ↦ x1 > x2)) motive
      · intro hd tl ih
        simp only [motive] at ih ⊢
        obtain ⟨X, s, h_eq, hX_ne_nil⟩ := ih
        revert h_eq
        apply s.recOn
        · intro h_eq
          rw [Seq.corec_nil] at h_eq
          · simp at h_eq
          simp [apply_aux]
        intro s_hd s_tl h_eq
        rw [Seq.corec_cons] at h_eq
        pick_goal 2
        · simp only [apply_aux, Seq.recOn_cons]
          exact Eq.refl _
        simp [Seq.cons_eq_cons] at h_eq
        obtain ⟨h_hd, h_tl⟩ := h_eq
        constructor
        · rw [h_tl]
          apply s_tl.recOn
          · rw [Seq.corec_nil]
            · simp
            · simp [apply_aux]
          intro s_tl_hd s_tl_tl
          rw [Seq.corec_cons]
          pick_goal 2
          · simp only [apply_aux, Seq.recOn_cons]
            exact Eq.refl _
          simp [h_hd, lt_iff_lt]
          conv => rhs; rw [← add_zero X.leadingExp]
          apply WithBot.add_lt_add_left
          · contrapose hX_ne_nil
            simp at hX_ne_nil ⊢
            rwa [leadingExp_eq_bot]
          · exact h_neg
        use ?_, ?_
        constructor
        · exact h_tl
        · intro h
          apply mul_eq_nil at h
          tauto
      · simp only [motive]
        use one _, s
        constructor
        · rfl
        · simp [one, const]

theorem apply_isApproximation {s : LazySeries} (h_analytic : analytic s) {basis : Basis}
    {ms : PreMS basis}
    (h_basis : MS.wellOrderedBasis basis) (h_wo : ms.wellOrdered)
    (h_neg : ms.hasNegativeLeading) {F : ℝ → ℝ}
    (h_approx : ms.isApproximation F basis) : (apply s ms).isApproximation (s.toFun ∘ F) basis := by
  have hF_tendsto_zero : Tendsto F atTop (nhds 0) := by
    apply hasNegativeLeading_tendsto_zero h_neg h_approx
  cases basis with
  | nil => cases h_neg
  | cons basis_hd basis_tl =>
    simp [hasNegativeLeading] at h_neg
    let motive : (F : ℝ → ℝ) → (ms : PreMS (basis_hd :: basis_tl)) → Prop := fun F' ms' =>
      ∃ (s : LazySeries), (analytic s) ∧
        ∃ X Y fX fY, F' =ᶠ[atTop] fX + fY * s.toFun ∘ F ∧ ms' = X + ((s.apply ms).mul Y) ∧
        X.wellOrdered ∧ X.isApproximation fX (basis_hd :: basis_tl) ∧
        Y.wellOrdered ∧ Y.isApproximation fY (basis_hd :: basis_tl)
    apply isApproximation.coind motive
    · intro f ms' ih
      simp [motive] at ih
      obtain ⟨s, h_analytic, ⟨X, Y, fX, fY, hf_eq, h_ms_eq, hX_wo, hX_approx, hY_wo, hY_approx⟩⟩ := ih
      have hF_in_ball : ∀ᶠ x in atTop, F x ∈ EMetric.ball 0 (toFormalMultilinearSeries s).radius := by
        cases h_rad : s.toFormalMultilinearSeries.radius with
        | top => simp
        | coe r =>
          have := NormedAddCommGroup.tendsto_nhds_zero.mp hF_tendsto_zero
          simp [analytic] at h_analytic
          specialize this r (by simpa [h_rad] using h_analytic)
          simpa using this
      revert h_ms_eq hX_wo hX_approx
      apply X.recOn
      · intro h_ms_eq _ hX_approx
        replace hX_approx := isApproximation_nil hX_approx
        revert h_ms_eq hY_wo hY_approx
        apply Y.recOn
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
          revert h_ms_eq hf_eq h_analytic hF_in_ball
          apply s.recOn
          · intro h_analytic hf_eq hF_in_ball h_ms_eq
            left
            constructor
            · simpa [apply_nil] using h_ms_eq
            · trans; exact hf_eq
              simpa [toFun_nil]
          · intro s_hd s_tl h_analytic hf_eq hF_in_ball h_ms_eq
            right
            simp [-apply_cons] at h_ms_eq -- TODO: rewrite
            rw [apply_cons] at h_ms_eq
            simp only [mul_cons_cons, zero_add] at h_ms_eq
            rw [mul_assoc'] at h_ms_eq
            pick_goal 2
            · exact apply_wellOrdered h_wo h_neg
            use Y_deg
            use (const s_hd basis_tl).mul Y_coef
            use (mulMonomial Y_tl (const s_hd basis_tl) 0) + ((apply s_tl ms).mul (ms.mul (Seq.cons (Y_deg, Y_coef) Y_tl)))
            use fun x ↦ s_hd * (YC x)
            constructor
            · exact h_ms_eq
            · constructor
              · apply mul_isApproximation (MS.wellOrderedBasis_tail h_basis)
                · apply const_isApproximation_const (MS.wellOrderedBasis_tail h_basis)
                · exact hY_coef
              · constructor
                · intro deg h_deg
                  apply EventuallyEq.trans_isLittleO (f₂ := fY * toFun (Seq.cons s_hd s_tl) ∘ F)
                  · trans; exact hf_eq
                    apply eventuallyEq_iff_sub.mpr
                    simpa
                  conv =>
                    rhs; ext x; rw [← mul_one (basis_hd x ^ deg)]
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
                  use ms.mul (Seq.cons (Y_deg, Y_coef) Y_tl)
                  use (fun x ↦ s_hd * (fY x - basis_hd x ^ Y_deg * YC x))
                  use F * fY
                  constructor
                  · simp only [EventuallyEq] at hf_eq hX_approx ⊢
                    apply Eventually.mono <| (hf_eq.and hX_approx).and hF_in_ball
                    intro x ⟨⟨hf_eq, hX_approx⟩, hF_in_ball⟩
                    simp [hf_eq, hX_approx, toFun_cons h_analytic hF_in_ball]
                    ring_nf!
                  constructor
                  · rfl
                  constructor
                  · apply mulMonomial_wellOrdered hY_tl_wo
                    exact const_wellOrdered
                  constructor
                  · have := mulMonomial_isApproximation h_basis (m_coef := const s_hd basis_tl) (m_deg := 0) hY_tl
                      (const_isApproximation_const (MS.wellOrderedBasis_tail h_basis))
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
        apply Y.recOn
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
          revert h_ms_eq hf_eq h_analytic hF_in_ball
          apply s.recOn
          · intro h_analytic hf_eq hF_in_ball h_ms_eq
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
          · intro s_hd s_tl h_analytic hf_eq hF_in_ball h_ms_eq
            simp only [apply_cons, zero_add, mul_assoc, mul_cons_cons] at h_ms_eq
            rw [add_cons_cons] at h_ms_eq
            split_ifs at h_ms_eq
            · use X_deg
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
                  rhs; ext x; rw [← mul_one (basis_hd x ^ deg)]
                apply IsLittleO.mul_isBigO
                · apply hY_comp deg
                  linarith
                apply toFun_IsBigO_one h_analytic hF_tendsto_zero
              simp [motive]
              use .cons s_hd s_tl
              constructor
              · exact h_analytic
              focus
              replace h_ms_eq : ms' = Seq.cons (X_deg, X_coef)
                  (add X_tl
                  ((apply (Seq.cons s_hd s_tl) ms).mul (Seq.cons (Y_deg, Y_coef) Y_tl))) := by
                rw [h_ms_eq]
                congr
                simp [apply_cons]
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
                  lhs; ext x; rw [show f x + (-fX x - fY x * toFun (Seq.cons s_hd s_tl) (F x)) =
                    f x - (fX x + fY x * toFun (Seq.cons s_hd s_tl) (F x)) by ring_nf]
                apply eventuallyEq_iff_sub.mp
                exact hf_eq
              constructor
              · simp
              constructor
              · exact hX_tl_wo
              constructor
              · exact hX_tl
              constructor
              · exact hY_wo
              · exact hY_approx
            · simp only [← add_assoc] at h_ms_eq
              use Y_deg
              use (const s_hd basis_tl).mul Y_coef
              use ?_
              use fun x ↦ s_hd * YC x
              constructor
              · exact h_ms_eq
              constructor
              · apply mul_isApproximation (MS.wellOrderedBasis_tail h_basis)
                · apply const_isApproximation_const (MS.wellOrderedBasis_tail h_basis)
                · exact hY_coef
              constructor
              · intro deg h_deg
                apply EventuallyEq.trans_isLittleO hf_eq
                apply IsLittleO.add
                · apply hX_comp deg
                  linarith
                conv =>
                  rhs; ext x; rw [← mul_one (basis_hd x ^ deg)]
                apply IsLittleO.mul_isBigO
                · apply hY_comp deg h_deg
                apply toFun_IsBigO_one h_analytic hF_tendsto_zero
              simp [motive]
              use s_tl
              constructor
              · apply tail_analytic h_analytic
              use HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) (Seq.cons (X_deg, X_coef) X_tl) (mulMonomial Y_tl (const s_hd basis_tl) 0)
              use ms.mul (Seq.cons (Y_deg, Y_coef) Y_tl)
              use fun x ↦ fX x + s_hd * (fY x - basis_hd x ^ Y_deg * YC x)
              use F * fY
              constructor
              · simp only [EventuallyEq] at hf_eq ⊢
                apply Eventually.mono <| hf_eq.and hF_in_ball
                intro x ⟨hf_eq, hF_in_ball⟩
                simp [hf_eq, toFun_cons h_analytic hF_in_ball]
                ring
              constructor
              · rw [mul_assoc']
                exact apply_wellOrdered h_wo h_neg
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
                  · exact const_isApproximation_const (MS.wellOrderedBasis_tail h_basis)
              constructor
              · apply mul_wellOrdered
                · exact h_wo
                · exact hY_wo
              · apply mul_isApproximation h_basis
                · exact h_approx
                · exact hY_approx
            · have h : X_deg = Y_deg := by linarith
              simp only [← add_assoc] at h_ms_eq
              use X_deg
              use X_coef + ((const s_hd basis_tl).mul Y_coef)
              use ?_
              use fun x ↦ XC x + s_hd * YC x
              constructor
              · exact h_ms_eq
              constructor
              · apply add_isApproximation
                · exact hX_coef
                · apply mul_isApproximation (MS.wellOrderedBasis_tail h_basis)
                  · apply const_isApproximation_const (MS.wellOrderedBasis_tail h_basis)
                  · exact hY_coef
              constructor
              · intro deg h_deg
                apply EventuallyEq.trans_isLittleO hf_eq
                apply IsLittleO.add
                · exact hX_comp deg h_deg
                conv =>
                  rhs; ext x; rw [← mul_one (basis_hd x ^ deg)]
                apply IsLittleO.mul_isBigO
                · exact hY_comp deg (h ▸ h_deg)
                apply toFun_IsBigO_one h_analytic hF_tendsto_zero
              simp [motive]
              use s_tl
              constructor
              · exact tail_analytic h_analytic
              use HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) X_tl (mulMonomial Y_tl (const s_hd basis_tl) 0)
              use ms.mul (Seq.cons (Y_deg, Y_coef) Y_tl)
              use fun x ↦ (fX x - basis_hd x ^ X_deg * XC x) + s_hd * (fY x - basis_hd x ^ Y_deg * YC x)
              use F * fY
              constructor
              · simp only [EventuallyEq] at hf_eq ⊢
                apply Eventually.mono <| hf_eq.and hF_in_ball
                intro x ⟨hf_eq, hF_in_ball⟩
                simp [h, hf_eq, toFun_cons h_analytic hF_in_ball]
                ring
              constructor
              · rw [mul_assoc']
                exact apply_wellOrdered h_wo h_neg
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
                  · apply const_isApproximation_const (MS.wellOrderedBasis_tail h_basis)
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

theorem analytic_of_all_le_one {s : LazySeries} (h : s.All fun x ↦ |x| ≤ 1) : s.analytic := by
  simp [analytic]
  apply lt_of_lt_of_le (b := 1)
  · simp
  apply FormalMultilinearSeries.le_radius_of_bound (C := 1)
  simp only [toFormalMultilinearSeries_norm]
  intro n
  have := Seq.all_get h (n := n)
  generalize s.get? n = t at *
  cases t with
  | none => simp
  | some x =>
    simpa using this

end LazySeries

end PreMS

end TendstoTactic
