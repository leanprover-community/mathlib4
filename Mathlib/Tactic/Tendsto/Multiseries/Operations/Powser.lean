/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Tactic.Tendsto.Multiseries.Basic
import Mathlib.Tactic.Tendsto.Multiseries.Operations.Mul
import Mathlib.Tactic.Tendsto.Multiseries.Trimming

/-!
# Substituting multiseries into analytic series

-/



open Filter Asymptotics Stream' Seq

namespace TendstoTactic

namespace PreMS

abbrev LazySeries := Seq ℝ

namespace LazySeries

-- I do not know why it is necessary
universe v in
@[cases_eliminator]
def recOn {motive : LazySeries → Sort v} (s : LazySeries) (nil : motive nil)
    (cons : ∀ x s, motive (cons x s)) :
    motive s :=
  Stream'.Seq.recOn s nil cons

noncomputable def apply_aux {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (ms : PreMS (basis_hd :: basis_tl)) : PreMS (basis_hd :: basis_tl) × LazySeries →
    Option ((PreMS (basis_hd :: basis_tl)) × (PreMS (basis_hd :: basis_tl) × LazySeries)) :=
      fun (cur_power, cur_s) =>
        match destruct cur_s with
        | none => none
        | some (c, cs) => .some ((mulConst cur_power c), (cur_power.mul ms, cs))

noncomputable def apply (s : LazySeries) {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (ms : PreMS (basis_hd :: basis_tl)) : PreMS (basis_hd :: basis_tl) :=
  let terms := Seq.corec (apply_aux ms) (PreMS.one _, s) -- [c0, c1 * ms, c2, * ms^2, ...]
  merge1 terms

-- theorems

noncomputable def coeff (s : LazySeries) (n : ℕ) : ℝ :=
  (s.get? n).getD 0

noncomputable def toFormalMultilinearSeries (s : LazySeries) : FormalMultilinearSeries ℝ ℝ ℝ :=
  .ofScalars ℝ (coeff s)

theorem toFormalMultilinearSeries_coeff {s : LazySeries} {n : ℕ} :
    s.toFormalMultilinearSeries.coeff n = (s.get? n).getD 0 := by
  unfold FormalMultilinearSeries.coeff toFormalMultilinearSeries
  eta_expand
  simp_rw [Pi.one_apply, FormalMultilinearSeries.ofScalars_apply_eq, coeff]
  simp

theorem toFormalMultilinearSeries_norm {s : LazySeries} {n : ℕ} :
    ‖(s.toFormalMultilinearSeries) n‖ = |(s.get? n).getD 0| := by
  simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef, Real.norm_eq_abs]
  congr
  exact toFormalMultilinearSeries_coeff

def analytic (s : LazySeries) : Prop := 0 < s.toFormalMultilinearSeries.radius

open ENNReal in
theorem tail_radius_eq {s_hd : ℝ} {s_tl : LazySeries} :
    (toFormalMultilinearSeries (.cons s_hd s_tl)).radius =
    s_tl.toFormalMultilinearSeries.radius := by
  apply le_antisymm
  · refine le_of_forall_nnreal_lt (fun r hr ↦ ?_)
    obtain ⟨C, ⟨_, h_bound⟩⟩ := FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius _ hr
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
    obtain ⟨C, ⟨_, h_bound⟩⟩ := FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius _ hr
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

@[simp]
theorem toFun_nil : toFun Seq.nil = 0 := by
  simp [toFun]
  unfold toFormalMultilinearSeries coeff
  simp
  unfold FormalMultilinearSeries.ofScalars FormalMultilinearSeries.sum
  simp
  rfl

theorem toFun_cons {s_hd : ℝ} {s_tl : LazySeries} {t : ℝ}
    (h : analytic (Seq.cons s_hd s_tl))
    (ht : t ∈ EMetric.ball 0 (toFormalMultilinearSeries (Seq.cons s_hd s_tl)).radius):
    toFun (.cons s_hd s_tl) t = s_hd + ((toFun s_tl) t) * t := by
  have h_tl := tail_analytic h
  have h_hsum := FormalMultilinearSeries.hasFPowerSeriesOnBall _ h
  replace h_hsum := HasFPowerSeriesOnBall.hasSum h_hsum ht
  have h_hsum_tl := FormalMultilinearSeries.hasFPowerSeriesOnBall _ h_tl
  replace h_hsum_tl := HasFPowerSeriesOnBall.hasSum h_hsum_tl (tail_radius_eq ▸ ht)
  simp at h_hsum h_hsum_tl
  simp_rw [toFormalMultilinearSeries_coeff] at h_hsum h_hsum_tl
  unfold toFun
  generalize (toFormalMultilinearSeries (Seq.cons s_hd s_tl)).sum t = a at *
  generalize (toFormalMultilinearSeries s_tl).sum t = b at *
  apply HasSum.unique h_hsum
  replace h_hsum_tl := HasSum.mul_right t h_hsum_tl
  ring_nf at h_hsum_tl
  conv at h_hsum_tl =>
    arg 1
    ext i
    rw [← pow_succ']
    rw [show Seq.get? s_tl i = Seq.get? (.cons s_hd s_tl) (i + 1) by simp]
  have := HasSum.zero_add (f := (fun n ↦ t ^ n * (Seq.get? (Seq.cons s_hd s_tl) n).getD 0))
    h_hsum_tl
  simpa using this

theorem toFun_tendsto_head {s_hd : ℝ} {s_tl : LazySeries}
    (h_analytic : analytic (.cons s_hd s_tl)) :
    Tendsto (toFun (.cons s_hd s_tl)) (nhds 0) (nhds s_hd) := by
  have : (toFun (.cons s_hd s_tl)) 0 = s_hd := by
    simp [toFun, FormalMultilinearSeries.sum]
    rw [tsum_eq_zero_add']
    · simp
      unfold toFormalMultilinearSeries
      simp [FormalMultilinearSeries.ofScalars, FormalMultilinearSeries.coeff, coeff]
    · simp
      exact summable_zero
  conv =>
    arg 3
    rw [← this]
  apply ContinuousAt.tendsto
  have h_hsum := FormalMultilinearSeries.hasFPowerSeriesOnBall _ h_analytic
  replace h_hsum := HasFPowerSeriesOnBall.hasFPowerSeriesAt h_hsum
  exact HasFPowerSeriesAt.continuousAt h_hsum

theorem toFun_IsBigO_one {s : LazySeries} (h_analytic : s.analytic) {f : ℝ → ℝ}
    (hF : Tendsto f atTop (nhds 0)) : ((toFun s) ∘ f) =O[atTop] (1 : ℝ → ℝ) := by
  cases' s with s_hd s_tl
  · simp [toFun_nil]
    apply isBigO_zero
  · apply isBigO_const_of_tendsto (y := s_hd) _ (by exact ne_zero_of_eq_one rfl)
    apply Tendsto.comp _ hF
    apply toFun_tendsto_head h_analytic

theorem mul_bounded_majorated {f g basis_hd : ℝ → ℝ} {exp : ℝ} (hf : majorated f basis_hd exp)
    (hg : g =O[atTop] (fun _ ↦ (1 : ℝ))) :
    majorated (f * g) basis_hd exp := by
  simp only [majorated] at *
  intro exp h_exp
  conv =>
    rhs; ext t; rw [← mul_one (basis_hd t ^ exp)]
  apply IsLittleO.mul_isBigO
  · exact hf _ h_exp
  · exact hg

@[simp]
theorem apply_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    apply .nil ms = Seq.nil := by
  simp [apply, apply_aux, Seq.corec_nil]

@[simp]
theorem apply_cons {s_hd : ℝ} {s_tl : LazySeries}
    {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    (apply (.cons s_hd s_tl) ms) = .cons (0, PreMS.const _ s_hd) ((apply s_tl ms).mul ms) := by
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
  let motive : Seq (PreMS (basis_hd :: basis_tl)) → Seq (PreMS (basis_hd :: basis_tl)) → Prop :=
    fun x y =>
    ∃ (X : PreMS (basis_hd :: basis_tl)), ∃ s,
      x = Seq.corec (apply_aux ms) (X.mul ms, s) ∧
      y = Seq.map (fun X ↦ X.mul ms) (Seq.corec (apply_aux ms) (X, s))
  apply Seq.eq_of_bisim' motive
  · simp [motive]
    use const (basis_hd :: basis_tl) 1, s_tl
  · intro x y ih
    simp [motive] at ih
    obtain ⟨X, s, hx, hy⟩ := ih
    subst hx hy
    cases' s with s_hd s_tl
    · right
      unfold apply_aux
      simp [Seq.corec_nil]
    · left
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
        · rw [mul_mulConst_left]
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

@[simp]
theorem apply_cons_leadingExp {s_hd : ℝ} {s_tl : LazySeries} {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS (basis_hd :: basis_tl)} :
    (apply (.cons s_hd s_tl) ms).leadingExp = 0 := by
  simp

theorem apply_leadingExp_le_zero {s : LazySeries} {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS (basis_hd :: basis_tl)} :
    (apply s ms).leadingExp ≤ 0 := by
  cases' s <;> simp

theorem apply_WellOrdered {s : LazySeries} {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS (basis_hd :: basis_tl)}
    (h_wo : ms.WellOrdered) (h_neg : ms.leadingExp < 0) :
    (apply s ms).WellOrdered := by
  by_cases h_ms_ne_nil : ms = .nil
  · rw [h_ms_ne_nil]
    cases' s with s_hd s_tl
    · simp
      exact WellOrdered.nil
    · simp
      apply WellOrdered.cons_nil
      exact const_WellOrdered
  simp [apply]
  apply merge1_WellOrdered
  · let motive : Seq (PreMS (basis_hd :: basis_tl)) → Prop := fun a =>
      ∃ X s, a = Seq.corec (apply_aux ms) (X, s) ∧ X.WellOrdered
    apply Seq.All.coind motive
    · simp only [motive]
      use one _, s
      simp
      exact const_WellOrdered
    · intro hd tl ih
      simp only [motive] at ih ⊢
      obtain ⟨X, s, h_eq⟩ := ih
      cases' s with s_hd s_tl
      · rw [Seq.corec_nil] at h_eq
        · simp at h_eq
        simp [apply_aux]
      rw [Seq.corec_cons] at h_eq
      pick_goal 2
      · simp only [apply_aux]
        exact Eq.refl _
      simp [Seq.cons_eq_cons] at h_eq
      obtain ⟨⟨h_hd, h_tl⟩, hX_wo⟩ := h_eq
      constructor
      · rw [h_hd]
        exact mulConst_WellOrdered hX_wo
      use ?_, ?_
      constructor
      · exact h_tl
      · exact mul_WellOrdered hX_wo h_wo
  · let motive : Seq (PreMS (basis_hd :: basis_tl)) → Prop := fun a =>
      ∃ X s, a = Seq.corec (apply_aux ms) (X, s) ∧ X ≠ .nil
    apply Seq.Pairwise.coind_trans (R := (fun x1 x2 ↦ x1 > x2)) motive
    · simp only [motive]
      use one _, s
      constructor
      · rfl
      · simp [one, const]
    · intro hd tl ih
      simp only [motive] at ih ⊢
      obtain ⟨X, s, h_eq, hX_ne_nil⟩ := ih
      cases' s with s_hd s_tl
      · rw [Seq.corec_nil] at h_eq
        · simp at h_eq
        simp [apply_aux]
      rw [Seq.corec_cons] at h_eq
      pick_goal 2
      · simp only [apply_aux]
        exact Eq.refl _
      simp [Seq.cons_eq_cons] at h_eq
      obtain ⟨h_hd, h_tl⟩ := h_eq
      constructor
      · rw [h_tl]
        cases' s_tl with s_tl_hd s_tl_tl
        · rw [Seq.corec_nil]
          · simp
          · simp [apply_aux]
        rw [Seq.corec_cons]
        pick_goal 2
        · simp only [apply_aux]
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

theorem apply_Approximates {s : LazySeries} (h_analytic : analytic s) {basis_hd : ℝ → ℝ}
    {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl)) (h_wo : ms.WellOrdered)
    (h_neg : ms.leadingExp < 0) {f : ℝ → ℝ}
    (h_approx : ms.Approximates f) : (apply s ms).Approximates (s.toFun ∘ f) := by
  have hF_tendsto_zero : Tendsto f atTop (nhds 0) := by
    apply neg_leadingExp_tendsto_zero h_neg h_approx
  let motive : (f : ℝ → ℝ) → (ms : PreMS (basis_hd :: basis_tl)) → Prop := fun f' ms' =>
    ∃ (s : LazySeries), (analytic s) ∧
      ∃ X Y fX fY, f' =ᶠ[atTop] fX + fY * s.toFun ∘ f ∧ ms' = X + ((s.apply ms).mul Y) ∧
      X.WellOrdered ∧ X.Approximates fX ∧
      Y.WellOrdered ∧ Y.Approximates fY
  apply Approximates.coind motive
  · simp [motive]
    use s
    constructor
    · exact h_analytic
    use .nil, one _, 0, 1
    simp
    constructor
    · apply WellOrdered.nil
    constructor
    · apply Approximates.nil
      rfl
    constructor
    · apply const_WellOrdered
    · apply one_Approximates h_basis
  · intro f' ms' ih
    simp [motive] at ih
    obtain ⟨s, h_analytic, ⟨X, Y, fX, fY, hf_eq, h_ms_eq, hX_wo, hX_approx, hY_wo, hY_approx⟩⟩ := ih
    have hF_in_ball : ∀ᶠ x in atTop,
        f x ∈ EMetric.ball 0 (toFormalMultilinearSeries s).radius := by
      cases h_rad : s.toFormalMultilinearSeries.radius with
      | top => simp
      | coe r =>
        have := NormedAddCommGroup.tendsto_nhds_zero.mp hF_tendsto_zero
        simp [analytic] at h_analytic
        specialize this r (by simpa [h_rad] using h_analytic)
        simpa using this
    cases' X with X_exp X_coef X_tl
    · apply Approximates_nil at hX_approx
      cases' Y with Y_exp Y_coef Y_tl
      · apply Approximates_nil at hY_approx
        left
        constructor
        · simpa using h_ms_eq
        · trans; exact hf_eq
          conv =>
            rhs
            ext
            rw [← zero_add 0]
          apply EventuallyEq.add
          · exact hX_approx
          · simp only [Filter.EventuallyEq] at hY_approx ⊢
            apply Filter.Eventually.mono hY_approx
            intro t h
            simp [h]
      · obtain ⟨fYC, hY_coef, hY_maj, hY_tl⟩ := Approximates_cons hY_approx
        obtain ⟨_, _, hY_tl_wo⟩ := WellOrdered_cons hY_wo
        cases' s with s_hd s_tl
        · left
          constructor
          · simpa [apply_nil] using h_ms_eq
          · trans; exact hf_eq
            simpa [toFun_nil]
        · right
          simp [-apply_cons] at h_ms_eq -- TODO: rewrite
          rw [apply_cons] at h_ms_eq
          simp only [mul_cons_cons, zero_add] at h_ms_eq
          rw [mul_assoc'] at h_ms_eq
          pick_goal 2
          · exact apply_WellOrdered h_wo h_neg
          use Y_exp, (const basis_tl s_hd).mul Y_coef,
            (mulMonomial Y_tl (const basis_tl s_hd) 0) +
              ((apply s_tl ms).mul (ms.mul (Seq.cons (Y_exp, Y_coef) Y_tl))),
            fun t ↦ s_hd * (fYC t)
          constructor
          · exact h_ms_eq
          · constructor
            · apply mul_Approximates (h_basis.tail)
              · apply const_Approximates (h_basis.tail)
              · exact hY_coef
            · constructor
              · apply majorated_of_EventuallyEq (f := fY * toFun (Seq.cons s_hd s_tl) ∘ f)
                · trans; exact hf_eq
                  apply eventuallyEq_iff_sub.mpr
                  simpa
                · apply mul_bounded_majorated hY_maj
                  exact toFun_IsBigO_one h_analytic hF_tendsto_zero
              · simp only [motive]
                use s_tl
                constructor
                · apply tail_analytic h_analytic
                use mulMonomial Y_tl (const basis_tl s_hd) 0,
                  ms.mul (Seq.cons (Y_exp, Y_coef) Y_tl),
                  fun t ↦ s_hd * (fY t - basis_hd t ^ Y_exp * fYC t), f * fY
                constructor
                · simp only [EventuallyEq] at hf_eq hX_approx ⊢
                  apply Eventually.mono <| (hf_eq.and hX_approx).and hF_in_ball
                  intro t ⟨⟨hf_eq, hX_approx⟩, hF_in_ball⟩
                  simp [hf_eq, hX_approx, toFun_cons h_analytic hF_in_ball]
                  ring_nf!
                constructor
                · rfl
                constructor
                · apply mulMonomial_WellOrdered hY_tl_wo
                  exact const_WellOrdered
                constructor
                · have := mulMonomial_Approximates h_basis (M_coef := const basis_tl s_hd)
                    (M_exp := 0) hY_tl
                    (const_Approximates (h_basis.tail))
                  simpa using this
                constructor
                · apply mul_WellOrdered h_wo hY_wo
                apply mul_Approximates h_basis
                · exact h_approx
                · exact hY_approx
    · right
      obtain ⟨fXC, hX_coef, hX_maj, hX_tl⟩ := Approximates_cons hX_approx
      obtain ⟨_, _, hX_tl_wo⟩ := WellOrdered_cons hX_wo
      cases' Y with Y_exp Y_coef Y_tl
      · apply Approximates_nil at hY_approx
        replace hf_eq : f' =ᶠ[atTop] fX := by
          trans
          · exact hf_eq
          conv =>
            rhs
            ext t
            rw [← add_zero (fX t)]
          apply EventuallyEq.add
          · rfl
          conv => rhs; ext t; rw [← zero_mul ((s.toFun ∘ f) t)]
          apply EventuallyEq.mul
          · exact hY_approx
          · rfl
        simp at h_ms_eq -- #1 (i've copypasted it to below)
        use X_exp, X_coef, X_tl, fXC
        constructor
        · exact h_ms_eq
        constructor
        · exact hX_coef
        constructor
        · apply majorated_of_EventuallyEq hf_eq
          exact hX_maj
        · simp [motive]
          use s
          constructor
          · exact h_analytic
          use X_tl, .nil, fun t ↦ fX t - basis_hd t ^ X_exp * fXC t, 0
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
          · apply WellOrdered.nil
          · apply Approximates.nil
            rfl
      · obtain ⟨fYC, hY_coef, hY_maj, hY_tl⟩ := Approximates_cons hY_approx
        obtain ⟨_, _, hY_tl_wo⟩ := WellOrdered_cons hY_wo
        cases' s with s_hd s_tl
        · replace hf_eq : f' =ᶠ[atTop] fX := by
            trans
            · exact hf_eq
            conv =>
              rhs
              ext t
              rw [← add_zero (fX t)]
            apply EventuallyEq.add
            · rfl
            conv => rhs; ext t; rw [← mul_zero (fY t)]
            apply EventuallyEq.mul
            · rfl
            · simp [toFun_nil]
              rfl
          simp [apply_nil] at h_ms_eq -- copypaste from #1
          use X_exp, X_coef, X_tl, fXC
          constructor
          · exact h_ms_eq
          constructor
          · exact hX_coef
          constructor
          · apply majorated_of_EventuallyEq hf_eq
            exact hX_maj
          · simp [motive]
            use .nil
            constructor
            · exact h_analytic
            use X_tl, .nil, fun t ↦ fX t - basis_hd t ^ X_exp * fXC t, 0
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
            · exact WellOrdered.nil
            · apply Approximates.nil
              rfl
        · simp only [apply_cons, zero_add, mul_assoc, mul_cons_cons] at h_ms_eq
          rw [add_cons_cons] at h_ms_eq
          split_ifs at h_ms_eq
          · use X_exp, X_coef, ?_, fXC
            constructor
            · exact h_ms_eq
            constructor
            · exact hX_coef
            constructor
            · apply majorated_of_EventuallyEq hf_eq
              rw [show X_exp = X_exp ⊔ Y_exp by simp; linarith]
              apply add_majorated hX_maj
              apply mul_bounded_majorated hY_maj
              exact toFun_IsBigO_one h_analytic hF_tendsto_zero
            simp [motive]
            use .cons s_hd s_tl
            constructor
            · exact h_analytic
            use X_tl, .cons (Y_exp, Y_coef) Y_tl, fun t ↦ fX t - basis_hd t ^ X_exp * fXC t, fY
            constructor
            · apply eventuallyEq_iff_sub.mpr
              eta_expand
              simp
              ring_nf
              conv =>
                lhs; ext t; rw [show f' t + (-fX t - fY t * toFun (Seq.cons s_hd s_tl) (f t)) =
                  f' t - (fX t + fY t * toFun (Seq.cons s_hd s_tl) (f t)) by ring_nf]
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
            use Y_exp, (const basis_tl s_hd).mul Y_coef, ?_, fun t ↦ s_hd * fYC t
            constructor
            · exact h_ms_eq
            constructor
            · apply mul_Approximates (h_basis.tail)
              · apply const_Approximates (h_basis.tail)
              · exact hY_coef
            constructor
            · apply majorated_of_EventuallyEq hf_eq
              rw [show Y_exp = X_exp ⊔ Y_exp by simp; linarith]
              apply add_majorated hX_maj
              apply mul_bounded_majorated hY_maj
              exact toFun_IsBigO_one h_analytic hF_tendsto_zero
            simp [motive]
            use s_tl
            constructor
            · apply tail_analytic h_analytic
            use HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) (Seq.cons (X_exp, X_coef) X_tl)
                (mulMonomial Y_tl (const basis_tl s_hd) 0),
              ms.mul (Seq.cons (Y_exp, Y_coef) Y_tl),
              fun t ↦ fX t + s_hd * (fY t - basis_hd t ^ Y_exp * fYC t), f * fY
            constructor
            · simp only [EventuallyEq] at hf_eq ⊢
              apply Eventually.mono <| hf_eq.and hF_in_ball
              intro t ⟨hf_eq, hF_in_ball⟩
              simp [hf_eq, toFun_cons h_analytic hF_in_ball]
              ring
            constructor
            · rw [mul_assoc']
              exact apply_WellOrdered h_wo h_neg
            constructor
            · apply add_WellOrdered
              · exact hX_wo
              apply mulMonomial_WellOrdered
              · exact hY_tl_wo
              · exact const_WellOrdered
            constructor
            · apply add_Approximates
              · exact hX_approx
              · conv =>
                  arg 2
                  ext t
                  rw [show s_hd = (fun u ↦ s_hd * (basis_hd t)^(0 : ℝ)) t by simp]
                apply mulMonomial_Approximates h_basis
                · exact hY_tl
                · exact const_Approximates (h_basis.tail)
            constructor
            · apply mul_WellOrdered
              · exact h_wo
              · exact hY_wo
            · apply mul_Approximates h_basis
              · exact h_approx
              · exact hY_approx
          · have h : X_exp = Y_exp := by linarith
            simp only [← add_assoc] at h_ms_eq
            use X_exp, X_coef + ((const basis_tl s_hd).mul Y_coef), ?_,
              fun t ↦ fXC t + s_hd * fYC t
            constructor
            · exact h_ms_eq
            constructor
            · apply add_Approximates
              · exact hX_coef
              · apply mul_Approximates (h_basis.tail)
                · apply const_Approximates (h_basis.tail)
                · exact hY_coef
            constructor
            · apply majorated_of_EventuallyEq hf_eq
              rw [show X_exp = X_exp ⊔ Y_exp by simp; linarith]
              apply add_majorated hX_maj
              apply mul_bounded_majorated hY_maj
              exact toFun_IsBigO_one h_analytic hF_tendsto_zero
            simp [motive]
            use s_tl
            constructor
            · exact tail_analytic h_analytic
            use HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) X_tl
                (mulMonomial Y_tl (const basis_tl s_hd) 0),
              ms.mul (Seq.cons (Y_exp, Y_coef) Y_tl),
              fun t ↦ (fX t - basis_hd t ^ X_exp * fXC t) + s_hd *
                (fY t - basis_hd t ^ Y_exp * fYC t),
              f * fY
            constructor
            · simp only [EventuallyEq] at hf_eq ⊢
              apply Eventually.mono <| hf_eq.and hF_in_ball
              intro t ⟨hf_eq, hF_in_ball⟩
              simp [h, hf_eq, toFun_cons h_analytic hF_in_ball]
              ring
            constructor
            · rw [mul_assoc']
              exact apply_WellOrdered h_wo h_neg
            constructor
            · apply add_WellOrdered
              · exact hX_tl_wo
              · apply mulMonomial_WellOrdered
                · exact hY_tl_wo
                · exact const_WellOrdered
            constructor
            · apply add_Approximates
              · exact hX_tl
              · conv =>
                  arg 2
                  ext t
                  rw [show s_hd = (fun u ↦ s_hd * (basis_hd u)^(0 : ℝ)) t by simp]
                apply mulMonomial_Approximates h_basis
                · exact hY_tl
                · apply const_Approximates (h_basis.tail)
            constructor
            · apply mul_WellOrdered
              · exact h_wo
              · exact hY_wo
            · apply mul_Approximates h_basis
              · exact h_approx
              · exact hY_approx

theorem analytic_of_all_le_one {s : LazySeries} (h : s.All fun x ↦ |x| ≤ 1) : s.analytic := by
  simp [analytic]
  apply lt_of_lt_of_le (b := 1)
  · simp
  apply FormalMultilinearSeries.le_radius_of_bound (C := 1)
  simp only [toFormalMultilinearSeries_norm]
  intro n
  cases' h_get : s.get? n with val
  · simp
  have := Seq.All_get h h_get
  simpa

section Zeros

def zeros : LazySeries := Seq.corec (fun () ↦ some (0, ())) ()

theorem zeros_eq_cons : zeros = .cons 0 zeros := by
  simp [zeros]
  nth_rw 1 [corec_cons]
  rfl

theorem zeros_get {n : ℕ} : zeros.get? n = .some 0 := by
  induction n with
  | zero =>
    rw [zeros_eq_cons]
    simp
  | succ =>
    rw [zeros_eq_cons]
    simpa

theorem zeros_toFun : zeros.toFun = 0 := by
  simp [toFun, toFormalMultilinearSeries]
  unfold FormalMultilinearSeries.sum FormalMultilinearSeries.ofScalars
  simp [coeff, zeros_get]
  rfl

theorem zeros_analytic : analytic zeros := by
  apply analytic_of_all_le_one
  apply All.coind (fun s ↦ s = zeros)
  · rfl
  · intro hd tl h_eq
    rw [zeros_eq_cons, Seq.cons_eq_cons] at h_eq
    rw [h_eq.left, h_eq.right]
    simp

-- I am almost sure we don't really need `h_wo` and `h_approx`
theorem zeros_apply_Approximates {basis_hd} {basis_tl} {ms : PreMS (basis_hd :: basis_tl)} {f : ℝ → ℝ}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl)) (h_wo : ms.WellOrdered) (h_approx : ms.Approximates f)
    (h_neg : ms.leadingExp < 0) : (zeros.apply ms).Approximates 0 := by
  rw [show 0 = zeros.toFun ∘ f by rw [zeros_toFun]; rfl]
  apply apply_Approximates zeros_analytic h_basis h_wo h_neg h_approx

end Zeros

end LazySeries

end PreMS

end TendstoTactic
