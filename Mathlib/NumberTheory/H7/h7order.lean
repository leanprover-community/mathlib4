/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.NormedSpace.Connected

set_option autoImplicit true
set_option linter.style.multiGoal false
set_option linter.style.cases false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars true
set_option linter.style.commandStart false
set_option linter.style.longFile 0

open BigOperators Module.Free Fintype
  Matrix Set Polynomial Finset Complex

open Differentiable AnalyticAt

lemma cexp_mul : deriv (fun x => cexp (c * x)) x = c * cexp (c * x) := by
  change deriv (fun x => exp ((fun x => c * x) x)) x = c * exp (c * x)
  rw [deriv_cexp]
  · rw [deriv_fun_mul]
    · simp only [deriv_const', zero_mul, deriv_id'', mul_one, zero_add]
      exact CommMonoid.mul_comm (cexp (c * x)) c
    · exact differentiableAt_const c
    · exact differentiableAt_fun_id
  · apply mul <| differentiable_const _; exact differentiable_fun_id

theorem zero_if_order_inf : ∀ (f : ℂ → ℂ) (z : ℂ) (hf : ∀ z, AnalyticAt ℂ f z),
  (∀ z, f z = 0) → analyticOrderAt f z₀ = ⊤ := by
  intros f z hf h0
  rw [analyticOrderAt_eq_top]
  refine (AnalyticAt.frequently_eq_iff_eventually_eq (hf z₀) ?_).mp ?_
  · exact analyticAt_const
  · refine Filter.Frequently.of_forall ?_
    · intros x
      exact h0 x

theorem order_inf_if_zero : ∀ (f : ℂ → ℂ) (z : ℂ) (hf : ∀ z, AnalyticAt ℂ f z),
 analyticOrderAt f z = ⊤ → (∀ z, f z = 0) := by
  intros f z hf hr
  have := @analyticOrderAt_eq_top ℂ _ _ _ _ f z
  rw [this] at hr
  rw [← AnalyticAt.frequently_eq_iff_eventually_eq (hf z)] at hr
  have hfon : AnalyticOnNhd ℂ f univ := by {
    unfold AnalyticOnNhd
    intros x hx
    simp_all only}
  have :=  AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero (hfon) ?_ ?_ hr
  · exact fun z ↦ this trivial
  · exact isPreconnected_univ
  · exact trivial
  · exact analyticAt_const

lemma zero_iff_order_inf : ∀ (f : ℂ → ℂ) (z : ℂ) (hf : ∀ z, AnalyticAt ℂ f z),
  (∀ z, f z = 0) ↔ analyticOrderAt f z = ⊤ := by
  intros f z hf
  constructor
  · exact zero_if_order_inf f z hf
  · exact order_inf_if_zero f z hf

lemma analytic_iter_deriv (k : ℕ) (f : ℂ → ℂ) z (hf : AnalyticAt ℂ f z) :
  AnalyticAt ℂ (iteratedDeriv k f) z := by
  rw [← Eq.symm iteratedDeriv_eq_iterate]
  exact AnalyticAt.iterated_deriv hf k

-- iteratedDeriv_one
lemma unfilter {A f} (p : A → Prop) :
  (∀ᶠ z in f, p z) ↔ ∃ U ∈ f, ∀ z ∈ U, p z := by
    constructor
    · intro h; use {x | p x}; exact ⟨h, by aesop⟩
    · intro h
      rcases h with ⟨U, ⟨hU, hUp⟩⟩
      exact Filter.mem_of_superset hU hUp

lemma test1 (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z):
    deriv (fun z => f z + g z) z = deriv f z + deriv g z := by
  refine deriv_add ?_ ?_
  · exact AnalyticAt.differentiableAt hf
  · exact AnalyticAt.differentiableAt hg

-- lemma: if the order of f is n > 0, then the order of the *single* derivative of f is n - 1
lemma order_gt_zero_then_deriv_n_neg_1 (f : ℂ → ℂ) z₀ (hf : AnalyticAt ℂ f z₀) (n : ℕ) :
  analyticOrderAt f z₀ = n → n > 0 → analyticOrderAt (deriv f) z₀ = (n - 1 : ℕ) := by {
    intros horder hn
    rw [AnalyticAt.analyticOrderAt_eq_natCast hf] at horder
    obtain ⟨g, hg, ⟨hgneq0, hexp⟩⟩ := horder
    rw [AnalyticAt.analyticOrderAt_eq_natCast]
    use fun z => n • g z + (z - z₀) • deriv g z
    constructor
    · refine fun_add ?_ ?_
      · simp only [nsmul_eq_mul]
        exact fun_const_smul hg
      · refine fun_mul ?_ (AnalyticAt.deriv hg)
        · refine fun_sub ?_ ?_
          · refine Differentiable.analyticAt (differentiable_fun_id) z₀
          · refine Differentiable.analyticAt (differentiable_const z₀) z₀
    · constructor
      · simp_all only [gt_iff_lt, ne_eq, smul_eq_mul, nsmul_eq_mul,
          sub_self, zero_mul, add_zero, mul_eq_zero, Nat.cast_eq_zero, or_false]
        apply Aesop.BuiltinRules.not_intro
        intro a
        subst a
        simp_all only [lt_self_iff_false]
      · rw [unfilter] at *
        rcases hexp with ⟨Ug, hU, hUf⟩
        have := AnalyticAt.exists_mem_nhds_analyticOnNhd hg
        obtain ⟨Ur, ⟨hgz,hgN⟩⟩ := this
        use interior (Ug ∩ Ur)
        constructor
        · simp only [interior_inter, Filter.inter_mem_iff, interior_mem_nhds]
          simp_all only [gt_iff_lt, ne_eq, smul_eq_mul, and_self]
        · intros z Hz
          have Hderiv : deriv (fun z => (z - z₀)^n • g z) z =
            (z - z₀) ^ (n - 1) * (↑n * g z) + (z - z₀) ^ (n - 1) * ((z - z₀) * deriv g z) := by {
              simp only [smul_eq_mul]
              rw [deriv_fun_mul]
              simp only [differentiableAt_fun_id, differentiableAt_const, DifferentiableAt.fun_sub,
                deriv_fun_pow'', deriv_fun_sub, deriv_id'', deriv_const', sub_zero, mul_one]
              · have : (z - z₀) ^ n * deriv g z + ↑n * (z - z₀) ^ (n - 1) * g z =
                (z - z₀) ^ (n - 1) * ((z - z₀)) * deriv g z + ↑n * (z - z₀) ^ (n - 1) * g z := by {
                  simp only [add_left_inj, mul_eq_mul_right_iff]
                  left
                  nth_rw 3 [← pow_one (z - z₀)]
                  rw [← pow_add]
                  rw [Nat.sub_add_cancel hn]
                }
                simp [this, add_comm]
                have : ↑n * (z - z₀) ^ (n - 1) = (z - z₀) ^ (n - 1) * ↑n  := by {
                   exact Nat.cast_comm n ((z - z₀) ^ (n - 1))}
                rw [this, mul_assoc]
                ring
                --exact Mathlib.Tactic.Ring.mul_pf_left (z - z₀) (n - 1) rfl
              · aesop
              · apply AnalyticAt.differentiableAt
                simp only [interior_inter, mem_inter_iff] at Hz
                have : z ∈ Ur := by {
                  rcases Hz with ⟨h1,h2⟩
                  have :  interior Ur ⊆ Ur  := interior_subset
                  simp_all only [gt_iff_lt, ne_eq, smul_eq_mul]
                  apply this
                  simp_all only
                }
                simp_all only [gt_iff_lt, ne_eq, smul_eq_mul]
                obtain ⟨left, right⟩ := Hz
                apply hgN
                simp_all only
            }
          simp only [nsmul_eq_mul, smul_eq_mul]
          rw [← mul_add] at Hderiv
          rw [← Hderiv]
          have hL : f =ᶠ[nhds z] (fun z => (fun z ↦ (z - z₀) ^ n • g z) z) := by {
            unfold Filter.EventuallyEq
            simp only [smul_eq_mul]
            rw [unfilter]
            use interior (Ug ∩ Ur)
            constructor
            · rw [IsOpen.mem_nhds_iff]
              exact Hz
              apply isOpen_interior
            · intros z Hz
              apply hUf
              simp only [interior_inter, mem_inter_iff] at Hz
              rcases Hz with ⟨h1,h2⟩
              have : interior Ug ⊆ Ug := interior_subset
              simp_all only [gt_iff_lt, ne_eq, smul_eq_mul]
              apply this
              simp_all only}
          have := Filter.EventuallyEq.deriv_eq hL
          rw [this]
    · exact AnalyticAt.deriv hf}

lemma order_geq_k_then_deriv_n_neg_1 (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z₀) (k n : ℕ)  :
   n = analyticOrderAt f z₀ → n > 0 → k ≤ n → analyticOrderAt (deriv^[k] f) z₀ = (n - k : ℕ) := by {
    revert n
    induction' k with k hk
    · intros n Hn Hpos Hk
      simp only [Function.iterate_zero, id_eq, tsub_zero, Hn]
    · intros n Hn Hpos Hk
      have : analyticOrderAt (deriv (deriv^[k] f)) z₀ = ((n - k) - 1 : ℕ) := by {
        apply order_gt_zero_then_deriv_n_neg_1
        · exact iterated_deriv hf k
        · apply hk
          · assumption
          · assumption
          · linarith
        · simp_all only [gt_iff_lt, ENat.coe_sub, tsub_pos_iff_lt]
          exact Hk}
      have h1 : (n - (k + 1))= (n - k - 1) := by {
        simp_all only [gt_iff_lt, ENat.coe_sub, Nat.cast_one]; rfl}
      rw [h1]
      simp only at this
      rw [← this]
      congr
      rw [Function.iterate_succ', Function.comp_apply]
      }

lemma order_deriv_top : ∀ z₀ (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z₀), f z₀ = 0 →
    ((analyticOrderAt (deriv f) z₀) = ⊤ ↔ analyticOrderAt f z₀ = ⊤) := by {
  intros z₀ f hf hzero
  simp_rw [analyticOrderAt_eq_top,Metric.eventually_nhds_iff_ball]
  constructor
  · intros H
    obtain ⟨r₁, ⟨hr₁0, hB⟩⟩ := AnalyticAt.exists_ball_analyticOnNhd hf
    obtain ⟨r₂, hr₂, hball⟩ := H
    let r := min r₁ r₂
    use r
    have hf : DifferentiableOn ℂ f (Metric.ball z₀ r) := by {
      apply AnalyticOn.differentiableOn
      refine AnalyticOnNhd.analyticOn ?_
      unfold AnalyticOnNhd at *
      intros x hx
      simp_all only [Metric.mem_ball, dist_self, gt_iff_lt, lt_inf_iff, r]}
    have hg : DifferentiableOn ℂ (fun _ ↦ (0 : ℂ)) (Metric.ball z₀ r) := differentiableOn_const 0
    have hf' : EqOn (deriv f) (deriv (fun _ ↦ (0 : ℂ))) (Metric.ball z₀ r) := by {
      simp only [deriv_const']
      unfold EqOn
      intros x
      have := hball x
      simp only [Metric.mem_ball] at this
      simp only [Metric.mem_ball]
      intros H
      apply this
      simp_all only [gt_iff_lt, Metric.mem_ball, differentiableOn_const,
        implies_true, lt_inf_iff, r]}
    have hx : z₀ ∈ (Metric.ball z₀ r) := by {
      simp only [Metric.mem_ball, dist_self]
      simp_all only [gt_iff_lt, Metric.mem_ball, differentiableOn_const, deriv_const']
      simp_all only [lt_inf_iff, and_self, r]}
    have := IsOpen.eqOn_of_deriv_eq ?_ ?_ hf hg hf' hx
    · constructor
      · simp_all only [gt_iff_lt, Metric.mem_ball,
        differentiableOn_const, deriv_const', dist_self, lt_inf_iff,
        and_self, forall_const, r]
      · intro y a
        simp_all only [gt_iff_lt, Metric.mem_ball, differentiableOn_const,
        deriv_const', dist_self, lt_inf_iff, and_self, forall_const, r]
        obtain ⟨left, right⟩ := a
        apply this
        simp_all only [Metric.mem_ball, lt_inf_iff, and_self]
    · simp only [Metric.isOpen_ball]
    · apply IsConnected.isPreconnected
      apply Metric.isConnected_ball
      simp_all only [gt_iff_lt, Metric.mem_ball, differentiableOn_const,
      deriv_const', dist_self, lt_inf_iff, and_self,
        r]
  · intros H
    obtain ⟨r₁, ⟨hr₁0, hB⟩⟩ := AnalyticAt.exists_ball_analyticOnNhd hf
    obtain ⟨r₂, hr₂, hball⟩ := H
    let r := min r₁ r₂
    use r
    constructor
    · simp_all only [Metric.mem_ball, dist_self, gt_iff_lt, lt_inf_iff, and_self, r]
    · intros x hx
      have hf' : EqOn f ((fun _ ↦ (0 : ℂ))) (Metric.ball z₀ r) := by {
          unfold EqOn
          intros x1 hx1
          simp only
          apply hball
          simp only [Metric.mem_ball, r] at *
          simp_all only [dist_self, gt_iff_lt, lt_inf_iff]
        }
      unfold EqOn at hf'
      have hf'' : derivWithin (fun _ => (0 : ℂ)) (Metric.ball z₀ r) x =
        derivWithin f (Metric.ball z₀ r) x := by {
        apply Filter.EventuallyEq.derivWithin_eq_of_nhds
        unfold Filter.EventuallyEq
        rw [unfilter]
        use Metric.ball z₀ r
        constructor
        · refine IsOpen.mem_nhds ?_ hx
          · exact Metric.isOpen_ball
        · exact fun z a ↦ Eq.symm (Complex.ext (congrArg re (hf' a)) (congrArg im (hf' a)))
        }
      rw [← derivWithin_of_mem_nhds]
      · rw [← hf'']
        simp only [derivWithin_fun_const, Pi.zero_apply, r]
      · rw [IsOpen.mem_nhds_iff]
        exact hx
        simp_all only [Metric.mem_ball, dist_self, gt_iff_lt, lt_inf_iff, implies_true, r]
        simp only [Metric.isOpen_ball]
          }

lemma deriv_n_neg_1_then_order_gt_zero (f : ℂ → ℂ) z₀ (hf : AnalyticAt ℂ f z₀) (n : ℕ) :
  f z₀ = 0 → analyticOrderAt (deriv f) z₀ = (n - 1 : ℕ)
    → n > 0 → analyticOrderAt f z₀ = n := by {
    intros hzero horder hn
    have : ∃ m, analyticOrderAt f z₀ = m := by simp
    obtain ⟨m, Hn'⟩ := this
    cases' m with n'
    · rw [← order_deriv_top] at Hn'
      rw [horder] at Hn'
      · by_contra hn'
        simp_all only [gt_iff_lt, ENat.coe_sub, Nat.cast_one,
          ENat.sub_eq_top_iff, ENat.coe_ne_top, ne_eq,
          ENat.one_ne_top, not_false_eq_true, and_true]
      · exact hf
      · exact hzero
    · cases' n' with n''
      · norm_cast at hzero
        have : analyticOrderAt f z₀ = 0 := by
          {simp_all only [ENat.coe_sub, Nat.cast_one, gt_iff_lt,
          CharP.cast_eq_zero]}
        rw [AnalyticAt.analyticOrderAt_eq_zero hf] at this
        by_contra H
        · apply this
          exact hzero
      · have hnn : analyticOrderAt (deriv f) z₀ = ((n'' + 1) - 1 : ℕ) := by
          refine order_gt_zero_then_deriv_n_neg_1 f z₀ hf (n'' + 1) Hn' ?_
          aesop
        simp only [horder] at hnn
        have : n = n'' + 1 := by
          norm_cast at hnn
          simp at hnn
          rw [← hnn]
          exact (Nat.sub_eq_iff_eq_add hn).mp rfl
        rw [this]
        exact Hn'
  }

-- theorem factorial_mul_Deriv (r : ℕ) (z z₀ : ℂ) (f: ℂ → ℂ) :
--    f z  = (z - z₀)^r * (deriv f z₀) := by {
--     sorry
--    }

-- theorem factorial_mul_Deriv' (r : ℕ) (z₀ : ℂ) (f: ℂ → ℂ) :
--     deriv^[r] f z₀ = (r.factorial) * (deriv f z₀) := by
--   induction r with
--   | zero =>
--     sorry
--   | succ k ih => sorry

lemma existrprime (r : ℕ) (z₀ : ℂ) (R R₁ : ℂ → ℂ)
  (hf : AnalyticAt ℂ R z) (hf : ∀ z : ℂ, AnalyticAt ℂ R₁ z)
  (hR₁ : ∀ z, R z  = (z - z₀)^r * R₁ z) :
  ∀ k ≤ r, ∃ R₂ : ℂ → ℂ, deriv^[k] R z =
   (z - z₀)^(r-k) * (r.factorial/(r-k).factorial * R₁ z + (z-z₀)* R₂ z) := by {
      intros k hkr
      induction' k with k IH
      sorry
      sorry
    }




lemma iterated_deriv_eq_zero_iff_order_eq_n :
  ∀ z₀ n (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z₀) (ho : analyticOrderAt f z₀ ≠ ⊤),
    (∀ k < n, deriv^[k] f z₀ = 0) ∧ (deriv^[n] f z₀ ≠ 0)
    --(∀ k < n, analyticOrderAt (deriv^[k] f) z₀ = 0) ∧ (deriv^[n] f z₀ ≠ 0)
    ↔ analyticOrderAt f z₀ = n := by
  intros z₀ n
  induction' n with n IH
  · simp only [ne_eq, not_lt_zero', IsEmpty.forall_iff, implies_true,
    Function.iterate_zero, id_eq, true_and, CharP.cast_eq_zero]
    exact fun f hf ho ↦ Iff.symm (AnalyticAt.analyticOrderAt_eq_zero hf)
  · intros f hf hfin
    constructor
    · intros H
      obtain ⟨hz, hnz⟩:= H
      have hfzero : f z₀ = 0 := by {
        specialize hz 0 (Nat.zero_lt_succ n)
        exact hz
      }
      have IH' := IH (deriv f) (AnalyticAt.deriv hf) ?_
      · --obtain ⟨IH1, IH2⟩ := IH'
        --[order_gt_zero_then_deriv_n_neg_1] at IH'
        suffices analyticOrderAt (deriv f) z₀ = (n : ℕ) by
          refine deriv_n_neg_1_then_order_gt_zero f z₀ hf (n + 1) hfzero this ?_
          simp only [gt_iff_lt, lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff, pos_of_gt,
            or_true]
        rw[← IH']
        constructor
        · have (k : ℕ) : deriv^[k] (deriv f) = deriv^[k+1] f := rfl
          intro k hk
          rw[this k]
          specialize hz (k+1)
          have : k+1 < n+1 := by omega
          specialize hz this
          exact hz
        · exact hnz
      · have := order_gt_zero_then_deriv_n_neg_1 f  z₀ hf
        specialize hz 0 (by omega)
        obtain ⟨r, hr⟩ := (WithTop.ne_top_iff_exists).mp hfin
        specialize this r hr.symm
        simp at hz
        have r0 : r > 0 := by
          suffices analyticOrderAt f z₀ > 0 by
            suffices @WithTop.some ℕ r > 0 by exact ENat.coe_lt_coe.mp this
            rw[hr]
            exact this
          have := analyticOrderAt_ne_zero.mpr ⟨hf, hz⟩
          exact pos_of_ne_zero this
        specialize this r0
        rw[this]
        exact ENat.coe_ne_top (r - 1)
    · intros ho
      constructor
      · intros k hk
        have thing := order_geq_k_then_deriv_n_neg_1 f hf k (n+1) ho.symm
        have : n+1 > 0 := by omega
        specialize thing this hk.le
        have : n + 1 - k > 0 := by omega
        have : analyticOrderAt (deriv^[k] f) z₀ ≠ 0 := by
          rw[thing]
          rw [@Nat.cast_ne_zero]
          omega
        rw[analyticOrderAt_ne_zero] at this
        exact this.2
      · have := order_geq_k_then_deriv_n_neg_1 f hf (n+1) (n+1) ho.symm (by omega) (by omega)
        simp at this
        rw[AnalyticAt.analyticOrderAt_eq_zero] at this
        assumption
        have (k : ℕ) : deriv^[k] (deriv f) = deriv^[k+1] f := rfl
        rw[this]
        exact iterated_deriv hf (n + 1)

lemma iterated_deriv_eq_zero_if_order_eq_n z₀ (n : ℕ) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z₀) :
    analyticOrderAt f z₀ = n → (∀ k < n, deriv^[k] f z₀ = 0) ∧ (deriv^[n] f z₀ ≠ 0) := by
  intros h
  rw [iterated_deriv_eq_zero_iff_order_eq_n]
  · exact h
  · exact hf
  · simp_all only [ne_eq, ENat.coe_ne_top, not_false_eq_true]

lemma notTop (m : ℕ∞): m ≠ ⊤ → ∃ n : ℕ, m = ↑n := by
  intro h
  exact Option.ne_none_iff_exists'.mp h

lemma iterated_deriv_eq_zero_imp_n_leq_order : ∀ (n : ℕ) z₀
  (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z₀)
  (ho : analyticOrderAt f z₀ ≠ ⊤),
  (∀ k < n, (deriv^[k] f) z₀ = 0) → n ≤ analyticOrderAt f z₀ := by
    intros n z₀ f hf ho hkn
    obtain ⟨m, Hm⟩ := notTop (analyticOrderAt f z₀) ho
    rw [Hm]
    rw [← iterated_deriv_eq_zero_iff_order_eq_n z₀ m f hf ho] at Hm
    rw [ENat.coe_le_coe]
    cases' le_or_gt n m with h h
    · exact h
    · rcases Hm with ⟨_, h'⟩
      cases (h' (hkn m h))

lemma shift_ball (x y z : ℂ) (renn : ENNReal) :
  x ∈ EMetric.ball y renn → z + x ∈ EMetric.ball (z + y) renn := by {
    simp only [EMetric.mem_ball, edist_add_left, imp_self]}

lemma HasFPowerSeriesWithout (f : ℂ → ℂ)
  (p : FormalMultilinearSeries ℂ ℂ ℂ) (U : Set ℂ) (z : ℂ) (hU : U ∈ nhds z) :
  HasFPowerSeriesWithinAt f p U z ↔ HasFPowerSeriesAt f p z := by {
    simp only [HasFPowerSeriesWithinAt, HasFPowerSeriesAt]
    constructor
    · intros H
      have hzmem : z ∈ U := by {exact mem_of_mem_nhds hU}
      rw [Metric.mem_nhds_iff] at hU
      obtain ⟨r', hr', hball⟩:= hU
      let r'' : ENNReal := Option.some ⟨r', by {linarith}⟩
      have hball' : EMetric.ball z r'' ⊆ U := by {
        simp_all only [ENNReal.some_eq_coe,
        Metric.emetric_ball_nnreal, NNReal.coe_mk, r'']
      }
      obtain ⟨renn,hr⟩:= H
      use min (renn) r''
      obtain ⟨r_le,r_pos,hs⟩ := hr
      constructor
      · simp_all only [ENNReal.some_eq_coe,
        Metric.emetric_ball_nnreal, NNReal.coe_mk,
        Set.insert_eq_of_mem,
        EMetric.mem_ball, edist_zero_right,
        FormalMultilinearSeries.apply_eq_prod_smul_coeff, prod_const,
        card_univ,
        Fintype.card_fin, smul_eq_mul, inf_le_iff, true_or, r'']
      · simp_all only [ENNReal.some_eq_coe, Metric.emetric_ball_nnreal,
        NNReal.coe_mk, Set.insert_eq_of_mem,
        EMetric.mem_ball, edist_zero_right,
        FormalMultilinearSeries.apply_eq_prod_smul_coeff, prod_const,
        card_univ,
        Fintype.card_fin, smul_eq_mul, lt_inf_iff,
        ENNReal.coe_pos, true_and, r'']
        exact hr'
      · intros y a
        apply hs
        · have : z + y ∈ EMetric.ball (z + 0) (min renn r'') := by {
            apply shift_ball
            exact a
            }
          have : z + y ∈ EMetric.ball z (min renn r'') := by {
            simp_all only [ENNReal.some_eq_coe,
            Metric.emetric_ball_nnreal, NNReal.coe_mk,
            Set.insert_eq_of_mem,
              EMetric.mem_ball, edist_zero_right,
              FormalMultilinearSeries.apply_eq_prod_smul_coeff, prod_const,
              card_univ, Fintype.card_fin, smul_eq_mul,
              lt_inf_iff, enorm_lt_coe, add_zero, edist_lt_coe, and_self,
              r'']
            }
          have : z + y ∈ EMetric.ball z r'' := by {
            rename_i this_1
            simp_all only [ENNReal.some_eq_coe,
            Metric.emetric_ball_nnreal, NNReal.coe_mk,
            Set.insert_eq_of_mem,
              EMetric.mem_ball, edist_zero_right,
              FormalMultilinearSeries.apply_eq_prod_smul_coeff, prod_const,
              card_univ, Fintype.card_fin, smul_eq_mul,
              lt_inf_iff, enorm_lt_coe, add_zero, edist_lt_coe, and_self,
              Metric.mem_ball, dist_self_add_left, r'']
            obtain ⟨left, right⟩ := a
            obtain ⟨left_1, right_1⟩ := this_1
            exact right
          }
          have : z + y ∈ U := by {
            rename_i this_1 this_2
            simp_all only [ENNReal.some_eq_coe,
            Metric.emetric_ball_nnreal, NNReal.coe_mk,
            Set.insert_eq_of_mem,
              EMetric.mem_ball, edist_zero_right,
              FormalMultilinearSeries.apply_eq_prod_smul_coeff,
              prod_const,
              card_univ, Fintype.card_fin, smul_eq_mul,
              lt_inf_iff, enorm_lt_coe, add_zero, edist_lt_coe, and_self,
              Metric.mem_ball, dist_self_add_left, r'']
            obtain ⟨left, right⟩ := a
            obtain ⟨left_1, right_1⟩ := this_1
            apply hball
            simp_all only [Metric.mem_ball, dist_self_add_left]
          }
          aesop
        · simp_all only [ENNReal.some_eq_coe,
          Metric.emetric_ball_nnreal, NNReal.coe_mk,
          Set.insert_eq_of_mem,
          EMetric.mem_ball, edist_zero_right,
          FormalMultilinearSeries.apply_eq_prod_smul_coeff,
          prod_const, card_univ,
          Fintype.card_fin, smul_eq_mul, lt_inf_iff, enorm_lt_coe, r'']
    · intros H
      obtain ⟨renn,hr⟩:= H
      use renn
      exact HasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall hr}

lemma AnalyticOnAt (f: ℂ → ℂ) (z : ℂ) (U : Set ℂ) (hU : U ∈ nhds z) :
  AnalyticOn ℂ f U → AnalyticAt ℂ f z := by {
    intros HA
    unfold AnalyticOn at HA
    unfold AnalyticWithinAt at HA
    unfold AnalyticAt
    have hzmem : z ∈ U := by {exact mem_of_mem_nhds hU}
    have := HA z hzmem
    obtain ⟨p,hp⟩ := this
    use p
    exact (HasFPowerSeriesWithout f p U z hU).mp hp}

lemma AnalyticOnEq (f g : ℂ → ℂ) (U : Set ℂ) :
  (∀ z ∈ U, f z = g z) → AnalyticOn ℂ f U → AnalyticOn ℂ g U := by {
    intros Heq HA
    unfold AnalyticOn at *
    unfold AnalyticWithinAt at *
    unfold HasFPowerSeriesWithinAt at *
    intro x Hx
    obtain ⟨p, renn, H⟩ := HA x Hx
    use p, renn
    constructor
    · exact H.r_le
    · exact H.r_pos
    · have : ∀ {y : ℂ}, x + y ∈ insert x U →
      y ∈ EMetric.ball 0 renn → HasSum (fun n ↦ (p n) fun x ↦ y) (f (x + y))
      := H.hasSum
      unfold HasSum at this ⊢
      have Hinsert : insert x U = U := by simp_all [Set.insert_eq_of_mem]
      rw [Hinsert] at this ⊢
      intros y Hxy
      have := this Hxy
      rwa [← Heq _ Hxy]}

lemma AnalyticAtEq (f g : ℂ → ℂ) (U : Set ℂ) (z : ℂ) :
  (hU : U ∈ nhds z)  → z ∈ U →
  (∀ z ∈ U, f z = g z) → AnalyticAt ℂ f z → AnalyticAt ℂ g z := sorry

lemma AnalyticOnEquiv (f g : ℂ → ℂ) (U : Set ℂ) :
  (∀ z ∈ U, f z = g z) → (AnalyticOn ℂ f U ↔ AnalyticOn ℂ g U) := by {
  intro Heq
  constructor
  · apply AnalyticOnEq f g U Heq
  · apply AnalyticOnEq g f U (by
  intro z a
  simp_all only)}

lemma AnalyticOnSubset (f : ℂ → ℂ) (U V : Set ℂ) :
    U ⊆ V → AnalyticOn ℂ f V → AnalyticOn ℂ f U := by {
    unfold AnalyticOn
    exact fun a a_1 x a_2 ↦ AnalyticWithinAt.mono (a_1 x (a a_2)) a}

lemma exists_mem_finset_min' {γ : Type _} {β : Type _} [LinearOrder γ]
    [DecidableEq γ] (s : Finset β) (f : β → γ) (Hs : s.Nonempty) :
  ∃ x ∈ s, ∃ y, y = f x ∧ ∀ x' ∈ s, y ≤ f x' := by
  let y := s.image f |>.min' (image_nonempty.mpr Hs)
  have : y ∈ Finset.image f s := min'_mem (image f s) (image_nonempty.mpr Hs)
  rw [Finset.mem_image] at this
  obtain ⟨x, hx, hy⟩ := this
  use x, hx, y
  constructor
  · exact id (Eq.symm hy)
  · intros x' hx'
    apply Finset.min'_le (image f s) (f x') (mem_image_of_mem _ hx')
