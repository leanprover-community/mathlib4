/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.NumberField.House
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.NormedSpace.Connected


set_option autoImplicit true
set_option linter.style.multiGoal false
set_option linter.style.cases false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars true
set_option linter.style.longFile 0

open BigOperators Module.Free Fintype
  Matrix Set Polynomial Finset Complex

open Differentiable AnalyticAt

lemma cexp_mul : deriv (fun x => cexp (c * x)) x = c * cexp (c * x) := by
  change deriv (fun x => exp ((fun x => c * x) x)) x = c * exp (c * x)
  rw [deriv_cexp]
  · rw [deriv_mul]
    · simp only [deriv_const', zero_mul, deriv_id'', mul_one, zero_add]
      exact CommMonoid.mul_comm (cexp (c * x)) c
    · exact differentiableAt_const c
    · exact differentiableAt_id'
  · apply mul <| differentiable_const _; exact differentiable_id'

theorem zero_if_order_inf : ∀ (f : ℂ → ℂ) z (hf : ∀ z, AnalyticAt ℂ f z),
  (∀ z, f z = 0) → AnalyticAt.order (hf z) = ⊤ := by
  intros f z hf h0
  rw [AnalyticAt.order_eq_top_iff]
  refine (AnalyticAt.frequently_eq_iff_eventually_eq (hf z) ?_).mp ?_
  · exact analyticAt_const
  · refine Filter.Frequently.of_forall ?_
    · intros x
      exact h0 x

theorem order_inf_if_zero : ∀ (f : ℂ → ℂ) z (hf : ∀ z, AnalyticAt ℂ f z),
 AnalyticAt.order (hf z) = ⊤ → (∀ z, f z = 0) := by
  intros f z hf hr
  have := AnalyticAt.order_eq_top_iff (hf z)
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

lemma zero_iff_order_inf : ∀ (f : ℂ → ℂ) z (hf : ∀ z, AnalyticAt ℂ f z),
  (∀ z, f z = 0) ↔ AnalyticAt.order (hf z) = ⊤ := by
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
  hf.order = n → n > 0 → (AnalyticAt.deriv hf).order = (n - 1 : ℕ) := by {
    intros horder hn
    rw [order_eq_nat_iff] at horder
    obtain ⟨g, hg, ⟨hgneq0, hexp⟩⟩ := horder
    rw [order_eq_nat_iff]
    use fun z => n • g z + (z - z₀) • deriv g z
    constructor
    · refine AnalyticAt.fun_add ?_ ?_
      · simp only [nsmul_eq_mul]
        exact AnalyticAt.fun_const_smul hg
      · refine fun_mul ?_ ?_
        · refine fun_sub ?_ ?_
          · refine Differentiable.analyticAt ?_ z₀
            exact differentiable_id'
          · refine Differentiable.analyticAt ?_ z₀
            exact differentiable_const z₀
        · exact AnalyticAt.deriv hg
    · constructor
      · aesop
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
              rw [deriv_smul]
              simp only [smul_eq_mul, differentiableAt_id', differentiableAt_const,
                DifferentiableAt.sub, deriv_pow'', deriv_sub, deriv_id'', deriv_const', sub_zero,
                mul_one]
              · have : (z - z₀) ^ n * deriv g z + ↑n * (z - z₀) ^ (n - 1) * g z =
                (z - z₀) ^ (n - 1) * ((z - z₀)) * deriv g z + ↑n * (z - z₀) ^ (n - 1) * g z := by {
                  simp only [add_left_inj, mul_eq_mul_right_iff]
                  left
                  nth_rw 3 [← pow_one (z - z₀)]
                  rw [← pow_add]
                  rw [Nat.sub_add_cancel hn]
                }
                rw [this, add_comm]
                have : ↑n * (z - z₀) ^ (n - 1) = (z - z₀) ^ (n - 1) * ↑n  := by {
                   exact Nat.cast_comm n ((z - z₀) ^ (n - 1))}
                rw [this, mul_assoc]
                simp only [add_right_inj]
                exact Mathlib.Tactic.Ring.mul_pf_left (z - z₀) (n - 1) rfl
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
              have :  interior Ug ⊆ Ug  := interior_subset
              simp_all only [gt_iff_lt, ne_eq, smul_eq_mul]
              apply this
              simp_all only}
          have := Filter.EventuallyEq.deriv_eq hL
          rw [this]}

lemma order_geq_k_then_deriv_n_neg_1 (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z₀) (k n : ℕ)  :
   n = hf.order → n > 0 → k ≤ n → (AnalyticAt.iterated_deriv hf k).order = (n - k : ℕ) := by {
    revert n
    induction' k with k hk
    · intros n Hn Hpos Hk
      simp [Hn]
    · intros n Hn Hpos Hk
      have : (AnalyticAt.deriv (AnalyticAt.iterated_deriv hf k)).order = ((n - k) - 1 : ℕ) := by {
        apply order_gt_zero_then_deriv_n_neg_1
        · apply hk
          · assumption
          · assumption
          · linarith
        · aesop
      }
      have h1 : (n - (k + 1))= (n - k - 1) := by {
        simp_all only [gt_iff_lt, ENat.coe_sub, Nat.cast_one]
        rfl
      }
      rw [h1]
      simp only at this
      rw [← this]
      congr
      rw [Function.iterate_succ',Function.comp_apply]
   }

#check IsOpen.eqOn_of_deriv_eq
lemma order_deriv_top : ∀ z₀ (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z₀), f z₀ = 0 →
    (AnalyticAt.order (AnalyticAt.deriv hf) = ⊤ ↔ AnalyticAt.order hf = ⊤) := by {
  intros z₀ f hf hzero
  simp_rw [AnalyticAt.order_eq_top_iff,Metric.eventually_nhds_iff_ball]
  constructor
  · intros H
    have := AnalyticAt.exists_ball_analyticOnNhd hf
    obtain ⟨r₁, ⟨hr₁0, hB⟩⟩ := this
    obtain ⟨r₂, hr₂, hball⟩ := H
    let r := min r₁ r₂
    use r
    have hf : DifferentiableOn ℂ f (Metric.ball z₀ r) := by {
      apply AnalyticOn.differentiableOn
      refine AnalyticOnNhd.analyticOn ?_
      unfold AnalyticOnNhd at *
      intros x hx
      simp_all only [Metric.mem_ball, dist_self, gt_iff_lt, lt_inf_iff, r]
    }
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
        implies_true, lt_inf_iff, r]
    }
    have hx : z₀ ∈ (Metric.ball z₀ r) := by {
      simp only [Metric.mem_ball, dist_self]
      simp_all only [gt_iff_lt, Metric.mem_ball, differentiableOn_const, deriv_const']
      simp_all only [lt_inf_iff, and_self, r]
      }
    have  := IsOpen.eqOn_of_deriv_eq ?_ ?_ hf hg hf' hx
    · constructor
      · aesop
      · aesop--sorry
    · simp only [Metric.isOpen_ball]
    · apply IsConnected.isPreconnected
      apply isConnected_ball
  · intros H
    have := AnalyticAt.exists_ball_analyticOnNhd hf
    obtain ⟨r, hB⟩ := this
    obtain ⟨ε, hε, hball⟩ := H
    use ε
    constructor
    · exact hε
    · intros x hx
      --have := deriv_const

}

#check order_deriv_top
#check order_eq_zero_iff
lemma iterated_deriv_eq_zero_iff_order_eq_n :
  ∀ z₀ n (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z₀) (ho : AnalyticAt.order hf ≠ ⊤),
    (∀ k < n, (AnalyticAt.iterated_deriv hf k).order = 0) ∧ (deriv^[n] f z₀ ≠ 0)
    ↔ AnalyticAt.order hf = n := by
  intros z₀ n
  induction' n with n IH
  · simp only [ne_eq, not_lt_zero', IsEmpty.forall_iff, implies_true, Function.iterate_zero, id_eq,
    true_and, CharP.cast_eq_zero]
    exact fun f hf ho ↦ Iff.symm (order_eq_zero_iff hf)
  · intros f hf hfin
    constructor
    · intros H
      obtain ⟨hz,hnz⟩:= H
      have IH' := IH (deriv f) (AnalyticAt.deriv hf) ?_
      · sorry
      · have := order_deriv_top z₀ f hf ?_
        · by_contra H
          apply hfin
          rwa [← this]
        · sorry
    · intros ho
      constructor
      · intros k hk
        sorry
        --rw [order_eq_zero_iff]
      · sorry


lemma iterated_deriv_eq_zero_imp_n_leq_order : ∀ z₀ (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z₀)
  (ho : AnalyticAt.order hf ≠ ⊤),
  (∀ k < n, iteratedDeriv k f z₀ = 0) → n ≤ AnalyticAt.order hf := by {
    intros z₀ f hf ho hkn
    sorry
  }
-- intros f z hf ho hd
-- rw [le_iff_eq_or_lt]
-- left
-- apply Eq.symm
-- rw [← iterated_deriv_eq_zero_iff_order_eq_n]
-- constructor
-- · intros k hkn
--   have := hd k.toNat
--   sorry
-- · sorry
-- · exact ho z
-- · sorry
-- · sorry
