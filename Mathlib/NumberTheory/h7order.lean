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

lemma analytic_iter_deriv (k : ℕ) (f : ℂ → ℂ) (hf : ∀ z, AnalyticAt ℂ f z) :
  ∀ z : ℂ, AnalyticAt ℂ (iteratedDeriv k f) z := by
  intro z
  rw [← Eq.symm iteratedDeriv_eq_iterate]
  exact AnalyticAt.iterated_deriv (hf z) k

-- lemma: if the order of f is n > 0, then the order of the *single* derivative of f is n - 1
lemma order_gt_zero_then_deriv_n_neg_1 (f : ℂ → ℂ) (hf : ∀ z, AnalyticAt ℂ f z)
   (hfdev : ∀ z : ℂ, AnalyticAt ℂ (iteratedDeriv k f) z)  :
 (∀ z : ℂ, 0 < AnalyticAt.order (hf z)) →
   ∀ z, AnalyticAt.order (hfdev z) = AnalyticAt.order (hf z) - 1 := by {
    intros H
    intros z
    sorry
   }

#check order_eq_nat_iff
lemma order_geq_k_then_deriv_n_neg_1 (k : ℕ) (f : ℂ → ℂ) (hf : ∀ z, AnalyticAt ℂ f z)
   (hfdev : ∀ z : ℂ, AnalyticAt ℂ (iteratedDeriv k f) z) :
   (∀ z : ℂ, k ≤ AnalyticAt.order (hf z)) → ∀ z, AnalyticAt.order (hfdev z) =
      (n : ℕ∞).toNat - k := by {

    intros hof z

    have hz : ∀ z, iteratedDeriv 0 f z = f z := by {
    intro z_1
    simp_all only [iteratedDeriv_zero]}

    induction' k with k hk
    · simp only [iteratedDeriv_zero, CharP.cast_eq_zero, tsub_zero]
      have  : (hf z).order = (n : ℕ∞).toNat ↔ ∃ g, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
         ∀ᶠ (z' : ℂ) in nhds z, f z' = (z' - z) ^ n.toNat • g z' := by {
        rw [order_eq_nat_iff]
      }
      rw [this]
      use (iteratedDeriv (0 : ℕ∞).toNat f)
      have H : AnalyticAt ℂ (iteratedDeriv (n : ℕ∞).toNat f) z := by {
        rw [iteratedDeriv_eq_iterate]
        exact AnalyticAt.iterated_deriv (hf z) (n : ℕ∞).toNat
      }
      constructor
      · simp only [ENat.toNat_zero, iteratedDeriv_zero]
        exact hf z
      · constructor
        · simp only [iteratedDeriv_zero] at hfdev
          have := hof z
          have Hiff : (hf z).order = 0 ↔
           f z ≠ 0 := by {rw [order_eq_zero_iff]}
          have Hifftop := order_eq_top_iff (hf z)
          simp only [ENat.toNat_zero, iteratedDeriv_zero]
          rw [le_iff_eq_or_lt] at this
          cases' this with h1 h2
          · rw [← Hiff]
            simp only [CharP.cast_eq_zero] at h1
            exact h1.symm
          · have maybeH := apply_eq_zero_of_order_toNat_ne_zero (hf z)
            have useH : (hf z).order ≠ 0 := by {
              norm_cast
              exact pos_iff_ne_zero.mp h2
              }
            --simp only [ENat.toNat_eq_zero, not_or, and_imp] at this
            --intros Hd


            --rw [← frequently_zero_iff_eventually_zero] at Hifftop








          --rw [Hiff]
        · simp only [ENat.toNat_zero, iteratedDeriv_zero, smul_eq_mul]
          refine (frequently_eq_iff_eventually_eq (hf z) ?_).mp ?_
          · refine fun_mul ?_ (hf z)
            refine Differentiable.analyticAt ?_ z
            simp only [differentiable_id', differentiable_const, Differentiable.sub,
              Differentiable.pow]
          · refine frequently_nhdsWithin_iff.mpr ?_
            simp only [mem_compl_iff, mem_singleton_iff]
            refine Filter.Eventually.and_frequently ?_ ?_
            · sorry
            · sorry

        --   rw [← Hiff]
        --   unfold order
        --   unfold order at this
        --   rw [le_iff_eq_or_lt] at this
        --   split
        --   · rename_i ht
        --     simp only [ENat.top_ne_zero]
        --     sorry
        --   · sorry
        -- · simp only [iteratedDeriv_one, smul_eq_mul]


    · have hfdev_plus_one : ∀ z : ℂ, AnalyticAt ℂ (iteratedDeriv (k + 1) f) z := sorry
      simp only at hk
      sorry
   }

-- lemma: if the order of f is n > 0, then the order of the *single* derivative of f is n - 1
--   this follows from the definition (characterization?) of the order as being (z - z₀)^n*g(z)

-- lemma: by induction if the order ≥ k, then the order of the k-th derivative is n - k

-- have hfoo : ∀ (z : ℂ), AnalyticAt ℂ (iteratedDeriv k f) z :=
 -- by {exact fun z ↦ analytic_iter_deriv k f hf z}

-- have := order_inf_if_zero (iteratedDeriv k f) z hfoo

lemma iterated_deriv_eq_zero_iff_order_eq_n :
  ∀ n (f : ℂ → ℂ) z (hf : ∀ z, AnalyticAt ℂ f z) (ho : AnalyticAt.order (hf z) ≠ ⊤)
   (hfdev : ∀ z : ℂ, AnalyticAt ℂ (iteratedDeriv k f) z),
  (∀ k < n, AnalyticAt.order (hfdev z) = 0) ∧ (iteratedDeriv k f z ≠ 0)
    ↔ AnalyticAt.order (hf z) = n := by
  intros n f z hf hord hfdev
  constructor
  · intros H
    obtain ⟨H1, H2⟩ := H
    sorry
  · intros H
    constructor
    · intros k hk
      sorry
    · by_contra H
      sorry

lemma iterated_deriv_eq_zero_imp_n_leq_order : ∀ (f : ℂ → ℂ) z₀ (hf : ∀ z, AnalyticAt ℂ f z)
   (ho : ∀ z, AnalyticAt.order (hf z) ≠ ⊤),
 (∀ k < n, iteratedDeriv k f z₀ = 0) → n ≤ AnalyticAt.order (hf z₀) := by

intros f z hf ho hd
rw [le_iff_eq_or_lt]
left
apply Eq.symm
rw [← iterated_deriv_eq_zero_iff_order_eq_n]
constructor
· intros k hkn
  have := hd k.toNat
  sorry
· sorry
· exact ho z
· sorry
· sorry
