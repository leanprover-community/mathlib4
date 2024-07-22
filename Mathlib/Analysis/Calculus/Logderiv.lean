/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Logarithmic Derivatives

We define the logarithmic derivative of a function f as `deriv f / f`. We then prove some basic
facts about this, including how it changes under multiplication and composition.

We conclude by showing that the logarithmic derivative of a sequence of functions converging
locally uniformly to a function is the logarithmic derivative of the limit function. This is useful
for example for the Mittag-Leffler expansion of the cotangent function.
-/

noncomputable section

open Filter Function

open scoped Topology BigOperators Classical

variable {𝕜 𝕜': Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']

/-- The logarithmic derivative of a function defined as `deriv f /f`. Note that it will be zero
at `x` if `f` is not DifferentiableAt `x`. -/
def logDeriv (f : 𝕜 → 𝕜') :=
  deriv f / f

lemma logDeriv_eq_zero_of_not_differentiableAt (f : 𝕜 → 𝕜') (x : 𝕜) (h : ¬DifferentiableAt 𝕜 f x) :
    logDeriv f x = 0 := by
  simp only [logDeriv, Pi.div_apply, deriv_zero_of_not_differentiableAt h, zero_div]

@[simp]
theorem logDeriv_id (x : 𝕜) : logDeriv id x = 1 / x := by
  rw [logDeriv]
  simp only [deriv_id', Pi.div_apply, id_eq, one_div]

@[simp]
theorem logDeriv_const (a : 𝕜') : logDeriv (fun _ : 𝕜 ↦ a) = 0 := by
  rw [logDeriv]
  ext1 x
  simp only [deriv_const', Pi.div_apply, zero_div, Pi.zero_apply]

theorem logDeriv_mul {f g : 𝕜 → 𝕜'} (x : 𝕜) (hf : f x ≠ 0) (hg : g x ≠ 0)
    (hdf : DifferentiableAt 𝕜 f x) (hdg : DifferentiableAt 𝕜 g x) :
      logDeriv (fun z => f z * g z) x = logDeriv f x + logDeriv g x := by
  simp only [logDeriv, Pi.div_apply, deriv_mul hdf hdg]
  field_simp [hf, hg , mul_comm]

theorem logDeriv_mul_const {f : 𝕜 → 𝕜'} (x : 𝕜) (a : 𝕜') (ha : a ≠ 0):
    logDeriv (fun z => f z * a) x = logDeriv f x := by
  simp only [logDeriv, deriv_mul_const_field', Pi.div_apply]
  rw [mul_div_mul_right (deriv (fun x ↦ f x) x) (f x) ha]

theorem logDeriv_const_mul {f : 𝕜 → 𝕜'} (x : 𝕜) (a : 𝕜') (ha : a ≠ 0):
    logDeriv (fun z => a * f z) x = logDeriv f x := by
  simp only [logDeriv, deriv_const_mul_field', Pi.div_apply]
  rw [mul_div_mul_left (deriv (fun x ↦ f x) x) (f x) ha]

/-- The logarithmic derivative of a finite product is the sum of the logarithmic derivatives. -/
theorem logDeriv_prod {α : Type*} (s : Finset α) (f : α → 𝕜 → 𝕜') (t : 𝕜) (hf : ∀ x ∈ s, f x t ≠ 0)
    (hd : ∀ x ∈ s, DifferentiableAt 𝕜 (f x) t) :
    logDeriv (∏ i in s, f i) t = ∑ i in s, logDeriv (f i) t := by
  induction' s using Finset.cons_induction_on with a s ha ih
  · simp only [Finset.prod_empty, Finset.sum_empty]
    exact congrFun (logDeriv_const (1 : 𝕜')) t
  · rw [Finset.forall_mem_cons] at hf
    rw [Finset.cons_eq_insert _ _ ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have := logDeriv_mul (f := f a) (g := ∏ i in s, f i) t ?_ ?_ ?_ ?_
    · simp only [ne_eq, Finset.cons_eq_insert, Finset.mem_insert, forall_eq_or_imp,
        Finset.prod_apply] at *
      rw [ih hf.2 (fun _ hx ↦ hd.2 _ hx)] at this
      rw [← this]
      congr
      exact Finset.prod_fn s fun c ↦ f c
    · exact hf.1
    · simp only [Finset.prod_apply, Finset.prod_ne_zero_iff]
      exact hf.2
    · apply hd
      simp only [Finset.cons_eq_insert, Finset.mem_insert, eq_self_iff_true, true_or_iff]
    · rw [Finset.prod_fn]
      apply DifferentiableAt.finset_prod
      intro r hr
      apply hd
      simp only [Finset.cons_eq_insert, Finset.mem_insert, hr, or_true]

lemma logDeriv_pow {x : 𝕜} {n : ℕ} (hn : n ≠ 0) (hx : x ≠ 0) :
    logDeriv (fun z => z ^ n) x = n * logDeriv id x := by
  simp only [logDeriv, deriv_pow', Pi.div_apply, deriv_id', id_eq, one_div]
  field_simp [hx, mul_assoc, pow_sub_one_mul hn x]

lemma logDeriv_zpow {x : 𝕜} {n : ℤ} (hx : x ≠ 0) :
    logDeriv (fun z => z ^ n) x = n * logDeriv id x := by
  simp only [logDeriv, deriv_zpow', Pi.div_apply, zpow_sub_one₀ hx, deriv_id', id_eq, one_div]
  field_simp [hx, mul_assoc, mul_comm (x^n) x]
  simpa only [one_mul, div_one] using
    (mul_div_mul_right (n : 𝕜) 1 (mul_ne_zero hx (zpow_ne_zero n hx)))

theorem logDeriv_comp {f g : 𝕜 → 𝕜} {x : 𝕜} (hf : DifferentiableAt 𝕜 f (g x))
    (hg : DifferentiableAt 𝕜 g x) : logDeriv (f ∘ g) x = (logDeriv f) (g x) * deriv g x := by
  simp only [logDeriv, Pi.div_apply, deriv.comp _ hf hg, comp_apply]
  ring

lemma logDeriv_fun_pow {f : 𝕜 → 𝕜} {x : 𝕜} {n : ℕ} (hn : n ≠ 0) (hf : f x ≠ 0)
    (hdf : DifferentiableAt 𝕜 f x) :  logDeriv (fun z => (f z) ^ n) x = n * logDeriv f x := by
  rw [← comp_def (fun z => z^n) f,
    logDeriv_comp (f := fun z => z^n) (g := f) (differentiableAt_pow n) hdf, logDeriv_pow hn hf]
  simp only [logDeriv, deriv_id', Pi.div_apply, id_eq, one_div]
  ring

lemma logDeriv_fun_zpow {f : 𝕜 → 𝕜} {x : 𝕜} {n : ℤ} (hf : f x ≠ 0) (hdf : DifferentiableAt 𝕜 f x) :
    logDeriv (fun z => (f z) ^ n) x = n * logDeriv f x := by
  rw [show (fun z => (f z)^n) = (fun z => z^n) ∘ f by rfl,
    logDeriv_comp (f := fun z => z^n) (g := f) ?_ hdf, logDeriv_zpow hf]
  · simp only [logDeriv, deriv_id', Pi.div_apply, id_eq, one_div]
    ring
  · simp only [differentiableAt_zpow, ne_eq, hf, not_false_eq_true, true_or]
