/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Logarithmic Derivatives

We define the logarithmic derivative of a function f as `deriv f / f`. We then prove some basic
facts about this, including how it changes under multiplication and composition.

We conclude by showing that the logarithmic derivative of a sequence of functions converging
locally uniformly to a function is the logarithmic derivative of the limit function.
-/

noncomputable section

open Filter Function

open scoped Topology BigOperators Classical

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The logarithmic derivative of a function defined as deriv f /f. Note that it will be zero
if `f` is not differentiable. -/
def logDeriv (f : 𝕜 → 𝕜) :=
  deriv f / f

lemma logDeriv_zero_of_not_differenitableAt (f : 𝕜 → 𝕜) (x : 𝕜) (h : ¬DifferentiableAt 𝕜 f x) :
    logDeriv f x = 0 := by
  simp only [logDeriv, Pi.div_apply, deriv_zero_of_not_differentiableAt h, zero_div]

theorem logDeriv_id (x : 𝕜) : logDeriv id x = 1 / x := by
  rw [logDeriv]
  simp only [deriv_id', Pi.div_apply, id_eq, one_div]

theorem logDeriv_const (a : 𝕜) : logDeriv (fun _ => a) = 0 := by
  rw [logDeriv]
  ext1 x
  simp only [deriv_const', Pi.div_apply, zero_div, Pi.zero_apply]

theorem logDerv_mul (f g : 𝕜 → 𝕜) (x : 𝕜) (hfg : f x * g x ≠ 0) (hdf : DifferentiableAt 𝕜 f x)
    (hdg : DifferentiableAt 𝕜 g x) :
    logDeriv (fun z => f z * g z) x = logDeriv f x + logDeriv g x := by
  simp only [logDeriv, Pi.div_apply, deriv_mul hdf hdg]
  field_simp [(mul_ne_zero_iff.1 hfg).1, (mul_ne_zero_iff.1 hfg).2, mul_comm]

theorem logDerv_mul_const (f : 𝕜 → 𝕜) (x a : 𝕜) (hf :  f x * a ≠ 0) (hdf : DifferentiableAt 𝕜 f x) :
    logDeriv (fun z => f z * a) x = logDeriv f x  := by
  rw [logDerv_mul f (fun _ => a) x hf hdf]
  simp only [logDeriv_const, Pi.zero_apply, add_zero]
  fun_prop

theorem logDerv_const_mul (f : 𝕜 → 𝕜) (x a : 𝕜) (hf :  a * f x ≠ 0) (hdf : DifferentiableAt 𝕜 f x) :
    logDeriv (fun z => a * f z) x = logDeriv f x  := by
  rw [logDerv_mul (fun _ => a)  f x hf _ hdf]
  simp only [logDeriv_const, Pi.zero_apply, zero_add]
  fun_prop

/-- The logarithmic derivative of a finite product is the sum of the logarithmic derivatives. -/
theorem logDeriv_prod {α : Type*} (s : Finset α) (f : α → 𝕜 → 𝕜) (t : 𝕜) (hf : ∀ x ∈ s, f x t ≠ 0)
    (hd : ∀ x ∈ s, DifferentiableAt 𝕜 (f x) t) :
    logDeriv (∏ i in s, f i) t = ∑ i in s, logDeriv (f i) t := by
  induction' s using Finset.cons_induction_on with a s ha ih
  · simp only [Finset.prod_empty, Finset.sum_empty]
    exact congrFun (logDeriv_const (1 : 𝕜)) t
  · rw [Finset.forall_mem_cons] at hf
    rw [Finset.cons_eq_insert _ _ ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have := logDerv_mul (f a) (∏ i in s, f i) t ?_ ?_ ?_
    · simp only [ne_eq, Finset.cons_eq_insert, Finset.mem_insert, forall_eq_or_imp,
      Finset.prod_apply] at *
      rw [ih hf.2 (fun _ hx ↦ hd.2 _ hx)] at this
      rw [← this]
      congr
      exact Finset.prod_fn s fun c ↦ f c
    · apply mul_ne_zero hf.1
      simp only [Finset.prod_apply, Finset.prod_ne_zero_iff]
      exact hf.2
    · apply hd
      simp only [Finset.cons_eq_insert, Finset.mem_insert, eq_self_iff_true, true_or_iff]
    · rw [Finset.prod_fn]
      apply DifferentiableAt.finset_prod
      intro r hr
      apply hd
      simp only [Finset.cons_eq_insert, Finset.mem_insert, hr , or_true]

theorem logDeriv_comp (f g : 𝕜 → 𝕜) (x : 𝕜) (hf : DifferentiableAt 𝕜 f (g x))
    (hg : DifferentiableAt 𝕜 g x) : logDeriv (f ∘ g) x = (logDeriv f) (g x) * deriv g x := by
  simp only [logDeriv, Pi.div_apply, deriv.comp _ hf hg, comp_apply]
  ring

/-- The logarithmic derivative of a sequence of functions converging locally uniformly to a
function is the logarithmic derivative of the limit function-/
theorem logDeriv_tendsto {ι : Type*} [Preorder ι] (f : ι  → ℂ → ℂ) (g : ℂ → ℂ) {s : Set ℂ}
    (hs : IsOpen s) (x : s) (hF : TendstoLocallyUniformlyOn f g atTop s)
    (hf : ∀ᶠ n : ι in atTop, DifferentiableOn ℂ (f n) s) (hg : g x ≠ 0) :
    Tendsto (fun n : ι => logDeriv (f n) x) atTop (𝓝 ((logDeriv g) x)) := by
  simp_rw [logDeriv]
  apply Tendsto.div ((hF.deriv hf hs).tendsto_at x.2) (hF.tendsto_at x.2) hg

section examples
