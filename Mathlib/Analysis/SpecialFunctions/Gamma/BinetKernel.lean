import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.NormNum.NatFactorial


/-!
# The Binet Kernel Function

This file analyzes the kernel function K(t) = 1/(e^t - 1) - 1/t + 1/2 that appears
in Binet's integral representation of log Γ.

## Main Results

* `BinetKernel.tendsto_Ktilde_zero`: K̃(t) → 1/12 as t → 0⁺
* `BinetKernel.K_nonneg`: K(t) ≥ 0 for t > 0
* `BinetKernel.Ktilde_le`: K̃(t) ≤ 1/12 for t ≥ 0
* `BinetKernel.integrable_Ktilde_exp_complex`: integrability of `t ↦ K̃(t) * exp(-t*z)` on `(0, ∞)` for `0 < re z`
* `BinetKernel.Ktilde_ge_one_div_twelve_mul_exp_neg_div_twelve`:
  Robbins-type lower bound `(1/12) * exp(-t/12) ≤ K̃(t)` for `t > 0`

## Mathematical Background

The function 1/(e^t - 1) has the Laurent expansion at t = 0:
  1/(e^t - 1) = 1/t - 1/2 + t/12 - t³/720 + ...

Therefore (formally, via Taylor expansions):
  K(t) = 1/(e^t - 1) - 1/t + 1/2
       = (1/t - 1/2 + t/12 - t³/720 + ...) - 1/t + 1/2
       = t/12 - t³/720 + O(t⁵)

This shows K(t) → 0 as t → 0⁺. The normalized Binet kernel is:
  K̃(t) = K(t) / t = (1/(e^t - 1) - 1/t + 1/2) / t for t > 0

which satisfies K̃(t) → 1/12 as t → 0⁺.

## References

* Whittaker & Watson, "A Course of Modern Analysis", Chapter 12
* NIST DLMF 5.11
-/

open Real Set Filter MeasureTheory Topology
open scoped Topology

namespace BinetKernel

/-! ### General monotonicity and positivity lemmas -/

/-- If a function has nonnegative derivative on `[0, ∞)`, it is monotone there. -/
private lemma monotoneOn_of_deriv_nonneg_Ici {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ici 0))
    (hderiv : ∀ x ∈ Set.Ici 0, 0 ≤ deriv f x) :
    MonotoneOn f (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hf.continuousOn (hf.mono interior_subset)
  intro x hx
  rw [interior_Ici] at hx
  exact hderiv x (Set.mem_Ici.mpr (le_of_lt hx))

/-- If `deriv f ≥ 0` on `[0, ∞)` and `f 0 = 0`, then `f x ≥ 0` for `x ≥ 0`. -/
private lemma nonneg_of_deriv_nonneg_Ici {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ici 0))
    (hderiv : ∀ x ∈ Set.Ici 0, 0 ≤ deriv f x) (h0 : f 0 = 0) :
    ∀ {x}, 0 ≤ x → 0 ≤ f x := by
  intro x hx
  have hmono := monotoneOn_of_deriv_nonneg_Ici hf hderiv
  have hx' : x ∈ Set.Ici 0 := hx
  have h0' : (0 : ℝ) ∈ Set.Ici 0 := by simp
  have hle := hmono h0' hx' hx
  simpa [h0] using hle

/-! ### Taylor-type lower bounds for exp

These are already in Mathlib as `Real.sum_le_exp_of_nonneg` and `Real.quadratic_le_exp_of_nonneg`.
We provide convenient aliases with the naming convention used here.
-/

/-- The function `exp x - 1 - x` is nonnegative for `x ≥ 0`.
This is the error term in the first-order Taylor approximation.
Alias for the consequence of `Real.add_one_le_exp`. -/
private lemma exp_sub_one_sub_x_nonneg {x : ℝ} (_hx : 0 ≤ x) : 0 ≤ Real.exp x - 1 - x := by
  have h := Real.add_one_le_exp x
  linarith

/-- For `t ≥ 0`, we have `exp t ≥ 1 + t + t²/2`.
This is `Real.quadratic_le_exp_of_nonneg` from Mathlib. -/
private lemma exp_ge_one_add_sq {t : ℝ} (ht : 0 ≤ t) : 1 + t + t ^ 2 / 2 ≤ Real.exp t :=
  Real.quadratic_le_exp_of_nonneg ht

/-- For `t ≥ 0`, we have `exp t ≥ 1 + t + t²/2 + t³/6`.
Uses `Real.sum_le_exp_of_nonneg` with n = 4. -/
private lemma exp_ge_one_add_cu {t : ℝ} (ht : 0 ≤ t) :
    1 + t + t ^ 2 / 2 + t ^ 3 / 6 ≤ Real.exp t := by
  have h := Real.sum_le_exp_of_nonneg ht 4
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    pow_zero, Nat.cast_one, div_one, pow_one, Nat.factorial] at h
  convert h using 1; ring

/-- For `t ≥ 0`, we have `exp t ≥ 1 + t + t²/2 + t³/6 + t⁴/24`.
Uses `Real.sum_le_exp_of_nonneg` with n = 5. -/
private lemma exp_ge_one_add_quartic {t : ℝ} (ht : 0 ≤ t) :
    1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 ≤ Real.exp t := by
  have h := Real.sum_le_exp_of_nonneg ht 5
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    pow_zero, Nat.cast_one, div_one, pow_one, Nat.factorial] at h
  convert h using 1; ring

/-! ## Section 1: Basic definitions and elementary properties -/

/-- The unnormalized Binet kernel: K(t) = 1/(e^t - 1) - 1/t + 1/2 for t > 0. -/
noncomputable def K (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else 1/(Real.exp t - 1) - 1/t + 1/2

/-- The normalized Binet kernel: K̃(t) = K(t)/t for t > 0.
This is the kernel that appears in the Binet integral. -/
noncomputable def Ktilde (t : ℝ) : ℝ :=
  if t ≤ 0 then 1/12 else (1/(Real.exp t - 1) - 1/t + 1/2) / t

/-- For t > 0, K has the explicit formula. -/
lemma K_pos {t : ℝ} (ht : 0 < t) : K t = 1/(Real.exp t - 1) - 1/t + 1/2 := by
  simp [K, not_le.mpr ht]

/-- For t > 0, K̃ has the explicit formula. -/
lemma Ktilde_pos {t : ℝ} (ht : 0 < t) :
    Ktilde t = (1/(Real.exp t - 1) - 1/t + 1/2) / t := by
  simp [Ktilde, not_le.mpr ht]

/-- K̃(0) = 1/12 by definition (the limit value). -/
lemma Ktilde_zero : Ktilde 0 = 1/12 := by simp [Ktilde]

/-! ## Section 2: The key identity for the kernel -/

/-- For t > 0, e^t > 1, so e^t - 1 > 0. -/
private lemma exp_sub_one_pos {t : ℝ} (ht : 0 < t) : 0 < Real.exp t - 1 := by
  have h1 : Real.exp 0 = 1 := Real.exp_zero
  have h2 : Real.exp t > Real.exp 0 := Real.exp_lt_exp.mpr ht
  linarith

/-- K̃ is continuous on (0, ∞). -/
lemma continuousOn_Ktilde_Ioi : ContinuousOn Ktilde (Set.Ioi 0) := by
  intro t ht
  have hne_t : t ≠ 0 := ne_of_gt ht
  have hne_exp : Real.exp t - 1 ≠ 0 := ne_of_gt (exp_sub_one_pos ht)
  have h1 : ContinuousAt (fun x => 1 / (Real.exp x - 1)) t :=
    continuousAt_const.div (Real.continuous_exp.continuousAt.sub continuousAt_const) hne_exp
  have h2 : ContinuousAt (fun x => 1 / x) t := continuousAt_const.div continuousAt_id hne_t
  have h3 : ContinuousAt (fun x => 1 / (Real.exp x - 1) - 1 / x + 1 / 2) t :=
    (h1.sub h2).add continuousAt_const
  have h4 : ContinuousAt (fun x => (1 / (Real.exp x - 1) - 1 / x + 1 / 2) / x) t :=
    h3.div continuousAt_id hne_t
  apply h4.continuousWithinAt.congr
  · intro y hy
    unfold Ktilde
    rw [if_neg (not_le.mpr hy)]
  · unfold Ktilde
    rw [if_neg (not_le.mpr ht)]



/-- Key algebraic identity: For t > 0,
  K(t) = 1/(e^t - 1) - 1/t + 1/2 = (t - (e^t - 1) + t(e^t - 1)/2) / (t(e^t - 1))
This helps analyze the sign and bounds. -/
private lemma K_eq_alt {t : ℝ} (ht : 0 < t) :
    K t = (t - (Real.exp t - 1) + t * (Real.exp t - 1) / 2) / (t * (Real.exp t - 1)) := by
  rw [K_pos ht]
  have hexp : Real.exp t - 1 > 0 := exp_sub_one_pos ht
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hexp_ne : Real.exp t - 1 ≠ 0 := ne_of_gt hexp
  field_simp

/-- Alternative form: K(t) = (e^t(t-2) + t + 2) / (2t(e^t - 1)) -/
private lemma K_eq_alt' {t : ℝ} (ht : 0 < t) :
    K t = (Real.exp t * (t - 2) + t + 2) / (2 * t * (Real.exp t - 1)) := by
  rw [K_pos ht]
  have hexp : Real.exp t - 1 > 0 := exp_sub_one_pos ht
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hexp_ne : Real.exp t - 1 ≠ 0 := ne_of_gt hexp
  field_simp
  ring

/-! ## Section 3: Sign analysis -/

/-- The function f(t) = e^t(t-2) + t + 2 that appears in the numerator.
We need to show f(t) ≥ 0 for t ≥ 0. -/
private noncomputable def f (t : ℝ) : ℝ := Real.exp t * (t - 2) + t + 2

private lemma f_zero : f 0 = 0 := by simp [f]

/-- The derivative of f(t) = e^t(t-2) + t + 2 is f'(t) = e^t(t-1) + 1. -/
private lemma f_deriv (t : ℝ) : HasDerivAt f (Real.exp t * (t - 1) + 1) t := by
  unfold f
  -- f(t) = e^t * (t - 2) + t + 2
  -- f'(t) = e^t(t-2) + e^t + 1 = e^t(t-1) + 1
  have h1 : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
  have h2 : HasDerivAt (fun x => x - 2) 1 t := (hasDerivAt_id t).sub_const 2
  have h3 : HasDerivAt (fun x => Real.exp x * (x - 2)) (Real.exp t * (t - 2) + Real.exp t * 1) t :=
    h1.mul h2
  have h4 : HasDerivAt (fun x => x + 2) 1 t := (hasDerivAt_id t).add_const 2
  have h5 := h3.add h4
  convert h5 using 1
  · ext x; simp only [Pi.add_apply]; ring
  · ring

private lemma f_deriv' (t : ℝ) : deriv f t = Real.exp t * (t - 1) + 1 :=
  (f_deriv t).deriv

/-- f has a minimum at t = 1, where f(1) = 3 - e. -/
private lemma f_at_one : f 1 = 3 - Real.exp 1 := by simp [f]; ring

/-- e < 3, so f(1) = 3 - e > 0. -/
private lemma f_one_pos : 0 < f 1 := by
  rw [f_at_one]
  have h : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  linarith

/-- For t > 0, e^t(1-t) < 1. This is because g(t) = e^t(1-t) is strictly decreasing
with g(0) = 1, so g(t) < 1 for t > 0.

Proof: g'(t) = e^t(1-t) + e^t(-1) = e^t(-t) = -te^t < 0 for t > 0.
By MVT: g(t) - g(0) = g'(c) * t < 0 for some c ∈ (0, t), so g(t) < g(0) = 1. -/
private lemma exp_mul_one_sub_lt_one {t : ℝ} (ht : 0 < t) : Real.exp t * (1 - t) < 1 := by
  -- g(t) = e^t(1-t), g(0) = 1, and g is strictly decreasing for t > 0
  -- This can be proved via MVT or by direct analysis
  have hg_deriv : ∀ s, HasDerivAt (fun x => Real.exp x * (1 - x)) (-Real.exp s * s) s := by
    intro s
    have h1 : HasDerivAt Real.exp (Real.exp s) s := Real.hasDerivAt_exp s
    have h2 : HasDerivAt (fun x => 1 - x) (-1) s := by
      have := (hasDerivAt_const s 1).sub (hasDerivAt_id s)
      simp only at this
      convert this using 1; ring
    have h3 := h1.mul h2
    convert h3 using 1; ring
  -- Use strict monotonicity: g'(t) = -te^t < 0 for t > 0
  have hg_mono : StrictAntiOn (fun x => Real.exp x * (1 - x)) (Set.Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    · exact (Real.continuous_exp.mul (continuous_const.sub continuous_id)).continuousOn
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      rw [(hg_deriv x).deriv]
      have hexp_pos : 0 < Real.exp x := Real.exp_pos x
      nlinarith
  have h0 : (0 : ℝ) ∈ Set.Ici 0 := Set.mem_Ici.mpr (le_refl 0)
  have ht' : t ∈ Set.Ici 0 := Set.mem_Ici.mpr (le_of_lt ht)
  have := hg_mono h0 ht' ht
  simp at this
  linarith

/-- Key lemma: f'(t) > 0 for t > 0.
Since f'(t) = e^t(t-1) + 1 > 0 ⟺ 1 > e^t(1-t), which holds for t > 0. -/
private lemma f_deriv_pos {t : ℝ} (ht : 0 < t) : 0 < deriv f t := by
  rw [f_deriv' t]
  have h : Real.exp t * (1 - t) < 1 := exp_mul_one_sub_lt_one ht
  have : Real.exp t * (t - 1) = -(Real.exp t * (1 - t)) := by ring
  linarith

/-- Key lemma: f(t) ≥ 0 for all t ≥ 0.
Proof: f(0) = 0 and f'(t) > 0 for t > 0, so f is strictly increasing. -/
private lemma f_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · simp [f_zero]
  · -- f(t) > f(0) = 0 since f is strictly increasing
    have hf_diff : Differentiable ℝ f := fun x => (f_deriv x).differentiableAt
    have h_pos_deriv : ∀ x ∈ Set.Ioo 0 t, 0 < deriv f x := fun x hx => f_deriv_pos hx.1
    have h_mono := strictMonoOn_of_deriv_pos (convex_Icc 0 t)
      (hf_diff.continuous.continuousOn) (fun x hx => by
        rw [interior_Icc] at hx
        exact h_pos_deriv x hx)
    have h0 : (0 : ℝ) ∈ Set.Icc 0 t := left_mem_Icc.mpr (le_of_lt hpos)
    have ht' : t ∈ Set.Icc 0 t := right_mem_Icc.mpr (le_of_lt hpos)
    have := h_mono h0 ht' hpos
    rw [f_zero] at this
    exact le_of_lt this

/-- The Binet kernel K(t) is nonnegative for t > 0. -/
theorem K_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ K t := by
  rw [K_eq_alt' ht]
  have hexp : 0 < Real.exp t - 1 := exp_sub_one_pos ht
  have hdenom : 0 < 2 * t * (Real.exp t - 1) := by positivity
  apply div_nonneg _ hdenom.le
  -- The numerator is f(t) ≥ 0
  exact f_nonneg (le_of_lt ht)

/-- The normalized kernel K̃(t) is nonnegative for t ≥ 0. -/
theorem Ktilde_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Ktilde t := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · rw [Ktilde_zero]; norm_num
  · rw [Ktilde_pos hpos]
    have hK : 0 ≤ K t := K_nonneg hpos
    rw [K_pos hpos] at hK
    exact div_nonneg hK (le_of_lt hpos)

/-! ## Section 4: Upper bound -/

/-! ### Auxiliary function g for the Ktilde bound -/

/-- The auxiliary function g(t) = (t² - 6t + 12)e^t - (t² + 6t + 12).
We show g(t) ≥ 0 for t ≥ 0, which implies the bound Ktilde t ≤ 1/12. -/
private noncomputable def g_aux (t : ℝ) : ℝ := (t^2 - 6*t + 12) * Real.exp t - (t^2 + 6*t + 12)

/-- First derivative: g'(t) = (t² - 4t + 6)e^t - (2t + 6) -/
private noncomputable def g_aux' (t : ℝ) : ℝ := (t^2 - 4*t + 6) * Real.exp t - (2*t + 6)

/-- Second derivative: g''(t) = (t² - 2t + 2)e^t - 2 -/
private noncomputable def g_aux'' (t : ℝ) : ℝ := (t^2 - 2*t + 2) * Real.exp t - 2

/-- Third derivative: g'''(t) = t²e^t -/
private noncomputable def g_aux''' (t : ℝ) : ℝ := t^2 * Real.exp t

private lemma g_aux_zero : g_aux 0 = 0 := by simp [g_aux]
private lemma g_aux'_zero : g_aux' 0 = 0 := by simp [g_aux']
private lemma g_aux''_zero : g_aux'' 0 = 0 := by simp [g_aux'']

/-- g'''(t) = t²e^t ≥ 0 for all t ≥ 0. -/
private lemma g_aux'''_nonneg {t : ℝ} (_ht : 0 ≤ t) : 0 ≤ g_aux''' t := by
  simp only [g_aux''']
  exact mul_nonneg (sq_nonneg t) (Real.exp_pos t).le

private lemma g_aux'''_pos {t : ℝ} (ht : 0 < t) : 0 < g_aux''' t := by
  simp [g_aux''', sq_pos_of_ne_zero (ne_of_gt ht), Real.exp_pos]

/-! #### Derivative relations for g_aux hierarchy -/

/-- g'' has derivative g''' -/
private lemma hasDerivAt_g_aux'' (t : ℝ) : HasDerivAt g_aux'' (g_aux''' t) t := by
  unfold g_aux'' g_aux'''
  -- d/dt [(t² - 2t + 2)e^t - 2] = (2t - 2)e^t + (t² - 2t + 2)e^t = t²e^t
  have h1 : HasDerivAt (fun x => x^2 - 2*x + 2) (2*t - 2) t := by
    have := (hasDerivAt_pow 2 t).sub ((hasDerivAt_id t).const_mul 2)
    convert this.add (hasDerivAt_const t 2) using 1; ring
  have h2 : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
  have h3 : HasDerivAt (fun x => (x^2 - 2*x + 2) * Real.exp x)
      ((2*t - 2) * Real.exp t + (t^2 - 2*t + 2) * Real.exp t) t := h1.mul h2
  have h4 : HasDerivAt (fun x => (x^2 - 2*x + 2) * Real.exp x - 2)
      ((2*t - 2) * Real.exp t + (t^2 - 2*t + 2) * Real.exp t - 0) t :=
    h3.sub (hasDerivAt_const t 2)
  simp only [sub_zero] at h4
  convert h4 using 1
  ring

/-- g' has derivative g'' -/
private lemma hasDerivAt_g_aux' (t : ℝ) : HasDerivAt g_aux' (g_aux'' t) t := by
  unfold g_aux' g_aux''
  -- d/dt [(t² - 4t + 6)e^t - (2t + 6)] = (2t - 4)e^t + (t² - 4t + 6)e^t - 2
  --                                    = (t² - 2t + 2)e^t - 2
  have h1 : HasDerivAt (fun x => x^2 - 4*x + 6) (2*t - 4) t := by
    have := (hasDerivAt_pow 2 t).sub ((hasDerivAt_id t).const_mul 4)
    convert this.add (hasDerivAt_const t 6) using 1; ring
  have h2 : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
  have h3 : HasDerivAt (fun x => (x^2 - 4*x + 6) * Real.exp x)
      ((2*t - 4) * Real.exp t + (t^2 - 4*t + 6) * Real.exp t) t := h1.mul h2
  have h4 : HasDerivAt (fun x => 2*x + 6) 2 t := by
    convert (hasDerivAt_id t).const_mul 2 |>.add (hasDerivAt_const t 6) using 1
    ring
  have h5 : HasDerivAt (fun x => (x^2 - 4*x + 6) * Real.exp x - (2*x + 6))
      ((2*t - 4) * Real.exp t + (t^2 - 4*t + 6) * Real.exp t - 2) t := h3.sub h4
  convert h5 using 1
  ring

/-- g has derivative g' -/
private lemma hasDerivAt_g_aux (t : ℝ) : HasDerivAt g_aux (g_aux' t) t := by
  unfold g_aux g_aux'
  -- d/dt [(t² - 6t + 12)e^t - (t² + 6t + 12)]
  --   = (2t - 6)e^t + (t² - 6t + 12)e^t - (2t + 6)
  --   = (t² - 4t + 6)e^t - (2t + 6)
  have h1 : HasDerivAt (fun x => x^2 - 6*x + 12) (2*t - 6) t := by
    have := (hasDerivAt_pow 2 t).sub ((hasDerivAt_id t).const_mul 6)
    convert this.add (hasDerivAt_const t 12) using 1; ring
  have h2 : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
  have h3 : HasDerivAt (fun x => (x^2 - 6*x + 12) * Real.exp x)
      ((2*t - 6) * Real.exp t + (t^2 - 6*t + 12) * Real.exp t) t := h1.mul h2
  have h4 : HasDerivAt (fun x => x^2 + 6*x + 12) (2*t + 6) t := by
    have := (hasDerivAt_pow 2 t).add ((hasDerivAt_id t).const_mul 6)
    convert this.add (hasDerivAt_const t 12) using 1; ring
  have h5 : HasDerivAt (fun x => (x^2 - 6*x + 12) * Real.exp x - (x^2 + 6*x + 12))
      ((2*t - 6) * Real.exp t + (t^2 - 6*t + 12) * Real.exp t - (2*t + 6)) t := h3.sub h4
  convert h5 using 1
  ring

/-! #### Non-negativity proofs for g_aux hierarchy -/

/-- g'' is differentiable on [0, ∞) -/
private lemma differentiableOn_g_aux'' : DifferentiableOn ℝ g_aux'' (Set.Ici 0) := fun x _ =>
  (hasDerivAt_g_aux'' x).differentiableAt.differentiableWithinAt

/-- g' is differentiable on [0, ∞) -/
private lemma differentiableOn_g_aux' : DifferentiableOn ℝ g_aux' (Set.Ici 0) := fun x _ =>
  (hasDerivAt_g_aux' x).differentiableAt.differentiableWithinAt

/-- g is differentiable on [0, ∞) -/
private lemma differentiableOn_g_aux : DifferentiableOn ℝ g_aux (Set.Ici 0) := fun x _ =>
  (hasDerivAt_g_aux x).differentiableAt.differentiableWithinAt

/-- g''(t) ≥ 0 for t ≥ 0. Follows from g''(0) = 0 and g''' ≥ 0. -/
private lemma g_aux''_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ g_aux'' t := by
  apply nonneg_of_deriv_nonneg_Ici differentiableOn_g_aux''
  · intro x hx
    rw [(hasDerivAt_g_aux'' x).deriv]
    exact g_aux'''_nonneg hx
  · exact g_aux''_zero
  · exact ht

private lemma g_aux''_pos {t : ℝ} (ht : 0 < t) : 0 < g_aux'' t := by
  have hdiff : Differentiable ℝ g_aux'' := fun x => (hasDerivAt_g_aux'' x).differentiableAt
  have h_pos_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) t, 0 < deriv g_aux'' x := fun x hx => by
    -- `deriv g_aux'' x = g_aux''' x`
    simpa [(hasDerivAt_g_aux'' x).deriv] using g_aux'''_pos (t := x) hx.1
  have h_mono :=
    strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) t)
      (hdiff.continuous.continuousOn) (fun x hx => by
        rw [interior_Icc] at hx
        exact h_pos_deriv x hx)
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, le_of_lt ht⟩
  have ht' : t ∈ Set.Icc (0 : ℝ) t := ⟨le_of_lt ht, le_rfl⟩
  have := h_mono h0 ht' ht
  simpa [g_aux''_zero] using this

/-- g'(t) ≥ 0 for t ≥ 0. Follows from g'(0) = 0 and g'' ≥ 0. -/
private lemma g_aux'_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ g_aux' t := by
  apply nonneg_of_deriv_nonneg_Ici differentiableOn_g_aux'
  · intro x hx
    rw [(hasDerivAt_g_aux' x).deriv]
    exact g_aux''_nonneg hx
  · exact g_aux'_zero
  · exact ht

private lemma g_aux'_pos {t : ℝ} (ht : 0 < t) : 0 < g_aux' t := by
  have hdiff : Differentiable ℝ g_aux' := fun x => (hasDerivAt_g_aux' x).differentiableAt
  have h_pos_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) t, 0 < deriv g_aux' x := fun x hx => by
    simpa [(hasDerivAt_g_aux' x).deriv] using g_aux''_pos (t := x) hx.1
  have h_mono :=
    strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) t)
      (hdiff.continuous.continuousOn) (fun x hx => by
        rw [interior_Icc] at hx
        exact h_pos_deriv x hx)
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, le_of_lt ht⟩
  have ht' : t ∈ Set.Icc (0 : ℝ) t := ⟨le_of_lt ht, le_rfl⟩
  have := h_mono h0 ht' ht
  simpa [g_aux'_zero] using this

/-- g(t) ≥ 0 for t ≥ 0. This is the key inequality for proving Ktilde t ≤ 1/12.
Follows from g(0) = 0 and g' ≥ 0. -/
private lemma g_aux_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ g_aux t := by
  apply nonneg_of_deriv_nonneg_Ici differentiableOn_g_aux
  · intro x hx
    rw [(hasDerivAt_g_aux x).deriv]
    exact g_aux'_nonneg hx
  · exact g_aux_zero
  · exact ht

private lemma g_aux_pos {t : ℝ} (ht : 0 < t) : 0 < g_aux t := by
  have hdiff : Differentiable ℝ g_aux := fun x => (hasDerivAt_g_aux x).differentiableAt
  have h_pos_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) t, 0 < deriv g_aux x := fun x hx => by
    simpa [(hasDerivAt_g_aux x).deriv] using g_aux'_pos (t := x) hx.1
  have h_mono :=
    strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) t)
      (hdiff.continuous.continuousOn) (fun x hx => by
        rw [interior_Icc] at hx
        exact h_pos_deriv x hx)
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, le_of_lt ht⟩
  have ht' : t ∈ Set.Icc (0 : ℝ) t := ⟨le_of_lt ht, le_rfl⟩
  have := h_mono h0 ht' ht
  simpa [g_aux_zero] using this

/-- The Taylor expansion shows K(t) = t/12 - t³/720 + O(t⁵), so K(t)/t → 1/12 as t → 0⁺.
Since K(t) < t/12 for t > 0 (the higher order terms are negative), we have K(t)/t < 1/12.

The proof uses the algebraic identity K(t) = f(t)/(2t(e^t-1)) and bounds on f. -/
theorem Ktilde_le {t : ℝ} (ht : 0 ≤ t) : Ktilde t ≤ 1/12 := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · -- t = 0: Ktilde 0 = 1/12 by definition
    rw [Ktilde_zero]
  · -- t > 0: Use K(t) = f(t)/(2t(e^t-1)) where f(t) = e^t(t-2) + t + 2
    have hexp : 0 < Real.exp t - 1 := exp_sub_one_pos hpos
    have hdenom : 0 < 2 * t * (Real.exp t - 1) := by positivity
    have hf_nonneg : 0 ≤ f t := f_nonneg (le_of_lt hpos)
    -- Ktilde t = K t / t = f(t) / (2t²(e^t-1))
    calc Ktilde t = (1 / (Real.exp t - 1) - 1 / t + 1 / 2) / t := Ktilde_pos hpos
      _ = (Real.exp t * (t - 2) + t + 2) / (2 * t * (Real.exp t - 1)) / t := by
          rw [← K_pos hpos, K_eq_alt' hpos]
      _ = f t / (2 * t ^ 2 * (Real.exp t - 1)) := by
          unfold f
          field_simp
      _ ≤ 1 / 12 := by
          rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * t ^ 2 * (Real.exp t - 1)) (by norm_num : (0 : ℝ) < 12)]
          -- Need: 12 * f(t) ≤ 2 * t² * (e^t - 1)
          -- This is equivalent to g_aux(t) ≥ 0 by algebra
          have h_nonneg : 0 ≤ g_aux t := g_aux_nonneg (le_of_lt hpos)
          -- g_aux(t) = (t² - 6t + 12)e^t - (t² + 6t + 12)
          -- 12 * f(t) = 12(e^t(t-2) + t + 2) = 12te^t - 24e^t + 12t + 24
          -- 2t²(e^t - 1) = 2t²e^t - 2t²
          -- Goal: 12te^t - 24e^t + 12t + 24 ≤ 2t²e^t - 2t²
          -- Rearranged: 0 ≤ 2t²e^t - 12te^t + 24e^t - 12t - 24 - 2t²
          --           = 2((t² - 6t + 12)e^t - (t² + 6t + 12)) = 2 * g_aux(t)
          have hgoal : 0 ≤ 2 * g_aux t := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h_nonneg
          unfold g_aux at hgoal
          unfold f
          linarith [hgoal, Real.exp_pos t, sq_nonneg t]

theorem Ktilde_lt {t : ℝ} (ht : 0 < t) : Ktilde t < 1 / 12 := by
  have hexp : 0 < Real.exp t - 1 := exp_sub_one_pos ht
  calc
    Ktilde t
        = f t / (2 * t ^ 2 * (Real.exp t - 1)) := by
            -- same algebra as in `Ktilde_le`
            have hdenom : 0 < 2 * t * (Real.exp t - 1) := by positivity
            calc
              Ktilde t = (1 / (Real.exp t - 1) - 1 / t + 1 / 2) / t := Ktilde_pos ht
              _ = (Real.exp t * (t - 2) + t + 2) / (2 * t * (Real.exp t - 1)) / t := by
                    rw [← K_pos ht, K_eq_alt' ht]
              _ = f t / (2 * t ^ 2 * (Real.exp t - 1)) := by
                    unfold f
                    field_simp
    _ < 1 / 12 := by
          -- Reduce to a strict inequality equivalent to `g_aux t > 0`.
          have hdenom : (0 : ℝ) < 2 * t ^ 2 * (Real.exp t - 1) := by positivity
          have h12 : (0 : ℝ) < (12 : ℝ) := by norm_num
          -- Cross-multiply.
          rw [div_lt_div_iff₀ hdenom h12]
          -- Goal is `f t * 12 < 1 * (2 * t ^ 2 * (Real.exp t - 1))`.
          have hpos_g : 0 < g_aux t := g_aux_pos ht
          have hpos : 0 < 2 * g_aux t := mul_pos (by norm_num) hpos_g
          unfold g_aux at hpos
          unfold f
          -- This is the same algebraic rearrangement as in `Ktilde_le`, but strict.
          linarith [hpos, Real.exp_pos t, sq_nonneg t]

/-! ## Section 4b: Robbins-type lower bound for `Ktilde` -/

/-!
Robbins' sharpened factorial lower bound is equivalent (via Binet's integral) to a pointwise
lower bound on the Binet kernel:

`(1/12) * exp(-t/12) ≤ Ktilde t` for all `t > 0`.

We prove this by reducing it to positivity of an explicit auxiliary function and then using a
derivative-chain argument (similar to the proof of `Ktilde_le`).
-/

private noncomputable def robbinsAux (t : ℝ) : ℝ :=
  12 * Real.exp (t * (13 / 12 : ℝ)) * (t - 2)
    + 12 * Real.exp (t * (1 / 12 : ℝ)) * (t + 2)
    - 2 * t ^ 2 * Real.exp t + 2 * t ^ 2

private noncomputable def robbinsAux' (t : ℝ) : ℝ :=
  Real.exp (t * (13 / 12 : ℝ)) * (13 * t - 14)
    + Real.exp (t * (1 / 12 : ℝ)) * (t + 14)
    - 2 * Real.exp t * (t * (t + 2)) + 4 * t

private noncomputable def robbinsAux'' (t : ℝ) : ℝ :=
  Real.exp (t * (13 / 12 : ℝ)) * ((169 * t - 26) / 12)
    + Real.exp (t * (1 / 12 : ℝ)) * ((t + 26) / 12)
    - 2 * Real.exp t * (t ^ 2 + 4 * t + 2) + 4

private noncomputable def robbinsAux''' (t : ℝ) : ℝ :=
  Real.exp (t * (13 / 12 : ℝ)) * ((2197 * t + 1690) / 144)
    + Real.exp (t * (1 / 12 : ℝ)) * ((t + 38) / 144)
    - 2 * Real.exp t * (t ^ 2 + 6 * t + 6)

private noncomputable def robbinsAux'''' (t : ℝ) : ℝ :=
  Real.exp (t * (13 / 12 : ℝ)) * ((28561 * t + 48334) / 1728)
    + Real.exp (t * (1 / 12 : ℝ)) * ((t + 50) / 1728)
    - 2 * Real.exp t * (t ^ 2 + 8 * t + 12)

private lemma robbinsAux_zero : robbinsAux 0 = 0 := by
  simp [robbinsAux]

private lemma robbinsAux'_zero : robbinsAux' 0 = 0 := by
  simp [robbinsAux']

private lemma robbinsAux''_zero : robbinsAux'' 0 = 0 := by
  simp [robbinsAux'']
  norm_num

private lemma robbinsAux'''_zero : robbinsAux''' 0 = 0 := by
  simp [robbinsAux''']
  norm_num

private lemma hasDerivAt_robbinsAux (t : ℝ) : HasDerivAt robbinsAux (robbinsAux' t) t := by
  -- Differentiate term-by-term; using the fact `d/dt (exp (t*c)) = exp (t*c) * c`.
  have hexp13 : HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)))
      (Real.exp (t * (13 / 12 : ℝ)) * (13 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (13 / 12 : ℝ)) (13 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (13 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (13 / 12 : ℝ))).comp t hlin
  have hexp1 : HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)))
      (Real.exp (t * (1 / 12 : ℝ)) * (1 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (1 / 12 : ℝ)) (1 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (1 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (1 / 12 : ℝ))).comp t hlin
  have hA :
      HasDerivAt (fun x : ℝ => 12 * Real.exp (x * (13 / 12 : ℝ)) * (x - 2))
        (Real.exp (t * (13 / 12 : ℝ)) * (13 * t - 14)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => x - 2) 1 t := (hasDerivAt_id t).sub_const 2
    have hmul :
        HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)) * (x - 2))
          (Real.exp (t * (13 / 12 : ℝ)) * (13 / 12 : ℝ) * (t - 2) + Real.exp (t * (13 / 12 : ℝ)) * 1) t :=
      (hexp13.mul hpoly)
    -- multiply by 12
    have h := hmul.const_mul (12 : ℝ)
    -- normalize function and derivative values
    convert h using 1 <;> ring_nf
  have hB :
      HasDerivAt (fun x : ℝ => 12 * Real.exp (x * (1 / 12 : ℝ)) * (x + 2))
        (Real.exp (t * (1 / 12 : ℝ)) * (t + 14)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => x + 2) 1 t := (hasDerivAt_id t).add_const 2
    have hmul :
        HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)) * (x + 2))
          (Real.exp (t * (1 / 12 : ℝ)) * (1 / 12 : ℝ) * (t + 2) + Real.exp (t * (1 / 12 : ℝ)) * 1) t :=
      (hexp1.mul hpoly)
    have h := hmul.const_mul (12 : ℝ)
    convert h using 1 <;> ring_nf
  have hC :
      HasDerivAt (fun x : ℝ => -2 * x ^ 2 * Real.exp x)
        (-2 * (Real.exp t * (t * (t + 2)))) t := by
    have hpow : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℝ) * t) t := by
      simpa using (hasDerivAt_pow 2 t)
    have hexp : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
    have hmul : HasDerivAt (fun x : ℝ => x ^ 2 * Real.exp x)
        ((2 : ℝ) * t * Real.exp t + t ^ 2 * Real.exp t) t := hpow.mul hexp
    have h := hmul.const_mul (-2 : ℝ)
    convert h using 1 <;> ring_nf
  have hD :
      HasDerivAt (fun x : ℝ => 2 * x ^ 2) (4 * t) t := by
    have hpow : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℝ) * t) t := by
      simpa using (hasDerivAt_pow 2 t)
    have h := hpow.const_mul (2 : ℝ)
    convert h using 1; ring_nf
  -- combine
  have h := ((hA.add hB).add (hC.add hD))
  -- unfold the target definitions and normalize
  unfold robbinsAux robbinsAux'
  convert h using 1
  · funext x
    -- unfold pointwise addition/multiplication of functions, then normalize
    simp [Pi.add_apply, sub_eq_add_neg, add_assoc, add_comm, mul_assoc, mul_comm]
  · ring_nf

private lemma hasDerivAt_robbinsAux' (t : ℝ) : HasDerivAt robbinsAux' (robbinsAux'' t) t := by
  have hexp13 : HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)))
      (Real.exp (t * (13 / 12 : ℝ)) * (13 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (13 / 12 : ℝ)) (13 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (13 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (13 / 12 : ℝ))).comp t hlin
  have hexp1 : HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)))
      (Real.exp (t * (1 / 12 : ℝ)) * (1 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (1 / 12 : ℝ)) (1 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (1 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (1 / 12 : ℝ))).comp t hlin
  have hA :
      HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)) * (13 * x - 14))
        (Real.exp (t * (13 / 12 : ℝ)) * ((169 * t - 26) / 12)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => 13 * x - 14) 13 t := by
      simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
        ((hasDerivAt_id t).const_mul (13 : ℝ)).sub_const 14
    have hmul := hexp13.mul hpoly
    -- normalize the derivative value
    convert hmul using 1; ring_nf
  have hB :
      HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)) * (x + 14))
        (Real.exp (t * (1 / 12 : ℝ)) * ((t + 26) / 12)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => x + 14) 1 t := (hasDerivAt_id t).add_const 14
    have hmul := hexp1.mul hpoly
    convert hmul using 1; ring_nf
  have hC :
      HasDerivAt (fun x : ℝ => -2 * Real.exp x * (x * (x + 2)))
        (-2 * Real.exp t * (t ^ 2 + 4 * t + 2)) t := by
    have hexp : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
    have hpoly : HasDerivAt (fun x : ℝ => x * (x + 2)) (t + (t + 2)) t := by
      -- derivative of x*(x+2) is (x+2)+x
      have h1 : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
      have h2 : HasDerivAt (fun x : ℝ => x + 2) 1 t := (hasDerivAt_id t).add_const 2
      have := h1.mul h2
      simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using this
    have hmul := hexp.mul hpoly
    have h := hmul.const_mul (-2 : ℝ)
    convert h using 1
    · funext x
      simp [Pi.mul_apply, mul_assoc, mul_comm, mul_left_comm]
    · ring_nf
  have hD : HasDerivAt (fun x : ℝ => 4 * x) 4 t := by
    simpa [mul_comm] using (hasDerivAt_id t).const_mul (4 : ℝ)
  have h := ((hA.add hB).add (hC.add hD))
  unfold robbinsAux' robbinsAux''
  convert h using 1
  · funext x
    simp [Pi.add_apply, sub_eq_add_neg, add_assoc, add_comm, mul_assoc, mul_comm]
  · ring_nf

private lemma hasDerivAt_robbinsAux'' (t : ℝ) : HasDerivAt robbinsAux'' (robbinsAux''' t) t := by
  have hexp13 : HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)))
      (Real.exp (t * (13 / 12 : ℝ)) * (13 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (13 / 12 : ℝ)) (13 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (13 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (13 / 12 : ℝ))).comp t hlin
  have hexp1 : HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)))
      (Real.exp (t * (1 / 12 : ℝ)) * (1 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (1 / 12 : ℝ)) (1 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (1 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (1 / 12 : ℝ))).comp t hlin
  have hA :
      HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)) * ((169 * x - 26) / 12))
        (Real.exp (t * (13 / 12 : ℝ)) * ((2197 * t + 1690) / 144)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => ((169 * x - 26) / 12)) (169 / 12) t := by
      have : HasDerivAt (fun x : ℝ => (169 * x - 26)) 169 t := by
        simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
          ((hasDerivAt_id t).const_mul (169 : ℝ)).sub_const 26
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this.const_mul (1 / 12 : ℝ)
    have hmul := hexp13.mul hpoly
    convert hmul using 1; ring_nf
  have hB :
      HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)) * ((x + 26) / 12))
        (Real.exp (t * (1 / 12 : ℝ)) * ((t + 38) / 144)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => ((x + 26) / 12)) (1 / 12) t := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        ((hasDerivAt_id t).add_const 26).const_mul (1 / 12 : ℝ)
    have hmul := hexp1.mul hpoly
    convert hmul using 1; ring_nf
  have hC :
      HasDerivAt (fun x : ℝ => -2 * Real.exp x * (x ^ 2 + 4 * x + 2))
        (-2 * Real.exp t * (t ^ 2 + 6 * t + 6)) t := by
    have hexp : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
    have hpoly : HasDerivAt (fun x : ℝ => x ^ 2 + 4 * x + 2) (2 * t + 4) t := by
      have h1 : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℝ) * t) t := by
        simpa using (hasDerivAt_pow 2 t)
      have h2 : HasDerivAt (fun x : ℝ => 4 * x) 4 t := by
        simpa [mul_comm] using (hasDerivAt_id t).const_mul (4 : ℝ)
      have h3 : HasDerivAt (fun x : ℝ => (2 : ℝ)) 0 t := hasDerivAt_const t 2
      have := (h1.add (h2.add h3))
      simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using this
    have hmul := hexp.mul hpoly
    have h := hmul.const_mul (-2 : ℝ)
    convert h using 1
    · funext x
      simp [Pi.mul_apply, mul_comm, mul_left_comm]
    · ring_nf
  have hD : HasDerivAt (fun _x : ℝ => (4 : ℝ)) 0 t := hasDerivAt_const t 4
  have h := ((hA.add hB).add hC).add hD
  unfold robbinsAux'' robbinsAux'''
  convert h using 1
  · funext x
    simp [Pi.add_apply, sub_eq_add_neg, add_comm, mul_comm]
  · ring_nf

private lemma hasDerivAt_robbinsAux''' (t : ℝ) : HasDerivAt robbinsAux''' (robbinsAux'''' t) t := by
  have hexp13 : HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)))
      (Real.exp (t * (13 / 12 : ℝ)) * (13 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (13 / 12 : ℝ)) (13 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (13 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (13 / 12 : ℝ))).comp t hlin
  have hexp1 : HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)))
      (Real.exp (t * (1 / 12 : ℝ)) * (1 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (1 / 12 : ℝ)) (1 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (1 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (1 / 12 : ℝ))).comp t hlin
  have hA :
      HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)) * ((2197 * x + 1690) / 144))
        (Real.exp (t * (13 / 12 : ℝ)) * ((28561 * t + 48334) / 1728)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => ((2197 * x + 1690) / 144)) (2197 / 144) t := by
      have : HasDerivAt (fun x : ℝ => (2197 * x + 1690)) 2197 t := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          ((hasDerivAt_id t).const_mul (2197 : ℝ)).add_const 1690
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this.const_mul (1 / 144 : ℝ)
    have hmul := hexp13.mul hpoly
    convert hmul using 1; ring_nf
  have hB :
      HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)) * ((x + 38) / 144))
        (Real.exp (t * (1 / 12 : ℝ)) * ((t + 50) / 1728)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => ((x + 38) / 144)) (1 / 144) t := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        ((hasDerivAt_id t).add_const 38).const_mul (1 / 144 : ℝ)
    have hmul := hexp1.mul hpoly
    convert hmul using 1; ring_nf
  have hC :
      HasDerivAt (fun x : ℝ => -2 * Real.exp x * (x ^ 2 + 6 * x + 6))
        (-2 * Real.exp t * (t ^ 2 + 8 * t + 12)) t := by
    have hexp : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
    have hpoly : HasDerivAt (fun x : ℝ => x ^ 2 + 6 * x + 6) (2 * t + 6) t := by
      have h1 : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℝ) * t) t := by
        simpa using (hasDerivAt_pow 2 t)
      have h2 : HasDerivAt (fun x : ℝ => 6 * x) 6 t := by
        simpa [mul_comm] using (hasDerivAt_id t).const_mul (6 : ℝ)
      have h3 : HasDerivAt (fun x : ℝ => (6 : ℝ)) 0 t := hasDerivAt_const t 6
      have := h1.add (h2.add h3)
      simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using this
    have hmul := hexp.mul hpoly
    have h := hmul.const_mul (-2 : ℝ)
    convert h using 1
    · funext x
      simp [Pi.mul_apply, mul_comm, mul_left_comm]
    · ring_nf
  have h := (hA.add hB).add hC
  unfold robbinsAux''' robbinsAux''''
  convert h using 1
  · funext x
    simp [Pi.add_apply, sub_eq_add_neg, add_comm, mul_comm]
  · ring_nf

private lemma differentiableOn_robbinsAux : DifferentiableOn ℝ robbinsAux (Set.Ici 0) := fun x _ =>
  (hasDerivAt_robbinsAux x).differentiableAt.differentiableWithinAt

private lemma differentiableOn_robbinsAux' : DifferentiableOn ℝ robbinsAux' (Set.Ici 0) := fun x _ =>
  (hasDerivAt_robbinsAux' x).differentiableAt.differentiableWithinAt

private lemma differentiableOn_robbinsAux'' : DifferentiableOn ℝ robbinsAux'' (Set.Ici 0) := fun x _ =>
  (hasDerivAt_robbinsAux'' x).differentiableAt.differentiableWithinAt

private lemma differentiableOn_robbinsAux''' : DifferentiableOn ℝ robbinsAux''' (Set.Ici 0) := fun x _ =>
  (hasDerivAt_robbinsAux''' x).differentiableAt.differentiableWithinAt

/-! ### Positivity of the fourth derivative -/

private noncomputable def robbinsPoly (t : ℝ) : ℝ :=
  (3431 / 864 : ℝ) + (29645 / 10368 : ℝ) * t - (130765 / 248832 : ℝ) * t ^ 2 +
    (28561 / 497664 : ℝ) * t ^ 3

private noncomputable def robbinsPoly' (t : ℝ) : ℝ :=
  (28561 / 165888 : ℝ) * t ^ 2 - (130765 / 124416 : ℝ) * t + (29645 / 10368 : ℝ)

private lemma hasDerivAt_robbinsPoly (t : ℝ) : HasDerivAt robbinsPoly (robbinsPoly' t) t := by
  unfold robbinsPoly robbinsPoly'
  -- derivative of a cubic polynomial
  have h0 : HasDerivAt (fun _x : ℝ => (3431 / 864 : ℝ)) 0 t := hasDerivAt_const t _
  have h1 : HasDerivAt (fun x : ℝ => (29645 / 10368 : ℝ) * x) (29645 / 10368 : ℝ) t := by
    simpa [mul_comm] using (hasDerivAt_id t).const_mul (29645 / 10368 : ℝ)
  have h2 : HasDerivAt (fun x : ℝ => -(130765 / 248832 : ℝ) * x ^ 2)
      (-(130765 / 124416 : ℝ) * t) t := by
    have hpow : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℝ) * t) t := by
      simpa using (hasDerivAt_pow 2 t)
    have h := hpow.const_mul (-(130765 / 248832 : ℝ))
    convert h using 1; ring_nf
  have h3 : HasDerivAt (fun x : ℝ => (28561 / 497664 : ℝ) * x ^ 3)
      ((28561 / 165888 : ℝ) * t ^ 2) t := by
    have hpow : HasDerivAt (fun x : ℝ => x ^ 3) ((3 : ℝ) * t ^ 2) t := by
      simpa using (hasDerivAt_pow 3 t)
    have h := hpow.const_mul (28561 / 497664 : ℝ)
    convert h using 1; ring_nf
  have h := (((h0.add h1).add h2).add h3)
  convert h using 1
  · funext x
    simp [Pi.add_apply]
    ring_nf
  · ring_nf

private lemma robbinsPoly'_pos (t : ℝ) : 0 < robbinsPoly' t := by
  -- Use a discriminant computation (completing the square).
  have hderiv : deriv robbinsPoly t = robbinsPoly' t := by
    simpa using (hasDerivAt_robbinsPoly t).deriv
  -- `robbinsPoly'` is a quadratic with negative discriminant.
  -- We prove positivity by completing the square.
  -- Setup coefficients.
  let a : ℝ := (28561 / 165888 : ℝ)
  let b : ℝ := (-(130765 / 124416 : ℝ))
  let c : ℝ := (29645 / 10368 : ℝ)
  have ha : 0 < a := by norm_num [a]
  have hD : b ^ 2 - 4 * a * c < 0 := by
    -- exact rational computation
    norm_num [a, b, c]
  have hquad :
      robbinsPoly' t = a * t ^ 2 + b * t + c := by
    simp [robbinsPoly', a, b, c, pow_two, mul_assoc, mul_comm, sub_eq_add_neg]
  -- Apply the generic completed-square argument.
  have : 0 < a * t ^ 2 + b * t + c := by
    have ha0 : a ≠ 0 := ne_of_gt ha
    have hsq : a * t ^ 2 + b * t + c = a * (t + b / (2 * a)) ^ 2 + (4 * a * c - b ^ 2) / (4 * a) := by
      field_simp [ha0]
      ring
    have hconst_pos : 0 < (4 * a * c - b ^ 2) / (4 * a) := by
      have hn : 0 < 4 * a * c - b ^ 2 := by linarith
      have hd : 0 < 4 * a := by nlinarith [ha]
      exact div_pos hn hd
    have hsq_nonneg : 0 ≤ a * (t + b / (2 * a)) ^ 2 := by
      exact mul_nonneg (le_of_lt ha) (sq_nonneg _)
    have hsum_pos : 0 < a * (t + b / (2 * a)) ^ 2 + (4 * a * c - b ^ 2) / (4 * a) :=
      lt_of_lt_of_le hconst_pos (le_add_of_nonneg_left hsq_nonneg)
    simpa [hsq] using hsum_pos
  simpa [hquad]

private lemma robbinsPoly_pos {t : ℝ} (_ht : 0 ≤ t) : 0 < robbinsPoly t := by
  -- `robbinsPoly` is strictly increasing everywhere, so `robbinsPoly t ≥ robbinsPoly 0 > 0`.
  have hpos_deriv : ∀ x : ℝ, 0 < deriv robbinsPoly x := by
    intro x
    rw [(hasDerivAt_robbinsPoly x).deriv]
    exact robbinsPoly'_pos x
  have hmono : StrictMono robbinsPoly := strictMono_of_deriv_pos hpos_deriv
  have h0 : 0 < robbinsPoly 0 := by
    simp [robbinsPoly]
  -- since `0 < t`, or `t = 0`, both imply `0 < robbinsPoly t`
  have : 0 ≤ robbinsPoly 0 := le_of_lt h0
  have hle : robbinsPoly 0 ≤ robbinsPoly t := by
    exact (hmono.monotone (by simpa using _ht))
  exact lt_of_lt_of_le h0 hle

private lemma robbinsAux''''_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ robbinsAux'''' t := by
  -- Rewrite `exp (t * (13/12))` as `exp t * exp (t/12)` and use a cubic lower bound for the
  -- remaining bracket.
  have hexp13 : Real.exp (t * (13 / 12 : ℝ)) = Real.exp t * Real.exp (t * (1 / 12 : ℝ)) := by
    have : t * (13 / 12 : ℝ) = t + t * (1 / 12 : ℝ) := by ring
    calc
      Real.exp (t * (13 / 12 : ℝ)) = Real.exp (t + t * (1 / 12 : ℝ)) := by simp [this]
      _ = Real.exp t * Real.exp (t * (1 / 12 : ℝ)) := by simp [Real.exp_add]
  have hpi : 0 ≤ Real.exp (t * (1 / 12 : ℝ)) := (Real.exp_pos _).le
  have htlin : 0 ≤ (28561 * t + 48334) / 1728 := by
    have : (0 : ℝ) ≤ 28561 * t + 48334 := by nlinarith [ht]
    nlinarith
  have hExpLower :
      robbinsPoly t ≤
        Real.exp (t * (1 / 12 : ℝ)) * ((28561 * t + 48334) / 1728) - 2 * (t ^ 2 + 8 * t + 12) := by
    -- use `exp u ≥ 1 + u + u^2/2` with `u = t/12`
    have hu : 0 ≤ t * (1 / 12 : ℝ) := by nlinarith [ht]
    have hexp_lb : 1 + (t * (1 / 12 : ℝ)) + (t * (1 / 12 : ℝ)) ^ 2 / 2 ≤ Real.exp (t * (1 / 12 : ℝ)) :=
      exp_ge_one_add_sq hu
    -- multiply by the nonnegative scalar `((28561*t+48334)/1728)`
    have hmul :
        (1 + (t * (1 / 12 : ℝ)) + (t * (1 / 12 : ℝ)) ^ 2 / 2) * ((28561 * t + 48334) / 1728)
          ≤ Real.exp (t * (1 / 12 : ℝ)) * ((28561 * t + 48334) / 1728) :=
      mul_le_mul_of_nonneg_right hexp_lb htlin
    have hsub :
        (1 + (t * (1 / 12 : ℝ)) + (t * (1 / 12 : ℝ)) ^ 2 / 2) * ((28561 * t + 48334) / 1728)
            - 2 * (t ^ 2 + 8 * t + 12)
          ≤ Real.exp (t * (1 / 12 : ℝ)) * ((28561 * t + 48334) / 1728) - 2 * (t ^ 2 + 8 * t + 12) :=
      sub_le_sub_right hmul _
    -- show the LHS equals `robbinsPoly t`
    have : (1 + (t * (1 / 12 : ℝ)) + (t * (1 / 12 : ℝ)) ^ 2 / 2) * ((28561 * t + 48334) / 1728)
          - 2 * (t ^ 2 + 8 * t + 12) = robbinsPoly t := by
      -- purely algebraic normalization
      unfold robbinsPoly
      ring
    -- rewrite the LHS of `hsub` using the explicit polynomial identity, without
    -- triggering simp-normalization of the `sub_le_sub_right` step.
    calc
      robbinsPoly t =
          (1 + (t * (1 / 12 : ℝ)) + (t * (1 / 12 : ℝ)) ^ 2 / 2) * ((28561 * t + 48334) / 1728)
            - 2 * (t ^ 2 + 8 * t + 12) := by
              simpa using this.symm
      _ ≤ Real.exp (t * (1 / 12 : ℝ)) * ((28561 * t + 48334) / 1728) - 2 * (t ^ 2 + 8 * t + 12) := hsub
  have hpoly_pos : 0 < robbinsPoly t := robbinsPoly_pos (t := t) ht
  have hbracket : 0 ≤ Real.exp (t * (1 / 12 : ℝ)) * ((28561 * t + 48334) / 1728) - 2 * (t ^ 2 + 8 * t + 12) :=
    le_of_lt (lt_of_lt_of_le hpoly_pos hExpLower)
  -- finish: `robbinsAux''''` is `exp t * bracket + exp(t/12) * ((t+50)/1728)`
  have hterm2 : 0 ≤ Real.exp (t * (1 / 12 : ℝ)) * ((t + 50) / 1728) := by
    have : 0 ≤ (t + 50) / 1728 := by nlinarith [ht]
    exact mul_nonneg (Real.exp_pos _).le this
  -- rewrite and conclude
  have : robbinsAux'''' t =
      Real.exp t * (Real.exp (t * (1 / 12 : ℝ)) * ((28561 * t + 48334) / 1728) - 2 * (t ^ 2 + 8 * t + 12))
        + Real.exp (t * (1 / 12 : ℝ)) * ((t + 50) / 1728) := by
    unfold robbinsAux''''
    -- use `hexp13` and `ring`
    simp [hexp13, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg]
    ring
  rw [this]
  exact add_nonneg (mul_nonneg (Real.exp_pos _).le hbracket) hterm2

private lemma robbinsAux'''_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ robbinsAux''' t := by
  apply nonneg_of_deriv_nonneg_Ici differentiableOn_robbinsAux'''
  · intro x hx
    rw [(hasDerivAt_robbinsAux''' x).deriv]
    exact robbinsAux''''_nonneg (t := x) hx
  · exact robbinsAux'''_zero
  · exact ht

private lemma robbinsAux''_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ robbinsAux'' t := by
  apply nonneg_of_deriv_nonneg_Ici differentiableOn_robbinsAux''
  · intro x hx
    rw [(hasDerivAt_robbinsAux'' x).deriv]
    exact robbinsAux'''_nonneg (t := x) hx
  · exact robbinsAux''_zero
  · exact ht

private lemma robbinsAux'_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ robbinsAux' t := by
  apply nonneg_of_deriv_nonneg_Ici differentiableOn_robbinsAux'
  · intro x hx
    rw [(hasDerivAt_robbinsAux' x).deriv]
    exact robbinsAux''_nonneg (t := x) hx
  · exact robbinsAux'_zero
  · exact ht

private lemma robbinsAux_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ robbinsAux t := by
  apply nonneg_of_deriv_nonneg_Ici differentiableOn_robbinsAux
  · intro x hx
    rw [(hasDerivAt_robbinsAux x).deriv]
    exact robbinsAux'_nonneg (t := x) hx
  · exact robbinsAux_zero
  · exact ht

theorem Ktilde_ge_one_div_twelve_mul_exp_neg_div_twelve {t : ℝ} (ht : 0 < t) :
    (1 / 12 : ℝ) * Real.exp (-t / 12) ≤ Ktilde t := by
  -- Rewrite `Ktilde t` via the `f`-formula and reduce to `robbinsAux_nonneg`.
  have ht0 : 0 ≤ t := le_of_lt ht
  have hexp : 0 < Real.exp t - 1 := exp_sub_one_pos ht
  have hK : Ktilde t = f t / (2 * t ^ 2 * (Real.exp t - 1)) := by
    -- same algebra as in `Ktilde_le`
    calc
      Ktilde t = (1 / (Real.exp t - 1) - 1 / t + 1 / 2) / t := Ktilde_pos ht
      _ = (Real.exp t * (t - 2) + t + 2) / (2 * t * (Real.exp t - 1)) / t := by
            rw [← K_pos ht, K_eq_alt' ht]
      _ = f t / (2 * t ^ 2 * (Real.exp t - 1)) := by
            unfold f
            field_simp
  rw [hK]
  -- Convert to `2*t^2*(exp t - 1) ≤ 12*exp(t/12)*f t`.
  have hdenom : 0 < (2 * t ^ 2 * (Real.exp t - 1)) := by positivity
  -- multiply the desired inequality by the positive scalar `12*exp(t/12)*(2*t^2*(exp t -1))`
  have hmain :
      2 * t ^ 2 * (Real.exp t - 1) ≤ 12 * Real.exp (t * (1 / 12 : ℝ)) * f t := by
    -- this is exactly `robbinsAux_nonneg` after expanding `robbinsAux`
    have h0 : 0 ≤ robbinsAux t := robbinsAux_nonneg (t := t) ht0
    -- rewrite `robbinsAux` into the target inequality
    have hrobbins :
        robbinsAux t = 12 * Real.exp (t * (1 / 12 : ℝ)) * f t - 2 * t ^ 2 * (Real.exp t - 1) := by
      -- unfold and simplify
      unfold robbinsAux f
      -- use `exp_add` to rewrite `exp(t + t/12)` as product
      have : t * (13 / 12 : ℝ) = t + t * (1 / 12 : ℝ) := by ring
      simp [this, Real.exp_add, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg]
      ring
    -- conclude
    have : 2 * t ^ 2 * (Real.exp t - 1) ≤ 12 * Real.exp (t * (1 / 12 : ℝ)) * f t := by
      -- `0 ≤ A - B` implies `B ≤ A`
      have : 0 ≤ 12 * Real.exp (t * (1 / 12 : ℝ)) * f t - 2 * t ^ 2 * (Real.exp t - 1) := by
        simpa [hrobbins] using h0
      exact sub_nonneg.1 this
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  -- divide both sides by the positive denominator
  -- and rewrite `exp(-t/12)` as inverse.
  have : (1 / 12 : ℝ) * Real.exp (-t / 12) ≤ f t / (2 * t ^ 2 * (Real.exp t - 1)) := by
    -- start from `le_div_iff₀`
    have : ((1 / 12 : ℝ) * Real.exp (-t / 12)) * (2 * t ^ 2 * (Real.exp t - 1)) ≤ f t := by
      -- multiply `hmain` by `exp(-t/12)/12` and simplify
      have hexp' : Real.exp (-t / 12) = (Real.exp (t * (1 / 12 : ℝ)))⁻¹ := by
        -- `exp(-a)= (exp a)⁻¹`
        have : (-t / 12 : ℝ) = -(t * (1 / 12 : ℝ)) := by ring
        simp [this, Real.exp_neg]
      -- use `hmain` and rearrange
      have hmain' :
          ((1 / 12 : ℝ) * Real.exp (-t / 12)) * (2 * t ^ 2 * (Real.exp t - 1))
            ≤ ((1 / 12 : ℝ) * Real.exp (-t / 12)) * (12 * Real.exp (t * (1 / 12 : ℝ)) * f t) := by
        exact mul_le_mul_of_nonneg_left hmain (by positivity)
      -- simplify RHS to `f t`
      -- `((1/12)*exp(-t/12))*(12*exp(t/12)*f t) = f t`
      calc
        ((1 / 12 : ℝ) * Real.exp (-t / 12)) * (2 * t ^ 2 * (Real.exp t - 1))
            ≤ ((1 / 12 : ℝ) * Real.exp (-t / 12)) * (12 * Real.exp (t * (1 / 12 : ℝ)) * f t) := hmain'
        _ = f t := by
            -- Cancel the exponential factors and `12` by a clean algebraic rearrangement.
            have hExp : Real.exp (-t / 12) * Real.exp (t * (1 / 12 : ℝ)) = 1 := by
              have : (-t / 12 : ℝ) + (t * (1 / 12 : ℝ)) = 0 := by ring
              have := congrArg Real.exp this
              simpa [Real.exp_add, Real.exp_zero] using this
            calc
              ((1 / 12 : ℝ) * Real.exp (-t / 12)) * (12 * Real.exp (t * (1 / 12 : ℝ)) * f t)
                  = ((1 / 12 : ℝ) * 12) * (Real.exp (-t / 12) * Real.exp (t * (1 / 12 : ℝ))) * f t := by
                      ring
              _ = (Real.exp (-t / 12) * Real.exp (t * (1 / 12 : ℝ))) * f t := by
                      simp [mul_assoc]
              _ = f t := by
                      simpa [mul_assoc] using congrArg (fun z => z * f t) hExp
    -- now conclude by dividing by the positive denominator
    have : (1 / 12 : ℝ) * Real.exp (-t / 12) ≤ f t / (2 * t ^ 2 * (Real.exp t - 1)) := by
      exact (le_div_iff₀ hdenom).2 this
    exact this
  -- and finish with the rewritten `Ktilde`
  exact this

/-! ## Section 5: Limit at zero -/

/-- Auxiliary: (exp t - 1)/t → 1 as t → 0.
This follows from the derivative of exp at 0 being 1. -/
lemma tendsto_exp_sub_one_div :
    Tendsto (fun t => (Real.exp t - 1) / t) (𝓝[>] 0) (𝓝 1) := by
  have h := Real.hasDerivAt_exp 0
  rw [Real.exp_zero] at h
  -- HasDerivAt.tendsto_slope_zero_right gives:
  -- Tendsto (fun t => t⁻¹ • (exp(0 + t) - exp 0)) (𝓝[>] 0) (𝓝 1)
  have := h.tendsto_slope_zero_right
  simp only [zero_add, Real.exp_zero, smul_eq_mul] at this
  -- Convert t⁻¹ * (exp t - 1) to (exp t - 1) / t
  refine this.congr (fun t => ?_)
  rw [inv_mul_eq_div]

/-- The Taylor remainder h(t) = exp(t) - 1 - t - t²/2 satisfies h(t)/t³ → 1/6 as t → 0. -/
lemma tendsto_exp_taylor3_div_cube :
    Tendsto (fun t => (Real.exp t - 1 - t - t^2/2) / t^3) (𝓝[>] 0) (𝓝 (1/6 : ℝ)) := by
  -- exp(t) - 1 - t - t²/2 = (exp(t) - (1 + t + t²/2 + t³/6)) + t³/6
  -- The first part is o(t³), so dividing by t³ gives 0 + 1/6
  have h_taylor : (fun x => Real.exp x - ∑ i ∈ Finset.range 4, x ^ i / Nat.factorial i) =o[𝓝 0] (· ^ 3) :=
    Real.exp_sub_sum_range_succ_isLittleO_pow 3
  -- Compute: ∑ i ∈ range 4, x^i/i! = 1 + x + x²/2 + x³/6
  have h_sum : ∀ x : ℝ, ∑ i ∈ Finset.range 4, x ^ i / Nat.factorial i = 1 + x + x^2/2 + x^3/6 := by
    intro x; simp [Finset.sum_range_succ]; ring
  -- Rewrite: exp(t) - 1 - t - t²/2 = (exp(t) - sum) + t³/6
  have h_decomp : ∀ t : ℝ, Real.exp t - 1 - t - t^2/2 =
      (Real.exp t - ∑ i ∈ Finset.range 4, t ^ i / Nat.factorial i) + t^3/6 := by
    intro t; rw [h_sum]; ring
  -- The ratio (exp - sum)/t³ → 0 since exp - sum = o(t³)
  have h_zero : Tendsto (fun t => (Real.exp t - ∑ i ∈ Finset.range 4, t ^ i / Nat.factorial i) / t^3)
      (𝓝[>] 0) (𝓝 0) := by
    have := h_taylor.tendsto_div_nhds_zero
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  -- Combine: our expression equals (o-term)/t³ + 1/6 → 0 + 1/6
  have h_add : Tendsto (fun t => (Real.exp t - ∑ i ∈ Finset.range 4, t ^ i / Nat.factorial i) / t^3 + 1/6)
      (𝓝[>] 0) (𝓝 (0 + 1/6)) := h_zero.add tendsto_const_nhds
  simp only [zero_add] at h_add
  refine h_add.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hne : t ≠ 0 := ne_of_gt ht
  rw [h_decomp]
  field_simp

/-- Auxiliary: f(t)/t³ → 1/6 as t → 0⁺.
Since f(t) = exp(t)(t-2) + t + 2, Taylor expansion gives f(t) = t³/6 + O(t⁴). -/
lemma tendsto_f_div_cube :
    Tendsto (fun t => f t / t ^ 3) (𝓝[>] 0) (𝓝 (1/6 : ℝ)) := by
  -- f(t) = exp(t)(t-2) + t + 2
  -- Using the Taylor expansion exp(t) = 1 + t + t²/2 + t³/6 + O(t⁴):
  -- f(t) = (1 + t + t²/2 + t³/6 + ...)(t-2) + t + 2 = t³/6 + O(t⁴)
  -- So f(t)/t³ → 1/6
  -- Strategy: decompose f(t) = t³/2 + h(t)(t-2) where h(t) = exp(t) - 1 - t - t²/2
  -- Then f(t)/t³ = 1/2 + (h(t)/t³)(t-2) → 1/2 + (1/6)(-2) = 1/6
  have h1 : Tendsto (fun t => (Real.exp t - 1 - t - t^2/2) / t^3 * (t - 2))
      (𝓝[>] 0) (𝓝 ((1/6 : ℝ) * (-2))) := by
    apply Tendsto.mul tendsto_exp_taylor3_div_cube
    have : Tendsto (fun x : ℝ => x - 2) (𝓝 0) (𝓝 (-2)) := by
      have h : (0 : ℝ) - 2 = -2 := by norm_num
      exact h ▸ tendsto_id.sub tendsto_const_nhds
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have h2 : Tendsto (fun t => 1/2 + (Real.exp t - 1 - t - t^2/2) / t^3 * (t - 2))
      (𝓝[>] 0) (𝓝 (1/2 + (1/6) * (-2))) := tendsto_const_nhds.add h1
  have heq : (1/2 + (1/6) * (-2) : ℝ) = 1/6 := by norm_num
  rw [← heq]
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hne : t ≠ 0 := ne_of_gt ht
  -- f(t) = t³/2 + h(t)(t-2) where h = exp - 1 - t - t²/2
  have hdecomp : f t = t^3/2 + (Real.exp t - 1 - t - t^2/2) * (t - 2) := by unfold f; ring
  rw [hdecomp]
  field_simp

/-- The kernel K̃(t) → 1/12 as t → 0⁺.
This follows from the Taylor expansion: K(t) = t/12 - t³/720 + O(t⁵), so K(t)/t → 1/12. -/
theorem tendsto_Ktilde_zero :
    Tendsto Ktilde (𝓝[>] 0) (𝓝 (1/12 : ℝ)) := by
  -- Strategy: Ktilde t = f(t) / (2t²(exp t - 1)) for t > 0
  --         = (f(t)/t³) / (2 · (exp t - 1)/t)
  -- Since f(t)/t³ → 1/6 and (exp t - 1)/t → 1,
  -- we get Ktilde t → (1/6) / (2·1) = 1/12
  have h1 : ∀ᶠ t in 𝓝[>] 0, t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ne_of_gt ht
  have h2 : ∀ᶠ t in 𝓝[>] 0, 0 < Real.exp t - 1 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact exp_sub_one_pos ht
  have h3 : ∀ᶠ t in 𝓝[>] 0, Ktilde t = f t / (2 * t^2 * (Real.exp t - 1)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [Ktilde_pos ht, ← K_pos ht, K_eq_alt' ht]
    unfold f; field_simp
  rw [tendsto_congr' h3]
  -- Rewrite as (f(t)/t³) / (2 · (exp t - 1)/t)
  have h4 : ∀ᶠ t in 𝓝[>] 0, f t / (2 * t^2 * (Real.exp t - 1)) =
      (f t / t^3) / (2 * ((Real.exp t - 1) / t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hne : t ≠ 0 := ne_of_gt ht
    have hexp' : Real.exp t - 1 ≠ 0 := ne_of_gt (exp_sub_one_pos ht)
    field_simp
  rw [tendsto_congr' h4]
  -- Apply limit laws: (1/6) / (2 * 1) = 1/12
  have hlim_num := tendsto_f_div_cube
  have hlim_den := tendsto_exp_sub_one_div.const_mul 2
  have hne : (2 : ℝ) * 1 ≠ 0 := by norm_num
  convert hlim_num.div hlim_den hne using 1
  norm_num

/-- K̃ is continuous on ℝ. -/
lemma continuous_Ktilde : Continuous Ktilde := by
  -- Ktilde is continuous because:
  -- - For x > 0: continuousOn_Ktilde_Ioi
  -- - For x < 0: Ktilde is constant 1/12
  -- - At x = 0: left limit is 1/12, right limit is 1/12 (tendsto_Ktilde_zero)
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : 0 < x
  · exact continuousOn_Ktilde_Ioi.continuousAt (Ioi_mem_nhds hx)
  · push_neg at hx
    by_cases hx0 : x < 0
    · -- For x < 0, Ktilde is constant 1/12 in a neighborhood
      have hev : ∀ᶠ y in 𝓝 x, Ktilde y = 1/12 := by
        filter_upwards [Iio_mem_nhds hx0] with y hy
        unfold Ktilde; rw [if_pos (le_of_lt hy)]
      rw [ContinuousAt]
      have hval : Ktilde x = 1/12 := by unfold Ktilde; rw [if_pos (le_of_lt hx0)]
      rw [hval]
      exact tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm)
    · -- x = 0: use left/right continuity
      have hx_eq : x = 0 := le_antisymm hx (not_lt.mp hx0)
      subst hx_eq
      rw [continuousAt_iff_continuous_left'_right']
      constructor
      · -- Left continuity: Ktilde is constant 1/12 on Iio 0
        rw [ContinuousWithinAt]
        have hval : Ktilde 0 = 1/12 := Ktilde_zero
        rw [hval]
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with y hy
        unfold Ktilde; rw [if_pos (le_of_lt hy)]
      · -- Right continuity: from tendsto_Ktilde_zero
        rw [ContinuousWithinAt, Ktilde_zero]
        exact tendsto_Ktilde_zero

/-! ## Section 6: Integrability -/

/-- Ktilde is bounded on [0, ∞). -/
lemma Ktilde_bdd : ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ‖Ktilde t‖ ≤ C := by
  use 1/12
  intro t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (Ktilde_nonneg ht)]
  exact Ktilde_le ht

/-- The kernel K̃(t) * e^{-tx} is integrable on (0, ∞) for x > 0. -/
theorem integrable_Ktilde_exp {x : ℝ} (hx : 0 < x) :
    Integrable (fun t => Ktilde t * Real.exp (-t * x))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)) := by
  -- exp(-t*x) = exp((-x)*t) is integrable on (0, ∞) since -x < 0
  have h_exp_int : IntegrableOn (fun t => Real.exp (-x * t)) (Set.Ioi 0) := by
    exact integrableOn_exp_mul_Ioi (neg_neg_of_pos hx) 0
  -- Rewrite exp(-t*x) as exp((-x)*t)
  have h_exp_eq : Set.EqOn (fun t => Real.exp (-x * t)) (fun t => Real.exp (-t * x)) (Set.Ioi 0) :=
    fun t _ => by ring_nf
  have h_exp_int' : IntegrableOn (fun t => Real.exp (-t * x)) (Set.Ioi 0) :=
    h_exp_int.congr_fun h_exp_eq measurableSet_Ioi
  -- Ktilde is bounded and continuous (hence measurable)
  have h_bdd : ∃ C, ∀ t, ‖Ktilde t‖ ≤ C := by
    use 1/12
    intro t
    by_cases ht : 0 ≤ t
    · rw [Real.norm_eq_abs, abs_of_nonneg (Ktilde_nonneg ht)]
      exact Ktilde_le ht
    · push_neg at ht
      simp only [Ktilde, if_pos (le_of_lt ht)]
      norm_num
  have h_meas : AEStronglyMeasurable Ktilde
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)) :=
    continuous_Ktilde.aestronglyMeasurable.restrict
  -- Convert h_bdd to the ae form needed by bdd_mul
  obtain ⟨C, hC⟩ := h_bdd
  have h_bdd_ae : ∀ᵐ t ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)),
      ‖Ktilde t‖ ≤ C := by
    filter_upwards with t
    exact hC t
  exact h_exp_int'.integrable.bdd_mul h_meas h_bdd_ae

/-- The Binet integral ∫₀^∞ K̃(t) e^{-tz} dt converges for Re(z) > 0. -/
theorem integrable_Ktilde_exp_complex {z : ℂ} (hz : 0 < z.re) :
    MeasureTheory.Integrable
      (fun t : ℝ => (Ktilde t : ℂ) * Complex.exp (-t * z))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)) := by
  -- Complex.exp(-t*z) = Complex.exp((-z)*t) is integrable since Re(-z) < 0
  have h_neg_re : (-z).re < 0 := by simp [hz]
  have h_exp_int : IntegrableOn (fun t : ℝ => Complex.exp ((-z) * t)) (Set.Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi h_neg_re 0
  -- Rewrite exp(-t*z) as exp((-z)*t): they're equal since -z * t = -t * z
  have h_exp_eq : Set.EqOn (fun t : ℝ => Complex.exp ((-z) * t))
      (fun t : ℝ => Complex.exp (-t * z)) (Set.Ioi 0) := fun t _ => by
    have h : (-z) * (t : ℂ) = -(t : ℂ) * z := by ring
    simp only [h]
  have h_exp_int' : IntegrableOn (fun t : ℝ => Complex.exp (-t * z)) (Set.Ioi 0) :=
    h_exp_int.congr_fun h_exp_eq measurableSet_Ioi
  -- (Ktilde : ℂ) is bounded
  have h_bdd : ∃ C, ∀ t, ‖(Ktilde t : ℂ)‖ ≤ C := by
    use 1/12
    intro t
    simp only [Complex.norm_real, Real.norm_eq_abs]
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg (Ktilde_nonneg ht)]
      exact Ktilde_le ht
    · push_neg at ht
      simp only [Ktilde, if_pos (le_of_lt ht)]
      norm_num
  -- (Ktilde : ℂ) is AE strongly measurable
  have h_meas : AEStronglyMeasurable (fun t : ℝ => (Ktilde t : ℂ))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      continuous_Ktilde.aestronglyMeasurable.restrict
  -- Convert h_bdd to the ae form needed by bdd_mul
  obtain ⟨C, hC⟩ := h_bdd
  have h_bdd_ae : ∀ᵐ t ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)),
      ‖(Ktilde t : ℂ)‖ ≤ C := by
    filter_upwards with t
    exact hC t
  exact h_exp_int'.integrable.bdd_mul h_meas h_bdd_ae

end BinetKernel
