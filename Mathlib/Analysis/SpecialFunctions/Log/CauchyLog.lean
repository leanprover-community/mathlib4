/-
Copyright (c) 2026 Jonathan Reich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Reich
-/
module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Cauchy Functional Equation Characterization of Logarithm

In this file we prove that continuous functions satisfying the multiplicative-to-additive
functional equation `f(xy) = f(x) + f(y)` on positive reals are exactly the constant multiples
of the natural logarithm.

## Main definitions

* `Real.IsMultiplicativeAdditive`: A function `f : ℝ → ℝ` satisfies `f(xy) = f(x) + f(y)` for
  all positive `x` and `y`.

## Main results

* `Real.IsMultiplicativeAdditive.eq_const_mul_log`: If `f` is continuous on `(0, ∞)` and
  multiplicative-additive, then `f x = c * log x` for all positive `x`, where `c = f(exp 1)`.
* `Real.continuous_mulAdditive_eq_const_mul_log`: Existence form of the above.

## References

* Cauchy, A. L. "Cours d'analyse" (1821)
* Aczél, J. "Lectures on Functional Equations and Their Applications"

## Tags

logarithm, functional equation, Cauchy, characterization
-/

public section

open Set

namespace Real

/-- A function `f : ℝ → ℝ` is multiplicative-additive if `f(xy) = f(x) + f(y)` for all
positive real numbers `x` and `y`. -/
def IsMultiplicativeAdditive (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, 0 < x → 0 < y → f (x * y) = f x + f y

namespace IsMultiplicativeAdditive

variable {f : ℝ → ℝ}

theorem map_one (hf : IsMultiplicativeAdditive f) : f 1 = 0 := by
  have h := hf 1 1 one_pos one_pos
  simp only [mul_one] at h
  linarith

theorem map_pow (hf : IsMultiplicativeAdditive f) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    f (x ^ n) = n * f x := by
  induction n with
  | zero => simp [map_one hf]
  | succ n ih =>
    rw [pow_succ, hf (x ^ n) x (pow_pos hx n) hx, ih]
    push_cast; ring

theorem map_inv (hf : IsMultiplicativeAdditive f) {x : ℝ} (hx : 0 < x) : f x⁻¹ = -f x := by
  have h1 : f (x * x⁻¹) = f x + f x⁻¹ := hf x x⁻¹ hx (inv_pos.mpr hx)
  simp only [mul_inv_cancel₀ (ne_of_gt hx), map_one hf] at h1
  linarith

theorem map_zpow (hf : IsMultiplicativeAdditive f) {x : ℝ} (hx : 0 < x) (z : ℤ) :
    f (x ^ z) = z * f x := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simpa using map_pow hf hx n
  · simp only [zpow_neg, zpow_natCast, Int.cast_neg, Int.cast_natCast]
    rw [map_inv hf (pow_pos hx n), map_pow hf hx n]
    ring

theorem map_exp_nat (hf : IsMultiplicativeAdditive f) (n : ℕ) : f (exp n) = n * f (exp 1) := by
  have : exp (n : ℝ) = (exp 1) ^ n := by rw [← exp_nat_mul, mul_comm, one_mul]
  rw [this, map_pow hf (exp_pos 1) n]

theorem map_exp_int (hf : IsMultiplicativeAdditive f) (z : ℤ) : f (exp z) = z * f (exp 1) := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simpa using map_exp_nat hf n
  · simp only [Int.cast_neg, Int.cast_natCast, exp_neg]
    rw [map_inv hf (exp_pos n), map_exp_nat hf n]
    ring

/-- A continuous multiplicative-additive function equals `c * log` for `c = f(exp 1)`. -/
theorem eq_const_mul_log (hf : IsMultiplicativeAdditive f) (hf_cont : ContinuousOn f (Ioi 0))
    (x : ℝ) (hx : 0 < x) : f x = f (exp 1) * log x := by
  rw [← exp_log hx]
  set c := f (exp 1)
  set t := log x
  let g : ℝ → ℝ := fun s => f (exp s)
  let h : ℝ → ℝ := fun s => c * s
  have hg_cont : Continuous g := hf_cont.comp_continuous continuous_exp (fun s => exp_pos s)
  have hh_cont : Continuous h := continuous_const.mul continuous_id
  have hgh_rat : ∀ q : ℚ, g q = h q := fun q => by
    simp only [g, h]
    have hq_cast : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q
    have key : (q.den : ℕ) * f (exp (q : ℝ)) = q.num * f (exp 1) := by
      have h1 : exp (q.den * (q : ℝ)) = exp q.num := by rw [hq_cast]; field_simp
      have h2 : f (exp (q.den * (q : ℝ))) = q.den * f (exp (q : ℝ)) := by
        rw [exp_nat_mul]; exact map_pow hf (exp_pos _) q.den
      rw [h1, map_exp_int hf q.num] at h2; linarith
    calc f (exp (q : ℝ))
        = (q.num / q.den) * f (exp 1) := by field_simp; linarith [key]
      _ = c * q := by rw [hq_cast]; ring
  have hdense : DenseRange (fun q : ℚ => (q : ℝ)) := Rat.isDenseEmbedding_coe_real.dense
  have hgh : g = h := hdense.equalizer hg_cont hh_cont (funext hgh_rat)
  calc f (exp t) = g t := rfl
    _ = h t := congr_fun hgh t
    _ = c * log (exp t) := by rw [log_exp]

end IsMultiplicativeAdditive

/-- The logarithm is multiplicative-additive. -/
theorem log_isMultiplicativeAdditive : IsMultiplicativeAdditive log := fun _ _ hx hy =>
  log_mul (ne_of_gt hx) (ne_of_gt hy)

/-- Continuous multiplicative-additive functions on positive reals are constant multiples
of the logarithm. -/
theorem continuous_mulAdditive_eq_const_mul_log {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Ioi 0)) (hf_mul : IsMultiplicativeAdditive f) :
    ∃ c : ℝ, ∀ x : ℝ, 0 < x → f x = c * log x :=
  ⟨f (exp 1), fun x hx => hf_mul.eq_const_mul_log hf_cont x hx⟩

end Real
