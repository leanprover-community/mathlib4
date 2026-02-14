/-
Copyright (c) 2025 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Module.Connected

/-!
Auxiliary lemmata covering the analytic part of the proof of the Gelfond–Schneider theorem.
Move to appropriate files in Analysis/Complex or Analysis/Analytic and change docstring accordingly.
-/

@[expose] public section

open AnalyticOnNhd AnalyticAt Set

lemma iterated_deriv_mul_pow_sub_of_analytic (r : ℕ) (z₀ : ℂ) {R R₁ : ℂ → ℂ}
    (hf1 : ∀ z : ℂ, AnalyticAt ℂ R₁ z) (hR₁ : ∀ z, R z = (z - z₀)^r * R₁ z) :
    ∀ k ≤ r, ∃ R₂ : ℂ → ℂ, (∀ z : ℂ, AnalyticAt ℂ R₂ z) ∧ ∀ z, deriv^[k] R z =
    (z - z₀) ^ (r - k) * (r.factorial / (r - k).factorial * R₁ z + (z - z₀) * R₂ z) := by
  intros k hkr
  induction k generalizing r with
  | zero =>
    refine ⟨0, ?_⟩
    · simp only [Function.iterate_zero, id_eq, tsub_zero, Pi.zero_apply, mul_zero, add_zero]
      refine ⟨fun z ↦ Differentiable.analyticAt (differentiable_zero) z, fun z ↦ ?_⟩
      · rw [hR₁ z, mul_eq_mul_left_iff, pow_eq_zero_iff', div_self
        (h:= mod_cast Nat.factorial_ne_zero r)]; grind
  | succ k IH =>
    obtain ⟨R₂, hR₂, hR1⟩ := IH r hR₁ (by linarith)
    refine ⟨fun z ↦ (↑(r - k) * R₂ z +
         (↑r.factorial / ↑(r - k).factorial * deriv R₁ z + (R₂ z + (z - z₀) * deriv R₂ z))), ?_⟩
    · refine ⟨fun z ↦ by fun_prop, fun z ↦ ?_⟩
      · calc _ = deriv (deriv^[k] R) z := ?_
             _ = ↑(r - k) * (z - z₀) ^ (r - k - 1) * (↑r.factorial / ↑(r - k).factorial *
                 R₁ z + (z - z₀) * R₂ z) + (z - z₀) ^ (r - k) * (↑r.factorial / ↑(r - k).factorial *
                 deriv R₁ z + (R₂ z + (z - z₀) * deriv R₂ z)) := ?_
             _ = 1 * ((z - z₀) ^ (r - (k + 1)) *(↑r.factorial / ↑(r - k).factorial * R₁ z)) +
                 ↑(r - k - 1) * ((z - z₀) ^ (r - (k + 1)) *
                 (↑r.factorial / ↑(r - k).factorial * R₁ z)) +
                 ↑(r - k) * (z - z₀) ^ (r - (k + 1)) * ((z - z₀) * R₂ z) +
                 (z - z₀) ^ (r - k) * (↑r.factorial / ↑(r - k).factorial *
                 deriv R₁ z + (R₂ z + (z - z₀) * deriv R₂ z)) := ?_
             _ = (z - z₀) ^ (r - (k + 1)) * (↑r.factorial / ↑(r - (k + 1)).factorial *
                 R₁ z + (z - z₀) *(fun z ↦ ↑(r - k) * R₂ z + (↑r.factorial / ↑(r - k).factorial *
                 deriv R₁ z + (R₂ z + (z - z₀) * deriv R₂ z))) z) := ?_
        · symm
          have : deriv^[k] (deriv R) z = deriv^[k+1] R z := by
            rw [Function.iterate_succ, Function.comp_apply]
          induction k generalizing r with
            | zero => aesop
            | succ k IH =>
              rw [Function.iterate_succ, Function.comp_apply] at IH ⊢
              rw [← iteratedDeriv_eq_iterate] at this ⊢
              rw [← iteratedDeriv_succ, this]
        · conv => enter [1, 1]; ext z; rw [hR1 z];; simp (disch := fun_prop)
        · rw [mul_add, Nat.sub_sub r k 1, ← add_mul, mul_assoc]; congr; norm_cast; grind [mul_assoc]
        · simp only [one_mul, ← mul_assoc]; nth_rw 5 [mul_comm]; simp only [← add_assoc, mul_assoc]
          rw [← mul_add]; simp only [← mul_assoc]; nth_rw 6 [mul_comm]; nth_rw 7 [mul_comm];
          simp only [← mul_assoc]; nth_rw 7 [mul_comm]; simp only [mul_assoc, ← mul_add]
          have : (z - z₀) ^ (r - k) = (z - z₀) ^ (r - (k + 1)) * (z - z₀) ^ 1 := by
            rw [← pow_add]; congr; grind
          rw [this, mul_assoc, ← mul_add, pow_one, mul_eq_mul_left_iff]; left;
          nth_rw 1 [← mul_assoc, ← add_mul, ← one_mul (a := (r.factorial / (r - k).factorial : ℂ))]
          nth_rw 1 [← add_mul]; rw [add_assoc]; simp only [mul_assoc]; rw [← mul_add];
          nth_rw 2 [add_comm]; norm_cast; simp only [← mul_assoc, mul_div]
          have HR : ↑(r - (k + 1) + 1) = ↑(r - k) := by grind
          simp only [Nat.sub_sub r k 1, HR, add_assoc]; congr 1; simp only [mul_eq_mul_right_iff]
          left; nth_rw 2 [← Nat.mul_factorial_pred (hn := by grind)]; rw [Nat.sub_sub r k 1]
          ring_nf; nth_rw 2 [mul_comm]; nth_rw 3 [mul_comm]
          rw [Nat.cast_mul, mul_inv_rev, ← mul_assoc, mul_eq_mul_right_iff, inv_eq_zero,
            Nat.cast_eq_zero, mul_assoc, mul_inv_cancel₀ (h := by simp; grind)]
          grind
