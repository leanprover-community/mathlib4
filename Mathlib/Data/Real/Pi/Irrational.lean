/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Data.Real.Irrational

/-!
# `Real.pi` is irrational

The main result of this file is `irrational_pi`.
-/

noncomputable section

open intervalIntegral MeasureTheory.MeasureSpace Set Polynomial Real
open scoped Nat

private def I (n : ℕ) (θ : ℝ) : ℝ := ∫ x in (-1)..1, (1 - x ^ 2) ^ n * cos (x * θ)

variable {n : ℕ} {θ : ℝ}

private lemma I_zero : I 0 θ * θ = 2 * sin θ := by
  rw [mul_comm, I]
  simp [mul_integral_comp_mul_right, two_mul]

private lemma recursion' (n : ℕ) :
    I (n + 1) θ * θ ^ 2 = - (2 * 2 * ((n + 1) * (0 ^ n * cos θ))) +
      2 * (n + 1) * (2 * n + 1) * I n θ - 4 * (n + 1) * n * I (n - 1) θ := by
  rw [I]
  let f (x : ℝ) : ℝ := 1 - x ^ 2
  let u₁ (x : ℝ) : ℝ := f x ^ (n + 1)
  let u₁' (x : ℝ) : ℝ := - (2 * (n + 1) * x * f x ^ n)
  let v₁ (x : ℝ) : ℝ := sin (x * θ)
  let v₁' (x : ℝ) : ℝ := cos (x * θ) * θ
  let u₂ (x : ℝ) : ℝ := x * (f x) ^ n
  let u₂' (x : ℝ) : ℝ := (f x) ^ n - 2 * n * x ^ 2 * (f x) ^ (n - 1)
  let v₂ (x : ℝ) : ℝ := cos (x * θ)
  let v₂' (x : ℝ) : ℝ := -sin (x * θ) * θ
  have hfd : Continuous f := by fun_prop
  have hu₁d : Continuous u₁' := by fun_prop
  have hv₁d : Continuous v₁' := by fun_prop
  have hu₂d : Continuous u₂' := by fun_prop
  have hv₂d : Continuous v₂' := by fun_prop
  have hu₁_eval_one : u₁ 1 = 0 := by simp only [u₁, f]; simp
  have hu₁_eval_neg_one : u₁ (-1) = 0 := by simp only [u₁, f]; simp
  have t : u₂ 1 * v₂ 1 - u₂ (-1) * v₂ (-1) = 2 * (0 ^ n * cos θ) := by
    simp only [u₂, v₂, f, one_pow, sub_self, one_mul, neg_one_sq, neg_mul, cos_neg, sub_neg_eq_add]
    simp only [← two_mul]
  have hf (x) : HasDerivAt f (- 2 * x) x := by
    convert (hasDerivAt_pow 2 x).const_sub 1 using 1
    simp
  have hu₁ (x) : HasDerivAt u₁ (u₁' x) x := by
    convert (hf x).pow _ using 1
    simp only [Nat.add_succ_sub_one, u₁', Nat.cast_add_one]
    ring
  have hv₁ (x) : HasDerivAt v₁ (v₁' x) x := (hasDerivAt_mul_const θ).sin
  have hu₂ (x) : HasDerivAt u₂ (u₂' x) x := by
    convert HasDerivAt.mul (hasDerivAt_id' x) ((hf x).pow _) using 1
    simp only [u₂']
    ring
  have hv₂ (x) : HasDerivAt v₂ (v₂' x) x := (hasDerivAt_mul_const θ).cos
  convert_to (∫ (x : ℝ) in (-1)..1, u₁ x * v₁' x) * θ = _ using 1
  · simp_rw [u₁, v₁', ← intervalIntegral.integral_mul_const, sq θ, mul_assoc]
  rw [integral_mul_deriv_eq_deriv_mul (fun x _ => hu₁ x) (fun x _ => hv₁ x)
    (hu₁d.intervalIntegrable _ _) (hv₁d.intervalIntegrable _ _), hu₁_eval_one, hu₁_eval_neg_one,
    zero_mul, zero_mul, sub_zero, zero_sub, ← integral_neg, ← integral_mul_const]
  convert_to ((-2 : ℝ) * (n + 1)) * ∫ (x : ℝ) in (-1)..1, (u₂ x * v₂' x) = _ using 1
  · rw [← integral_const_mul]
    congr 1 with x
    dsimp [u₁', v₁, u₂, v₂']
    ring
  rw [integral_mul_deriv_eq_deriv_mul (fun x _ => hu₂ x) (fun x _ => hv₂ x)
    (hu₂d.intervalIntegrable _ _)
    (hv₂d.intervalIntegrable _ _), mul_sub, t, neg_mul, neg_mul, neg_mul, sub_neg_eq_add]
  have (x) : u₂' x = (2 * n + 1) * f x ^ n - 2 * n * f x ^ (n - 1) := by
    cases' n with n
    · simp [u₂']
    simp only [u₂', pow_succ _ n, f, Nat.succ_sub_one, Nat.cast_succ]
    ring
  simp_rw [this, sub_mul, mul_assoc _ _ (v₂ _)]
  have : Continuous v₂ := by fun_prop
  rw [mul_mul_mul_comm, integral_sub, mul_sub, add_sub_assoc]
  · congr 1
    simp_rw [integral_const_mul]
    simp only [I, f, v₂]
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

private lemma recursion (n : ℕ) :
    I (n + 2) θ * θ ^ 2 =
      2 * (n + 2) * (2 * n + 3) * I (n + 1) θ - 4 * (n + 2) * (n + 1) * I n θ := by
  rw [recursion' (n + 1), Nat.cast_add_one, zero_pow (Nat.succ_ne_zero _)]
  simp
  ring_nf

private lemma I_one : I 1 θ * θ ^ 3 = 4 * sin θ - 4 * θ * cos θ := by
  rw [_root_.pow_succ, ← mul_assoc, recursion' 0, Nat.cast_zero, mul_zero, mul_zero, zero_mul,
    sub_zero, zero_add, mul_one, mul_one, add_mul, mul_assoc, mul_assoc, I_zero]
  ring

private def sinPoly : ℕ → ℤ[X]
  | 0 => C 2
  | 1 => C 4
  | (n+2) => ((2 : ℤ) * (2 * n + 3)) • sinPoly (n + 1) + monomial 2 (-4) * sinPoly n

private def cosPoly : ℕ → ℤ[X]
  | 0 => 0
  | 1 => monomial 1 (-4)
  | (n+2) => ((2 : ℤ) * (2 * n + 3)) • cosPoly (n + 1) + monomial 2 (-4) * cosPoly n

private lemma sinPoly_natDegree_le : ∀ n : ℕ, (sinPoly n).natDegree ≤ n
  | 0 => by simp [sinPoly]
  | 1 => by simp only [natDegree_C, mul_one, zero_le', sinPoly]
  | (n+2) => by
      rw [sinPoly]
      refine natDegree_add_le_of_degree_le ((natDegree_smul_le _ _).trans ?_) ?_
      · exact (sinPoly_natDegree_le (n + 1)).trans (by simp)
      refine natDegree_mul_le.trans ?_
      simpa [add_comm 2] using sinPoly_natDegree_le n

private lemma cosPoly_natDegree_le : ∀ n : ℕ, (cosPoly n).natDegree ≤ n
  | 0 => by simp [cosPoly]
  | 1 => (natDegree_monomial_le _).trans (by simp)
  | (n+2) => by
      rw [cosPoly]
      refine natDegree_add_le_of_degree_le ((natDegree_smul_le _ _).trans ?_) ?_
      · exact (cosPoly_natDegree_le (n + 1)).trans (by simp)
      refine natDegree_mul_le.trans ?_
      simp only [Int.reduceNeg, map_neg, natDegree_neg, natDegree_monomial, OfNat.ofNat_ne_zero,
        ↓reduceIte]
      linarith [cosPoly_natDegree_le n]

private lemma sinPoly_add_cosPoly_eval (θ : ℝ) :
    ∀ n : ℕ,
      I n θ * θ ^ (2 * n + 1) = n ! * ((sinPoly n).eval₂ (Int.castRingHom _) θ * sin θ +
        (cosPoly n).eval₂ (Int.castRingHom _) θ * cos θ)
  | 0 => by simp [sinPoly, cosPoly, I_zero, eval₂_C]
  | 1 => by
      simp only [I_one, cosPoly, sinPoly, Nat.factorial_one, Nat.cast_one, mul_one, eval₂_C,
        eval₂_monomial, Nat.reduceAdd]
      simp [sub_eq_add_neg]
  | (n+2) => by
      rw [Nat.mul_succ, add_right_comm, add_comm (_ + _), pow_add, ← mul_assoc, recursion, sub_mul,
        mul_assoc, mul_assoc _ (I n θ), sinPoly_add_cosPoly_eval, mul_add_one 2, add_right_comm,
        pow_add, ← mul_assoc (I n θ), sinPoly_add_cosPoly_eval, sinPoly, cosPoly, eval₂_add,
        eval₂_add, eval₂_smul, eval₂_smul, eval₂_mul, eval₂_mul, eval₂_monomial]
      simp only [map_mul, map_ofNat, map_add, map_natCast, Int.reduceNeg, map_neg, neg_mul,
        Nat.factorial_succ]
      push_cast
      ring

open BigOperators

private lemma is_integer {p : ℤ[X]} (a b : ℤ) {k : ℕ} (hp : p.natDegree ≤ k) :
    ∃ z : ℤ, p.eval₂ (Int.castRingHom ℝ) (a / b) * b ^ k = z := by
  rcases eq_or_ne b 0 with rfl | hb
  · rcases k.eq_zero_or_pos with rfl | hk
    · exact ⟨p.coeff 0, by simp⟩
    exact ⟨0, by simp [hk.ne']⟩
  refine ⟨∑ i in p.support, p.coeff i * a ^ i * b ^ (k - i), ?_⟩
  conv => lhs; rw [← sum_monomial_eq p]
  rw [eval₂_sum, sum, Finset.sum_mul, Int.cast_sum]
  simp only [eval₂_monomial, eq_intCast, div_pow, Int.cast_mul, Int.cast_pow]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have ik := (le_natDegree_of_mem_supp i hi).trans hp
  rw [mul_assoc, div_mul_comm, ← Int.cast_pow, ← Int.cast_pow, ← Int.cast_pow,
    ← pow_sub_mul_pow b ik, ← Int.cast_div_charZero, Int.mul_ediv_cancel _ (pow_ne_zero _ hb),
    ← mul_assoc, mul_right_comm, ← Int.cast_pow]
  exact dvd_mul_left _ _

open Filter

private lemma I_pos : 0 < I n (π / 2) := by
  refine integral_pos (by norm_num) (Continuous.continuousOn (by continuity)) ?_ ⟨0, by simp⟩
  refine fun x hx => mul_nonneg (pow_nonneg ?_ _) ?_
  · rw [sub_nonneg, sq_le_one_iff_abs_le_one, abs_le]
    exact ⟨hx.1.le, hx.2⟩
  refine cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_ <;>
  nlinarith [hx.1, hx.2, pi_pos]

private lemma I_le (n : ℕ) : I n (π / 2) ≤ 2 := by
  rw [← norm_of_nonneg I_pos.le]
  refine (norm_integral_le_of_norm_le_const ?_).trans (show (1 : ℝ) * _ ≤ _ by norm_num)
  intros x hx
  simp only [uIoc_of_le, neg_le_self_iff, zero_le_one, mem_Ioc] at hx
  rw [norm_eq_abs, abs_mul, abs_pow]
  refine mul_le_one (pow_le_one _ (abs_nonneg _) ?_) (abs_nonneg _) (abs_cos_le_one _)
  rw [abs_le]
  constructor <;> nlinarith

private lemma my_tendsto_pow_div_factorial_at_top (a : ℝ) :
    Tendsto (fun n => (a : ℝ) ^ (2 * n + 1) / n !) atTop (nhds 0) := by
  rw [← mul_zero a]
  refine ((tendsto_pow_div_factorial_atTop (a ^ 2)).const_mul a).congr (fun x => ?_)
  rw [← pow_mul, mul_div_assoc', _root_.pow_succ']

private lemma not_irrational.exists_rep {x : ℝ} :
    ¬Irrational x → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ x = a / b := by
  rw [Irrational, not_not, mem_range]
  rintro ⟨q, rfl⟩
  exact ⟨q.num, q.den, q.pos, by exact_mod_cast (Rat.num_div_den _).symm⟩

@[simp] theorem irrational_pi : Irrational π := by
  apply Irrational.of_div_nat 2
  rw [Nat.cast_two]
  by_contra h'
  obtain ⟨a, b, hb, h⟩ := not_irrational.exists_rep h'
  have ha : (0 : ℝ) < a := by
    have : 0 < (a : ℝ) / b := h ▸ pi_div_two_pos
    rwa [lt_div_iff (by positivity), zero_mul] at this
  have k (n : ℕ) : 0 < (a : ℝ) ^ (2 * n + 1) / n ! := by positivity
  have j : ∀ᶠ n : ℕ in atTop, (a : ℝ) ^ (2 * n + 1) / n ! * I n (π / 2) < 1 := by
    have := eventually_lt_of_tendsto_lt (show (0 : ℝ) < 1 / 2 by norm_num)
              (my_tendsto_pow_div_factorial_at_top a)
    filter_upwards [this] with n hn
    rw [lt_div_iff (zero_lt_two : (0 : ℝ) < 2)] at hn
    exact hn.trans_le' (mul_le_mul_of_nonneg_left (I_le _) (by positivity))
  obtain ⟨n, hn⟩ := j.exists
  have hn' : 0 < a ^ (2 * n + 1) / n ! * I n (π / 2) := mul_pos (k _) I_pos
  obtain ⟨z, hz⟩ : ∃ z : ℤ, (sinPoly n).eval₂ (Int.castRingHom ℝ) (a / b) * b ^ (2 * n + 1) = z :=
    is_integer a b ((sinPoly_natDegree_le _).trans (by linarith))
  have e := sinPoly_add_cosPoly_eval (π / 2) n
  rw [cos_pi_div_two, sin_pi_div_two, mul_zero, mul_one, add_zero] at e
  have : a ^ (2 * n + 1) / n ! * I n (π / 2) =
      eval₂ (Int.castRingHom ℝ) (π / 2) (sinPoly n) * b ^ (2 * n + 1) := by
    nth_rw 2 [h] at e
    field_simp at e ⊢
    linear_combination e
  have : (0 : ℝ) < z ∧ (z : ℝ) < 1 := by simp [← hz, ← h, ← this, hn', hn]
  norm_cast at this
  omega

end
