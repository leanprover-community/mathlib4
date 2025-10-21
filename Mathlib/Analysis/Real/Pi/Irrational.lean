/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.NumberTheory.Real.Irrational

/-!
# `Real.pi` is irrational

The main result of this file is `irrational_pi`.

The proof is adapted from https://en.wikipedia.org/wiki/Proof_that_%CF%80_is_irrational#Cartwright's_proof.

The proof idea is as follows.
* Define a sequence of integrals `I n θ = ∫ x in (-1)..1, (1 - x ^ 2) ^ n * cos (x * θ)`.
* Give a recursion formula for `I (n + 2) θ * θ ^ 2` in terms of `I n θ` and `I (n + 1) θ`.
  Note we do not find it helpful to define `J` as in the above proof, and instead work directly
  with `I`.
* Define polynomials with integer coefficients `sinPoly n` and `cosPoly n` such that
  `I n θ * θ ^ (2 * n + 1) = n ! * (sinPoly n θ * sin θ + cosPoly n θ * cos θ)`.
  Note that in the informal proof, these polynomials are not defined explicitly, but we find it
  useful to define them by recursion.
* Show that both these polynomials have degree bounded by `n`.
* Show that `0 < I n (π / 2) ≤ 2` for all `n`.
* Now we can finish: if `π / 2` is rational, write it as `a / b` with `a, b > 0`. Then
  `b ^ (2 * n + 1) * sinPoly n (a / b)` is a positive integer by the degree bound. But it is equal
  to `a ^ (2 * n + 1) / n ! * I n (π / 2) ≤ 2 * a * (2 * n + 1) / n !`, which converges to 0 as
  `n → ∞`.

-/

noncomputable section

open intervalIntegral MeasureTheory.MeasureSpace Set Polynomial Real
open scoped Nat

/-- The sequence of integrals used for Cartwright's proof of irrationality of `π`. -/
private def I (n : ℕ) (θ : ℝ) : ℝ := ∫ x in (-1)..1, (1 - x ^ 2) ^ n * cos (x * θ)

variable {n : ℕ} {θ : ℝ}

private lemma I_zero : I 0 θ * θ = 2 * sin θ := by
  rw [mul_comm, I]
  simp [mul_integral_comp_mul_right, two_mul]

/--
Auxiliary for the proof that `π` is irrational.
While it is most natural to give the recursive formula for `I (n + 2) θ`, as well as give the second
base case of `I 1 θ`, it is in fact more convenient to give the recursive formula for `I (n + 1) θ`
in terms of `I n θ` and `I (n - 1) θ` (note the natural subtraction!).
Despite the usually inconvenient subtraction, this in fact allows deducing both of the above facts
with significantly fewer analysis computations.
In addition, note the `0 ^ n` on the right-hand side - this is intentional, and again allows
combining the proof of the "usual" recursion formula and the base case `I 1 θ`.
-/
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
  have t : u₂ 1 * v₂ 1 - u₂ (-1) * v₂ (-1) = 2 * (0 ^ n * cos θ) := by simp [u₂, v₂, f, ← two_mul]
  have hf (x) : HasDerivAt f (- 2 * x) x := by
    convert (hasDerivAt_pow 2 x).const_sub 1 using 1
    simp
  have hu₁ (x) : HasDerivAt u₁ (u₁' x) x := by
    convert (hf x).pow _ using 1
    simp only [Nat.add_succ_sub_one, u₁', Nat.cast_add_one]
    ring
  have hv₁ (x) : HasDerivAt v₁ (v₁' x) x := (hasDerivAt_mul_const θ).sin
  have hu₂ (x) : HasDerivAt u₂ (u₂' x) x := by
    convert (hasDerivAt_id' x).fun_mul ((hf x).fun_pow _) using 1
    simp only [u₂']
    ring
  have hv₂ (x) : HasDerivAt v₂ (v₂' x) x := (hasDerivAt_mul_const θ).cos
  convert_to (∫ (x : ℝ) in (-1)..1, u₁ x * v₁' x) * θ = _ using 1
  · simp_rw [u₁, v₁', f, ← intervalIntegral.integral_mul_const, sq θ, mul_assoc]
  rw [integral_mul_deriv_eq_deriv_mul (fun x _ => hu₁ x) (fun x _ => hv₁ x)
    (hu₁d.intervalIntegrable _ _) (hv₁d.intervalIntegrable _ _), hu₁_eval_one, hu₁_eval_neg_one,
    zero_mul, zero_mul, sub_zero, zero_sub, ← integral_neg, ← integral_mul_const]
  convert_to ((-2 : ℝ) * (n + 1)) * ∫ (x : ℝ) in (-1)..1, (u₂ x * v₂' x) = _ using 1
  · rw [← integral_const_mul]
    congr 1 with x
    dsimp [u₁', v₁, u₂, v₂']
    ring
  rw [integral_mul_deriv_eq_deriv_mul (fun x _ => hu₂ x) (fun x _ => hv₂ x)
    (hu₂d.intervalIntegrable _ _) (hv₂d.intervalIntegrable _ _),
    mul_sub, t, neg_mul, neg_mul, neg_mul, sub_neg_eq_add]
  have (x : _) : u₂' x = (2 * n + 1) * f x ^ n - 2 * n * f x ^ (n - 1) := by
    cases n with
    | zero => simp [u₂']
    | succ n => ring!
  simp_rw [this, sub_mul, mul_assoc _ _ (v₂ _)]
  have : Continuous v₂ := by fun_prop
  rw [mul_mul_mul_comm, integral_sub, mul_sub, add_sub_assoc]
  · congr 1
    simp_rw [integral_const_mul]
    ring!
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

/--
Auxiliary for the proof that `π` is irrational.
The recursive formula for `I (n + 2) θ * θ ^ 2` in terms of `I n θ` and `I (n + 1) θ`.
-/
private lemma recursion (n : ℕ) :
    I (n + 2) θ * θ ^ 2 =
      2 * (n + 2) * (2 * n + 3) * I (n + 1) θ - 4 * (n + 2) * (n + 1) * I n θ := by
  rw [recursion' (n + 1)]
  push_cast
  ring

/--
Auxiliary for the proof that `π` is irrational.
The second base case for the induction on `n`, giving an explicit formula for `I 1 θ`.
-/
private lemma I_one : I 1 θ * θ ^ 3 = 4 * sin θ - 4 * θ * cos θ := by
  rw [_root_.pow_succ, ← mul_assoc, recursion' 0, sub_mul, add_mul, mul_assoc _ (I 0 θ), I_zero]
  ring

/--
Auxiliary for the proof that `π` is irrational.
The first of the two integer-coefficient polynomials that describe the behaviour of the
sequence of integrals `I`.
While not given in the informal proof, these are easy to deduce from the recursion formulae.
-/
private def sinPoly : ℕ → ℤ[X]
  | 0 => C 2
  | 1 => C 4
  | (n+2) => ((2 : ℤ) * (2 * n + 3)) • sinPoly (n + 1) + monomial 2 (-4) * sinPoly n

/--
Auxiliary for the proof that `π` is irrational.
The second of the two integer-coefficient polynomials that describe the behaviour of the
sequence of integrals `I`.
While not given in the informal proof, these are easy to deduce from the recursion formulae.
-/
private def cosPoly : ℕ → ℤ[X]
  | 0 => 0
  | 1 => monomial 1 (-4)
  | (n+2) => ((2 : ℤ) * (2 * n + 3)) • cosPoly (n + 1) + monomial 2 (-4) * cosPoly n

/--
Auxiliary for the proof that `π` is irrational.
Prove a degree bound for `sinPoly n` by induction. Note this is where we find the value in an
explicit description of `sinPoly`.
-/
private lemma sinPoly_natDegree_le : ∀ n : ℕ, (sinPoly n).natDegree ≤ n
  | 0 => by simp [sinPoly]
  | 1 => by simp only [natDegree_C, zero_le', sinPoly]
  | n + 2 => by
      rw [sinPoly]
      refine natDegree_add_le_of_degree_le ((natDegree_smul_le _ _).trans ?_) ?_
      · exact (sinPoly_natDegree_le (n + 1)).trans (by simp)
      refine natDegree_mul_le.trans ?_
      simpa [add_comm 2] using sinPoly_natDegree_le n

/--
Auxiliary for the proof that `π` is irrational.
Prove a degree bound for `cosPoly n` by induction. Note this is where we find the value in an
explicit description of `cosPoly`.
-/
private lemma cosPoly_natDegree_le : ∀ n : ℕ, (cosPoly n).natDegree ≤ n
  | 0 => by simp [cosPoly]
  | 1 => (natDegree_monomial_le _).trans (by simp)
  | n + 2 => by
      rw [cosPoly]
      refine natDegree_add_le_of_degree_le ((natDegree_smul_le _ _).trans ?_) ?_
      · exact (cosPoly_natDegree_le (n + 1)).trans (by simp)
      exact natDegree_mul_le.trans (by simp [add_comm 2, cosPoly_natDegree_le n])

/--
Auxiliary for the proof that `π` is irrational.
The key lemma: the sequence of integrals `I` can be written as a linear combination of `sin` and
`cos`, with coefficients given by the polynomials `sinPoly` and `cosPoly`.
-/
private lemma sinPoly_add_cosPoly_eval (θ : ℝ) :
    ∀ n : ℕ,
      I n θ * θ ^ (2 * n + 1) = n ! * ((sinPoly n).eval₂ (Int.castRingHom _) θ * sin θ +
        (cosPoly n).eval₂ (Int.castRingHom _) θ * cos θ)
  | 0 => by simp [sinPoly, cosPoly, I_zero]
  | 1 => by simp [I_one, sinPoly, cosPoly, sub_eq_add_neg]
  | n + 2 => by
      calc I (n + 2) θ * θ ^ (2 * (n + 2) + 1) = I (n + 2) θ * θ ^ 2 * θ ^ (2 * n + 3) := by ring
        _ = 2 * (n + 2) * (2 * n + 3) * (I (n + 1) θ * θ ^ (2 * (n + 1) + 1)) -
            4 * (n + 2) * (n + 1) * θ ^ 2 * (I n θ * θ ^ (2 * n + 1)) := by rw [recursion]; ring
        _ = _ := by simp [sinPoly_add_cosPoly_eval, sinPoly, cosPoly, Nat.factorial_succ]; ring

/--
Auxiliary for the proof that `π` is irrational.
For a polynomial `p` with natural degree `≤ k` and integer coefficients, evaluating `p` at a
rational `a / b` gives a rational of the form `z / b ^ k`.
TODO: should this be moved elsewhere? It uses none of the pi-specific definitions.
-/
private lemma is_integer {p : ℤ[X]} (a b : ℤ) {k : ℕ} (hp : p.natDegree ≤ k) :
    ∃ z : ℤ, p.eval₂ (Int.castRingHom ℝ) (a / b) * b ^ k = z := by
  rcases eq_or_ne b 0 with rfl | hb
  · rcases k.eq_zero_or_pos with rfl | hk
    · exact ⟨p.coeff 0, by simp⟩
    exact ⟨0, by simp [hk.ne']⟩
  refine ⟨∑ i ∈ p.support, p.coeff i * a ^ i * b ^ (k - i), ?_⟩
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

/--
Auxiliary for the proof that `π` is irrational.
The integrand in the definition of `I` is nonnegative and takes a positive value at least one point,
so the integral is positive.
-/
private lemma I_pos : 0 < I n (π / 2) := by
  refine integral_pos (by simp) (by fun_prop) ?_ ⟨0, by simp⟩
  refine fun x hx => mul_nonneg (pow_nonneg ?_ _) ?_
  · rw [sub_nonneg, sq_le_one_iff_abs_le_one, abs_le]
    exact ⟨hx.1.le, hx.2⟩
  refine cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_ <;>
  nlinarith [hx.1, hx.2, pi_pos]

/--
Auxiliary for the proof that `π` is irrational.
The integrand in the definition of `I` is bounded by 1 and the interval has length 2, so the
integral is bounded above by `2`.
-/
private lemma I_le (n : ℕ) : I n (π / 2) ≤ 2 := by
  rw [← norm_of_nonneg I_pos.le]
  refine (norm_integral_le_of_norm_le_const ?_).trans (show (1 : ℝ) * _ ≤ _ by norm_num)
  intro x hx
  simp only [uIoc_of_le, neg_le_self_iff, zero_le_one, mem_Ioc] at hx
  rw [norm_eq_abs, abs_mul, abs_pow]
  refine mul_le_one₀ (pow_le_one₀ (abs_nonneg _) ?_) (abs_nonneg _) (abs_cos_le_one _)
  rw [abs_le]
  constructor <;> nlinarith

/--
Auxiliary for the proof that `π` is irrational.
For any real `a`, we have that `a ^ (2n+1) / n!` tends to `0` as `n → ∞`.  This is just a
reformulation of tendsto_pow_div_factorial_atTop, which asserts the same for `a ^ n / n!`
-/
private lemma tendsto_pow_div_factorial_at_top_aux (a : ℝ) :
    Tendsto (fun n => (a : ℝ) ^ (2 * n + 1) / n !) atTop (nhds 0) := by
  rw [← mul_zero a]
  refine ((FloorSemiring.tendsto_pow_div_factorial_atTop (a ^ 2)).const_mul a).congr (fun x => ?_)
  rw [← pow_mul, mul_div_assoc', _root_.pow_succ']

/-- If `x` is rational, it can be written as `a / b` with `a : ℤ` and `b : ℕ` satisfying `b > 0`. -/
private lemma not_irrational_exists_rep {x : ℝ} :
    ¬Irrational x → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ x = a / b := by
  rw [Irrational, not_not, mem_range]
  rintro ⟨q, rfl⟩
  exact ⟨q.num, q.den, q.pos, by exact_mod_cast (Rat.num_div_den _).symm⟩

@[simp] theorem irrational_pi : Irrational π := by
  apply Irrational.of_div_natCast 2
  rw [Nat.cast_two]
  by_contra h'
  obtain ⟨a, b, hb, h⟩ := not_irrational_exists_rep h'
  have ha : (0 : ℝ) < a := by
    have : 0 < (a : ℝ) / b := h ▸ pi_div_two_pos
    rwa [lt_div_iff₀ (by positivity), zero_mul] at this
  have k (n : ℕ) : 0 < (a : ℝ) ^ (2 * n + 1) / n ! := by positivity
  have j : ∀ᶠ n : ℕ in atTop, (a : ℝ) ^ (2 * n + 1) / n ! * I n (π / 2) < 1 := by
    have := (tendsto_pow_div_factorial_at_top_aux a).eventually_lt_const
      (show (0 : ℝ) < 1 / 2 by simp)
    filter_upwards [this] with n hn
    rw [lt_div_iff₀ (zero_lt_two : (0 : ℝ) < 2)] at hn
    exact hn.trans_le' (mul_le_mul_of_nonneg_left (I_le _) (by positivity))
  obtain ⟨n, hn⟩ := j.exists
  have hn' : 0 < a ^ (2 * n + 1) / n ! * I n (π / 2) := mul_pos (k _) I_pos
  obtain ⟨z, hz⟩ : ∃ z : ℤ, (sinPoly n).eval₂ (Int.castRingHom ℝ) (a / b) * b ^ (2 * n + 1) = z :=
    is_integer a b ((sinPoly_natDegree_le _).trans (by cutsat))
  have e := sinPoly_add_cosPoly_eval (π / 2) n
  rw [cos_pi_div_two, sin_pi_div_two, mul_zero, mul_one, add_zero] at e
  have : a ^ (2 * n + 1) / n ! * I n (π / 2) =
      eval₂ (Int.castRingHom ℝ) (π / 2) (sinPoly n) * b ^ (2 * n + 1) := by
    nth_rw 2 [h] at e
    simp [field, div_pow] at e ⊢
    linear_combination e
  have : (0 : ℝ) < z ∧ (z : ℝ) < 1 := by simp [← hz, ← h, ← this, hn', hn]
  norm_cast at this
  cutsat

end
