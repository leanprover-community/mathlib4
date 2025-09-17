/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Bernstein polynomials

The definition of the Bernstein polynomials
```
bernsteinPolynomial (R : Type*) [CommRing R] (n ν : ℕ) : R[X] :=
(choose n ν) * X^ν * (1 - X)^(n - ν)
```
and the fact that for `ν : Fin (n+1)` these are linearly independent over `ℚ`.

We prove the basic identities
* `(Finset.range (n + 1)).sum (fun ν ↦ bernsteinPolynomial R n ν) = 1`
* `(Finset.range (n + 1)).sum (fun ν ↦ ν • bernsteinPolynomial R n ν) = n • X`
* `(Finset.range (n + 1)).sum (fun ν ↦ (ν * (ν-1)) • bernsteinPolynomial R n ν) = (n * (n-1)) • X^2`

## Notes

See also `Mathlib/Analysis/SpecialFunctions/Bernstein.lean`, which defines the Bernstein
approximations of a continuous function `f : C([0,1], ℝ)`, and shows that these converge uniformly
to `f`.
-/


noncomputable section

open Nat (choose)

open Polynomial (X)

open scoped Polynomial

variable (R : Type*) [CommRing R]

/-- `bernsteinPolynomial R n ν` is `(choose n ν) * X^ν * (1 - X)^(n - ν)`.

Although the coefficients are integers, it is convenient to work over an arbitrary commutative ring.
-/
def bernsteinPolynomial (n ν : ℕ) : R[X] :=
  (choose n ν : R[X]) * X ^ ν * (1 - X) ^ (n - ν)

example : bernsteinPolynomial ℤ 3 2 = 3 * X ^ 2 - 3 * X ^ 3 := by
  norm_num [bernsteinPolynomial, choose]
  ring

namespace bernsteinPolynomial

theorem eq_zero_of_lt {n ν : ℕ} (h : n < ν) : bernsteinPolynomial R n ν = 0 := by
  simp [bernsteinPolynomial, Nat.choose_eq_zero_of_lt h]

section

variable {R} {S : Type*} [CommRing S]

@[simp]
theorem map (f : R →+* S) (n ν : ℕ) :
    (bernsteinPolynomial R n ν).map f = bernsteinPolynomial S n ν := by simp [bernsteinPolynomial]

end

theorem flip (n ν : ℕ) (h : ν ≤ n) :
    (bernsteinPolynomial R n ν).comp (1 - X) = bernsteinPolynomial R n (n - ν) := by
  simp [bernsteinPolynomial, h, tsub_tsub_assoc, mul_right_comm]

theorem flip' (n ν : ℕ) (h : ν ≤ n) :
    bernsteinPolynomial R n ν = (bernsteinPolynomial R n (n - ν)).comp (1 - X) := by
  simp [← flip _ _ _ h, Polynomial.comp_assoc]

theorem eval_at_0 (n ν : ℕ) : (bernsteinPolynomial R n ν).eval 0 = if ν = 0 then 1 else 0 := by
  rw [bernsteinPolynomial]
  split_ifs with h
  · subst h; simp
  · simp [zero_pow h]

theorem eval_at_1 (n ν : ℕ) : (bernsteinPolynomial R n ν).eval 1 = if ν = n then 1 else 0 := by
  rw [bernsteinPolynomial]
  split_ifs with h
  · subst h; simp
  · obtain hνn | hnν := Ne.lt_or_gt h
    · simp [zero_pow <| Nat.sub_ne_zero_of_lt hνn]
    · simp [Nat.choose_eq_zero_of_lt hnν]

theorem derivative_succ_aux (n ν : ℕ) :
    Polynomial.derivative (bernsteinPolynomial R (n + 1) (ν + 1)) =
      (n + 1) * (bernsteinPolynomial R n ν - bernsteinPolynomial R n (ν + 1)) := by
  rw [bernsteinPolynomial]
  suffices ((n + 1).choose (ν + 1) : R[X]) * ((↑(ν + 1 : ℕ) : R[X]) * X ^ ν) * (1 - X) ^ (n - ν) -
      ((n + 1).choose (ν + 1) : R[X]) * X ^ (ν + 1) * ((↑(n - ν) : R[X]) * (1 - X) ^ (n - ν - 1)) =
      (↑(n + 1) : R[X]) * ((n.choose ν : R[X]) * X ^ ν * (1 - X) ^ (n - ν) -
        (n.choose (ν + 1) : R[X]) * X ^ (ν + 1) * (1 - X) ^ (n - (ν + 1))) by
    simpa [Polynomial.derivative_pow, ← sub_eq_add_neg, Nat.succ_sub_succ_eq_sub,
      Polynomial.derivative_mul, Polynomial.derivative_natCast, zero_mul,
      Nat.cast_add, algebraMap.coe_one, Polynomial.derivative_X, mul_one, zero_add,
      Polynomial.derivative_sub, Polynomial.derivative_one, zero_sub, mul_neg, Nat.sub_zero,
      bernsteinPolynomial, map_add, map_natCast, Nat.cast_one]
  conv_rhs => rw [mul_sub]
  -- We'll prove the two terms match up separately.
  refine congr (congr_arg Sub.sub ?_) ?_
  · simp only [← mul_assoc]
    apply congr (congr_arg (· * ·) (congr (congr_arg (· * ·) _) rfl)) rfl
    -- Now it's just about binomial coefficients
    exact mod_cast congr_arg (fun m : ℕ => (m : R[X])) (Nat.succ_mul_choose_eq n ν).symm
  · rw [← tsub_add_eq_tsub_tsub, ← mul_assoc, ← mul_assoc]; congr 1
    rw [mul_comm, ← mul_assoc, ← mul_assoc]; congr 1
    norm_cast
    congr 1
    convert (Nat.choose_mul_succ_eq n (ν + 1)).symm using 1
    · convert mul_comm _ _ using 2
      simp
    · apply mul_comm

theorem derivative_succ (n ν : ℕ) : Polynomial.derivative (bernsteinPolynomial R n (ν + 1)) =
    n * (bernsteinPolynomial R (n - 1) ν - bernsteinPolynomial R (n - 1) (ν + 1)) := by
  cases n
  · simp [bernsteinPolynomial]
  · rw [Nat.cast_succ]; apply derivative_succ_aux

theorem derivative_zero (n : ℕ) :
    Polynomial.derivative (bernsteinPolynomial R n 0) = -n * bernsteinPolynomial R (n - 1) 0 := by
  simp [bernsteinPolynomial, Polynomial.derivative_pow]

theorem iterate_derivative_at_0_eq_zero_of_lt (n : ℕ) {ν k : ℕ} :
    k < ν → (Polynomial.derivative^[k] (bernsteinPolynomial R n ν)).eval 0 = 0 := by
  rcases ν with - | ν
  · rintro ⟨⟩
  · rw [Nat.lt_succ_iff]
    induction k generalizing n ν with
    | zero => simp [eval_at_0]
    | succ k ih =>
      simp only [derivative_succ, Function.comp_apply,
        Function.iterate_succ, Polynomial.iterate_derivative_sub,
        Polynomial.iterate_derivative_natCast_mul, Polynomial.eval_mul, Polynomial.eval_natCast,
        Polynomial.eval_sub]
      intro h
      apply mul_eq_zero_of_right
      rw [ih _ _ (Nat.le_of_succ_le h), sub_zero]
      convert ih _ _ (Nat.pred_le_pred h)
      exact (Nat.succ_pred_eq_of_pos (k.succ_pos.trans_le h)).symm

@[simp]
theorem iterate_derivative_succ_at_0_eq_zero (n ν : ℕ) :
    (Polynomial.derivative^[ν] (bernsteinPolynomial R n (ν + 1))).eval 0 = 0 :=
  iterate_derivative_at_0_eq_zero_of_lt R n (lt_add_one ν)

open Polynomial

@[simp]
theorem iterate_derivative_at_0 (n ν : ℕ) :
    (Polynomial.derivative^[ν] (bernsteinPolynomial R n ν)).eval 0 =
      (ascPochhammer R ν).eval ((n - (ν - 1) : ℕ) : R) := by
  by_cases h : ν ≤ n
  · induction ν generalizing n with
    | zero => simp [eval_at_0]
    | succ ν ih =>
      have h' : ν ≤ n - 1 := le_tsub_of_add_le_right h
      simp only [derivative_succ, ih (n - 1) h', iterate_derivative_succ_at_0_eq_zero,
        Nat.succ_sub_succ_eq_sub, tsub_zero, sub_zero, iterate_derivative_sub,
        iterate_derivative_natCast_mul, eval_one, eval_mul, eval_add, eval_sub, eval_X, eval_comp,
        eval_natCast, Function.comp_apply, Function.iterate_succ, ascPochhammer_succ_left]
      obtain rfl | h'' := ν.eq_zero_or_pos
      · simp
      · have : n - 1 - (ν - 1) = n - ν := by omega
        rw [this, ascPochhammer_eval_succ]
        rw_mod_cast [tsub_add_cancel_of_le (h'.trans n.pred_le)]
  · simp only [not_le] at h
    rw [tsub_eq_zero_iff_le.mpr (Nat.le_sub_one_of_lt h), eq_zero_of_lt R h]
    simp [pos_iff_ne_zero.mp (pos_of_gt h)]

theorem iterate_derivative_at_0_ne_zero [CharZero R] (n ν : ℕ) (h : ν ≤ n) :
    (Polynomial.derivative^[ν] (bernsteinPolynomial R n ν)).eval 0 ≠ 0 := by
  simp only [bernsteinPolynomial.iterate_derivative_at_0, Ne]
  simp only [← ascPochhammer_eval_cast]
  norm_cast
  apply ne_of_gt
  obtain rfl | h' := Nat.eq_zero_or_pos ν
  · simp
  · rw [← Nat.succ_pred_eq_of_pos h'] at h
    exact ascPochhammer_pos _ _ (tsub_pos_of_lt (Nat.lt_of_succ_le h))

/-!
Rather than redoing the work of evaluating the derivatives at 1,
we use the symmetry of the Bernstein polynomials.
-/


theorem iterate_derivative_at_1_eq_zero_of_lt (n : ℕ) {ν k : ℕ} :
    k < n - ν → (Polynomial.derivative^[k] (bernsteinPolynomial R n ν)).eval 1 = 0 := by
  intro w
  rw [flip' _ _ _ (tsub_pos_iff_lt.mp (pos_of_gt w)).le]
  simp [Polynomial.eval_comp, iterate_derivative_at_0_eq_zero_of_lt R n w]

@[simp]
theorem iterate_derivative_at_1 (n ν : ℕ) (h : ν ≤ n) :
    (Polynomial.derivative^[n - ν] (bernsteinPolynomial R n ν)).eval 1 =
      (-1) ^ (n - ν) * (ascPochhammer R (n - ν)).eval (ν + 1 : R) := by
  rw [flip' _ _ _ h]
  simp only [iterate_derivative_comp_one_sub_X, eval_mul, eval_pow, eval_neg, eval_one, eval_comp,
    eval_sub, eval_X, sub_self, iterate_derivative_at_0]
  obtain rfl | h' := h.eq_or_lt
  · simp
  · norm_cast
    congr
    omega

theorem iterate_derivative_at_1_ne_zero [CharZero R] (n ν : ℕ) (h : ν ≤ n) :
    (Polynomial.derivative^[n - ν] (bernsteinPolynomial R n ν)).eval 1 ≠ 0 := by
  rw [bernsteinPolynomial.iterate_derivative_at_1 _ _ _ h, Ne, neg_one_pow_mul_eq_zero_iff, ←
    Nat.cast_succ, ← ascPochhammer_eval_cast, ← Nat.cast_zero, Nat.cast_inj]
  exact (ascPochhammer_pos _ _ (Nat.succ_pos ν)).ne'

open Submodule

theorem linearIndependent_aux (n k : ℕ) (h : k ≤ n + 1) :
    LinearIndependent ℚ fun ν : Fin k => bernsteinPolynomial ℚ n ν := by
  induction k with
  | zero => apply linearIndependent_empty_type
  | succ k ih =>
    apply linearIndependent_fin_succ'.mpr
    fconstructor
    · exact ih (le_of_lt h)
    · -- The actual work!
      -- We show that the (n-k)-th derivative at 1 doesn't vanish,
      -- but vanishes for everything in the span.
      clear ih
      simp only [add_le_add_iff_right] at h
      simp only [Fin.val_last, Fin.init_def]
      dsimp
      apply notMem_span_of_apply_notMem_span_image (@Polynomial.derivative ℚ _ ^ (n - k))
      -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `span_image` into `span_image _`
      simp only [not_exists, not_and, Submodule.mem_map, Submodule.span_image _]
      intro p m
      apply_fun Polynomial.eval (1 : ℚ)
      simp only [Module.End.pow_apply]
      -- The right-hand side is nonzero,
      -- so it will suffice to show the left-hand side is always zero.
      suffices (Polynomial.derivative^[n - k] p).eval 1 = 0 by
        rw [this]
        exact (iterate_derivative_at_1_ne_zero ℚ n k h).symm
      refine span_induction ?_ ?_ ?_ ?_ m
      · simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
        rintro ⟨a, w⟩; simp only
        rw [iterate_derivative_at_1_eq_zero_of_lt ℚ n ((tsub_lt_tsub_iff_left_of_le h).mpr w)]
      · simp
      · intro x y _ _ hx hy; simp [hx, hy]
      · intro a x _ h; simp [h]

/-- The Bernstein polynomials are linearly independent.

We prove by induction that the collection of `bernsteinPolynomial n ν` for `ν = 0, ..., k`
are linearly independent.
The inductive step relies on the observation that the `(n-k)`-th derivative, evaluated at 1,
annihilates `bernsteinPolynomial n ν` for `ν < k`, but has a nonzero value at `ν = k`.
-/
theorem linearIndependent (n : ℕ) :
    LinearIndependent ℚ fun ν : Fin (n + 1) => bernsteinPolynomial ℚ n ν :=
  linearIndependent_aux n (n + 1) le_rfl

theorem sum (n : ℕ) : (∑ ν ∈ Finset.range (n + 1), bernsteinPolynomial R n ν) = 1 :=
  calc
    (∑ ν ∈ Finset.range (n + 1), bernsteinPolynomial R n ν) = (X + (1 - X)) ^ n := by
      rw [add_pow]
      simp only [bernsteinPolynomial, mul_comm, mul_assoc]
    _ = 1 := by simp

open Polynomial

open MvPolynomial hiding X

theorem sum_smul (n : ℕ) :
    (∑ ν ∈ Finset.range (n + 1), ν • bernsteinPolynomial R n ν) = n • X := by
  -- We calculate the `x`-derivative of `(x+y)^n`, evaluated at `y=(1-x)`,
  -- either directly or by using the binomial theorem.
  -- We'll work in `MvPolynomial Bool R`.
  let x : MvPolynomial Bool R := MvPolynomial.X true
  let y : MvPolynomial Bool R := MvPolynomial.X false
  have pderiv_true_x : pderiv true x = 1 := by rw [pderiv_X]; rfl
  have pderiv_true_y : pderiv true y = 0 := by rw [pderiv_X]; rfl
  let e : Bool → R[X] := fun i => cond i X (1 - X)
  -- Start with `(x+y)^n = (x+y)^n`,
  -- take the `x`-derivative, evaluate at `x=X, y=1-X`, and multiply by `X`:
  trans MvPolynomial.aeval e (pderiv true ((x + y) ^ n)) * X
  -- On the left-hand side we'll use the binomial theorem, then simplify.
  · -- We first prepare a tedious rewrite:
    have w : ∀ k : ℕ, k • bernsteinPolynomial R n k =
        (k : R[X]) * Polynomial.X ^ (k - 1) * (1 - Polynomial.X) ^ (n - k) * (n.choose k : R[X]) *
          Polynomial.X := by
      rintro (_ | k)
      · simp
      · rw [bernsteinPolynomial]
        simp only [← natCast_mul, Nat.add_succ_sub_one, add_zero, pow_succ]
        push_cast
        ring
    rw [add_pow, map_sum (pderiv true), map_sum (MvPolynomial.aeval e), Finset.sum_mul]
    -- Step inside the sum:
    refine Finset.sum_congr rfl fun k _ => (w k).trans ?_
    simp only [x, y, e, pderiv_true_x, pderiv_true_y, Algebra.id.smul_eq_mul, nsmul_eq_mul,
      Bool.cond_true, Bool.cond_false, add_zero, mul_one, mul_zero, smul_zero, MvPolynomial.aeval_X,
      MvPolynomial.pderiv_mul, Derivation.leibniz_pow, Derivation.map_natCast, map_natCast, map_pow,
      map_mul]
  · rw [(pderiv true).leibniz_pow, (pderiv true).map_add, pderiv_true_x, pderiv_true_y]
    simp only [x, y, e, Algebra.id.smul_eq_mul, nsmul_eq_mul, map_natCast, map_pow, map_add,
      map_mul, Bool.cond_true, Bool.cond_false, MvPolynomial.aeval_X, add_sub_cancel,
      one_pow, add_zero, mul_one]

theorem sum_mul_smul (n : ℕ) :
    (∑ ν ∈ Finset.range (n + 1), (ν * (ν - 1)) • bernsteinPolynomial R n ν) =
      (n * (n - 1)) • X ^ 2 := by
  -- We calculate the second `x`-derivative of `(x+y)^n`, evaluated at `y=(1-x)`,
  -- either directly or by using the binomial theorem.
  -- We'll work in `MvPolynomial Bool R`.
  let x : MvPolynomial Bool R := MvPolynomial.X true
  let y : MvPolynomial Bool R := MvPolynomial.X false
  have pderiv_true_x : pderiv true x = 1 := by rw [pderiv_X]; rfl
  have pderiv_true_y : pderiv true y = 0 := by rw [pderiv_X]; rfl
  let e : Bool → R[X] := fun i => cond i X (1 - X)
  -- Start with `(x+y)^n = (x+y)^n`,
  -- take the second `x`-derivative, evaluate at `x=X, y=1-X`, and multiply by `X`:
  trans MvPolynomial.aeval e (pderiv true (pderiv true ((x + y) ^ n))) * X ^ 2
  -- On the left-hand side we'll use the binomial theorem, then simplify.
  · -- We first prepare a tedious rewrite:
    have w : ∀ k : ℕ, (k * (k - 1)) • bernsteinPolynomial R n k =
        (n.choose k : R[X]) * ((1 - Polynomial.X) ^ (n - k) *
          ((k : R[X]) * ((↑(k - 1) : R[X]) * Polynomial.X ^ (k - 1 - 1)))) * Polynomial.X ^ 2 := by
      rintro (_ | _ | k)
      · simp
      · simp
      · rw [bernsteinPolynomial]
        simp only [← natCast_mul, Nat.add_succ_sub_one, add_zero, pow_succ]
        push_cast
        ring
    rw [add_pow, map_sum (pderiv true), map_sum (pderiv true), map_sum (MvPolynomial.aeval e),
      Finset.sum_mul]
    -- Step inside the sum:
    refine Finset.sum_congr rfl fun k _ => (w k).trans ?_
    simp only [x, y, e, pderiv_true_x, pderiv_true_y, Algebra.id.smul_eq_mul, nsmul_eq_mul,
      Bool.cond_true, Bool.cond_false, add_zero, zero_add, mul_zero, smul_zero, mul_one,
      MvPolynomial.aeval_X,
      Derivation.leibniz_pow, Derivation.leibniz, Derivation.map_natCast, map_natCast, map_pow,
      map_mul]
  -- On the right-hand side, we'll just simplify.
  · simp only [x, y, e, (pderiv _).leibniz_pow,
      (pderiv true).map_add, pderiv_true_x, pderiv_true_y, Algebra.id.smul_eq_mul, add_zero,
      mul_one, map_nsmul, map_pow, map_add, Bool.cond_true,
      Bool.cond_false, MvPolynomial.aeval_X, add_sub_cancel, one_pow, smul_smul,
      smul_one_mul]

/-- A certain linear combination of the previous three identities,
which we'll want later.
-/
theorem variance (n : ℕ) :
    (∑ ν ∈ Finset.range (n + 1), (n • Polynomial.X - (ν : R[X])) ^ 2 * bernsteinPolynomial R n ν) =
      n • Polynomial.X * ((1 : R[X]) - Polynomial.X) := by
  have p : ((((Finset.range (n + 1)).sum fun ν => (ν * (ν - 1)) • bernsteinPolynomial R n ν) +
      (1 - (2 * n) • Polynomial.X) * (Finset.range (n + 1)).sum fun ν =>
        ν • bernsteinPolynomial R n ν) + n ^ 2 • X ^ 2 *
          (Finset.range (n + 1)).sum fun ν => bernsteinPolynomial R n ν) = _ :=
    rfl
  conv at p =>
    lhs
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    simp only [← natCast_mul]
    simp only [← mul_assoc]
    simp only [← add_mul]
  conv at p =>
    rhs
    rw [sum, sum_smul, sum_mul_smul, ← natCast_mul]
  calc
    _ = _ := Finset.sum_congr rfl fun k m => ?_
    _ = _ := p
    _ = _ := ?_
  · congr 1; simp only [← natCast_mul, push_cast]
    cases k <;> · simp; ring
  · simp only [← natCast_mul, push_cast]
    cases n
    · simp
    · simp; ring

end bernsteinPolynomial
