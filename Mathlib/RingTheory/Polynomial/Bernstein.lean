/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.Polynomial.Derivative
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.Data.MvPolynomial.PDeriv

#align_import ring_theory.polynomial.bernstein from "leanprover-community/mathlib"@"bbeb185db4ccee8ed07dc48449414ebfa39cb821"

/-!
# Bernstein polynomials

The definition of the Bernstein polynomials
```
bernsteinPolynomial (R : Type*) [CommRing R] (n ν : ℕ) : R[X] :=
(choose n ν) * X^ν * (1 - X)^(n - ν)
```
and the fact that for `ν : fin (n+1)` these are linearly independent over `ℚ`.

We prove the basic identities
* `(Finset.range (n + 1)).sum (fun ν ↦ bernsteinPolynomial R n ν) = 1`
* `(Finset.range (n + 1)).sum (fun ν ↦ ν • bernsteinPolynomial R n ν) = n • X`
* `(Finset.range (n + 1)).sum (fun ν ↦ (ν * (ν-1)) • bernsteinPolynomial R n ν) = (n * (n-1)) • X^2`

## Notes

See also `Mathlib.Analysis.SpecialFunctions.Bernstein`, which defines the Bernstein approximations
of a continuous function `f : C([0,1], ℝ)`, and shows that these converge uniformly to `f`.
-/


noncomputable section

open Nat (choose)

open Polynomial (X)

open scoped BigOperators Polynomial

variable (R : Type*) [CommRing R]

/-- `bernsteinPolynomial R n ν` is `(choose n ν) * X^ν * (1 - X)^(n - ν)`.

Although the coefficients are integers, it is convenient to work over an arbitrary commutative ring.
-/
def bernsteinPolynomial (n ν : ℕ) : R[X] :=
  (choose n ν : R[X]) * X ^ ν * (1 - X) ^ (n - ν)
#align bernstein_polynomial bernsteinPolynomial

example : bernsteinPolynomial ℤ 3 2 = 3 * X ^ 2 - 3 * X ^ 3 := by
  norm_num [bernsteinPolynomial, choose]
  -- ⊢ 3 * X ^ 2 * (1 - X) = 3 * X ^ 2 - 3 * X ^ 3
  ring
  -- 🎉 no goals

namespace bernsteinPolynomial

theorem eq_zero_of_lt {n ν : ℕ} (h : n < ν) : bernsteinPolynomial R n ν = 0 := by
  simp [bernsteinPolynomial, Nat.choose_eq_zero_of_lt h]
  -- 🎉 no goals
#align bernstein_polynomial.eq_zero_of_lt bernsteinPolynomial.eq_zero_of_lt

section

variable {R} {S : Type*} [CommRing S]

@[simp]
theorem map (f : R →+* S) (n ν : ℕ) :
    (bernsteinPolynomial R n ν).map f = bernsteinPolynomial S n ν := by simp [bernsteinPolynomial]
                                                                        -- 🎉 no goals
#align bernstein_polynomial.map bernsteinPolynomial.map

end

theorem flip (n ν : ℕ) (h : ν ≤ n) :
    (bernsteinPolynomial R n ν).comp (1 - X) = bernsteinPolynomial R n (n - ν) := by
  simp [bernsteinPolynomial, h, tsub_tsub_assoc, mul_right_comm]
  -- 🎉 no goals
#align bernstein_polynomial.flip bernsteinPolynomial.flip

theorem flip' (n ν : ℕ) (h : ν ≤ n) :
    bernsteinPolynomial R n ν = (bernsteinPolynomial R n (n - ν)).comp (1 - X) := by
  simp [← flip _ _ _ h, Polynomial.comp_assoc]
  -- 🎉 no goals
#align bernstein_polynomial.flip' bernsteinPolynomial.flip'

theorem eval_at_0 (n ν : ℕ) : (bernsteinPolynomial R n ν).eval 0 = if ν = 0 then 1 else 0 := by
  rw [bernsteinPolynomial]
  -- ⊢ Polynomial.eval 0 (↑(choose n ν) * X ^ ν * (1 - X) ^ (n - ν)) = if ν = 0 the …
  split_ifs with h
  -- ⊢ Polynomial.eval 0 (↑(choose n ν) * X ^ ν * (1 - X) ^ (n - ν)) = 1
  · subst h; simp
    -- ⊢ Polynomial.eval 0 (↑(choose n 0) * X ^ 0 * (1 - X) ^ (n - 0)) = 1
             -- 🎉 no goals
  · simp [zero_pow (Nat.pos_of_ne_zero h)]
    -- 🎉 no goals
#align bernstein_polynomial.eval_at_0 bernsteinPolynomial.eval_at_0

theorem eval_at_1 (n ν : ℕ) : (bernsteinPolynomial R n ν).eval 1 = if ν = n then 1 else 0 := by
  rw [bernsteinPolynomial]
  -- ⊢ Polynomial.eval 1 (↑(choose n ν) * X ^ ν * (1 - X) ^ (n - ν)) = if ν = n the …
  split_ifs with h
  -- ⊢ Polynomial.eval 1 (↑(choose n ν) * X ^ ν * (1 - X) ^ (n - ν)) = 1
  · subst h; simp
    -- ⊢ Polynomial.eval 1 (↑(choose ν ν) * X ^ ν * (1 - X) ^ (ν - ν)) = 1
             -- 🎉 no goals
  · obtain w | w := (n - ν).eq_zero_or_pos
    -- ⊢ Polynomial.eval 1 (↑(choose n ν) * X ^ ν * (1 - X) ^ (n - ν)) = 0
    · simp [Nat.choose_eq_zero_of_lt ((tsub_eq_zero_iff_le.mp w).lt_of_ne (Ne.symm h))]
      -- 🎉 no goals
    · simp [zero_pow w]
      -- 🎉 no goals
#align bernstein_polynomial.eval_at_1 bernsteinPolynomial.eval_at_1

theorem derivative_succ_aux (n ν : ℕ) :
    Polynomial.derivative (bernsteinPolynomial R (n + 1) (ν + 1)) =
      (n + 1) * (bernsteinPolynomial R n ν - bernsteinPolynomial R n (ν + 1)) := by
  rw [bernsteinPolynomial]
  -- ⊢ ↑Polynomial.derivative (↑(choose (n + 1) (ν + 1)) * X ^ (ν + 1) * (1 - X) ^  …
  suffices ((n + 1).choose (ν + 1) : R[X]) * ((↑(ν + 1 : ℕ) : R[X]) * X ^ ν) * (1 - X) ^ (n - ν) -
      ((n + 1).choose (ν + 1) : R[X]) * X ^ (ν + 1) * ((↑(n - ν) : R[X]) * (1 - X) ^ (n - ν - 1)) =
      (↑(n + 1) : R[X]) * ((n.choose ν : R[X]) * X ^ ν * (1 - X) ^ (n - ν) -
        (n.choose (ν + 1) : R[X]) * X ^ (ν + 1) * (1 - X) ^ (n - (ν + 1))) by
    simpa [Polynomial.derivative_pow, ← sub_eq_add_neg, Nat.succ_sub_succ_eq_sub,
      Polynomial.derivative_mul, Polynomial.derivative_nat_cast, zero_mul,
      Nat.cast_add, algebraMap.coe_one, Polynomial.derivative_X, mul_one, zero_add,
      Polynomial.derivative_sub, Polynomial.derivative_one, zero_sub, mul_neg, Nat.sub_zero,
      bernsteinPolynomial, map_add, map_natCast, Nat.cast_one]
  conv_rhs => rw [mul_sub]
  -- ⊢ ↑(choose (n + 1) (ν + 1)) * (↑(ν + 1) * X ^ ν) * (1 - X) ^ (n - ν) - ↑(choos …
  -- We'll prove the two terms match up separately.
  refine' congr (congr_arg Sub.sub _) _
  -- ⊢ ↑(choose (n + 1) (ν + 1)) * (↑(ν + 1) * X ^ ν) * (1 - X) ^ (n - ν) = ↑(n + 1 …
  · simp only [← mul_assoc]
    -- ⊢ ↑(choose (n + 1) (ν + 1)) * ↑(ν + 1) * X ^ ν * (1 - X) ^ (n - ν) = ↑(n + 1)  …
    refine' congr (congr_arg (· * ·) (congr (congr_arg (· * ·) _) rfl)) rfl
    -- ⊢ ↑(choose (n + 1) (ν + 1)) * ↑(ν + 1) = ↑(n + 1) * ↑(choose n ν)
    -- Now it's just about binomial coefficients
    exact_mod_cast congr_arg (fun m : ℕ => (m : R[X])) (Nat.succ_mul_choose_eq n ν).symm
    -- 🎉 no goals
  · rw [← tsub_add_eq_tsub_tsub, ← mul_assoc, ← mul_assoc]; congr 1
    -- ⊢ ↑(choose (n + 1) (ν + 1)) * X ^ (ν + 1) * ↑(n - ν) * (1 - X) ^ (n - (ν + 1)) …
                                                            -- ⊢ ↑(choose (n + 1) (ν + 1)) * X ^ (ν + 1) * ↑(n - ν) = ↑(n + 1) * (↑(choose n  …
    rw [mul_comm, ← mul_assoc, ← mul_assoc]; congr 1
    -- ⊢ ↑(n - ν) * ↑(choose (n + 1) (ν + 1)) * X ^ (ν + 1) = ↑(n + 1) * ↑(choose n ( …
                                             -- ⊢ ↑(n - ν) * ↑(choose (n + 1) (ν + 1)) = ↑(n + 1) * ↑(choose n (ν + 1))
    norm_cast
    -- ⊢ ↑((n - ν) * choose (n + 1) (ν + 1)) = ↑((n + 1) * choose n (ν + 1))
    congr 1
    -- ⊢ (n - ν) * choose (n + 1) (ν + 1) = (n + 1) * choose n (ν + 1)
    convert (Nat.choose_mul_succ_eq n (ν + 1)).symm using 1
    -- ⊢ (n - ν) * choose (n + 1) (ν + 1) = choose (n + 1) (ν + 1) * (n + 1 - (ν + 1))
    · -- Porting note: was
      -- convert mul_comm _ _ using 2
      -- simp
      rw [mul_comm, Nat.succ_sub_succ_eq_sub]
      -- 🎉 no goals
    · apply mul_comm
      -- 🎉 no goals
#align bernstein_polynomial.derivative_succ_aux bernsteinPolynomial.derivative_succ_aux

theorem derivative_succ (n ν : ℕ) : Polynomial.derivative (bernsteinPolynomial R n (ν + 1)) =
    n * (bernsteinPolynomial R (n - 1) ν - bernsteinPolynomial R (n - 1) (ν + 1)) := by
  cases n
  -- ⊢ ↑Polynomial.derivative (bernsteinPolynomial R Nat.zero (ν + 1)) = ↑Nat.zero  …
  · simp [bernsteinPolynomial]
    -- 🎉 no goals
  · rw [Nat.cast_succ]; apply derivative_succ_aux
    -- ⊢ ↑Polynomial.derivative (bernsteinPolynomial R (Nat.succ n✝) (ν + 1)) = (↑n✝  …
                        -- 🎉 no goals
#align bernstein_polynomial.derivative_succ bernsteinPolynomial.derivative_succ

theorem derivative_zero (n : ℕ) :
    Polynomial.derivative (bernsteinPolynomial R n 0) = -n * bernsteinPolynomial R (n - 1) 0 := by
  simp [bernsteinPolynomial, Polynomial.derivative_pow]
  -- 🎉 no goals
#align bernstein_polynomial.derivative_zero bernsteinPolynomial.derivative_zero

theorem iterate_derivative_at_0_eq_zero_of_lt (n : ℕ) {ν k : ℕ} :
    k < ν → (Polynomial.derivative^[k] (bernsteinPolynomial R n ν)).eval 0 = 0 := by
  cases' ν with ν
  -- ⊢ k < Nat.zero → Polynomial.eval 0 ((↑Polynomial.derivative)^[k] (bernsteinPol …
  · rintro ⟨⟩
    -- 🎉 no goals
  · rw [Nat.lt_succ_iff]
    -- ⊢ k ≤ ν → Polynomial.eval 0 ((↑Polynomial.derivative)^[k] (bernsteinPolynomial …
    induction' k with k ih generalizing n ν
    -- ⊢ Nat.zero ≤ ν → Polynomial.eval 0 ((↑Polynomial.derivative)^[Nat.zero] (berns …
    · simp [eval_at_0]
      -- 🎉 no goals
    · simp only [derivative_succ, Int.coe_nat_eq_zero, mul_eq_zero, Function.comp_apply,
        Function.iterate_succ, Polynomial.iterate_derivative_sub,
        Polynomial.iterate_derivative_nat_cast_mul, Polynomial.eval_mul, Polynomial.eval_nat_cast,
        Polynomial.eval_sub]
      intro h
      -- ⊢ ↑n * (Polynomial.eval 0 ((↑Polynomial.derivative)^[k] (bernsteinPolynomial R …
      apply mul_eq_zero_of_right
      -- ⊢ Polynomial.eval 0 ((↑Polynomial.derivative)^[k] (bernsteinPolynomial R (n -  …
      rw [ih _ _ (Nat.le_of_succ_le h), sub_zero]
      -- ⊢ Polynomial.eval 0 ((↑Polynomial.derivative)^[k] (bernsteinPolynomial R (n -  …
      convert ih _ _ (Nat.pred_le_pred h)
      -- ⊢ ν = Nat.succ (Nat.pred ν)
      exact (Nat.succ_pred_eq_of_pos (k.succ_pos.trans_le h)).symm
      -- 🎉 no goals
#align bernstein_polynomial.iterate_derivative_at_0_eq_zero_of_lt bernsteinPolynomial.iterate_derivative_at_0_eq_zero_of_lt

@[simp]
theorem iterate_derivative_succ_at_0_eq_zero (n ν : ℕ) :
    (Polynomial.derivative^[ν] (bernsteinPolynomial R n (ν + 1))).eval 0 = 0 :=
  iterate_derivative_at_0_eq_zero_of_lt R n (lt_add_one ν)
#align bernstein_polynomial.iterate_derivative_succ_at_0_eq_zero bernsteinPolynomial.iterate_derivative_succ_at_0_eq_zero

open Polynomial

@[simp]
theorem iterate_derivative_at_0 (n ν : ℕ) :
    (Polynomial.derivative^[ν] (bernsteinPolynomial R n ν)).eval 0 =
      (pochhammer R ν).eval ((n - (ν - 1) : ℕ) : R) := by
  by_cases h : ν ≤ n
  -- ⊢ eval 0 ((↑derivative)^[ν] (bernsteinPolynomial R n ν)) = eval (↑(n - (ν - 1) …
  · induction' ν with ν ih generalizing n
    -- ⊢ eval 0 ((↑derivative)^[Nat.zero] (bernsteinPolynomial R n Nat.zero)) = eval  …
    · simp [eval_at_0]
      -- 🎉 no goals
    · have h' : ν ≤ n - 1 := le_tsub_of_add_le_right h
      -- ⊢ eval 0 ((↑derivative)^[Nat.succ ν] (bernsteinPolynomial R n (Nat.succ ν))) = …
      simp only [derivative_succ, ih (n - 1) h', iterate_derivative_succ_at_0_eq_zero,
        Nat.succ_sub_succ_eq_sub, tsub_zero, sub_zero, iterate_derivative_sub,
        iterate_derivative_nat_cast_mul, eval_one, eval_mul, eval_add, eval_sub, eval_X, eval_comp,
        eval_nat_cast, Function.comp_apply, Function.iterate_succ, pochhammer_succ_left]
      obtain rfl | h'' := ν.eq_zero_or_pos
      -- ⊢ ↑n * eval (↑(n - 1 - (0 - 1))) (pochhammer R 0) = ↑(n - 0) * eval (↑(n - 0)  …
      · simp
        -- 🎉 no goals
      · have : n - 1 - (ν - 1) = n - ν := by
          rw [gt_iff_lt, ← Nat.succ_le_iff] at h''
          rw [← tsub_add_eq_tsub_tsub, add_comm, tsub_add_cancel_of_le h'']
        rw [this, pochhammer_eval_succ]
        -- ⊢ ↑n * eval (↑(n - ν)) (pochhammer R ν) = (↑(n - ν) + ↑ν) * eval (↑(n - ν)) (p …
        rw_mod_cast [tsub_add_cancel_of_le (h'.trans n.pred_le)]
        -- 🎉 no goals
  · simp only [not_le] at h
    -- ⊢ eval 0 ((↑derivative)^[ν] (bernsteinPolynomial R n ν)) = eval (↑(n - (ν - 1) …
    rw [tsub_eq_zero_iff_le.mpr (Nat.le_pred_of_lt h), eq_zero_of_lt R h]
    -- ⊢ eval 0 ((↑derivative)^[ν] 0) = eval (↑0) (pochhammer R ν)
    simp [pos_iff_ne_zero.mp (pos_of_gt h)]
    -- 🎉 no goals
#align bernstein_polynomial.iterate_derivative_at_0 bernsteinPolynomial.iterate_derivative_at_0

theorem iterate_derivative_at_0_ne_zero [CharZero R] (n ν : ℕ) (h : ν ≤ n) :
    (Polynomial.derivative^[ν] (bernsteinPolynomial R n ν)).eval 0 ≠ 0 := by
  simp only [Int.coe_nat_eq_zero, bernsteinPolynomial.iterate_derivative_at_0, Ne.def,
    Nat.cast_eq_zero]
  simp only [← pochhammer_eval_cast]
  -- ⊢ ¬↑(eval (n - (ν - 1)) (pochhammer ℕ ν)) = 0
  norm_cast
  -- ⊢ ¬eval (n - (ν - 1)) (pochhammer ℕ ν) = 0
  apply ne_of_gt
  -- ⊢ 0 < eval (n - (ν - 1)) (pochhammer ℕ ν)
  obtain rfl | h' := Nat.eq_zero_or_pos ν
  -- ⊢ 0 < eval (n - (0 - 1)) (pochhammer ℕ 0)
  · simp
    -- 🎉 no goals
  · rw [← Nat.succ_pred_eq_of_pos h'] at h
    -- ⊢ 0 < eval (n - (ν - 1)) (pochhammer ℕ ν)
    exact pochhammer_pos _ _ (tsub_pos_of_lt (Nat.lt_of_succ_le h))
    -- 🎉 no goals
#align bernstein_polynomial.iterate_derivative_at_0_ne_zero bernsteinPolynomial.iterate_derivative_at_0_ne_zero

/-!
Rather than redoing the work of evaluating the derivatives at 1,
we use the symmetry of the Bernstein polynomials.
-/


theorem iterate_derivative_at_1_eq_zero_of_lt (n : ℕ) {ν k : ℕ} :
    k < n - ν → (Polynomial.derivative^[k] (bernsteinPolynomial R n ν)).eval 1 = 0 := by
  intro w
  -- ⊢ eval 1 ((↑derivative)^[k] (bernsteinPolynomial R n ν)) = 0
  rw [flip' _ _ _ (tsub_pos_iff_lt.mp (pos_of_gt w)).le]
  -- ⊢ eval 1 ((↑derivative)^[k] (comp (bernsteinPolynomial R n (n - ν)) (1 - X)))  …
  simp [Polynomial.eval_comp, iterate_derivative_at_0_eq_zero_of_lt R n w]
  -- 🎉 no goals
#align bernstein_polynomial.iterate_derivative_at_1_eq_zero_of_lt bernsteinPolynomial.iterate_derivative_at_1_eq_zero_of_lt

@[simp]
theorem iterate_derivative_at_1 (n ν : ℕ) (h : ν ≤ n) :
    (Polynomial.derivative^[n - ν] (bernsteinPolynomial R n ν)).eval 1 =
      (-1) ^ (n - ν) * (pochhammer R (n - ν)).eval (ν + 1 : R) := by
  rw [flip' _ _ _ h]
  -- ⊢ eval 1 ((↑derivative)^[n - ν] (comp (bernsteinPolynomial R n (n - ν)) (1 - X …
  simp [Polynomial.eval_comp, h]
  -- ⊢ (-1) ^ (n - ν) * eval (↑(n - (n - ν - 1))) (pochhammer R (n - ν)) = (-1) ^ ( …
  obtain rfl | h' := h.eq_or_lt
  -- ⊢ (-1) ^ (ν - ν) * eval (↑(ν - (ν - ν - 1))) (pochhammer R (ν - ν)) = (-1) ^ ( …
  · simp
    -- 🎉 no goals
  · congr
    -- ⊢ ↑(n - (n - ν - 1)) = ↑ν + 1
    norm_cast
    -- ⊢ ↑(n - (n - ν - 1)) = ↑(ν + 1)
    rw [← tsub_add_eq_tsub_tsub, tsub_tsub_cancel_of_le (Nat.succ_le_iff.mpr h')]
    -- 🎉 no goals
#align bernstein_polynomial.iterate_derivative_at_1 bernsteinPolynomial.iterate_derivative_at_1

theorem iterate_derivative_at_1_ne_zero [CharZero R] (n ν : ℕ) (h : ν ≤ n) :
    (Polynomial.derivative^[n - ν] (bernsteinPolynomial R n ν)).eval 1 ≠ 0 := by
  rw [bernsteinPolynomial.iterate_derivative_at_1 _ _ _ h, Ne.def, neg_one_pow_mul_eq_zero_iff, ←
    Nat.cast_succ, ← pochhammer_eval_cast, ← Nat.cast_zero, Nat.cast_inj]
  exact (pochhammer_pos _ _ (Nat.succ_pos ν)).ne'
  -- 🎉 no goals
#align bernstein_polynomial.iterate_derivative_at_1_ne_zero bernsteinPolynomial.iterate_derivative_at_1_ne_zero

open Submodule

theorem linearIndependent_aux (n k : ℕ) (h : k ≤ n + 1) :
    LinearIndependent ℚ fun ν : Fin k => bernsteinPolynomial ℚ n ν := by
  induction' k with k ih
  -- ⊢ LinearIndependent ℚ fun ν => bernsteinPolynomial ℚ n ↑ν
  · simp [Nat.zero_eq]
    -- ⊢ LinearIndependent ℚ fun ν => bernsteinPolynomial ℚ n ↑ν
    apply linearIndependent_empty_type
    -- 🎉 no goals
  · apply linearIndependent_fin_succ'.mpr
    -- ⊢ LinearIndependent ℚ (Fin.init fun ν => bernsteinPolynomial ℚ n ↑ν) ∧ ¬bernst …
    fconstructor
    -- ⊢ LinearIndependent ℚ (Fin.init fun ν => bernsteinPolynomial ℚ n ↑ν)
    · exact ih (le_of_lt h)
      -- 🎉 no goals
    · -- The actual work!
      -- We show that the (n-k)-th derivative at 1 doesn't vanish,
      -- but vanishes for everything in the span.
      clear ih
      -- ⊢ ¬bernsteinPolynomial ℚ n ↑(Fin.last k) ∈ span ℚ (Set.range (Fin.init fun ν = …
      simp only [Nat.succ_eq_add_one, add_le_add_iff_right] at h
      -- ⊢ ¬bernsteinPolynomial ℚ n ↑(Fin.last k) ∈ span ℚ (Set.range (Fin.init fun ν = …
      simp only [Fin.val_last, Fin.init_def]
      -- ⊢ ¬bernsteinPolynomial ℚ n k ∈ span ℚ (Set.range fun k_1 => bernsteinPolynomia …
      dsimp
      -- ⊢ ¬bernsteinPolynomial ℚ n k ∈ span ℚ (Set.range fun k_1 => bernsteinPolynomia …
      apply not_mem_span_of_apply_not_mem_span_image (@Polynomial.derivative ℚ _ ^ (n - k))
      -- ⊢ ¬↑(derivative ^ (n - k)) (bernsteinPolynomial ℚ n k) ∈ span ℚ (↑(derivative  …
      simp only [not_exists, not_and, Submodule.mem_map, Submodule.span_image]
      -- ⊢ ∀ (x : ℚ[X]), x ∈ span ℚ (Set.range fun k_1 => bernsteinPolynomial ℚ n ↑k_1) …
      intro p m
      -- ⊢ ¬↑(derivative ^ (n - k)) p = ↑(derivative ^ (n - k)) (bernsteinPolynomial ℚ  …
      apply_fun Polynomial.eval (1 : ℚ)
      -- ⊢ eval 1 (↑(derivative ^ (n - k)) p) ≠ eval 1 (↑(derivative ^ (n - k)) (bernst …
      simp only [LinearMap.pow_apply]
      -- ⊢ eval 1 ((↑derivative)^[n - k] p) ≠ eval 1 ((↑derivative)^[n - k] (bernsteinP …
      -- The right hand side is nonzero,
      -- so it will suffice to show the left hand side is always zero.
      suffices (Polynomial.derivative^[n - k] p).eval 1 = 0 by
        rw [this]
        exact (iterate_derivative_at_1_ne_zero ℚ n k h).symm
      refine span_induction m ?_ ?_ ?_ ?_
      · simp
        -- ⊢ ∀ (a : Fin k), eval 1 ((↑derivative)^[n - k] (bernsteinPolynomial ℚ n ↑a)) = 0
        rintro ⟨a, w⟩; simp only [Fin.val_mk]
        -- ⊢ eval 1 ((↑derivative)^[n - k] (bernsteinPolynomial ℚ n ↑{ val := a, isLt :=  …
                       -- ⊢ eval 1 ((↑derivative)^[n - k] (bernsteinPolynomial ℚ n a)) = 0
        rw [iterate_derivative_at_1_eq_zero_of_lt ℚ n ((tsub_lt_tsub_iff_left_of_le h).mpr w)]
        -- 🎉 no goals
      · simp
        -- 🎉 no goals
      · intro x y hx hy; simp [hx, hy]
        -- ⊢ eval 1 ((↑derivative)^[n - k] (x + y)) = 0
                         -- 🎉 no goals
      · intro a x h; simp [h]
        -- ⊢ eval 1 ((↑derivative)^[n - k] (a • x)) = 0
                     -- 🎉 no goals
#align bernstein_polynomial.linear_independent_aux bernsteinPolynomial.linearIndependent_aux

/-- The Bernstein polynomials are linearly independent.

We prove by induction that the collection of `bernsteinPolynomial n ν` for `ν = 0, ..., k`
are linearly independent.
The inductive step relies on the observation that the `(n-k)`-th derivative, evaluated at 1,
annihilates `bernsteinPolynomial n ν` for `ν < k`, but has a nonzero value at `ν = k`.
-/
theorem linearIndependent (n : ℕ) :
    LinearIndependent ℚ fun ν : Fin (n + 1) => bernsteinPolynomial ℚ n ν :=
  linearIndependent_aux n (n + 1) le_rfl
#align bernstein_polynomial.linear_independent bernsteinPolynomial.linearIndependent

theorem sum (n : ℕ) : (∑ ν in Finset.range (n + 1), bernsteinPolynomial R n ν) = 1 :=
  calc
    (∑ ν in Finset.range (n + 1), bernsteinPolynomial R n ν) = (X + (1 - X)) ^ n := by
      rw [add_pow]
      -- ⊢ ∑ ν in Finset.range (n + 1), bernsteinPolynomial R n ν = ∑ m in Finset.range …
      simp only [bernsteinPolynomial, mul_comm, mul_assoc, mul_left_comm]
      -- 🎉 no goals
    _ = 1 := by simp
                -- 🎉 no goals
#align bernstein_polynomial.sum bernsteinPolynomial.sum

open Polynomial

open MvPolynomial hiding X

theorem sum_smul (n : ℕ) :
    (∑ ν in Finset.range (n + 1), ν • bernsteinPolynomial R n ν) = n • X := by
  -- We calculate the `x`-derivative of `(x+y)^n`, evaluated at `y=(1-x)`,
  -- either directly or by using the binomial theorem.
  -- We'll work in `MvPolynomial Bool R`.
  let x : MvPolynomial Bool R := MvPolynomial.X true
  -- ⊢ ∑ ν in Finset.range (n + 1), ν • bernsteinPolynomial R n ν = n • X
  let y : MvPolynomial Bool R := MvPolynomial.X false
  -- ⊢ ∑ ν in Finset.range (n + 1), ν • bernsteinPolynomial R n ν = n • X
  have pderiv_true_x : pderiv true x = 1 := by rw [pderiv_X]; rfl
  -- ⊢ ∑ ν in Finset.range (n + 1), ν • bernsteinPolynomial R n ν = n • X
  have pderiv_true_y : pderiv true y = 0 := by rw [pderiv_X]; rfl
  -- ⊢ ∑ ν in Finset.range (n + 1), ν • bernsteinPolynomial R n ν = n • X
  let e : Bool → R[X] := fun i => cond i X (1 - X)
  -- ⊢ ∑ ν in Finset.range (n + 1), ν • bernsteinPolynomial R n ν = n • X
  -- Start with `(x+y)^n = (x+y)^n`,
  -- take the `x`-derivative, evaluate at `x=X, y=1-X`, and multiply by `X`:
  trans MvPolynomial.aeval e (pderiv true ((x + y) ^ n)) * X
  -- ⊢ ∑ ν in Finset.range (n + 1), ν • bernsteinPolynomial R n ν = ↑(MvPolynomial. …
  -- On the left hand side we'll use the binomial theorem, then simplify.
  · -- We first prepare a tedious rewrite:
    have w : ∀ k : ℕ, k • bernsteinPolynomial R n k =
        (k : R[X]) * Polynomial.X ^ (k - 1) * (1 - Polynomial.X) ^ (n - k) * (n.choose k : R[X]) *
          Polynomial.X := by
      rintro (_ | k)
      · simp
      · rw [bernsteinPolynomial]
        simp only [← nat_cast_mul, Nat.succ_eq_add_one, Nat.add_succ_sub_one, add_zero, pow_succ]
        push_cast
        ring
    rw [add_pow, (pderiv true).map_sum, (MvPolynomial.aeval e).map_sum, Finset.sum_mul]
    -- ⊢ ∑ ν in Finset.range (n + 1), ν • bernsteinPolynomial R n ν = ∑ x_1 in Finset …
    -- Step inside the sum:
    refine' Finset.sum_congr rfl fun k _ => (w k).trans _
    -- ⊢ ↑k * X ^ (k - 1) * (1 - X) ^ (n - k) * ↑(choose n k) * X = ↑(MvPolynomial.ae …
    simp only [pderiv_true_x, pderiv_true_y, Algebra.id.smul_eq_mul, nsmul_eq_mul, Bool.cond_true,
      Bool.cond_false, add_zero, mul_one, mul_zero, smul_zero, MvPolynomial.aeval_X,
      MvPolynomial.pderiv_mul, Derivation.leibniz_pow, Derivation.map_coe_nat, map_natCast, map_pow,
      map_mul]
  · rw [(pderiv true).leibniz_pow, (pderiv true).map_add, pderiv_true_x, pderiv_true_y]
    -- ⊢ ↑(MvPolynomial.aeval e) (n • (x + y) ^ (n - 1) • (1 + 0)) * X = n • X
    simp only [Algebra.id.smul_eq_mul, nsmul_eq_mul, map_natCast, map_pow, map_add, map_mul,
      Bool.cond_true, Bool.cond_false, MvPolynomial.aeval_X, add_sub_cancel'_right, one_pow,
      add_zero, mul_one]
#align bernstein_polynomial.sum_smul bernsteinPolynomial.sum_smul

theorem sum_mul_smul (n : ℕ) :
    (∑ ν in Finset.range (n + 1), (ν * (ν - 1)) • bernsteinPolynomial R n ν) =
      (n * (n - 1)) • X ^ 2 := by
  -- We calculate the second `x`-derivative of `(x+y)^n`, evaluated at `y=(1-x)`,
  -- either directly or by using the binomial theorem.
  -- We'll work in `MvPolynomial Bool R`.
  let x : MvPolynomial Bool R := MvPolynomial.X true
  -- ⊢ ∑ ν in Finset.range (n + 1), (ν * (ν - 1)) • bernsteinPolynomial R n ν = (n  …
  let y : MvPolynomial Bool R := MvPolynomial.X false
  -- ⊢ ∑ ν in Finset.range (n + 1), (ν * (ν - 1)) • bernsteinPolynomial R n ν = (n  …
  have pderiv_true_x : pderiv true x = 1 := by rw [pderiv_X]; rfl
  -- ⊢ ∑ ν in Finset.range (n + 1), (ν * (ν - 1)) • bernsteinPolynomial R n ν = (n  …
  have pderiv_true_y : pderiv true y = 0 := by rw [pderiv_X]; rfl
  -- ⊢ ∑ ν in Finset.range (n + 1), (ν * (ν - 1)) • bernsteinPolynomial R n ν = (n  …
  let e : Bool → R[X] := fun i => cond i X (1 - X)
  -- ⊢ ∑ ν in Finset.range (n + 1), (ν * (ν - 1)) • bernsteinPolynomial R n ν = (n  …
  -- Start with `(x+y)^n = (x+y)^n`,
  -- take the second `x`-derivative, evaluate at `x=X, y=1-X`, and multiply by `X`:
  trans MvPolynomial.aeval e (pderiv true (pderiv true ((x + y) ^ n))) * X ^ 2
  -- ⊢ ∑ ν in Finset.range (n + 1), (ν * (ν - 1)) • bernsteinPolynomial R n ν = ↑(M …
  -- On the left hand side we'll use the binomial theorem, then simplify.
  · -- We first prepare a tedious rewrite:
    have w : ∀ k : ℕ, (k * (k - 1)) • bernsteinPolynomial R n k =
        (n.choose k : R[X]) * ((1 - Polynomial.X) ^ (n - k) *
          ((k : R[X]) * ((↑(k - 1) : R[X]) * Polynomial.X ^ (k - 1 - 1)))) * Polynomial.X ^ 2 := by
      rintro (_ | _ | k)
      · simp
      · simp
      · rw [bernsteinPolynomial]
        simp only [← nat_cast_mul, Nat.succ_eq_add_one, Nat.add_succ_sub_one, add_zero, pow_succ]
        push_cast
        ring
    rw [add_pow, (pderiv true).map_sum, (pderiv true).map_sum, (MvPolynomial.aeval e).map_sum,
      Finset.sum_mul]
    -- Step inside the sum:
    refine' Finset.sum_congr rfl fun k _ => (w k).trans _
    -- ⊢ ↑(choose n k) * ((1 - X) ^ (n - k) * (↑k * (↑(k - 1) * X ^ (k - 1 - 1)))) *  …
    simp only [pderiv_true_x, pderiv_true_y, Algebra.id.smul_eq_mul, nsmul_eq_mul, Bool.cond_true,
      Bool.cond_false, add_zero, zero_add, mul_zero, smul_zero, mul_one,
      MvPolynomial.aeval_X, MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_of_ne,
      Derivation.leibniz_pow, Derivation.leibniz, Derivation.map_coe_nat, map_natCast, map_pow,
      map_mul, map_add]
  -- On the right hand side, we'll just simplify.
  · simp only [pderiv_one, pderiv_mul, (pderiv _).leibniz_pow, (pderiv _).map_coe_nat,
      (pderiv true).map_add, pderiv_true_x, pderiv_true_y, Algebra.id.smul_eq_mul, add_zero,
      mul_one, Derivation.map_smul_of_tower, map_nsmul, map_pow, map_add, Bool.cond_true,
      Bool.cond_false, MvPolynomial.aeval_X, add_sub_cancel'_right, one_pow, smul_smul,
      smul_one_mul]
#align bernstein_polynomial.sum_mul_smul bernsteinPolynomial.sum_mul_smul

/-- A certain linear combination of the previous three identities,
which we'll want later.
-/
theorem variance (n : ℕ) :
    (∑ ν in Finset.range (n + 1), (n • Polynomial.X - (ν : R[X])) ^ 2 * bernsteinPolynomial R n ν) =
      n • Polynomial.X * ((1 : R[X]) - Polynomial.X) := by
  have p : ((((Finset.range (n + 1)).sum fun ν => (ν * (ν - 1)) • bernsteinPolynomial R n ν) +
      (1 - (2 * n) • Polynomial.X) * (Finset.range (n + 1)).sum fun ν =>
        ν • bernsteinPolynomial R n ν) + n ^ 2 • X ^ 2 *
          (Finset.range (n + 1)).sum fun ν => bernsteinPolynomial R n ν) = _ :=
    rfl
  conv at p =>
    lhs
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    simp only [← nat_cast_mul]
    simp only [← mul_assoc]
    simp only [← add_mul]
  conv at p =>
    rhs
    rw [sum, sum_smul, sum_mul_smul, ← nat_cast_mul]
  calc
    _ = _ := Finset.sum_congr rfl fun k m => ?_
    _ = _ := p
    _ = _ := ?_
  · congr 1; simp only [← nat_cast_mul, push_cast]
    -- ⊢ (n • X - ↑k) ^ 2 = ↑(k * (k - 1)) + (↑1 - ↑(2 * n) * X) * ↑k + ↑(n ^ 2) * X  …
             -- ⊢ (↑n * X - ↑k) ^ 2 = ↑k * ↑(k - 1) + (1 - 2 * ↑n * X) * ↑k + ↑n ^ 2 * X ^ 2
    cases k <;> · simp; ring
    -- ⊢ (↑n * X - ↑Nat.zero) ^ 2 = ↑Nat.zero * ↑(Nat.zero - 1) + (1 - 2 * ↑n * X) *  …
                  -- ⊢ (↑n * X) ^ 2 = ↑n ^ 2 * X ^ 2
                        -- 🎉 no goals
                  -- ⊢ (↑n * X - (↑n✝ + 1)) ^ 2 = (↑n✝ + 1) * ↑n✝ + (1 - 2 * ↑n * X) * (↑n✝ + 1) +  …
                        -- 🎉 no goals
  · simp only [← nat_cast_mul, push_cast]
    -- ⊢ ↑n * ↑(n - 1) * X ^ 2 + (1 - 2 * ↑n * X) * (↑n * X) + ↑n ^ 2 * X ^ 2 * 1 = ↑ …
    cases n
    -- ⊢ ↑Nat.zero * ↑(Nat.zero - 1) * X ^ 2 + (1 - 2 * ↑Nat.zero * X) * (↑Nat.zero * …
    · simp
      -- 🎉 no goals
    · simp; ring
      -- ⊢ (↑n✝ + 1) * ↑n✝ * X ^ 2 + (1 - 2 * (↑n✝ + 1) * X) * ((↑n✝ + 1) * X) + (↑n✝ + …
            -- 🎉 no goals
#align bernstein_polynomial.variance bernsteinPolynomial.variance

end bernsteinPolynomial
