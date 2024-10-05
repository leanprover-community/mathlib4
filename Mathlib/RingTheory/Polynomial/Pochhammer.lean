/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic.Abel

/-!
# The Pochhammer polynomials

We define and prove some basic relations about
`ascPochhammer S n : S[X] := X * (X + 1) * ... * (X + n - 1)`
which is also known as the rising factorial and about
`descPochhammer R n : R[X] := X * (X - 1) * ... * (X - n + 1)`
which is also known as the falling factorial. Versions of this definition
that are focused on `Nat` can be found in `Data.Nat.Factorial` as `Nat.ascFactorial` and
`Nat.descFactorial`.

## Implementation

As with many other families of polynomials, even though the coefficients are always in `ℕ` or `ℤ` ,
we define the polynomial with coefficients in any `[Semiring S]` or `[Ring R]`.
With constraints `[NeZero (1 : 𝕂)]` and `[NoZeroDivisors 𝕂]` we can show that the
evaluation of `ascPochhammer S n` is zero iff `n` is a sufficiently large non-positive integer.

## TODO

There is lots more in this direction:
* q-factorials, q-binomials, q-Pochhammer.
-/


universe u v

open Polynomial

open Polynomial

section Semiring

variable (S : Type u) [Semiring S]

/-- `ascPochhammer S n` is the polynomial `X * (X + 1) * ... * (X + n - 1)`,
with coefficients in the semiring `S`.
-/
noncomputable def ascPochhammer : ℕ → S[X]
  | 0 => 1
  | n + 1 => X * (ascPochhammer n).comp (X + 1)

@[simp]
theorem ascPochhammer_zero : ascPochhammer S 0 = 1 :=
  rfl

@[simp]
theorem ascPochhammer_one : ascPochhammer S 1 = X := by simp [ascPochhammer]

theorem ascPochhammer_succ_left (n : ℕ) :
    ascPochhammer S (n + 1) = X * (ascPochhammer S n).comp (X + 1) := by
  rw [ascPochhammer]

theorem monic_ascPochhammer (n : ℕ) [Nontrivial S] [NoZeroDivisors S] :
    Monic <| ascPochhammer S n := by
  induction' n with n hn
  · simp
  · have : leadingCoeff (X + 1 : S[X]) = 1 := leadingCoeff_X_add_C 1
    rw [ascPochhammer_succ_left, Monic.def, leadingCoeff_mul,
      leadingCoeff_comp (ne_zero_of_eq_one <| natDegree_X_add_C 1 : natDegree (X + 1) ≠ 0), hn,
      monic_X, one_mul, one_mul, this, one_pow]

section

variable {S} {T : Type v} [Semiring T]

@[simp]
theorem ascPochhammer_map (f : S →+* T) (n : ℕ) :
    (ascPochhammer S n).map f = ascPochhammer T n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, ascPochhammer_succ_left, map_comp]

theorem ascPochhammer_eval₂ (f : S →+* T) (n : ℕ) (t : T) :
    (ascPochhammer T n).eval t = (ascPochhammer S n).eval₂ f t := by
  rw [← ascPochhammer_map f]
  exact eval_map f t

theorem ascPochhammer_eval_comp {R : Type*} [CommSemiring R] (n : ℕ) (p : R[X]) [Algebra R S]
    (x : S) : ((ascPochhammer S n).comp (p.map (algebraMap R S))).eval x =
    (ascPochhammer S n).eval (p.eval₂ (algebraMap R S) x) := by
  rw [ascPochhammer_eval₂ (algebraMap R S), ← eval₂_comp', ← ascPochhammer_map (algebraMap R S),
    ← map_comp, eval_map]

end

@[simp, norm_cast]
theorem ascPochhammer_eval_cast (n k : ℕ) :
    (((ascPochhammer ℕ n).eval k : ℕ) : S) = ((ascPochhammer S n).eval k : S) := by
  rw [← ascPochhammer_map (algebraMap ℕ S), eval_map, ← eq_natCast (algebraMap ℕ S),
      eval₂_at_natCast,Nat.cast_id]

theorem ascPochhammer_eval_zero {n : ℕ} : (ascPochhammer S n).eval 0 = if n = 0 then 1 else 0 := by
  cases n
  · simp
  · simp [X_mul, Nat.succ_ne_zero, ascPochhammer_succ_left]

theorem ascPochhammer_zero_eval_zero : (ascPochhammer S 0).eval 0 = 1 := by simp

@[simp]
theorem ascPochhammer_ne_zero_eval_zero {n : ℕ} (h : n ≠ 0) : (ascPochhammer S n).eval 0 = 0 := by
  simp [ascPochhammer_eval_zero, h]

theorem ascPochhammer_succ_right (n : ℕ) :
    ascPochhammer S (n + 1) = ascPochhammer S n * (X + (n : S[X])) := by
  suffices h : ascPochhammer ℕ (n + 1) = ascPochhammer ℕ n * (X + (n : ℕ[X])) by
    apply_fun Polynomial.map (algebraMap ℕ S) at h
    simpa only [ascPochhammer_map, Polynomial.map_mul, Polynomial.map_add, map_X,
      Polynomial.map_natCast] using h
  induction n with
  | zero => simp
  | succ n ih =>
    conv_lhs =>
      rw [ascPochhammer_succ_left, ih, mul_comp, ← mul_assoc, ← ascPochhammer_succ_left, add_comp,
          X_comp, natCast_comp, add_assoc, add_comm (1 : ℕ[X]), ← Nat.cast_succ]

theorem ascPochhammer_succ_eval {S : Type*} [Semiring S] (n : ℕ) (k : S) :
    (ascPochhammer S (n + 1)).eval k = (ascPochhammer S n).eval k * (k + n) := by
  rw [ascPochhammer_succ_right, mul_add, eval_add, eval_mul_X, ← Nat.cast_comm, ← C_eq_natCast,
    eval_C_mul, Nat.cast_comm, ← mul_add]

theorem ascPochhammer_succ_comp_X_add_one (n : ℕ) :
    (ascPochhammer S (n + 1)).comp (X + 1) =
      ascPochhammer S (n + 1) + (n + 1) • (ascPochhammer S n).comp (X + 1) := by
  suffices (ascPochhammer ℕ (n + 1)).comp (X + 1) =
      ascPochhammer ℕ (n + 1) + (n + 1) * (ascPochhammer ℕ n).comp (X + 1)
    by simpa [map_comp] using congr_arg (Polynomial.map (Nat.castRingHom S)) this
  nth_rw 2 [ascPochhammer_succ_left]
  rw [← add_mul, ascPochhammer_succ_right ℕ n, mul_comp, mul_comm, add_comp, X_comp, natCast_comp,
    add_comm, ← add_assoc]
  ring

theorem ascPochhammer_mul (n m : ℕ) :
    ascPochhammer S n * (ascPochhammer S m).comp (X + (n : S[X])) = ascPochhammer S (n + m) := by
  induction' m with m ih
  · simp
  · rw [ascPochhammer_succ_right, Polynomial.mul_X_add_natCast_comp, ← mul_assoc, ih,
      ← add_assoc, ascPochhammer_succ_right, Nat.cast_add, add_assoc]

theorem ascPochhammer_nat_eq_ascFactorial (n : ℕ) :
    ∀ k, (ascPochhammer ℕ k).eval n = n.ascFactorial k
  | 0 => by rw [ascPochhammer_zero, eval_one, Nat.ascFactorial_zero]
  | t + 1 => by
    rw [ascPochhammer_succ_right, eval_mul, ascPochhammer_nat_eq_ascFactorial n t, eval_add, eval_X,
      eval_natCast, Nat.cast_id, Nat.ascFactorial_succ, mul_comm]

theorem ascPochhammer_nat_eq_descFactorial (a b : ℕ) :
    (ascPochhammer ℕ b).eval a = (a + b - 1).descFactorial b := by
  rw [ascPochhammer_nat_eq_ascFactorial, Nat.add_descFactorial_eq_ascFactorial']

@[simp]
theorem ascPochhammer_natDegree (n : ℕ) [NoZeroDivisors S] [Nontrivial S] :
    (ascPochhammer S n).natDegree = n := by
  induction' n with n hn
  · simp
  · have : natDegree (X + (n : S[X])) = 1 := natDegree_X_add_C (n : S)
    rw [ascPochhammer_succ_right,
        natDegree_mul _ (ne_zero_of_natDegree_gt <| this.symm ▸ Nat.zero_lt_one), hn, this]
    cases n
    · simp
    · refine ne_zero_of_natDegree_gt <| hn.symm ▸ Nat.add_one_pos _

end Semiring

section StrictOrderedSemiring

variable {S : Type*} [StrictOrderedSemiring S]

theorem ascPochhammer_pos (n : ℕ) (s : S) (h : 0 < s) : 0 < (ascPochhammer S n).eval s := by
  induction n with
  | zero =>
    simp only [ascPochhammer_zero, eval_one]
    exact zero_lt_one
  | succ n ih =>
    rw [ascPochhammer_succ_right, mul_add, eval_add, ← Nat.cast_comm, eval_natCast_mul, eval_mul_X,
      Nat.cast_comm, ← mul_add]
    exact mul_pos ih (lt_of_lt_of_le h (le_add_of_nonneg_right (Nat.cast_nonneg n)))

end StrictOrderedSemiring

section Factorial

open Nat

variable (S : Type*) [Semiring S] (r n : ℕ)

@[simp]
theorem ascPochhammer_eval_one (S : Type*) [Semiring S] (n : ℕ) :
    (ascPochhammer S n).eval (1 : S) = (n ! : S) := by
  rw_mod_cast [ascPochhammer_nat_eq_ascFactorial, Nat.one_ascFactorial]

theorem factorial_mul_ascPochhammer (S : Type*) [Semiring S] (r n : ℕ) :
    (r ! : S) * (ascPochhammer S n).eval (r + 1 : S) = (r + n)! := by
  rw_mod_cast [ascPochhammer_nat_eq_ascFactorial, Nat.factorial_mul_ascFactorial]

theorem ascPochhammer_nat_eval_succ (r : ℕ) :
    ∀ n : ℕ, n * (ascPochhammer ℕ r).eval (n + 1) = (n + r) * (ascPochhammer ℕ r).eval n
  | 0 => by
    by_cases h : r = 0
    · simp only [h, zero_mul, zero_add]
    · simp only [ascPochhammer_eval_zero, zero_mul, if_neg h, mul_zero]
  | k + 1 => by simp only [ascPochhammer_nat_eq_ascFactorial, Nat.succ_ascFactorial, add_right_comm]

theorem ascPochhammer_eval_succ (r n : ℕ) :
    (n : S) * (ascPochhammer S r).eval (n + 1 : S) =
    (n + r) * (ascPochhammer S r).eval (n : S) :=
  mod_cast congr_arg Nat.cast (ascPochhammer_nat_eval_succ r n)

end Factorial

section Ring

variable (R : Type u) [Ring R]

/-- `descPochhammer R n` is the polynomial `X * (X - 1) * ... * (X - n + 1)`,
with coefficients in the ring `R`.
-/
noncomputable def descPochhammer : ℕ → R[X]
  | 0 => 1
  | n + 1 => X * (descPochhammer n).comp (X - 1)

@[simp]
theorem descPochhammer_zero : descPochhammer R 0 = 1 :=
  rfl

@[simp]
theorem descPochhammer_one : descPochhammer R 1 = X := by simp [descPochhammer]

theorem descPochhammer_succ_left (n : ℕ) :
    descPochhammer R (n + 1) = X * (descPochhammer R n).comp (X - 1) := by
  rw [descPochhammer]

theorem monic_descPochhammer (n : ℕ) [Nontrivial R] [NoZeroDivisors R] :
    Monic <| descPochhammer R n := by
  induction' n with n hn
  · simp
  · have h : leadingCoeff (X - 1 : R[X]) = 1 := leadingCoeff_X_sub_C 1
    have : natDegree (X - (1 : R[X])) ≠ 0 := ne_zero_of_eq_one <| natDegree_X_sub_C (1 : R)
    rw [descPochhammer_succ_left, Monic.def, leadingCoeff_mul, leadingCoeff_comp this, hn, monic_X,
        one_mul, one_mul, h, one_pow]

section

variable {R} {T : Type v} [Ring T]

@[simp]
theorem descPochhammer_map (f : R →+* T) (n : ℕ) :
    (descPochhammer R n).map f = descPochhammer T n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, descPochhammer_succ_left, map_comp]
end

@[simp, norm_cast]
theorem descPochhammer_eval_cast (n : ℕ) (k : ℤ) :
    (((descPochhammer ℤ n).eval k : ℤ) : R) = ((descPochhammer R n).eval k : R) := by
  rw [← descPochhammer_map (algebraMap ℤ R), eval_map, ← eq_intCast (algebraMap ℤ R)]
  simp only [algebraMap_int_eq, eq_intCast, eval₂_at_intCast, Nat.cast_id, eq_natCast, Int.cast_id]

theorem descPochhammer_eval_zero {n : ℕ} :
    (descPochhammer R n).eval 0 = if n = 0 then 1 else 0 := by
  cases n
  · simp
  · simp [X_mul, Nat.succ_ne_zero, descPochhammer_succ_left]

theorem descPochhammer_zero_eval_zero : (descPochhammer R 0).eval 0 = 1 := by simp

@[simp]
theorem descPochhammer_ne_zero_eval_zero {n : ℕ} (h : n ≠ 0) : (descPochhammer R n).eval 0 = 0 := by
  simp [descPochhammer_eval_zero, h]

theorem descPochhammer_succ_right (n : ℕ) :
    descPochhammer R (n + 1) = descPochhammer R n * (X - (n : R[X])) := by
  suffices h : descPochhammer ℤ (n + 1) = descPochhammer ℤ n * (X - (n : ℤ[X])) by
    apply_fun Polynomial.map (algebraMap ℤ R) at h
    simpa [descPochhammer_map, Polynomial.map_mul, Polynomial.map_add, map_X,
      Polynomial.map_intCast] using h
  induction n with
  | zero => simp [descPochhammer]
  | succ n ih =>
    conv_lhs =>
      rw [descPochhammer_succ_left, ih, mul_comp, ← mul_assoc, ← descPochhammer_succ_left, sub_comp,
          X_comp, natCast_comp]
    rw [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub_swap]

@[simp]
theorem descPochhammer_natDegree (n : ℕ) [NoZeroDivisors R] [Nontrivial R] :
    (descPochhammer R n).natDegree = n := by
  induction' n with n hn
  · simp
  · have : natDegree (X - (n : R[X])) = 1 := natDegree_X_sub_C (n : R)
    rw [descPochhammer_succ_right,
        natDegree_mul _ (ne_zero_of_natDegree_gt <| this.symm ▸ Nat.zero_lt_one), hn, this]
    cases n
    · simp
    · refine ne_zero_of_natDegree_gt <| hn.symm ▸ Nat.add_one_pos _

theorem descPochhammer_succ_eval {S : Type*} [Ring S] (n : ℕ) (k : S) :
    (descPochhammer S (n + 1)).eval k = (descPochhammer S n).eval k * (k - n) := by
  rw [descPochhammer_succ_right, mul_sub, eval_sub, eval_mul_X, ← Nat.cast_comm, ← C_eq_natCast,
    eval_C_mul, Nat.cast_comm, ← mul_sub]

theorem descPochhammer_succ_comp_X_sub_one (n : ℕ) :
    (descPochhammer R (n + 1)).comp (X - 1) =
      descPochhammer R (n + 1) - (n + (1 : R[X])) • (descPochhammer R n).comp (X - 1) := by
  suffices (descPochhammer ℤ (n + 1)).comp (X - 1) =
      descPochhammer ℤ (n + 1) - (n + 1) * (descPochhammer ℤ n).comp (X - 1)
    by simpa [map_comp] using congr_arg (Polynomial.map (Int.castRingHom R)) this
  nth_rw 2 [descPochhammer_succ_left]
  rw [← sub_mul, descPochhammer_succ_right ℤ n, mul_comp, mul_comm, sub_comp, X_comp, natCast_comp]
  ring

theorem descPochhammer_eq_ascPochhammer (n : ℕ) :
    descPochhammer ℤ n = (ascPochhammer ℤ n).comp ((X : ℤ[X]) - n + 1) := by
  induction n with
  | zero => rw [descPochhammer_zero, ascPochhammer_zero, one_comp]
  | succ n ih =>
    rw [Nat.cast_succ, sub_add, add_sub_cancel_right, descPochhammer_succ_right,
      ascPochhammer_succ_left, ih, X_mul, mul_X_comp, comp_assoc, add_comp, X_comp, one_comp]

theorem descPochhammer_eval_eq_ascPochhammer (r : R) (n : ℕ) :
    (descPochhammer R n).eval r = (ascPochhammer R n).eval (r - n + 1) := by
  induction n with
  | zero => rw [descPochhammer_zero, eval_one, ascPochhammer_zero, eval_one]
  | succ n ih =>
    rw [Nat.cast_succ, sub_add, add_sub_cancel_right, descPochhammer_succ_eval, ih,
      ascPochhammer_succ_left, X_mul, eval_mul_X, show (X + 1 : R[X]) =
      (X + 1 : ℕ[X]).map (algebraMap ℕ R) by simp only [Polynomial.map_add, map_X,
      Polynomial.map_one], ascPochhammer_eval_comp, eval₂_add, eval₂_X, eval₂_one]

theorem descPochhammer_mul (n m : ℕ) :
    descPochhammer R n * (descPochhammer R m).comp (X - (n : R[X])) = descPochhammer R (n + m) := by
  induction' m with m ih
  · simp
  · rw [descPochhammer_succ_right, Polynomial.mul_X_sub_intCast_comp, ← mul_assoc, ih,
      ← add_assoc, descPochhammer_succ_right, Nat.cast_add, sub_add_eq_sub_sub]

theorem ascPochhammer_eval_neg_eq_descPochhammer (r : R) : ∀ (k : ℕ),
    (ascPochhammer R k).eval (-r) = (-1)^k * (descPochhammer R k).eval r
  | 0 => by
    rw [ascPochhammer_zero, descPochhammer_zero]
    simp only [eval_one, pow_zero, mul_one]
  | (k+1) => by
    rw [ascPochhammer_succ_right, mul_add, eval_add, eval_mul_X, ← Nat.cast_comm, eval_natCast_mul,
      Nat.cast_comm, ← mul_add, ascPochhammer_eval_neg_eq_descPochhammer r k, mul_assoc,
      descPochhammer_succ_right, mul_sub, eval_sub, eval_mul_X, ← Nat.cast_comm, eval_natCast_mul,
      pow_add, pow_one, mul_assoc ((-1)^k) (-1), mul_sub, neg_one_mul, neg_mul_eq_mul_neg,
      Nat.cast_comm, sub_eq_add_neg, neg_one_mul, neg_neg, ← mul_add]

theorem descPochhammer_eval_eq_descFactorial (n k : ℕ) :
    (descPochhammer R k).eval (n : R) = n.descFactorial k := by
  induction k with
  | zero => rw [descPochhammer_zero, eval_one, Nat.descFactorial_zero, Nat.cast_one]
  | succ k ih =>
    rw [descPochhammer_succ_right, Nat.descFactorial_succ, mul_sub, eval_sub, eval_mul_X,
      ← Nat.cast_comm k, eval_natCast_mul, ← Nat.cast_comm n, ← sub_mul, ih]
    by_cases h : n < k
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h, Nat.cast_zero, mul_zero, mul_zero, Nat.cast_zero]
    · rw [Nat.cast_mul, Nat.cast_sub <| not_lt.mp h]

theorem descPochhammer_int_eq_ascFactorial (a b : ℕ) :
    (descPochhammer ℤ b).eval (a + b : ℤ) = (a + 1).ascFactorial b := by
  rw [← Nat.cast_add, descPochhammer_eval_eq_descFactorial ℤ (a + b) b,
    Nat.add_descFactorial_eq_ascFactorial]

/- If the Pochhammer function is evaluated at a sufficiently large non-postive integer, then it is
zero. -/
theorem ascPochhammer_eq_zero_of_nonpos_int {R : Type u} [Ring R] {n : ℕ} {k : R}
    (hnk : ∃ kn : ℤ, kn ≤ 0 ∧ k = kn ∧ n ≥ 1 - kn) : (ascPochhammer R n).eval k = 0 := by
  induction n with
  | zero =>
    absurd hnk
    push_neg
    exact fun _ _ _ ↦ by linarith [Nat.cast_zero (R:=ℤ)]
  | succ n ih =>
    rewrite [ascPochhammer_succ_eval]
    have {a b : R} : a = 0 ∨ b = 0 → a * b = 0 := -- This theorem should be moved to `mul_eq_zero`
      fun o => o.elim (fun h => mul_eq_zero_of_left h b) (mul_eq_zero_of_right a)
    refine this <| or_iff_not_imp_left.2 fun np =>  ?_
    have hp := ih.mt np
    push_neg at hp
    have ⟨kn, hkn, kkn, hn⟩ := hnk
    have hnx' := hp kn hkn kkn
    rewrite [Nat.cast_add_one n] at hn
    have : kn = -n := by linarith
    simp [kkn, this]

end Ring

section FieldLike

/-- The iff variation of `ascPochhammer_eq_zero_of_nonpos_int` for a ring with
`[NeZero (1 : R)]` and  `[NoZeroDivisors R]`.-/
theorem ascPochhammer_eq_zero_iff {R : Type*} [Ring R] [NeZero (1 : R)] [NoZeroDivisors R]
    (n : ℕ) (k : R) : (ascPochhammer R n).eval k = 0 ↔ ∃ kn : ℤ, kn ≤ 0 ∧ k = kn ∧ n ≥ 1 - kn := by
  refine ⟨fun zero ↦ ?_, fun hkn ↦ ascPochhammer_eq_zero_of_nonpos_int hkn⟩
  induction n with
  | zero =>
    simp only [ascPochhammer_zero, Polynomial.eval_one, one_ne_zero] at zero
  | succ n ih =>
    rewrite [ascPochhammer_succ_eval, mul_eq_zero] at zero
    cases zero with
    | inl h =>
      have ⟨kn, hkn, kkn⟩ := ih h
      exact ⟨kn, hkn, kkn.1, le_trans kkn.2 <| Nat.cast_le.2 <| Nat.le_succ n⟩
    | inr h =>
      refine ⟨-n, by linarith, ?_, (by simp; linarith)⟩
      rewrite [Int.cast_neg, Int.cast_natCast, eq_neg_iff_add_eq_zero]
      simp_all

end FieldLike
