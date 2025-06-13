/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
# Sum of iterated derivatives

This file introduces `Polynomial.sumIDeriv`, the sum of the iterated derivatives of a polynomial,
as a linear map. This is used in particular in the proof of the Lindemann-Weierstrass theorem
(see https://github.com/leanprover-community/mathlib4/pull/6718).

## Main results

* `Polynomial.sumIDeriv`: Sum of iterated derivatives of a polynomial, as a linear map
* `Polynomial.sumIDeriv_apply`, `Polynomial.sumIDeriv_apply_of_lt`,
  `Polynomial.sumIDeriv_apply_of_le`: `Polynomial.sumIDeriv` expressed as a sum
* `Polynomial.sumIDeriv_C`, `Polynomial.sumIDeriv_X`: `Polynomial.sumIDeriv` applied to simple
  polynomials
* `Polynomial.sumIDeriv_map`: `Polynomial.sumIDeriv` commutes with `Polynomial.map`
* `Polynomial.sumIDeriv_derivative`: `Polynomial.sumIDeriv` commutes with `Polynomial.derivative`
* `Polynomial.sumIDeriv_eq_self_add`: `sumIDeriv p = p + derivative (sumIDeriv p)`
* `Polynomial.exists_iterate_derivative_eq_factorial_smul`: the `k`'th iterated derivative of a
  polynomial has a common factor `k!`
* `Polynomial.aeval_iterate_derivative_of_lt`, `Polynomial.aeval_iterate_derivative_self`,
  `Polynomial.aeval_iterate_derivative_of_ge`: applying `Polynomial.aeval` to iterated derivatives
* `Polynomial.aeval_sumIDeriv`, `Polynomial.aeval_sumIDeriv_of_pos`: applying `Polynomial.aeval` to
  `Polynomial.sumIDeriv`

-/

open Finset
open scoped Nat

namespace Polynomial

variable {R S : Type*}

section Semiring

variable [Semiring R] [Semiring S]

/--
Sum of iterated derivatives of a polynomial, as a linear map

This definition does not allow different weights for the derivatives. It is likely that it could be
extended to allow them, but this was not needed for the initial use case (the integration by parts
of the integral $I_i$ in the
[Lindemann-Weierstrass](https://en.wikipedia.org/wiki/Lindemann%E2%80%93Weierstrass_theorem)
theorem).
-/
noncomputable def sumIDeriv : R[X] →ₗ[R] R[X] :=
  Finsupp.lsum ℕ (fun _ ↦ LinearMap.id) ∘ₗ derivativeFinsupp

theorem sumIDeriv_apply (p : R[X]) :
    sumIDeriv p = ∑ i ∈ range (p.natDegree + 1), derivative^[i] p := by
  dsimp [sumIDeriv]
  exact Finsupp.sum_of_support_subset _ (by simp) _ (by simp)

theorem sumIDeriv_apply_of_lt {p : R[X]} {n : ℕ} (hn : p.natDegree < n) :
    sumIDeriv p = ∑ i ∈ range n, derivative^[i] p := by
  dsimp [sumIDeriv]
  exact Finsupp.sum_of_support_subset _ (by simp [hn]) _ (by simp)

theorem sumIDeriv_apply_of_le {p : R[X]} {n : ℕ} (hn : p.natDegree ≤ n) :
    sumIDeriv p = ∑ i ∈ range (n + 1), derivative^[i] p := by
  dsimp [sumIDeriv]
  exact Finsupp.sum_of_support_subset _ (by simp [Nat.lt_succ, hn]) _ (by simp)

@[simp]
theorem sumIDeriv_C (a : R) : sumIDeriv (C a) = C a := by
  rw [sumIDeriv_apply, natDegree_C, zero_add, sum_range_one, Function.iterate_zero_apply]

@[simp]
theorem sumIDeriv_X : sumIDeriv X = X + C 1 := by
  rw [sumIDeriv_apply, natDegree_X, sum_range_succ, sum_range_one, Function.iterate_zero_apply,
    Function.iterate_one, derivative_X, eq_natCast, Nat.cast_one]

@[simp]
theorem sumIDeriv_map (p : R[X]) (f : R →+* S) :
    sumIDeriv (p.map f) = (sumIDeriv p).map f := by
  let n := max (p.map f).natDegree p.natDegree
  rw [sumIDeriv_apply_of_le (le_max_left _ _ : _ ≤ n)]
  rw [sumIDeriv_apply_of_le (le_max_right _ _ : _ ≤ n)]
  simp_rw [Polynomial.map_sum, iterate_derivative_map p f]

theorem sumIDeriv_derivative (p : R[X]) : sumIDeriv (derivative p) = derivative (sumIDeriv p) := by
  rw [sumIDeriv_apply_of_le ((natDegree_derivative_le p).trans tsub_le_self), sumIDeriv_apply,
    derivative_sum]
  simp_rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']

theorem sumIDeriv_eq_self_add (p : R[X]) : sumIDeriv p = p + derivative (sumIDeriv p) := by
  rw [sumIDeriv_apply, derivative_sum, sum_range_succ', sum_range_succ,
    add_comm, ← add_zero (Finset.sum _ _)]
  simp_rw [← Function.iterate_succ_apply' derivative, Nat.succ_eq_add_one,
    Function.iterate_zero_apply, iterate_derivative_eq_zero (Nat.lt_succ_self _)]

theorem exists_iterate_derivative_eq_factorial_smul (p : R[X]) (k : ℕ) :
    ∃ gp : R[X], gp.natDegree ≤ p.natDegree - k ∧ derivative^[k] p = k ! • gp := by
  refine ⟨_, (natDegree_sum_le _ _).trans ?_, iterate_derivative_eq_factorial_smul_sum p k⟩
  rw [fold_max_le]
  refine ⟨Nat.zero_le _, fun i hi => ?_⟩
  dsimp only [Function.comp]
  exact (natDegree_C_mul_le _ _).trans <| (natDegree_X_pow_le _).trans <|
    (le_natDegree_of_mem_supp _ hi).trans <| natDegree_iterate_derivative _ _

end Semiring

section CommSemiring

variable [CommSemiring R] {A : Type*} [CommRing A] [Algebra R A]

theorem aeval_iterate_derivative_of_lt (p : R[X]) (q : ℕ) (r : A) {p' : A[X]}
    (hp : p.map (algebraMap R A) = (X - C r) ^ q * p') {k : ℕ} (hk : k < q) :
    aeval r (derivative^[k] p) = 0 := by
  have h (x) : (X - C r) ^ (q - (k - x)) = (X - C r) ^ 1 * (X - C r) ^ (q - (k - x) - 1) := by
    rw [← pow_add, add_tsub_cancel_of_le]
    rw [Nat.lt_iff_add_one_le] at hk
    exact (le_tsub_of_add_le_left hk).trans (tsub_le_tsub_left (tsub_le_self : _ ≤ k) _)
  rw [aeval_def, eval₂_eq_eval_map, ← iterate_derivative_map]
  simp_rw [hp, iterate_derivative_mul, iterate_derivative_X_sub_pow, ← smul_mul_assoc, smul_smul,
    h, ← mul_smul_comm, mul_assoc, ← mul_sum, eval_mul, pow_one, eval_sub, eval_X, eval_C, sub_self,
    zero_mul]

theorem aeval_iterate_derivative_self (p : R[X]) (q : ℕ) (r : A) {p' : A[X]}
    (hp : p.map (algebraMap R A) = (X - C r) ^ q * p') :
    aeval r (derivative^[q] p) = q ! • p'.eval r := by
  have h (x) (h : 1 ≤ x) (h' : x ≤ q) :
      (X - C r) ^ (q - (q - x)) = (X - C r) ^ 1 * (X - C r) ^ (q - (q - x) - 1) := by
    rw [← pow_add, add_tsub_cancel_of_le]
    rwa [tsub_tsub_cancel_of_le h']
  rw [aeval_def, eval₂_eq_eval_map, ← iterate_derivative_map]
  simp_rw [hp, iterate_derivative_mul, iterate_derivative_X_sub_pow, ← smul_mul_assoc, smul_smul]
  rw [sum_range_succ', Nat.choose_zero_right, one_mul, tsub_zero, Nat.descFactorial_self, tsub_self,
    pow_zero, smul_mul_assoc, one_mul, Function.iterate_zero_apply, eval_add, eval_smul]
  convert zero_add _
  rw [eval_finset_sum]
  apply sum_eq_zero
  intro x hx
  rw [h (x + 1) le_add_self (Nat.add_one_le_iff.mpr (mem_range.mp hx)), pow_one,
    eval_mul, eval_smul, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
    smul_zero, zero_mul]

variable (A)

theorem aeval_iterate_derivative_of_ge (p : R[X]) (q : ℕ) {k : ℕ} (hk : q ≤ k) :
    ∃ gp : R[X], gp.natDegree ≤ p.natDegree - k ∧
      ∀ r : A, aeval r (derivative^[k] p) = q ! • aeval r gp := by
  obtain ⟨p', p'_le, hp'⟩ := exists_iterate_derivative_eq_factorial_smul p k
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨((q + k).descFactorial k : R[X]) * p', (natDegree_C_mul_le _ _).trans p'_le, fun r => ?_⟩
  simp_rw [hp', nsmul_eq_mul, map_mul, map_natCast, ← mul_assoc, ← Nat.cast_mul,
    Nat.add_descFactorial_eq_ascFactorial, Nat.factorial_mul_ascFactorial]

theorem aeval_sumIDeriv_eq_eval (p : R[X]) (r : A) :
    aeval r (sumIDeriv p) = eval r (sumIDeriv (map (algebraMap R A) p)) := by
  rw [aeval_def, eval, sumIDeriv_map, eval₂_map, RingHom.id_comp]

theorem aeval_sumIDeriv (p : R[X]) (q : ℕ) :
    ∃ gp : R[X], gp.natDegree ≤ p.natDegree - q ∧
      ∀ (r : A), (X - C r) ^ q ∣ p.map (algebraMap R A) →
        aeval r (sumIDeriv p) = q ! • aeval r gp := by
  have h (k) :
      ∃ gp : R[X], gp.natDegree ≤ p.natDegree - q ∧
        ∀ (r : A), (X - C r) ^ q ∣ p.map (algebraMap R A) →
          aeval r (derivative^[k] p) = q ! • aeval r gp := by
    cases lt_or_ge k q with
    | inl hk =>
      use 0
      rw [natDegree_zero]
      use Nat.zero_le _
      intro r ⟨p', hp⟩
      rw [map_zero, smul_zero, aeval_iterate_derivative_of_lt p q r hp hk]
    | inr hk =>
      obtain ⟨gp, gp_le, h⟩ := aeval_iterate_derivative_of_ge A p q hk
      exact ⟨gp, gp_le.trans (tsub_le_tsub_left hk _), fun r _ => h r⟩
  choose c h using h
  choose c_le hc using h
  refine ⟨(range (p.natDegree + 1)).sum c, ?_, ?_⟩
  · refine (natDegree_sum_le _ _).trans ?_
    rw [fold_max_le]
    exact ⟨Nat.zero_le _, fun i _ => c_le i⟩
  intro r ⟨p', hp⟩
  rw [sumIDeriv_apply, map_sum]; simp_rw [hc _ r ⟨_, hp⟩, map_sum, smul_sum]

theorem aeval_sumIDeriv_of_pos [Nontrivial A] [NoZeroDivisors A] (p : R[X]) {q : ℕ} (hq : 0 < q)
    (inj_amap : Function.Injective (algebraMap R A)) :
    ∃ gp : R[X], gp.natDegree ≤ p.natDegree - q ∧
      ∀ (r : A) {p' : A[X]},
        p.map (algebraMap R A) = (X - C r) ^ (q - 1) * p' →
        aeval r (sumIDeriv p) = (q - 1)! • p'.eval r + q ! • aeval r gp := by
  rcases eq_or_ne p 0 with (rfl | p0)
  · use 0
    rw [natDegree_zero]
    use Nat.zero_le _
    intro r p' hp
    rw [map_zero, map_zero, smul_zero, add_zero]
    rw [Polynomial.map_zero] at hp
    replace hp := (mul_eq_zero.mp hp.symm).resolve_left ?_
    · rw [hp, eval_zero, smul_zero]
    exact fun h => X_sub_C_ne_zero r (pow_eq_zero h)
  let c k := if hk : q ≤ k then (aeval_iterate_derivative_of_ge A p q hk).choose else 0
  have c_le (k) : (c k).natDegree ≤ p.natDegree - k := by
    dsimp only [c]
    split_ifs with h
    · exact (aeval_iterate_derivative_of_ge A p q h).choose_spec.1
    · rw [natDegree_zero]; exact Nat.zero_le _
  have hc (k) (hk : q ≤ k) : ∀ (r : A), aeval r (derivative^[k] p) = q ! • aeval r (c k) := by
    simp_rw [c, dif_pos hk]
    exact (aeval_iterate_derivative_of_ge A p q hk).choose_spec.2
  refine ⟨∑ x ∈ Ico q (p.natDegree + 1), c x, ?_, ?_⟩
  · refine (natDegree_sum_le _ _).trans ?_
    rw [fold_max_le]
    exact ⟨Nat.zero_le _, fun i hi => (c_le i).trans (tsub_le_tsub_left (mem_Ico.mp hi).1 _)⟩
  intro r p' hp
  have : range (p.natDegree + 1) = range q ∪ Ico q (p.natDegree + 1) := by
    rw [range_eq_Ico, Ico_union_Ico_eq_Ico hq.le]
    rw [← tsub_le_iff_right]
    calc
      q - 1 ≤ q - 1 + p'.natDegree := le_self_add
      _ = (p.map <| algebraMap R A).natDegree := by
        rw [hp, natDegree_mul, natDegree_pow, natDegree_X_sub_C, mul_one,
          ← Nat.sub_add_comm (Nat.one_le_of_lt hq)]
        · exact pow_ne_zero _ (X_sub_C_ne_zero r)
        · rintro rfl
          rw [mul_zero, Polynomial.map_eq_zero_iff inj_amap] at hp
          exact p0 hp
      _ ≤ p.natDegree := natDegree_map_le
  rw [← zero_add ((q - 1)! • p'.eval r)]
  rw [sumIDeriv_apply, map_sum, map_sum, this]
  have : range q = range (q - 1 + 1) := by rw [tsub_add_cancel_of_le (Nat.one_le_of_lt hq)]
  rw [sum_union, this, sum_range_succ]
  · congr 2
    · apply sum_eq_zero
      exact fun x hx => aeval_iterate_derivative_of_lt p _ r hp (mem_range.mp hx)
    · rw [← aeval_iterate_derivative_self _ _ _ hp]
    · rw [smul_sum, sum_congr rfl]
      intro k hk
      exact hc k (mem_Ico.mp hk).1 r
  · rw [range_eq_Ico, disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem]
    intro x hx
    rw [mem_inter, mem_Ico, mem_Ico] at hx
    exact hx.1.2.not_ge hx.2.1

end CommSemiring

theorem eval_sumIDeriv_of_pos
    [CommRing R] [Nontrivial R] [NoZeroDivisors R] (p : R[X]) {q : ℕ} (hq : 0 < q) :
    ∃ gp : R[X], gp.natDegree ≤ p.natDegree - q ∧
      ∀ (r : R) {p' : R[X]},
        p = ((X : R[X]) - C r) ^ (q - 1) * p' →
        eval r (sumIDeriv p) = (q - 1)! • p'.eval r + q ! • eval r gp := by
  simpa using aeval_sumIDeriv_of_pos R p hq Function.injective_id

end Polynomial
