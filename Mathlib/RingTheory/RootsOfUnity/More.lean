/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# More results on primitive roots of unity

(We put these in a separate file because of the `KummerExtension` import.)

Assume that `μ` is a primitive `n`th root of unity in an integral domain `R`. Then
$$ \prod_{k=1}^{n-1} (1 - \mu^k) = n \,; $$
see `IsPrimitiveRoot.prod_one_sub_pow_eq_order` and its variant
`IsPrimitiveRoot.prod_pow_sub_one_eq_order` in terms of `∏ (μ^k - 1)`.

We use this to deduce that `n` is divisible by `(μ - 1)^k` in `ℤ[μ] ⊆ R` when `k < n`.
-/

/-- If `A` is an `R`-algebra and `μ : A`, then `μ^k-1` is divisible by `μ-1` in `R[μ] ⊆ A`. -/
lemma Algebra.adjoin.sub_one_dvd_pow_sub_one (R : Type*) {A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (μ : A) (k : ℕ) :
    ∃ z ∈ adjoin R {μ}, μ ^ k - 1 = z * (μ - 1) := by
  refine ⟨(Finset.range k).sum (μ ^ ·), ?_, (geom_sum_mul μ k).symm⟩
  exact Subalgebra.sum_mem _ fun m _ ↦ Subalgebra.pow_mem _ (self_mem_adjoin_singleton _ μ) _

variable {R : Type*} [CommRing R] [IsDomain R]

namespace IsPrimitiveRoot

open Finset Polynomial BigOperators

/-- If `μ` is a primitive `n`th root of unity in `R`, then `∏(1≤k<n) (1-μ^k) = n`. -/
lemma prod_one_sub_pow_eq_order {n : ℕ} (hn : n ≠ 0) {μ : R} (hμ : IsPrimitiveRoot μ n) :
    ∏ k ∈ range (n - 1), (1 - μ ^ (k + 1)) = n := by
  have := X_pow_sub_C_eq_prod hμ (Nat.pos_of_ne_zero hn) (one_pow n)
  have HH : (X ^ n - C 1 : R[X]) = (X - C 1) * (range n).sum (fun k ↦ X ^ k) :=
    (mul_geom_sum X n).symm
  rw [HH] at this; clear HH
  let m + 1 := n
  rw [prod_range_succ', pow_zero, mul_one, mul_comm, eq_comm] at this
  replace this := mul_right_cancel₀ (Polynomial.X_sub_C_ne_zero 1) this
  apply_fun Polynomial.eval 1 at this
  simpa only [Nat.cast_add, Nat.cast_one, mul_one, map_pow, eval_prod, eval_sub, eval_X, eval_pow,
    eval_C, eval_geom_sum, one_pow, sum_const, card_range, nsmul_eq_mul] using this

/-- If `μ` is a primitive `n`th root of unity in `R`, then `(-1)^(n-1) * ∏(1≤k<n) (μ^k-1) = n`. -/
lemma prod_pow_sub_one_eq_order {n : ℕ} (hn : n ≠ 0) {μ : R} (hμ : IsPrimitiveRoot μ n) :
    (-1) ^ (n - 1) * ∏ k ∈ range (n - 1), (μ ^ (k + 1) - 1) = n := by
  have : (-1 : R) ^ (n - 1) = ∏ k ∈ range (n - 1), -1 := by rw [prod_const, card_range]
  simp only [this, ← prod_mul_distrib, neg_one_mul, neg_sub, ← prod_one_sub_pow_eq_order hn hμ]

/-- If `μ` is a primitive `n`th root of unity in `R` and `k < n`, then `n` is divisible
by `(μ-1)^k` in `ℤ[μ] ⊆ R`. -/
lemma order_eq_mul_self_sub_one_pow {k n : ℕ} (hn : k < n) {μ : R} (hμ : IsPrimitiveRoot μ n) :
    ∃ z ∈ Algebra.adjoin ℤ {μ}, n = z * (μ - 1) ^ k := by
  have := hμ.prod_pow_sub_one_eq_order (k.zero_le.trans_lt hn).ne'
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + k + 1 := by
    simp only [add_assoc]
    exact Nat.exists_eq_add_of_le' hn
  simp only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one] at this
  let Z k := Classical.choose <| Algebra.adjoin.sub_one_dvd_pow_sub_one ℤ μ k
  have Zdef k : Z k ∈ Algebra.adjoin ℤ {μ} ∧ μ ^ k - 1 = Z k * (μ - 1) :=
    Classical.choose_spec <| Algebra.adjoin.sub_one_dvd_pow_sub_one ℤ μ k
  refine ⟨(-1) ^ (m + k) * (∏ j ∈ range k, Z (j + 1)) * ∏ j ∈ Ico k (m + k), (μ ^ (j + 1) - 1),
    ?_, ?_⟩
  · apply Subalgebra.mul_mem
    · apply Subalgebra.mul_mem
      · exact Subalgebra.pow_mem _ (Subalgebra.neg_mem _ <| Subalgebra.one_mem _) _
      · exact Subalgebra.prod_mem _ fun j _ ↦ (Zdef _).1
    · refine Subalgebra.prod_mem _ fun j _ ↦ ?_
      apply Subalgebra.sub_mem
      · exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ μ) _
      · exact Subalgebra.one_mem _
  · push_cast
    rw [← this, mul_assoc, mul_assoc]
    congr 1
    conv => enter [2, 2, 2]; rw [← card_range k]
    rw [← prod_range_mul_prod_Ico (fun j : ℕ ↦ μ ^ (j + 1) - 1) (Nat.le_add_left k m),
      mul_comm _ (_ ^ card _), ← mul_assoc, prod_mul_pow_card]
    conv => enter [2, 1, 2, j]; rw [← (Zdef _).2]
