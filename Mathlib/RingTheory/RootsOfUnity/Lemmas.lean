/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.FieldTheory.KummerExtension
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# More results on primitive roots of unity

(We put these in a separate file because of the `KummerExtension` import.)

Assume that `μ` is a primitive `n`th root of unity in an integral domain `R`. Then
$$ \prod_{k=1}^{n-1} (1 - \mu^k) = n \,; $$
see `IsPrimitiveRoot.prod_one_sub_pow_eq_order` and its variant
`IsPrimitiveRoot.prod_pow_sub_one_eq_order` in terms of `∏ (μ^k - 1)`.

We use this to deduce that `n` is divisible by `(μ - 1)^k` in `ℤ[μ] ⊆ R` when `k < n`.
-/

public section

variable {R : Type*} [CommRing R] [IsDomain R]

namespace IsPrimitiveRoot

open Finset Polynomial

/-- If `μ` is a primitive `n`th root of unity in `R`, then `∏(1≤k<n) (1-μ^k) = n`.
(Stated with `n+1` in place of `n` to avoid the condition `n ≠ 0`.) -/
lemma prod_one_sub_pow_eq_order {n : ℕ} {μ : R} (hμ : IsPrimitiveRoot μ (n + 1)) :
    ∏ k ∈ range n, (1 - μ ^ (k + 1)) = n + 1 := by
  have := X_pow_sub_C_eq_prod hμ n.zero_lt_succ (one_pow (n + 1))
  rw [C_1, ← mul_geom_sum, prod_range_succ', pow_zero, mul_one, mul_comm, eq_comm] at this
  replace this := mul_right_cancel₀ (Polynomial.X_sub_C_ne_zero 1) this
  apply_fun Polynomial.eval 1 at this
  simpa only [mul_one, map_pow, eval_prod, eval_sub, eval_X, eval_pow, eval_C, eval_geom_sum,
    one_pow, sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using this

/-- If `μ` is a primitive `n`th root of unity in `R`, then `(-1)^(n-1) * ∏(1≤k<n) (μ^k-1) = n`.
(Stated with `n+1` in place of `n` to avoid the condition `n ≠ 0`.) -/
lemma prod_pow_sub_one_eq_order {n : ℕ} {μ : R} (hμ : IsPrimitiveRoot μ (n + 1)) :
    (-1) ^ n * ∏ k ∈ range n, (μ ^ (k + 1) - 1) = n + 1 := by
  have : (-1 : R) ^ n = ∏ k ∈ range n, -1 := by rw [prod_const, card_range]
  simp only [this, ← prod_mul_distrib, neg_one_mul, neg_sub, ← prod_one_sub_pow_eq_order hμ]

open Algebra in
/-- If `μ` is a primitive `n`th root of unity in `R` and `k < n`, then `n` is divisible
by `(μ-1)^k` in `ℤ[μ] ⊆ R`. -/
lemma self_sub_one_pow_dvd_order {k n : ℕ} (hn : k < n) {μ : R} (hμ : IsPrimitiveRoot μ n) :
    ∃ z ∈ ℤ[μ], n = z * (μ - 1) ^ k := by
  let n' + 1 := n
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.le_of_lt_succ hn)
  have hdvd k : ∃ z ∈ ℤ[μ], μ ^ k - 1 = z * (μ - 1) := by
    refine ⟨(Finset.range k).sum (μ ^ ·), ?_, (geom_sum_mul μ k).symm⟩
    exact Subalgebra.sum_mem _ fun m _ ↦ Subalgebra.pow_mem _ (self_mem_adjoin_singleton _ μ) _
  let Z k := Classical.choose <| hdvd k
  have Zdef k : Z k ∈ ℤ[μ] ∧ μ ^ k - 1 = Z k * (μ - 1) :=
    Classical.choose_spec <| hdvd k
  refine ⟨(-1) ^ (m + k) * (∏ j ∈ range k, Z (j + 1)) * ∏ j ∈ Ico k (m + k), (μ ^ (j + 1) - 1),
    ?_, ?_⟩
  · apply Subalgebra.mul_mem
    · apply Subalgebra.mul_mem
      · exact Subalgebra.pow_mem _ (Subalgebra.neg_mem _ <| Subalgebra.one_mem _) _
      · exact Subalgebra.prod_mem _ fun _ _ ↦ (Zdef _).1
    · refine Subalgebra.prod_mem _ fun _ _ ↦ ?_
      apply Subalgebra.sub_mem
      · exact Subalgebra.pow_mem _ (self_mem_adjoin_singleton ℤ μ) _
      · exact Subalgebra.one_mem _
  · push_cast
    have := Nat.cast_add (R := R) m k ▸ hμ.prod_pow_sub_one_eq_order
    rw [← this, mul_assoc, mul_assoc]
    congr 1
    conv => enter [2, 2, 2]; rw [← card_range k]
    rw [← prod_range_mul_prod_Ico _ (Nat.le_add_left k m), mul_comm _ (_ ^ #_), ← mul_assoc,
      prod_mul_pow_card]
    conv => enter [2, 1, 2, j]; rw [← (Zdef _).2]

end IsPrimitiveRoot
