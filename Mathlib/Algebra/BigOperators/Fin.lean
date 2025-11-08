/-
Copyright (c) 2020 Yury Kudryashov, Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Anne Baanen
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Big operators and `Fin`

Some results about products and sums over the type `Fin`.

The most important results are the induction formulas `Fin.prod_univ_castSucc`
and `Fin.prod_univ_succ`, and the formula `Fin.prod_const` for the product of a
constant function. These results have variants for sums instead of products.

## Main declarations

* `finFunctionFinEquiv`: An explicit equivalence between `Fin n → Fin m` and `Fin (m ^ n)`.
-/

assert_not_exists Field

open Finset

variable {ι M : Type*}

namespace Finset

@[to_additive]
theorem prod_range [CommMonoid M] {n : ℕ} (f : ℕ → M) :
    ∏ i ∈ Finset.range n, f i = ∏ i : Fin n, f i :=
  (Fin.prod_univ_eq_prod_range _ _).symm

end Finset

namespace Fin

section CommMonoid

variable [CommMonoid M] {n : ℕ}

@[to_additive]
theorem prod_ofFn (f : Fin n → M) : (List.ofFn f).prod = ∏ i, f i := by
  simp [prod_eq_multiset_prod]

@[to_additive]
theorem prod_univ_def (f : Fin n → M) : ∏ i, f i = ((List.finRange n).map f).prod := by
  rw [← List.ofFn_eq_map, prod_ofFn]

/-- A product of a function `f : Fin 0 → M` is `1` because `Fin 0` is empty -/
@[to_additive /-- A sum of a function `f : Fin 0 → M` is `0` because `Fin 0` is empty -/]
theorem prod_univ_zero (f : Fin 0 → M) : ∏ i, f i = 1 :=
  rfl

/-- A product of a function `f : Fin (n + 1) → M` over all `Fin (n + 1)`
is the product of `f x`, for some `x : Fin (n + 1)` times the remaining product -/
@[to_additive /-- A sum of a function `f : Fin (n + 1) → M` over all `Fin (n + 1)` is the sum of
`f x`, for some `x : Fin (n + 1)` plus the remaining sum -/]
theorem prod_univ_succAbove (f : Fin (n + 1) → M) (x : Fin (n + 1)) :
    ∏ i, f i = f x * ∏ i : Fin n, f (x.succAbove i) := by
  rw [univ_succAbove n x, prod_cons, Finset.prod_map, coe_succAboveEmb]

/-- A product of a function `f : Fin (n + 1) → M` over all `Fin (n + 1)`
is the product of `f 0` times the remaining product -/
@[to_additive /-- A sum of a function `f : Fin (n + 1) → M` over all `Fin (n + 1)` is the sum of
`f 0` plus the remaining sum -/]
theorem prod_univ_succ (f : Fin (n + 1) → M) :
    ∏ i, f i = f 0 * ∏ i : Fin n, f i.succ :=
  prod_univ_succAbove f 0

/-- A product of a function `f : Fin (n + 1) → M` over all `Fin (n + 1)`
is the product of `f (Fin.last n)` times the remaining product -/
@[to_additive /-- A sum of a function `f : Fin (n + 1) → M` over all `Fin (n + 1)` is the sum of
`f (Fin.last n)` plus the remaining sum -/]
theorem prod_univ_castSucc (f : Fin (n + 1) → M) :
    ∏ i, f i = (∏ i : Fin n, f (Fin.castSucc i)) * f (last n) := by
  simpa [mul_comm] using prod_univ_succAbove f (last n)

@[to_additive (attr := simp)]
theorem prod_univ_getElem (l : List M) : ∏ i : Fin l.length, l[i.1] = l.prod := by
  simp [Finset.prod_eq_multiset_prod]

@[to_additive (attr := simp)]
theorem prod_univ_fun_getElem (l : List ι) (f : ι → M) :
    ∏ i : Fin l.length, f l[i.1] = (l.map f).prod := by
  simp [Finset.prod_eq_multiset_prod]

@[to_additive (attr := simp)]
theorem prod_cons (x : M) (f : Fin n → M) :
    (∏ i : Fin n.succ, (cons x f : Fin n.succ → M) i) = x * ∏ i : Fin n, f i := by
  simp_rw [prod_univ_succ, cons_zero, cons_succ]

@[to_additive (attr := simp)]
theorem prod_snoc (x : M) (f : Fin n → M) :
    (∏ i : Fin n.succ, (snoc f x : Fin n.succ → M) i) = (∏ i : Fin n, f i) * x := by
  simp [prod_univ_castSucc]

@[to_additive sum_univ_one]
theorem prod_univ_one (f : Fin 1 → M) : ∏ i, f i = f 0 := by simp

@[to_additive (attr := simp)]
theorem prod_univ_two (f : Fin 2 → M) : ∏ i, f i = f 0 * f 1 := by
  simp [prod_univ_succ]

@[to_additive]
theorem prod_univ_two' (f : ι → M) (a b : ι) : ∏ i, f (![a, b] i) = f a * f b :=
  prod_univ_two _

@[to_additive]
theorem prod_univ_three (f : Fin 3 → M) : ∏ i, f i = f 0 * f 1 * f 2 := by
  rw [prod_univ_castSucc, prod_univ_two]
  rfl

@[to_additive]
theorem prod_univ_four (f : Fin 4 → M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 := by
  rw [prod_univ_castSucc, prod_univ_three]
  rfl

@[to_additive]
theorem prod_univ_five (f : Fin 5 → M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 := by
  rw [prod_univ_castSucc, prod_univ_four]
  rfl

@[to_additive]
theorem prod_univ_six (f : Fin 6 → M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 := by
  rw [prod_univ_castSucc, prod_univ_five]
  rfl

@[to_additive]
theorem prod_univ_seven (f : Fin 7 → M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 := by
  rw [prod_univ_castSucc, prod_univ_six]
  rfl

@[to_additive]
theorem prod_univ_eight (f : Fin 8 → M) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 := by
  rw [prod_univ_castSucc, prod_univ_seven]
  rfl

@[to_additive]
theorem prod_const (n : ℕ) (x : M) : ∏ _i : Fin n, x = x ^ n := by simp

@[to_additive]
theorem prod_congr' {a b : ℕ} (f : Fin b → M) (h : a = b) :
    (∏ i : Fin a, f (i.cast h)) = ∏ i : Fin b, f i := by
  subst h
  congr

@[to_additive]
theorem prod_univ_add {a b : ℕ} (f : Fin (a + b) → M) :
    (∏ i : Fin (a + b), f i) = (∏ i : Fin a, f (castAdd b i)) * ∏ i : Fin b, f (natAdd a i) := by
  rw [Fintype.prod_equiv finSumFinEquiv.symm f fun i => f (finSumFinEquiv.toFun i)]
  · apply Fintype.prod_sum_type
  · intro x
    simp only [Equiv.toFun_as_coe, Equiv.apply_symm_apply]

@[to_additive]
theorem prod_trunc {a b : ℕ} (f : Fin (a + b) → M) (hf : ∀ j : Fin b, f (natAdd a j) = 1) :
    (∏ i : Fin (a + b), f i) = ∏ i : Fin a, f (castAdd b i) := by
  rw [prod_univ_add, Fintype.prod_eq_one _ hf, mul_one]

/-!
### Products over intervals: `Fin.cast`
-/

section cast

variable {m : ℕ}

@[to_additive]
theorem prod_Icc_cast (h : n = m) (f : Fin m → M) (a b : Fin n) :
    ∏ i ∈ Icc (a.cast h) (b.cast h), f i = ∏ i ∈ Icc a b, f (i.cast h) := by
  simp [← map_finCongr_Icc]

@[to_additive]
theorem prod_Ico_cast (h : n = m) (f : Fin m → M) (a b : Fin n) :
    ∏ i ∈ Ico (a.cast h) (b.cast h), f i = ∏ i ∈ Ico a b, f (i.cast h) := by
  simp [← map_finCongr_Ico]

@[to_additive]
theorem prod_Ioc_cast (h : n = m) (f : Fin m → M) (a b : Fin n) :
    ∏ i ∈ Ioc (a.cast h) (b.cast h), f i = ∏ i ∈ Ioc a b, f (i.cast h) := by
  simp [← map_finCongr_Ioc]

@[to_additive]
theorem prod_Ioo_cast (h : n = m) (f : Fin m → M) (a b : Fin n) :
    ∏ i ∈ Ioo (a.cast h) (b.cast h), f i = ∏ i ∈ Ioo a b, f (i.cast h) := by
  simp [← map_finCongr_Ioo]

@[to_additive]
theorem prod_uIcc_cast (h : n = m) (f : Fin m → M) (a b : Fin n) :
    ∏ i ∈ uIcc (a.cast h) (b.cast h), f i = ∏ i ∈ uIcc a b, f (i.cast h) := by
  simp [← map_finCongr_uIcc]

@[to_additive]
theorem prod_Ici_cast (h : n = m) (f : Fin m → M) (a : Fin n) :
    ∏ i ≥ a.cast h, f i = ∏ i ≥ a, f (i.cast h) := by
  simp [← map_finCongr_Ici]

@[to_additive]
theorem prod_Ioi_cast (h : n = m) (f : Fin m → M) (a : Fin n) :
    ∏ i > a.cast h, f i = ∏ i > a, f (i.cast h) := by
  simp [← map_finCongr_Ioi]

@[to_additive]
theorem prod_Iic_cast (h : n = m) (f : Fin m → M) (a : Fin n) :
    ∏ i ≤ a.cast h, f i = ∏ i ≤ a, f (i.cast h) := by
  simp [← map_finCongr_Iic]

@[to_additive]
theorem prod_Iio_cast (h : n = m) (f : Fin m → M) (a : Fin n) :
    ∏ i < a.cast h, f i = ∏ i < a, f (i.cast h) := by
  simp [← map_finCongr_Iio]

end cast

/-!
### Products over intervals: `Fin.castLE`
-/

section castLE

variable {m : ℕ}

@[to_additive]
theorem prod_Icc_castLE (h : n ≤ m) (f : Fin m → M) (a b : Fin n) :
    ∏ i ∈ Icc (a.castLE h) (b.castLE h), f i = ∏ i ∈ Icc a b, f (i.castLE h) := by
  simp [← map_castLEEmb_Icc]

@[to_additive]
theorem prod_Ico_castLE (h : n ≤ m) (f : Fin m → M) (a b : Fin n) :
    ∏ i ∈ Ico (a.castLE h) (b.castLE h), f i = ∏ i ∈ Ico a b, f (i.castLE h) := by
  simp [← map_castLEEmb_Ico]

@[to_additive]
theorem prod_Ioc_castLE (h : n ≤ m) (f : Fin m → M) (a b : Fin n) :
    ∏ i ∈ Ioc (a.castLE h) (b.castLE h), f i = ∏ i ∈ Ioc a b, f (i.castLE h) := by
  simp [← map_castLEEmb_Ioc]

@[to_additive]
theorem prod_Ioo_castLE (h : n ≤ m) (f : Fin m → M) (a b : Fin n) :
    ∏ i ∈ Ioo (a.castLE h) (b.castLE h), f i = ∏ i ∈ Ioo a b, f (i.castLE h) := by
  simp [← map_castLEEmb_Ioo]

@[to_additive]
theorem prod_uIcc_castLE (h : n ≤ m) (f : Fin m → M) (a b : Fin n) :
    ∏ i ∈ uIcc (a.castLE h) (b.castLE h), f i = ∏ i ∈ uIcc a b, f (i.castLE h) := by
  simp [← map_castLEEmb_uIcc]

@[to_additive]
theorem prod_Iic_castLE (h : n ≤ m) (f : Fin m → M) (a : Fin n) :
    ∏ i ≤ a.castLE h, f i = ∏ i ≤ a, f (i.castLE h) := by
  simp [← map_castLEEmb_Iic]

@[to_additive]
theorem prod_Iio_castLE (h : n ≤ m) (f : Fin m → M) (a : Fin n) :
    ∏ i < a.castLE h, f i = ∏ i < a, f (i.castLE h) := by
  simp [← map_castLEEmb_Iio]

end castLE

/-!
### Products over intervals: `Fin.castAdd`
-/

section castAdd

@[to_additive]
theorem prod_Icc_castAdd (m : ℕ) (f : Fin (n + m) → M) (a b : Fin n) :
    ∏ i ∈ Icc (a.castAdd m) (b.castAdd m), f i = ∏ i ∈ Icc a b, f (i.castAdd m) := by
  simp [← map_castAddEmb_Icc]

@[to_additive]
theorem prod_Ico_castAdd (m : ℕ) (f : Fin (n + m) → M) (a b : Fin n) :
    ∏ i ∈ Ico (a.castAdd m) (b.castAdd m), f i = ∏ i ∈ Ico a b, f (i.castAdd m) := by
  simp [← map_castAddEmb_Ico]

@[to_additive]
theorem prod_Ioc_castAdd (m : ℕ) (f : Fin (n + m) → M) (a b : Fin n) :
    ∏ i ∈ Ioc (a.castAdd m) (b.castAdd m), f i = ∏ i ∈ Ioc a b, f (i.castAdd m) := by
  simp [← map_castAddEmb_Ioc]

@[to_additive]
theorem prod_Ioo_castAdd (m : ℕ) (f : Fin (n + m) → M) (a b : Fin n) :
    ∏ i ∈ Ioo (a.castAdd m) (b.castAdd m), f i = ∏ i ∈ Ioo a b, f (i.castAdd m) := by
  simp [← map_castAddEmb_Ioo]

@[to_additive]
theorem prod_uIcc_castAdd (m : ℕ) (f : Fin (n + m) → M) (a b : Fin n) :
    ∏ i ∈ uIcc (a.castAdd m) (b.castAdd m), f i = ∏ i ∈ uIcc a b, f (i.castAdd m) := by
  simp [← map_castAddEmb_uIcc]

@[to_additive]
theorem prod_Iic_castAdd (m : ℕ) (f : Fin (n + m) → M) (a : Fin n) :
    ∏ i ≤ a.castAdd m, f i = ∏ i ≤ a, f (i.castAdd m) := by
  simp [← map_castAddEmb_Iic]

@[to_additive]
theorem prod_Iio_castAdd (m : ℕ) (f : Fin (n + m) → M) (a : Fin n) :
    ∏ i < a.castAdd m, f i = ∏ i < a, f (i.castAdd m) := by
  simp [← map_castAddEmb_Iio]

end castAdd

/-!
### Products over intervals: `Fin.castSucc`
-/

section castSucc

@[to_additive]
theorem prod_Icc_castSucc (f : Fin (n + 1) → M) (a b : Fin n) :
    ∏ i ∈ Icc a.castSucc b.castSucc, f i = ∏ i ∈ Icc a b, f i.castSucc := by
  simp [← map_castSuccEmb_Icc]

@[to_additive]
theorem prod_Ico_castSucc (f : Fin (n + 1) → M) (a b : Fin n) :
    ∏ i ∈ Ico a.castSucc b.castSucc, f i = ∏ i ∈ Ico a b, f i.castSucc := by
  simp [← map_castSuccEmb_Ico]

@[to_additive]
theorem prod_Ioc_castSucc (f : Fin (n + 1) → M) (a b : Fin n) :
    ∏ i ∈ Ioc a.castSucc b.castSucc, f i = ∏ i ∈ Ioc a b, f i.castSucc := by
  simp [← map_castSuccEmb_Ioc]

@[to_additive]
theorem prod_Ioo_castSucc (f : Fin (n + 1) → M) (a b : Fin n) :
    ∏ i ∈ Ioo a.castSucc b.castSucc, f i = ∏ i ∈ Ioo a b, f i.castSucc := by
  simp [← map_castSuccEmb_Ioo]

@[to_additive]
theorem prod_uIcc_castSucc (f : Fin (n + 1) → M) (a b : Fin n) :
    ∏ i ∈ uIcc a.castSucc b.castSucc, f i = ∏ i ∈ uIcc a b, f i.castSucc := by
  simp [← map_castSuccEmb_uIcc]

@[to_additive]
theorem prod_Iic_castSucc (f : Fin (n + 1) → M) (a : Fin n) :
    ∏ i ≤ a.castSucc, f i = ∏ i ≤ a, f i.castSucc := by
  simp [← map_castSuccEmb_Iic]

@[to_additive]
theorem prod_Iio_castSucc (f : Fin (n + 1) → M) (a : Fin n) :
    ∏ i < a.castSucc, f i = ∏ i < a, f i.castSucc := by
  simp [← map_castSuccEmb_Iio]

end castSucc

/-!
### Products over intervals: `Fin.succ`
-/

section succ

@[to_additive]
theorem prod_Icc_succ (f : Fin (n + 1) → M) (a b : Fin n) :
    ∏ i ∈ Icc a.succ b.succ, f i = ∏ i ∈ Icc a b, f i.succ := by
  simp [← map_succEmb_Icc]

@[to_additive]
theorem prod_Ico_succ (f : Fin (n + 1) → M) (a b : Fin n) :
    ∏ i ∈ Ico a.succ b.succ, f i = ∏ i ∈ Ico a b, f i.succ := by
  simp [← map_succEmb_Ico]

@[to_additive]
theorem prod_Ioc_succ (f : Fin (n + 1) → M) (a b : Fin n) :
    ∏ i ∈ Ioc a.succ b.succ, f i = ∏ i ∈ Ioc a b, f i.succ := by
  simp [← map_succEmb_Ioc]

@[to_additive]
theorem prod_Ioo_succ (f : Fin (n + 1) → M) (a b : Fin n) :
    ∏ i ∈ Ioo a.succ b.succ, f i = ∏ i ∈ Ioo a b, f i.succ := by
  simp [← map_succEmb_Ioo]

@[to_additive]
theorem prod_uIcc_succ (f : Fin (n + 1) → M) (a b : Fin n) :
    ∏ i ∈ uIcc a.succ b.succ, f i = ∏ i ∈ uIcc a b, f i.succ := by
  simp [← map_succEmb_uIcc]

@[to_additive]
theorem prod_Ici_succ (f : Fin (n + 1) → M) (a : Fin n) :
    ∏ i ≥ a.succ, f i = ∏ i ≥ a, f i.succ := by
  simp [← map_succEmb_Ici]

@[to_additive (attr := simp)]
theorem prod_Ioi_succ (f : Fin (n + 1) → M) (a : Fin n) :
    ∏ i > a.succ, f i = ∏ i > a, f i.succ := by
  simp [← map_succEmb_Ioi]

@[to_additive]
theorem prod_Ioi_zero (f : Fin (n + 1) → M) :
    ∏ i > 0, f i = ∏ j : Fin n, f j.succ := by
  simp [Ioi_zero_eq_map]

end succ

/-- The product of `g i j` over `i j : Fin (n + 1)`, `i ≠ j`,
is equal to the product of `g i j * g j i` over `i < j`.

The additive version of this lemma is useful for some proofs about differential forms.
In this application, the function has the signature `f : Fin (n + 1) → Fin n → M`,
where `f i j` means `g i (Fin.succAbove i j)` in the informal statements.

Similarly, the product of `g i j * g j i` over `i < j`
is written as `f (Fin.castSucc i) j * f (Fin.succ j) i` over `i j : Fin n`, `j ≥ i`.
-/
@[to_additive /-- The sum of `g i j` over `i j : Fin (n + 1)`, `i ≠ j`,
is equal to the sum of `g i j + g j i` over `i < j`.

This lemma is useful for some proofs about differential forms.
In this application, the function has the signature `f : Fin (n + 1) → Fin n → M`,
where `f i j` means `g i (Fin.succAbove i j)` in the informal statements.

Similarly, the sum of `g i j + g j i` over `i < j`
is written as `f (Fin.castSucc i) j + f (Fin.succ j) i` over `i j : Fin n`, `j ≥ i`.
-/]
theorem prod_prod_eq_prod_triangle_mul (f : Fin (n + 1) → Fin n → M) :
    ∏ i, ∏ j, f i j = ∏ i : Fin n, ∏ j ≥ i, (f i.castSucc j * f j.succ i) := calc
  _ = (∏ i, ∏ j with i ≤ j.castSucc, f i j) * ∏ i, ∏ j with j.castSucc < i, f i j := by
    simp only [← Finset.prod_mul_distrib, ← not_le, Finset.prod_filter_mul_prod_filter_not]
  _ = (∏ i, ∏ j ≥ i, f i.castSucc j) * ∏ i, ∏ j ≤ i, f i.succ j := by
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_succ]
    simp [Finset.filter_le_eq_Ici, Finset.filter_ge_eq_Iic]
  _ = (∏ i, ∏ j ≥ i, f i.castSucc j) * ∏ i, ∏ j ≥ i, f j.succ i := by
    congr 1
    apply Finset.prod_comm'
    simp
  _ = ∏ i : Fin n, ∏ j ≥ i, (f i.castSucc j * f j.succ i) := by
    simp only [Finset.prod_mul_distrib]

end CommMonoid

theorem sum_pow_mul_eq_add_pow {n : ℕ} {R : Type*} [CommSemiring R] (a b : R) :
    (∑ s : Finset (Fin n), a ^ s.card * b ^ (n - s.card)) = (a + b) ^ n := by
  simpa using Fintype.sum_pow_mul_eq_add_pow (Fin n) a b

lemma sum_neg_one_pow (R : Type*) [Ring R] (m : ℕ) :
    (∑ n : Fin m, (-1) ^ n.1 : R) = if Even m then 0 else 1 := by
  induction m with
  | zero => simp
  | succ n IH =>
    simp only [Fin.sum_univ_castSucc, Fin.coe_castSucc, IH, Fin.val_last, Nat.even_add_one, ite_not]
    split_ifs with h
    · simp [*]
    · simp [(Nat.not_even_iff_odd.mp h).neg_pow]

section PartialProd

variable [Monoid M] {n : ℕ}

/-- For `f = (a₁, ..., aₙ)` in `αⁿ`, `partialProd f` is `(1, a₁, a₁a₂, ..., a₁...aₙ)` in `αⁿ⁺¹`. -/
@[to_additive /-- For `f = (a₁, ..., aₙ)` in `αⁿ`, `partialSum f` is
`(0, a₁, a₁ + a₂, ..., a₁ + ... + aₙ)` in `αⁿ⁺¹`. -/]
def partialProd (f : Fin n → M) (i : Fin (n + 1)) : M :=
  ((List.ofFn f).take i).prod

@[to_additive (attr := simp)]
theorem partialProd_zero (f : Fin n → M) : partialProd f 0 = 1 := by simp [partialProd]

@[to_additive]
theorem partialProd_succ (f : Fin n → M) (j : Fin n) :
    partialProd f j.succ = partialProd f (Fin.castSucc j) * f j := by
  simp [partialProd, List.take_succ]

@[to_additive]
theorem partialProd_succ' (f : Fin (n + 1) → M) (j : Fin (n + 1)) :
    partialProd f j.succ = f 0 * partialProd (Fin.tail f) j := by
  simp [partialProd]
  rfl

@[to_additive]
lemma partialProd_init {f : Fin (n + 1) → M} (i : Fin (n + 1)) :
    partialProd (init f) i = partialProd f i.castSucc :=
  i.inductionOn (by simp) fun i hi => by simp_all [init, partialProd_succ]

@[to_additive]
theorem partialProd_left_inv {G : Type*} [Group G] (f : Fin (n + 1) → G) :
    (f 0 • partialProd fun i : Fin n => (f i.castSucc)⁻¹ * f i.succ) = f :=
  funext fun x => Fin.inductionOn x (by simp) fun x hx => by
    simp only [Pi.smul_apply, smul_eq_mul] at hx ⊢
    rw [partialProd_succ, ← mul_assoc, hx, mul_inv_cancel_left]

@[to_additive]
theorem partialProd_right_inv {G : Type*} [Group G] (f : Fin n → G) (i : Fin n) :
    (partialProd f (Fin.castSucc i))⁻¹ * partialProd f i.succ = f i := by
  rw [partialProd_succ, inv_mul_cancel_left]

@[to_additive]
lemma partialProd_contractNth {G : Type*} [Monoid G] {n : ℕ}
    (g : Fin (n + 1) → G) (a : Fin (n + 1)) :
    partialProd (contractNth a (· * ·) g) = partialProd g ∘ a.succ.succAbove := by
  ext i
  refine inductionOn i ?_ ?_
  · simp only [partialProd_zero, Function.comp_apply, succ_succAbove_zero]
  · intro i hi
    simp only [Function.comp_apply, succ_succAbove_succ] at *
    rw [partialProd_succ, partialProd_succ, hi]
    rcases lt_trichotomy (i : ℕ) a with (h | h | h)
    · rw [succAbove_of_castSucc_lt, contractNth_apply_of_lt _ _ _ _ h,
        succAbove_of_castSucc_lt] <;>
      simp only [lt_def, coe_castSucc, val_succ] <;>
      omega
    · rw [succAbove_of_castSucc_lt, contractNth_apply_of_eq _ _ _ _ h,
        succAbove_of_le_castSucc, castSucc_fin_succ, partialProd_succ, mul_assoc] <;>
      simp only [castSucc_lt_succ_iff, le_def, coe_castSucc] <;>
      omega
    · rw [succAbove_of_le_castSucc, succAbove_of_le_castSucc, contractNth_apply_of_gt _ _ _ _ h,
        castSucc_fin_succ] <;>
      simp only [le_def, val_succ, coe_castSucc] <;>
      omega

/-- Let `(g₀, g₁, ..., gₙ)` be a tuple of elements in `Gⁿ⁺¹`.
Then if `k < j`, this says `(g₀g₁...gₖ₋₁)⁻¹ * g₀g₁...gₖ = gₖ`.
If `k = j`, it says `(g₀g₁...gₖ₋₁)⁻¹ * g₀g₁...gₖ₊₁ = gₖgₖ₊₁`.
If `k > j`, it says `(g₀g₁...gₖ)⁻¹ * g₀g₁...gₖ₊₁ = gₖ₊₁.`
Useful for defining group cohomology. -/
@[to_additive
      /-- Let `(g₀, g₁, ..., gₙ)` be a tuple of elements in `Gⁿ⁺¹`.
      Then if `k < j`, this says `-(g₀ + g₁ + ... + gₖ₋₁) + (g₀ + g₁ + ... + gₖ) = gₖ`.
      If `k = j`, it says `-(g₀ + g₁ + ... + gₖ₋₁) + (g₀ + g₁ + ... + gₖ₊₁) = gₖ + gₖ₊₁`.
      If `k > j`, it says `-(g₀ + g₁ + ... + gₖ) + (g₀ + g₁ + ... + gₖ₊₁) = gₖ₊₁.`
      Useful for defining group cohomology. -/]
theorem inv_partialProd_mul_eq_contractNth {G : Type*} [Group G] (g : Fin (n + 1) → G)
    (j : Fin (n + 1)) (k : Fin n) :
    (partialProd g (j.succ.succAbove (Fin.castSucc k)))⁻¹ * partialProd g (j.succAbove k).succ =
      j.contractNth (· * ·) g k := by
  rcases lt_trichotomy (k : ℕ) j with (h | h | h)
  · rwa [succAbove_of_castSucc_lt, succAbove_of_castSucc_lt, partialProd_right_inv,
    contractNth_apply_of_lt]
    · assumption
    · rw [castSucc_lt_iff_succ_le, succ_le_succ_iff, le_iff_val_le_val]
      exact le_of_lt h
  · rwa [succAbove_of_castSucc_lt, succAbove_of_le_castSucc, partialProd_succ,
    castSucc_fin_succ, ← mul_assoc,
      partialProd_right_inv, contractNth_apply_of_eq]
    · simp [le_iff_val_le_val, ← h]
    · rw [castSucc_lt_iff_succ_le, succ_le_succ_iff, le_iff_val_le_val]
      exact le_of_eq h
  · rwa [succAbove_of_le_castSucc, succAbove_of_le_castSucc, partialProd_succ, partialProd_succ,
      castSucc_fin_succ, partialProd_succ, inv_mul_cancel_left, contractNth_apply_of_gt]
    · exact le_iff_val_le_val.2 (le_of_lt h)
    · rw [le_iff_val_le_val, val_succ]
      exact Nat.succ_le_of_lt h

end PartialProd

end Fin

/-- Equivalence between `Fin n → Fin m` and `Fin (m ^ n)`. -/
@[simps!]
def finFunctionFinEquiv {m n : ℕ} : (Fin n → Fin m) ≃ Fin (m ^ n) :=
  Equiv.ofRightInverseOfCardLE (le_of_eq <| by simp_rw [Fintype.card_fun, Fintype.card_fin])
    (fun f => ⟨∑ i, f i * m ^ (i : ℕ), by
      induction n with
      | zero => simp
      | succ n ih =>
        cases m
        · exact isEmptyElim (f <| Fin.last _)
        simp_rw [Fin.sum_univ_castSucc, Fin.coe_castSucc, Fin.val_last]
        refine (Nat.add_lt_add_of_lt_of_le (ih _) <| Nat.mul_le_mul_right _
          (Fin.is_le _)).trans_eq ?_
        rw [← one_add_mul (_ : ℕ), add_comm, pow_succ']⟩)
    (fun a b => ⟨a / m ^ (b : ℕ) % m, by
      rcases n with - | n
      · exact b.elim0
      rcases m with - | m
      · rw [zero_pow n.succ_ne_zero] at a
        exact a.elim0
      · exact Nat.mod_lt _ m.succ_pos⟩)
    fun a => by
      dsimp
      induction n with
      | zero => subsingleton [(finCongr <| pow_zero _).subsingleton]
      | succ n ih =>
        simp_rw [Fin.forall_iff, Fin.ext_iff] at ih
        ext
        simp_rw [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero, Nat.div_one,
          mul_one, pow_succ', ← Nat.div_div_eq_div_mul, mul_left_comm _ m, ← mul_sum]
        rw [ih _ (Nat.div_lt_of_lt_mul (a.is_lt.trans_eq (pow_succ' _ _))), Nat.mod_add_div]

theorem finFunctionFinEquiv_apply {m n : ℕ} (f : Fin n → Fin m) :
    (finFunctionFinEquiv f : ℕ) = ∑ i : Fin n, ↑(f i) * m ^ (i : ℕ) :=
  rfl

theorem finFunctionFinEquiv_single {m n : ℕ} [NeZero m] (i : Fin n) (j : Fin m) :
    (finFunctionFinEquiv (Pi.single i j) : ℕ) = j * m ^ (i : ℕ) := by
  rw [finFunctionFinEquiv_apply, Fintype.sum_eq_single i, Pi.single_eq_same]
  rintro x hx
  rw [Pi.single_eq_of_ne hx, Fin.val_zero, zero_mul]

/-- Equivalence between `∀ i : Fin m, Fin (n i)` and `Fin (∏ i : Fin m, n i)`. -/
def finPiFinEquiv {m : ℕ} {n : Fin m → ℕ} : (∀ i : Fin m, Fin (n i)) ≃ Fin (∏ i : Fin m, n i) :=
  Equiv.ofRightInverseOfCardLE (le_of_eq <| by simp_rw [Fintype.card_pi, Fintype.card_fin])
    (fun f => ⟨∑ i, f i * ∏ j, n (Fin.castLE i.is_lt.le j), by
      induction m with
      | zero => simp
      | succ m ih =>
      rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
      suffices
        ∀ (n : Fin m → ℕ) (nn : ℕ) (f : ∀ i : Fin m, Fin (n i)) (fn : Fin nn),
          ((∑ i : Fin m, ↑(f i) * ∏ j : Fin i, n (Fin.castLE i.prop.le j)) + ↑fn * ∏ j, n j) <
            (∏ i : Fin m, n i) * nn by
        solve_by_elim
      intro n nn f fn
      cases nn
      · exact isEmptyElim fn
      refine (Nat.add_lt_add_of_lt_of_le (ih _) <| Nat.mul_le_mul_right _ (Fin.is_le _)).trans_eq ?_
      rw [← one_add_mul (_ : ℕ), mul_comm, add_comm]⟩)
    (fun a b => ⟨(a / ∏ j : Fin b, n (Fin.castLE b.is_lt.le j)) % n b, by
      cases m
      · exact b.elim0
      rcases h : n b with nb | nb
      · rw [prod_eq_zero (Finset.mem_univ _) h] at a
        exact isEmptyElim a
      exact Nat.mod_lt _ nb.succ_pos⟩)
    (by
      intro a; revert a; dsimp only [Fin.val_mk]
      refine Fin.consInduction ?_ ?_ n
      · intro a
        have : Subsingleton (Fin (∏ i : Fin 0, i.elim0)) :=
          (finCongr <| prod_empty).subsingleton
        subsingleton
      · intro n x xs ih a
        simp_rw [Fin.forall_iff, Fin.ext_iff] at ih
        ext
        simp_rw [Fin.sum_univ_succ, Fin.cons_succ]
        have := fun i : Fin n =>
          Fintype.prod_equiv (finCongr <| Fin.val_succ i)
            (fun j => (Fin.cons x xs : _ → ℕ) (Fin.castLE (Fin.is_lt _).le j))
            (fun j => (Fin.cons x xs : _ → ℕ) (Fin.castLE (Nat.succ_le_succ (Fin.is_lt _).le) j))
            fun j => rfl
        simp_rw [this]
        clear this
        simp_rw [Fin.val_zero, Fintype.prod_empty, Nat.div_one, mul_one, Fin.cons_zero,
          Fin.prod_univ_succ, Fin.castLE_zero, Fin.cons_zero, ← Nat.div_div_eq_div_mul,
          mul_left_comm (_ % _ : ℕ), ← mul_sum]
        convert Nat.mod_add_div _ _
        exact ih (a / x) (Nat.div_lt_of_lt_mul <| a.is_lt.trans_eq (Fin.prod_univ_succ _)))

theorem finPiFinEquiv_apply {m : ℕ} {n : Fin m → ℕ} (f : ∀ i : Fin m, Fin (n i)) :
    (finPiFinEquiv f : ℕ) = ∑ i, f i * ∏ j, n (Fin.castLE i.is_lt.le j) := rfl

theorem finPiFinEquiv_single {m : ℕ} {n : Fin m → ℕ} [∀ i, NeZero (n i)] (i : Fin m)
    (j : Fin (n i)) :
    (finPiFinEquiv (Pi.single i j : ∀ i : Fin m, Fin (n i)) : ℕ) =
      j * ∏ j, n (Fin.castLE i.is_lt.le j) := by
  rw [finPiFinEquiv_apply, Fintype.sum_eq_single i, Pi.single_eq_same]
  rintro x hx
  rw [Pi.single_eq_of_ne hx, Fin.val_zero, zero_mul]

/-- Equivalence between the Sigma type `(i : Fin m) × Fin (n i)` and `Fin (∑ i : Fin m, n i)`. -/
def finSigmaFinEquiv {m : ℕ} {n : Fin m → ℕ} : (i : Fin m) × Fin (n i) ≃ Fin (∑ i : Fin m, n i) :=
  match m with
  | 0 => @Equiv.equivOfIsEmpty _ _ _ (by simpa using Fin.isEmpty')
  | Nat.succ m =>
    calc _ ≃ _ := (@finSumFinEquiv m 1).sigmaCongrLeft.symm
      _ ≃ _ := Equiv.sumSigmaDistrib _
      _ ≃ _ := finSigmaFinEquiv.sumCongr (Equiv.uniqueSigma _)
      _ ≃ _ := finSumFinEquiv
      _ ≃ _ := finCongr (Fin.sum_univ_castSucc n).symm

@[simp]
theorem finSigmaFinEquiv_apply {m : ℕ} {n : Fin m → ℕ} (k : (i : Fin m) × Fin (n i)) :
    (finSigmaFinEquiv k : ℕ) = ∑ i : Fin k.1, n (Fin.castLE k.1.2.le i) + k.2 := by
  induction m with
  | zero => exact k.fst.elim0
  | succ m ih =>
  rcases k with ⟨⟨iv, hi⟩, j⟩
  rw [finSigmaFinEquiv]
  unfold finSumFinEquiv
  simp only [Equiv.coe_fn_mk, Equiv.sigmaCongrLeft, Equiv.coe_fn_symm_mk, Equiv.trans_def,
    Equiv.trans_apply, finCongr_apply, Fin.coe_cast]
  by_cases him : iv < m
  · conv in Sigma.mk _ _ =>
      equals ⟨Sum.inl ⟨iv, him⟩, j⟩ => simp [Fin.addCases, him]
    simpa using ih _
  · replace him := Nat.eq_of_lt_succ_of_not_lt hi him
    subst him
    conv in Sigma.mk _ _ =>
      equals ⟨Sum.inr 0, j⟩ => simp [Fin.addCases, Fin.natAdd]
    simp
    rfl

/-- `finSigmaFinEquiv` on `Fin 1 × f` is just `f` -/
theorem finSigmaFinEquiv_one {n : Fin 1 → ℕ} (ij : (i : Fin 1) × Fin (n i)) :
    (finSigmaFinEquiv ij : ℕ) = ij.2 := by
  rw [finSigmaFinEquiv_apply, add_eq_right]
  apply @Finset.sum_of_isEmpty _ _ _ _ (by simpa using Fin.isEmpty')

namespace List

section CommMonoid

variable [CommMonoid M]

@[to_additive]
theorem prod_take_ofFn {n : ℕ} (f : Fin n → M) (i : ℕ) :
    ((ofFn f).take i).prod = ∏ j with j.val < i, f j := by
  induction i with
  | zero =>
    simp
  | succ i IH =>
    by_cases h : i < n
    · have : i < length (ofFn f) := by rwa [length_ofFn]
      rw [prod_take_succ _ _ this]
      have A : ({j | j.val < i + 1} : Finset (Fin n)) =
          insert ⟨i, h⟩ ({j | Fin.val j < i} : Finset (Fin n)) := by
        ext ⟨_, _⟩
        simp [Nat.lt_succ_iff_lt_or_eq, or_comm]
      rw [A, prod_insert (by simp), IH, mul_comm]
      simp
    · have A : (ofFn f).take i = (ofFn f).take i.succ := by
        rw [← length_ofFn (f := f)] at h
        have : length (ofFn f) ≤ i := not_lt.mp h
        rw [take_of_length_le this, take_of_length_le (le_trans this (Nat.le_succ _))]
      have B : ∀ j : Fin n, ((j : ℕ) < i.succ) = ((j : ℕ) < i) := by
        intro j
        have : (j : ℕ) < i := lt_of_lt_of_le j.2 (not_lt.mp h)
        simp [this, lt_trans this (Nat.lt_succ_self _)]
      simp [← A, B, IH]

@[to_additive]
theorem prod_ofFn {n : ℕ} {f : Fin n → M} : (ofFn f).prod = ∏ i, f i :=
  Fin.prod_ofFn f

end CommMonoid

@[to_additive]
theorem alternatingProd_eq_finset_prod {G : Type*} [DivisionCommMonoid G] :
    ∀ (L : List G), alternatingProd L = ∏ i : Fin L.length, L[i] ^ (-1 : ℤ) ^ (i : ℕ)
  | [] => by
    rw [alternatingProd, Finset.prod_eq_one]
    rintro ⟨i, ⟨⟩⟩
  | g::[] => by
    change g = ∏ i : Fin 1, [g][i] ^ (-1 : ℤ) ^ (i : ℕ)
    rw [Fin.prod_univ_succ]; simp
  | g::h::L =>
    calc g * h⁻¹ * L.alternatingProd
      = g * h⁻¹ * ∏ i : Fin L.length, L[i] ^ (-1 : ℤ) ^ (i : ℕ) :=
        congr_arg _ (alternatingProd_eq_finset_prod _)
    _ = ∏ i : Fin (L.length + 2), (g::h::L)[i] ^ (-1 : ℤ) ^ (i : ℕ) := by
        { rw [Fin.prod_univ_succ, Fin.prod_univ_succ, mul_assoc]
          simp [pow_add]}

end List
