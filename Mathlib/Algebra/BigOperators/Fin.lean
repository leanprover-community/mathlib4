/-
Copyright (c) 2020 Yury Kudryashov, Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Anne Baanen

! This file was ported from Lean 3 source module algebra.big_operators.fin
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin

/-!
# Big operators and `Fin`

Some results about products and sums over the type `Fin`.

The most important results are the induction formulas `Fin.prod_univ_castSucc`
and `Fin.prod_univ_succ`, and the formula `Fin.prod_const` for the product of a
constant function. These results have variants for sums instead of products.

-/

open BigOperators

open Finset

variable {α : Type _} {β : Type _}

namespace Finset

@[to_additive]
theorem prod_range [CommMonoid β] {n : ℕ} (f : ℕ → β) :
    (∏ i in Finset.range n, f i) = ∏ i : Fin n, f i :=
  prod_bij' (fun k w => ⟨k, mem_range.mp w⟩) (fun _ _ => mem_univ _)
    (fun _ _ => congr_arg _ (Fin.val_mk _).symm) (fun a _ => a) (fun a _ => mem_range.mpr a.prop)
    (fun _ _ => Fin.val_mk _) fun _ _ => Fin.eta _ _
#align finset.prod_range Finset.prod_range
#align finset.sum_range Finset.sum_range

end Finset

namespace Fin

@[to_additive]
theorem prod_univ_def [CommMonoid β] {n : ℕ} (f : Fin n → β) :
    (∏ i, f i) = ((List.finRange n).map f).prod := by simp [univ_def]
#align fin.prod_univ_def Fin.prod_univ_def
#align fin.sum_univ_def Fin.sum_univ_def

@[to_additive]
theorem prod_ofFn [CommMonoid β] {n : ℕ} (f : Fin n → β) : (List.ofFn f).prod = ∏ i, f i := by
  rw [List.ofFn_eq_map, prod_univ_def]
#align fin.prod_of_fn Fin.prod_ofFn
#align fin.sum_of_fn Fin.sum_ofFn

/-- A product of a function `f : Fin 0 → β` is `1` because `Fin 0` is empty -/
@[to_additive "A sum of a function `f : Fin 0 → β` is `0` because `Fin 0` is empty"]
theorem prod_univ_zero [CommMonoid β] (f : Fin 0 → β) : (∏ i, f i) = 1 :=
  rfl
#align fin.prod_univ_zero Fin.prod_univ_zero
#align fin.sum_univ_zero Fin.sum_univ_zero

/-- A product of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)`
is the product of `f x`, for some `x : Fin (n + 1)` times the remaining product -/
@[to_additive "A sum of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)` is the sum of
`f x`, for some `x : Fin (n + 1)` plus the remaining product"]
theorem prod_univ_succAbove [CommMonoid β] {n : ℕ} (f : Fin (n + 1) → β) (x : Fin (n + 1)) :
    (∏ i, f i) = f x * ∏ i : Fin n, f (x.succAbove i) := by
  rw [univ_succAbove, prod_cons, Finset.prod_map _ x.succAbove.toEmbedding,
    RelEmbedding.coe_toEmbedding]
#align fin.prod_univ_succ_above Fin.prod_univ_succAbove
#align fin.sum_univ_succ_above Fin.sum_univ_succAbove

/-- A product of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)`
is the product of `f 0` plus the remaining product -/
@[to_additive "A sum of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)` is the sum of
`f 0` plus the remaining product"]
theorem prod_univ_succ [CommMonoid β] {n : ℕ} (f : Fin (n + 1) → β) :
    (∏ i, f i) = f 0 * ∏ i : Fin n, f i.succ :=
  prod_univ_succAbove f 0
#align fin.prod_univ_succ Fin.prod_univ_succ
#align fin.sum_univ_succ Fin.sum_univ_succ

/-- A product of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)`
is the product of `f (Fin.last n)` plus the remaining product -/
@[to_additive "A sum of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)` is the sum of
`f (Fin.last n)` plus the remaining sum"]
theorem prod_univ_castSucc [CommMonoid β] {n : ℕ} (f : Fin (n + 1) → β) :
    (∏ i, f i) = (∏ i : Fin n, f (Fin.castSucc i)) * f (last n) := by
  simpa [mul_comm] using prod_univ_succAbove f (last n)
#align fin.prod_univ_cast_succ Fin.prod_univ_castSucc
#align fin.sum_univ_cast_succ Fin.sum_univ_castSucc

@[to_additive]
theorem prod_cons [CommMonoid β] {n : ℕ} (x : β) (f : Fin n → β) :
    (∏ i : Fin n.succ, (cons x f : Fin n.succ → β) i) = x * ∏ i : Fin n, f i := by
  simp_rw [prod_univ_succ, cons_zero, cons_succ]
#align fin.prod_cons Fin.prod_cons
#align fin.sum_cons Fin.sum_cons

@[to_additive sum_univ_one]
theorem prod_univ_one [CommMonoid β] (f : Fin 1 → β) : (∏ i, f i) = f 0 := by simp
#align fin.prod_univ_one Fin.prod_univ_one
#align fin.sum_univ_one Fin.sum_univ_one

@[to_additive (attr := simp)]
theorem prod_univ_two [CommMonoid β] (f : Fin 2 → β) : (∏ i, f i) = f 0 * f 1 := by
  simp [prod_univ_succ]
#align fin.prod_univ_two Fin.prod_univ_two
#align fin.sum_univ_two Fin.sum_univ_two

@[to_additive]
theorem prod_univ_three [CommMonoid β] (f : Fin 3 → β) : (∏ i, f i) = f 0 * f 1 * f 2 := by
  rw [prod_univ_castSucc, prod_univ_two]
  rfl
#align fin.prod_univ_three Fin.prod_univ_three
#align fin.sum_univ_three Fin.sum_univ_three

@[to_additive]
theorem prod_univ_four [CommMonoid β] (f : Fin 4 → β) : (∏ i, f i) = f 0 * f 1 * f 2 * f 3 := by
  rw [prod_univ_castSucc, prod_univ_three]
  rfl
#align fin.prod_univ_four Fin.prod_univ_four
#align fin.sum_univ_four Fin.sum_univ_four

@[to_additive]
theorem prod_univ_five [CommMonoid β] (f : Fin 5 → β) :
    (∏ i, f i) = f 0 * f 1 * f 2 * f 3 * f 4 := by
  rw [prod_univ_castSucc, prod_univ_four]
  rfl
#align fin.prod_univ_five Fin.prod_univ_five
#align fin.sum_univ_five Fin.sum_univ_five

@[to_additive]
theorem prod_univ_six [CommMonoid β] (f : Fin 6 → β) :
    (∏ i, f i) = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 := by
  rw [prod_univ_castSucc, prod_univ_five]
  rfl
#align fin.prod_univ_six Fin.prod_univ_six
#align fin.sum_univ_six Fin.sum_univ_six

@[to_additive]
theorem prod_univ_seven [CommMonoid β] (f : Fin 7 → β) :
    (∏ i, f i) = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 := by
  rw [prod_univ_castSucc, prod_univ_six]
  rfl
#align fin.prod_univ_seven Fin.prod_univ_seven
#align fin.sum_univ_seven Fin.sum_univ_seven

@[to_additive]
theorem prod_univ_eight [CommMonoid β] (f : Fin 8 → β) :
    (∏ i, f i) = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 := by
  rw [prod_univ_castSucc, prod_univ_seven]
  rfl
#align fin.prod_univ_eight Fin.prod_univ_eight
#align fin.sum_univ_eight Fin.sum_univ_eight

theorem sum_pow_mul_eq_add_pow {n : ℕ} {R : Type _} [CommSemiring R] (a b : R) :
    (∑ s : Finset (Fin n), a ^ s.card * b ^ (n - s.card)) = (a + b) ^ n := by
  simpa using Fintype.sum_pow_mul_eq_add_pow (Fin n) a b
#align fin.sum_pow_mul_eq_add_pow Fin.sum_pow_mul_eq_add_pow

theorem prod_const [CommMonoid α] (n : ℕ) (x : α) : (∏ _i : Fin n, x) = x ^ n := by simp
#align fin.prod_const Fin.prod_const

theorem sum_const [AddCommMonoid α] (n : ℕ) (x : α) : (∑ _i : Fin n, x) = n • x := by simp
#align fin.sum_const Fin.sum_const

@[to_additive]
theorem prod_Ioi_zero {M : Type _} [CommMonoid M] {n : ℕ} {v : Fin n.succ → M} :
    (∏ i in Ioi 0, v i) = ∏ j : Fin n, v j.succ := by
  rw [Ioi_zero_eq_map, Finset.prod_map, RelEmbedding.coe_toEmbedding, val_succEmbedding]
#align fin.prod_Ioi_zero Fin.prod_Ioi_zero
#align fin.sum_Ioi_zero Fin.sum_Ioi_zero

@[to_additive]
theorem prod_Ioi_succ {M : Type _} [CommMonoid M] {n : ℕ} (i : Fin n) (v : Fin n.succ → M) :
    (∏ j in Ioi i.succ, v j) = ∏ j in Ioi i, v j.succ := by
  rw [Ioi_succ, Finset.prod_map, RelEmbedding.coe_toEmbedding, val_succEmbedding]
#align fin.prod_Ioi_succ Fin.prod_Ioi_succ
#align fin.sum_Ioi_succ Fin.sum_Ioi_succ

@[to_additive]
theorem prod_congr' {M : Type _} [CommMonoid M] {a b : ℕ} (f : Fin b → M) (h : a = b) :
    (∏ i : Fin a, f (cast h i)) = ∏ i : Fin b, f i := by
  subst h
  congr
#align fin.prod_congr' Fin.prod_congr'
#align fin.sum_congr' Fin.sum_congr'

@[to_additive]
theorem prod_univ_add {M : Type _} [CommMonoid M] {a b : ℕ} (f : Fin (a + b) → M) :
    (∏ i : Fin (a + b), f i) = (∏ i : Fin a, f (castAdd b i)) * ∏ i : Fin b, f (natAdd a i) := by
  rw [Fintype.prod_equiv finSumFinEquiv.symm f fun i => f (finSumFinEquiv.toFun i)]
  · apply Fintype.prod_sum_type
  · intro x
    simp only [Equiv.toFun_as_coe, Equiv.apply_symm_apply]
#align fin.prod_univ_add Fin.prod_univ_add
#align fin.sum_univ_add Fin.sum_univ_add

@[to_additive]
theorem prod_trunc {M : Type _} [CommMonoid M] {a b : ℕ} (f : Fin (a + b) → M)
    (hf : ∀ j : Fin b, f (natAdd a j) = 1) :
    (∏ i : Fin (a + b), f i) = ∏ i : Fin a, f (castLE (Nat.le.intro rfl) i) := by
  rw [prod_univ_add, Fintype.prod_eq_one _ hf, mul_one]
  rfl
#align fin.prod_trunc Fin.prod_trunc
#align fin.sum_trunc Fin.sum_trunc

section PartialProd

variable [Monoid α] {n : ℕ}

/-- For `f = (a₁, ..., aₙ)` in `αⁿ`, `partialProd f` is `(1, a₁, a₁a₂, ..., a₁...aₙ)` in `αⁿ⁺¹`. -/
@[to_additive "For `f = (a₁, ..., aₙ)` in `αⁿ`, `partialSum f` is\n
`(0, a₁, a₁ + a₂, ..., a₁ + ... + aₙ)` in `αⁿ⁺¹`."]
def partialProd (f : Fin n → α) (i : Fin (n + 1)) : α :=
  ((List.ofFn f).take i).prod
#align fin.partial_prod Fin.partialProd
#align fin.partial_sum Fin.partialSum

@[to_additive (attr := simp)]
theorem partialProd_zero (f : Fin n → α) : partialProd f 0 = 1 := by simp [partialProd]
#align fin.partial_prod_zero Fin.partialProd_zero
#align fin.partial_sum_zero Fin.partialSum_zero

@[to_additive]
theorem partialProd_succ (f : Fin n → α) (j : Fin n) :
    partialProd f j.succ = partialProd f (Fin.castSucc j) * f j := by
  simp [partialProd, List.take_succ, List.ofFnNthVal, dif_pos j.is_lt, ← Option.coe_def]
#align fin.partial_prod_succ Fin.partialProd_succ
#align fin.partial_sum_succ Fin.partialSum_succ

@[to_additive]
theorem partialProd_succ' (f : Fin (n + 1) → α) (j : Fin (n + 1)) :
    partialProd f j.succ = f 0 * partialProd (Fin.tail f) j := by
  simp [partialProd]
  rfl
#align fin.partial_prod_succ' Fin.partialProd_succ'
#align fin.partial_sum_succ' Fin.partialSum_succ'

@[to_additive]
theorem partialProd_left_inv {G : Type _} [Group G] (f : Fin (n + 1) → G) :
    (f 0 • partialProd fun i : Fin n => (f i)⁻¹ * f i.succ) = f :=
  funext fun x => Fin.inductionOn x (by simp) fun x hx => by
    simp only [coe_eq_castSucc, Pi.smul_apply, smul_eq_mul] at hx⊢
    rw [partialProd_succ, ← mul_assoc, hx, mul_inv_cancel_left]
#align fin.partial_prod_left_inv Fin.partialProd_left_inv
#align fin.partial_sum_left_neg Fin.partialSum_left_neg

-- Porting note:
-- 1) Changed `i` in statement to `(Fin.castLT i (Nat.lt_succ_of_lt i.2))` because of
--    coercion issues. Might need to be fixed later.
-- 2) The current proof is really bad! It should be redone once `assoc_rw` is
--    implemented and `rw` knows that `i.succ = i + 1`.
-- 3) The original Mathport output was:
--   cases' i with i hn
--   induction' i with i hi generalizing hn
--   · simp [← Fin.succ_mk, partialProd_succ]
--   · specialize hi (lt_trans (Nat.lt_succ_self i) hn)
--     simp only [mul_inv_rev, Fin.coe_eq_castSucc, Fin.succ_mk, Fin.castSucc_mk, smul_eq_mul,
--       Pi.smul_apply] at hi ⊢
--     rw [← Fin.succ_mk _ _ (lt_trans (Nat.lt_succ_self _) hn), ← Fin.succ_mk]
--     simp only [partialProd_succ, mul_inv_rev, Fin.castSucc_mk]
--     assoc_rw [hi, inv_mul_cancel_left]
@[to_additive]
theorem partialProd_right_inv {G : Type _} [Group G] (g : G) (f : Fin n → G) (i : Fin n) :
    ((g • partialProd f) (Fin.castLT i (Nat.lt_succ_of_lt i.2)))⁻¹ *
    (g • partialProd f) i.succ = f i := by
  rcases i with ⟨i, hn⟩
  induction i with
  | zero =>
    simp
    change partialProd f (succ ⟨0, hn⟩) = f ⟨0, hn⟩
    rw [partialProd_succ]
    simp
  | succ i hi =>
    specialize hi (lt_trans (Nat.lt_succ_self i) hn)
    simp at hi ⊢
    change (partialProd f (succ ⟨i, Nat.lt_of_succ_lt hn⟩))⁻¹ * g⁻¹ * (g *
      partialProd f (succ ⟨i + 1, hn⟩)) = f ⟨Nat.succ i, hn⟩
    rw [partialProd_succ, partialProd_succ, Fin.castSucc_mk, Fin.castSucc_mk, mul_inv_rev]
    simp_rw [← mul_assoc] at hi ⊢
    suffices h : (f ⟨i, Nat.lt_of_succ_lt hn⟩)⁻¹ *
        ((partialProd f ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_succ_lt hn)⟩)⁻¹ * g⁻¹ *
        (g * partialProd f ⟨i + 1, Nat.succ_lt_succ (Nat.lt_of_succ_lt hn)⟩)) *
        f ⟨Nat.succ i, hn⟩ = f ⟨Nat.succ i, hn⟩
    · simp_rw[←mul_assoc] at h
      assumption
    · rw [mul_left_eq_self, inv_mul_eq_one, ←hi, ← mul_assoc]
#align fin.partial_prod_right_inv Fin.partialProd_right_inv
#align fin.partial_sum_right_neg Fin.partialSum_right_neg

end PartialProd

end Fin

namespace List

section CommMonoid

variable [CommMonoid α]

@[to_additive]
theorem prod_take_ofFn {n : ℕ} (f : Fin n → α) (i : ℕ) :
    ((ofFn f).take i).prod = ∏ j in Finset.univ.filter fun j : Fin n => j.val < i, f j := by
  induction i with
  | zero =>
    simp
  | succ i IH =>
    by_cases h : i < n
    · have : i < length (ofFn f) := by rwa [length_ofFn f]
      rw [prod_take_succ _ _ this]
      have A : ((Finset.univ : Finset (Fin n)).filter fun j => j.val < i + 1) =
          ((Finset.univ : Finset (Fin n)).filter fun j => j.val < i) ∪ {(⟨i, h⟩ : Fin n)} := by
        ext ⟨_, _⟩
        simp [Nat.lt_succ_iff_lt_or_eq]
      have B : _root_.Disjoint (Finset.filter (fun j : Fin n => j.val < i) Finset.univ)
          (singleton (⟨i, h⟩ : Fin n)) := by simp
      rw [A, Finset.prod_union B, IH]
      simp
    · have A : (ofFn f).take i = (ofFn f).take i.succ := by
        rw [← length_ofFn f] at h
        have : length (ofFn f) ≤ i := not_lt.mp h
        rw [take_all_of_le this, take_all_of_le (le_trans this (Nat.le_succ _))]
      have B : ∀ j : Fin n, ((j : ℕ) < i.succ) = ((j : ℕ) < i) := by
        intro j
        have : (j : ℕ) < i := lt_of_lt_of_le j.2 (not_lt.mp h)
        simp [this, lt_trans this (Nat.lt_succ_self _)]
      simp [← A, B, IH]
#align list.prod_take_of_fn List.prod_take_ofFn
#align list.sum_take_of_fn List.sum_take_ofFn

@[to_additive]
theorem prod_ofFn {n : ℕ} {f : Fin n → α} : (ofFn f).prod = ∏ i, f i := by
  convert prod_take_ofFn f n
  · rw [take_all_of_le (le_of_eq (length_ofFn f))]
  · simp
#align list.prod_of_fn List.prod_ofFn
#align list.sum_of_fn List.sum_ofFn

end CommMonoid

-- Porting note: Statement had deprecated `L.nthLe i i.is_lt` instead of `L.get i`.
@[to_additive]
theorem alternatingProd_eq_finset_prod {G : Type _} [CommGroup G] :
    ∀ (L : List G), alternatingProd L = ∏ i : Fin L.length, L.get i ^ (-1 : ℤ) ^ (i : ℕ)
  | [] => by
    rw [alternatingProd, Finset.prod_eq_one]
    rintro ⟨i, ⟨⟩⟩
  | g::[] => by
    show g = ∏ i : Fin 1, [g].get i ^ (-1 : ℤ) ^ (i : ℕ)
    rw [Fin.prod_univ_succ]; simp
  | g::h::L =>
    calc g * h⁻¹ * L.alternatingProd
      = g * h⁻¹ * ∏ i : Fin L.length, L.get i ^ (-1 : ℤ) ^ (i : ℕ) :=
        congr_arg _ (alternatingProd_eq_finset_prod _)
    _ = ∏ i : Fin (L.length + 2), List.get (g::h::L) i ^ (-1 : ℤ) ^ (i : ℕ) := by
        { rw [Fin.prod_univ_succ, Fin.prod_univ_succ, mul_assoc]
          simp [Nat.succ_eq_add_one, pow_add]}
#align list.alternating_prod_eq_finset_prod List.alternatingProd_eq_finset_prod
#align list.alternating_sum_eq_finset_sum List.alternatingSum_eq_finset_sum

end List
