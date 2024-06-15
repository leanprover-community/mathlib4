/-
Copyright (c) 2020 Yury Kudryashov, Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Anne Baanen
-/
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.GroupTheory.GroupAction.Pi
import Mathlib.Logic.Equiv.Fin

#align_import algebra.big_operators.fin from "leanprover-community/mathlib"@"cc5dd6244981976cc9da7afc4eee5682b037a013"

/-!
# Big operators and `Fin`

Some results about products and sums over the type `Fin`.

The most important results are the induction formulas `Fin.prod_univ_castSucc`
and `Fin.prod_univ_succ`, and the formula `Fin.prod_const` for the product of a
constant function. These results have variants for sums instead of products.

## Main declarations

* `finFunctionFinEquiv`: An explicit equivalence between `Fin n → Fin m` and `Fin (m ^ n)`.
-/

open Finset

variable {α : Type*} {β : Type*}

namespace Finset

@[to_additive]
theorem prod_range [CommMonoid β] {n : ℕ} (f : ℕ → β) :
    ∏ i ∈ Finset.range n, f i = ∏ i : Fin n, f i :=
  (Fin.prod_univ_eq_prod_range _ _).symm
#align finset.prod_range Finset.prod_range
#align finset.sum_range Finset.sum_range

end Finset

namespace Fin

@[to_additive]
theorem prod_ofFn [CommMonoid β] {n : ℕ} (f : Fin n → β) : (List.ofFn f).prod = ∏ i, f i := by
  simp [prod_eq_multiset_prod]
#align fin.prod_of_fn Fin.prod_ofFn
#align fin.sum_of_fn Fin.sum_ofFn

@[to_additive]
theorem prod_univ_def [CommMonoid β] {n : ℕ} (f : Fin n → β) :
    ∏ i, f i = ((List.finRange n).map f).prod := by
  rw [← List.ofFn_eq_map, prod_ofFn]
#align fin.prod_univ_def Fin.prod_univ_def
#align fin.sum_univ_def Fin.sum_univ_def

/-- A product of a function `f : Fin 0 → β` is `1` because `Fin 0` is empty -/
@[to_additive "A sum of a function `f : Fin 0 → β` is `0` because `Fin 0` is empty"]
theorem prod_univ_zero [CommMonoid β] (f : Fin 0 → β) : ∏ i, f i = 1 :=
  rfl
#align fin.prod_univ_zero Fin.prod_univ_zero
#align fin.sum_univ_zero Fin.sum_univ_zero

/-- A product of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)`
is the product of `f x`, for some `x : Fin (n + 1)` times the remaining product -/
@[to_additive "A sum of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)` is the sum of
`f x`, for some `x : Fin (n + 1)` plus the remaining product"]
theorem prod_univ_succAbove [CommMonoid β] {n : ℕ} (f : Fin (n + 1) → β) (x : Fin (n + 1)) :
    ∏ i, f i = f x * ∏ i : Fin n, f (x.succAbove i) := by
  rw [univ_succAbove, prod_cons, Finset.prod_map _ x.succAboveEmb]
  rfl
#align fin.prod_univ_succ_above Fin.prod_univ_succAbove
#align fin.sum_univ_succ_above Fin.sum_univ_succAbove

/-- A product of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)`
is the product of `f 0` plus the remaining product -/
@[to_additive "A sum of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)` is the sum of
`f 0` plus the remaining product"]
theorem prod_univ_succ [CommMonoid β] {n : ℕ} (f : Fin (n + 1) → β) :
    ∏ i, f i = f 0 * ∏ i : Fin n, f i.succ :=
  prod_univ_succAbove f 0
#align fin.prod_univ_succ Fin.prod_univ_succ
#align fin.sum_univ_succ Fin.sum_univ_succ

/-- A product of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)`
is the product of `f (Fin.last n)` plus the remaining product -/
@[to_additive "A sum of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)` is the sum of
`f (Fin.last n)` plus the remaining sum"]
theorem prod_univ_castSucc [CommMonoid β] {n : ℕ} (f : Fin (n + 1) → β) :
    ∏ i, f i = (∏ i : Fin n, f (Fin.castSucc i)) * f (last n) := by
  simpa [mul_comm] using prod_univ_succAbove f (last n)
#align fin.prod_univ_cast_succ Fin.prod_univ_castSucc
#align fin.sum_univ_cast_succ Fin.sum_univ_castSucc

@[to_additive (attr := simp)]
theorem prod_univ_get [CommMonoid α] (l : List α) : ∏ i, l.get i = l.prod := by
  simp [Finset.prod_eq_multiset_prod]

@[to_additive (attr := simp)]
theorem prod_univ_get' [CommMonoid β] (l : List α) (f : α → β) :
    ∏ i, f (l.get i) = (l.map f).prod := by
  simp [Finset.prod_eq_multiset_prod]

@[to_additive]
theorem prod_cons [CommMonoid β] {n : ℕ} (x : β) (f : Fin n → β) :
    (∏ i : Fin n.succ, (cons x f : Fin n.succ → β) i) = x * ∏ i : Fin n, f i := by
  simp_rw [prod_univ_succ, cons_zero, cons_succ]
#align fin.prod_cons Fin.prod_cons
#align fin.sum_cons Fin.sum_cons

@[to_additive sum_univ_one]
theorem prod_univ_one [CommMonoid β] (f : Fin 1 → β) : ∏ i, f i = f 0 := by simp
#align fin.prod_univ_one Fin.prod_univ_one
#align fin.sum_univ_one Fin.sum_univ_one

@[to_additive (attr := simp)]
theorem prod_univ_two [CommMonoid β] (f : Fin 2 → β) : ∏ i, f i = f 0 * f 1 := by
  simp [prod_univ_succ]
#align fin.prod_univ_two Fin.prod_univ_two
#align fin.sum_univ_two Fin.sum_univ_two

@[to_additive]
theorem prod_univ_two' [CommMonoid β] (f : α → β) (a b : α) :
    ∏ i, f (![a, b] i) = f a * f b :=
  prod_univ_two _

@[to_additive]
theorem prod_univ_three [CommMonoid β] (f : Fin 3 → β) : ∏ i, f i = f 0 * f 1 * f 2 := by
  rw [prod_univ_castSucc, prod_univ_two]
  rfl
#align fin.prod_univ_three Fin.prod_univ_three
#align fin.sum_univ_three Fin.sum_univ_three

@[to_additive]
theorem prod_univ_four [CommMonoid β] (f : Fin 4 → β) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 := by
  rw [prod_univ_castSucc, prod_univ_three]
  rfl
#align fin.prod_univ_four Fin.prod_univ_four
#align fin.sum_univ_four Fin.sum_univ_four

@[to_additive]
theorem prod_univ_five [CommMonoid β] (f : Fin 5 → β) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 := by
  rw [prod_univ_castSucc, prod_univ_four]
  rfl
#align fin.prod_univ_five Fin.prod_univ_five
#align fin.sum_univ_five Fin.sum_univ_five

@[to_additive]
theorem prod_univ_six [CommMonoid β] (f : Fin 6 → β) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 := by
  rw [prod_univ_castSucc, prod_univ_five]
  rfl
#align fin.prod_univ_six Fin.prod_univ_six
#align fin.sum_univ_six Fin.sum_univ_six

@[to_additive]
theorem prod_univ_seven [CommMonoid β] (f : Fin 7 → β) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 := by
  rw [prod_univ_castSucc, prod_univ_six]
  rfl
#align fin.prod_univ_seven Fin.prod_univ_seven
#align fin.sum_univ_seven Fin.sum_univ_seven

@[to_additive]
theorem prod_univ_eight [CommMonoid β] (f : Fin 8 → β) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 := by
  rw [prod_univ_castSucc, prod_univ_seven]
  rfl
#align fin.prod_univ_eight Fin.prod_univ_eight
#align fin.sum_univ_eight Fin.sum_univ_eight

theorem sum_pow_mul_eq_add_pow {n : ℕ} {R : Type*} [CommSemiring R] (a b : R) :
    (∑ s : Finset (Fin n), a ^ s.card * b ^ (n - s.card)) = (a + b) ^ n := by
  simpa using Fintype.sum_pow_mul_eq_add_pow (Fin n) a b
#align fin.sum_pow_mul_eq_add_pow Fin.sum_pow_mul_eq_add_pow

theorem prod_const [CommMonoid α] (n : ℕ) (x : α) : ∏ _i : Fin n, x = x ^ n := by simp
#align fin.prod_const Fin.prod_const

theorem sum_const [AddCommMonoid α] (n : ℕ) (x : α) : ∑ _i : Fin n, x = n • x := by simp
#align fin.sum_const Fin.sum_const

@[to_additive]
theorem prod_Ioi_zero {M : Type*} [CommMonoid M] {n : ℕ} {v : Fin n.succ → M} :
    ∏ i ∈ Ioi 0, v i = ∏ j : Fin n, v j.succ := by
  rw [Ioi_zero_eq_map, Finset.prod_map, val_succEmb]
#align fin.prod_Ioi_zero Fin.prod_Ioi_zero
#align fin.sum_Ioi_zero Fin.sum_Ioi_zero

@[to_additive]
theorem prod_Ioi_succ {M : Type*} [CommMonoid M] {n : ℕ} (i : Fin n) (v : Fin n.succ → M) :
    ∏ j ∈ Ioi i.succ, v j = ∏ j ∈ Ioi i, v j.succ := by
  rw [Ioi_succ, Finset.prod_map, val_succEmb]
#align fin.prod_Ioi_succ Fin.prod_Ioi_succ
#align fin.sum_Ioi_succ Fin.sum_Ioi_succ

@[to_additive]
theorem prod_congr' {M : Type*} [CommMonoid M] {a b : ℕ} (f : Fin b → M) (h : a = b) :
    (∏ i : Fin a, f (cast h i)) = ∏ i : Fin b, f i := by
  subst h
  congr
#align fin.prod_congr' Fin.prod_congr'
#align fin.sum_congr' Fin.sum_congr'

@[to_additive]
theorem prod_univ_add {M : Type*} [CommMonoid M] {a b : ℕ} (f : Fin (a + b) → M) :
    (∏ i : Fin (a + b), f i) = (∏ i : Fin a, f (castAdd b i)) * ∏ i : Fin b, f (natAdd a i) := by
  rw [Fintype.prod_equiv finSumFinEquiv.symm f fun i => f (finSumFinEquiv.toFun i)]
  · apply Fintype.prod_sum_type
  · intro x
    simp only [Equiv.toFun_as_coe, Equiv.apply_symm_apply]
#align fin.prod_univ_add Fin.prod_univ_add
#align fin.sum_univ_add Fin.sum_univ_add

@[to_additive]
theorem prod_trunc {M : Type*} [CommMonoid M] {a b : ℕ} (f : Fin (a + b) → M)
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
  simp [partialProd, List.take_succ, List.ofFnNthVal, dif_pos j.is_lt]
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
theorem partialProd_left_inv {G : Type*} [Group G] (f : Fin (n + 1) → G) :
    (f 0 • partialProd fun i : Fin n => (f i)⁻¹ * f i.succ) = f :=
  funext fun x => Fin.inductionOn x (by simp) fun x hx => by
    simp only [coe_eq_castSucc, Pi.smul_apply, smul_eq_mul] at hx ⊢
    rw [partialProd_succ, ← mul_assoc, hx, mul_inv_cancel_left]
#align fin.partial_prod_left_inv Fin.partialProd_left_inv
#align fin.partial_sum_left_neg Fin.partialSum_left_neg

@[to_additive]
theorem partialProd_right_inv {G : Type*} [Group G] (f : Fin n → G) (i : Fin n) :
    (partialProd f (Fin.castSucc i))⁻¹ * partialProd f i.succ = f i := by
  cases' i with i hn
  induction i with
  | zero => simp [-Fin.succ_mk, partialProd_succ]
  | succ i hi =>
    specialize hi (lt_trans (Nat.lt_succ_self i) hn)
    simp only [Fin.coe_eq_castSucc, Fin.succ_mk, Fin.castSucc_mk] at hi ⊢
    rw [← Fin.succ_mk _ _ (lt_trans (Nat.lt_succ_self _) hn), ← Fin.succ_mk _ _ hn]
    simp only [partialProd_succ, mul_inv_rev, Fin.castSucc_mk]
    -- Porting note: was
    -- assoc_rw [hi, inv_mul_cancel_left]
    rw [← mul_assoc, mul_left_eq_self, mul_assoc, hi, mul_left_inv]
#align fin.partial_prod_right_inv Fin.partialProd_right_inv
#align fin.partial_sum_right_neg Fin.partialSum_right_neg

/-- Let `(g₀, g₁, ..., gₙ)` be a tuple of elements in `Gⁿ⁺¹`.
Then if `k < j`, this says `(g₀g₁...gₖ₋₁)⁻¹ * g₀g₁...gₖ = gₖ`.
If `k = j`, it says `(g₀g₁...gₖ₋₁)⁻¹ * g₀g₁...gₖ₊₁ = gₖgₖ₊₁`.
If `k > j`, it says `(g₀g₁...gₖ)⁻¹ * g₀g₁...gₖ₊₁ = gₖ₊₁.`
Useful for defining group cohomology. -/
@[to_additive
      "Let `(g₀, g₁, ..., gₙ)` be a tuple of elements in `Gⁿ⁺¹`.
      Then if `k < j`, this says `-(g₀ + g₁ + ... + gₖ₋₁) + (g₀ + g₁ + ... + gₖ) = gₖ`.
      If `k = j`, it says `-(g₀ + g₁ + ... + gₖ₋₁) + (g₀ + g₁ + ... + gₖ₊₁) = gₖ + gₖ₊₁`.
      If `k > j`, it says `-(g₀ + g₁ + ... + gₖ) + (g₀ + g₁ + ... + gₖ₊₁) = gₖ₊₁.`
      Useful for defining group cohomology."]
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
#align fin.inv_partial_prod_mul_eq_contract_nth Fin.inv_partialProd_mul_eq_contractNth
#align fin.neg_partial_sum_add_eq_contract_nth Fin.neg_partialSum_add_eq_contractNth

end PartialProd

end Fin

/-- Equivalence between `Fin n → Fin m` and `Fin (m ^ n)`. -/
@[simps!]
def finFunctionFinEquiv {m n : ℕ} : (Fin n → Fin m) ≃ Fin (m ^ n) :=
  Equiv.ofRightInverseOfCardLE (le_of_eq <| by simp_rw [Fintype.card_fun, Fintype.card_fin])
    (fun f => ⟨∑ i, f i * m ^ (i : ℕ), by
      induction' n with n ih
      · simp
      cases m
      · exact isEmptyElim (f <| Fin.last _)
      simp_rw [Fin.sum_univ_castSucc, Fin.coe_castSucc, Fin.val_last]
      refine (Nat.add_lt_add_of_lt_of_le (ih _) <| Nat.mul_le_mul_right _ (Fin.is_le _)).trans_eq ?_
      rw [← one_add_mul (_ : ℕ), add_comm, pow_succ']⟩)
    (fun a b => ⟨a / m ^ (b : ℕ) % m, by
      cases' n with n
      · exact b.elim0
      cases' m with m
      · rw [zero_pow n.succ_ne_zero] at a
        exact a.elim0
      · exact Nat.mod_lt _ m.succ_pos⟩)
    fun a => by
      dsimp
      induction' n with n ih
      · haveI : Subsingleton (Fin (m ^ 0)) := (finCongr <| pow_zero _).subsingleton
        exact Subsingleton.elim _ _
      simp_rw [Fin.forall_iff, Fin.ext_iff] at ih
      ext
      simp_rw [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero, Nat.div_one,
        mul_one, pow_succ', ← Nat.div_div_eq_div_mul, mul_left_comm _ m, ← mul_sum]
      rw [ih _ (Nat.div_lt_of_lt_mul ?_), Nat.mod_add_div]
      -- Porting note: replaces `a.is_lt` in the wildcard above. Caused by a refactor of the `npow`
      -- instance for `Fin`.
      exact a.is_lt.trans_eq (pow_succ' _ _)
#align fin_function_fin_equiv finFunctionFinEquiv

theorem finFunctionFinEquiv_apply {m n : ℕ} (f : Fin n → Fin m) :
    (finFunctionFinEquiv f : ℕ) = ∑ i : Fin n, ↑(f i) * m ^ (i : ℕ) :=
  rfl
#align fin_function_fin_equiv_apply finFunctionFinEquiv_apply

theorem finFunctionFinEquiv_single {m n : ℕ} [NeZero m] (i : Fin n) (j : Fin m) :
    (finFunctionFinEquiv (Pi.single i j) : ℕ) = j * m ^ (i : ℕ) := by
  rw [finFunctionFinEquiv_apply, Fintype.sum_eq_single i, Pi.single_eq_same]
  rintro x hx
  rw [Pi.single_eq_of_ne hx, Fin.val_zero', zero_mul]
#align fin_function_fin_equiv_single finFunctionFinEquiv_single

/-- Equivalence between `∀ i : Fin m, Fin (n i)` and `Fin (∏ i : Fin m, n i)`. -/
def finPiFinEquiv {m : ℕ} {n : Fin m → ℕ} : (∀ i : Fin m, Fin (n i)) ≃ Fin (∏ i : Fin m, n i) :=
  Equiv.ofRightInverseOfCardLE (le_of_eq <| by simp_rw [Fintype.card_pi, Fintype.card_fin])
    (fun f => ⟨∑ i, f i * ∏ j, n (Fin.castLE i.is_lt.le j), by
      induction' m with m ih
      · simp
      rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
      suffices
        ∀ (n : Fin m → ℕ) (nn : ℕ) (f : ∀ i : Fin m, Fin (n i)) (fn : Fin nn),
          ((∑ i : Fin m, ↑(f i) * ∏ j : Fin i, n (Fin.castLE i.prop.le j)) + ↑fn * ∏ j, n j) <
            (∏ i : Fin m, n i) * nn by
        replace := this (Fin.init n) (n (Fin.last _)) (Fin.init f) (f (Fin.last _))
        rw [← Fin.snoc_init_self f]
        simp (config := { singlePass := true }) only [← Fin.snoc_init_self n]
        simp_rw [Fin.snoc_castSucc, Fin.snoc_last, Fin.snoc_init_self n]
        exact this
      intro n nn f fn
      cases nn
      · exact isEmptyElim fn
      refine (Nat.add_lt_add_of_lt_of_le (ih _) <| Nat.mul_le_mul_right _ (Fin.is_le _)).trans_eq ?_
      rw [← one_add_mul (_ : ℕ), mul_comm, add_comm]⟩)
    (fun a b => ⟨(a / ∏ j : Fin b, n (Fin.castLE b.is_lt.le j)) % n b, by
      cases m
      · exact b.elim0
      cases' h : n b with nb
      · rw [prod_eq_zero (Finset.mem_univ _) h] at a
        exact isEmptyElim a
      exact Nat.mod_lt _ nb.succ_pos⟩)
    (by
      intro a; revert a; dsimp only [Fin.val_mk]
      refine Fin.consInduction ?_ ?_ n
      · intro a
        haveI : Subsingleton (Fin (∏ i : Fin 0, i.elim0)) :=
          (finCongr <| prod_empty).subsingleton
        exact Subsingleton.elim _ _
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
        dsimp only [Fin.val_zero]
        simp_rw [Fintype.prod_empty, Nat.div_one, mul_one, Fin.cons_zero, Fin.prod_univ_succ]
        change (_ + ∑ y : _, _ / (x * _) % _ * (x * _)) = _
        simp_rw [← Nat.div_div_eq_div_mul, mul_left_comm (_ % _ : ℕ), ← mul_sum]
        convert Nat.mod_add_div _ _
        -- Porting note: new
        refine (ih (a / x) (Nat.div_lt_of_lt_mul <| a.is_lt.trans_eq ?_))
        exact Fin.prod_univ_succ _
        -- Porting note: was:
        /-
        refine' Eq.trans _ (ih (a / x) (Nat.div_lt_of_lt_mul <| a.is_lt.trans_eq _))
        swap
        · convert Fin.prod_univ_succ (Fin.cons x xs : _ → ℕ)
          simp_rw [Fin.cons_succ]
        congr with i
        congr with j
        · cases j
          rfl
        · cases j
          rfl-/)
#align fin_pi_fin_equiv finPiFinEquiv

theorem finPiFinEquiv_apply {m : ℕ} {n : Fin m → ℕ} (f : ∀ i : Fin m, Fin (n i)) :
    (finPiFinEquiv f : ℕ) = ∑ i, f i * ∏ j, n (Fin.castLE i.is_lt.le j) := rfl
#align fin_pi_fin_equiv_apply finPiFinEquiv_apply

theorem finPiFinEquiv_single {m : ℕ} {n : Fin m → ℕ} [∀ i, NeZero (n i)] (i : Fin m)
    (j : Fin (n i)) :
    (finPiFinEquiv (Pi.single i j : ∀ i : Fin m, Fin (n i)) : ℕ) =
      j * ∏ j, n (Fin.castLE i.is_lt.le j) := by
  rw [finPiFinEquiv_apply, Fintype.sum_eq_single i, Pi.single_eq_same]
  rintro x hx
  rw [Pi.single_eq_of_ne hx, Fin.val_zero', zero_mul]
#align fin_pi_fin_equiv_single finPiFinEquiv_single

namespace List

section CommMonoid

variable [CommMonoid α]

@[to_additive]
theorem prod_take_ofFn {n : ℕ} (f : Fin n → α) (i : ℕ) :
    ((ofFn f).take i).prod = ∏ j ∈ Finset.univ.filter fun j : Fin n => j.val < i, f j := by
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
theorem prod_ofFn {n : ℕ} {f : Fin n → α} : (ofFn f).prod = ∏ i, f i :=
  Fin.prod_ofFn f
#align list.prod_of_fn List.prod_ofFn
#align list.sum_of_fn List.sum_ofFn

end CommMonoid

@[to_additive]
theorem alternatingProd_eq_finset_prod {G : Type*} [CommGroup G] :
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
