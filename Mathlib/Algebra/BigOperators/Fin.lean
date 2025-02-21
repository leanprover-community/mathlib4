/-
Copyright (c) 2020 Yury Kudryashov, Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Anne Baanen
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Logic.Equiv.Fin

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

variable {α : Type*} {β : Type*}

namespace Finset

@[to_additive]
theorem prod_range [CommMonoid β] {n : ℕ} (f : ℕ → β) :
    ∏ i ∈ Finset.range n, f i = ∏ i : Fin n, f i :=
  (Fin.prod_univ_eq_prod_range _ _).symm

end Finset

namespace Fin

@[to_additive]
theorem prod_ofFn [CommMonoid β] {n : ℕ} (f : Fin n → β) : (List.ofFn f).prod = ∏ i, f i := by
  simp [prod_eq_multiset_prod]

@[to_additive]
theorem prod_univ_def [CommMonoid β] {n : ℕ} (f : Fin n → β) :
    ∏ i, f i = ((List.finRange n).map f).prod := by
  rw [← List.ofFn_eq_map, prod_ofFn]

/-- A product of a function `f : Fin 0 → β` is `1` because `Fin 0` is empty -/
@[to_additive "A sum of a function `f : Fin 0 → β` is `0` because `Fin 0` is empty"]
theorem prod_univ_zero [CommMonoid β] (f : Fin 0 → β) : ∏ i, f i = 1 :=
  rfl

/-- A product of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)`
is the product of `f x`, for some `x : Fin (n + 1)` times the remaining product -/
@[to_additive "A sum of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)` is the sum of
`f x`, for some `x : Fin (n + 1)` plus the remaining sum"]
theorem prod_univ_succAbove [CommMonoid β] {n : ℕ} (f : Fin (n + 1) → β) (x : Fin (n + 1)) :
    ∏ i, f i = f x * ∏ i : Fin n, f (x.succAbove i) := by
  rw [univ_succAbove, prod_cons, Finset.prod_map _ x.succAboveEmb]
  rfl

/-- A product of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)`
is the product of `f 0` plus the remaining product -/
@[to_additive "A sum of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)` is the sum of
`f 0` plus the remaining sum"]
theorem prod_univ_succ [CommMonoid β] {n : ℕ} (f : Fin (n + 1) → β) :
    ∏ i, f i = f 0 * ∏ i : Fin n, f i.succ :=
  prod_univ_succAbove f 0

/-- A product of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)`
is the product of `f (Fin.last n)` plus the remaining product -/
@[to_additive "A sum of a function `f : Fin (n + 1) → β` over all `Fin (n + 1)` is the sum of
`f (Fin.last n)` plus the remaining sum"]
theorem prod_univ_castSucc [CommMonoid β] {n : ℕ} (f : Fin (n + 1) → β) :
    ∏ i, f i = (∏ i : Fin n, f (Fin.castSucc i)) * f (last n) := by
  simpa [mul_comm] using prod_univ_succAbove f (last n)

@[to_additive (attr := simp)]
theorem prod_univ_get [CommMonoid α] (l : List α) : ∏ i : Fin l.length, l[i.1] = l.prod := by
  simp [Finset.prod_eq_multiset_prod]

@[to_additive (attr := simp)]
theorem prod_univ_get' [CommMonoid β] (l : List α) (f : α → β) :
    ∏ i : Fin l.length, f l[i.1] = (l.map f).prod := by
  simp [Finset.prod_eq_multiset_prod]

@[to_additive (attr := simp)]
theorem prod_cons [CommMonoid β] {n : ℕ} (x : β) (f : Fin n → β) :
    (∏ i : Fin n.succ, (cons x f : Fin n.succ → β) i) = x * ∏ i : Fin n, f i := by
  simp_rw [prod_univ_succ, cons_zero, cons_succ]

@[to_additive (attr := simp)]
theorem prod_snoc [CommMonoid β] {n : ℕ} (x : β) (f : Fin n → β) :
    (∏ i : Fin n.succ, (snoc f x : Fin n.succ → β) i) = (∏ i : Fin n, f i) * x := by
  simp [prod_univ_castSucc]

@[to_additive sum_univ_one]
theorem prod_univ_one [CommMonoid β] (f : Fin 1 → β) : ∏ i, f i = f 0 := by simp

@[to_additive (attr := simp)]
theorem prod_univ_two [CommMonoid β] (f : Fin 2 → β) : ∏ i, f i = f 0 * f 1 := by
  simp [prod_univ_succ]

@[to_additive]
theorem prod_univ_two' [CommMonoid β] (f : α → β) (a b : α) :
    ∏ i, f (![a, b] i) = f a * f b :=
  prod_univ_two _

@[to_additive]
theorem prod_univ_three [CommMonoid β] (f : Fin 3 → β) : ∏ i, f i = f 0 * f 1 * f 2 := by
  rw [prod_univ_castSucc, prod_univ_two]
  rfl

@[to_additive]
theorem prod_univ_four [CommMonoid β] (f : Fin 4 → β) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 := by
  rw [prod_univ_castSucc, prod_univ_three]
  rfl

@[to_additive]
theorem prod_univ_five [CommMonoid β] (f : Fin 5 → β) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 := by
  rw [prod_univ_castSucc, prod_univ_four]
  rfl

@[to_additive]
theorem prod_univ_six [CommMonoid β] (f : Fin 6 → β) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 := by
  rw [prod_univ_castSucc, prod_univ_five]
  rfl

@[to_additive]
theorem prod_univ_seven [CommMonoid β] (f : Fin 7 → β) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 := by
  rw [prod_univ_castSucc, prod_univ_six]
  rfl

@[to_additive]
theorem prod_univ_eight [CommMonoid β] (f : Fin 8 → β) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 := by
  rw [prod_univ_castSucc, prod_univ_seven]
  rfl

theorem sum_pow_mul_eq_add_pow {n : ℕ} {R : Type*} [CommSemiring R] (a b : R) :
    (∑ s : Finset (Fin n), a ^ s.card * b ^ (n - s.card)) = (a + b) ^ n := by
  simpa using Fintype.sum_pow_mul_eq_add_pow (Fin n) a b

theorem prod_const [CommMonoid α] (n : ℕ) (x : α) : ∏ _i : Fin n, x = x ^ n := by simp

theorem sum_const [AddCommMonoid α] (n : ℕ) (x : α) : ∑ _i : Fin n, x = n • x := by simp

@[to_additive]
theorem prod_Ioi_zero {M : Type*} [CommMonoid M] {n : ℕ} {v : Fin n.succ → M} :
    ∏ i ∈ Ioi 0, v i = ∏ j : Fin n, v j.succ := by
  rw [Ioi_zero_eq_map, Finset.prod_map, val_succEmb]

@[to_additive]
theorem prod_Ioi_succ {M : Type*} [CommMonoid M] {n : ℕ} (i : Fin n) (v : Fin n.succ → M) :
    ∏ j ∈ Ioi i.succ, v j = ∏ j ∈ Ioi i, v j.succ := by
  rw [Ioi_succ, Finset.prod_map, val_succEmb]

@[to_additive]
theorem prod_congr' {M : Type*} [CommMonoid M] {a b : ℕ} (f : Fin b → M) (h : a = b) :
    (∏ i : Fin a, f (i.cast h)) = ∏ i : Fin b, f i := by
  subst h
  congr

@[to_additive]
theorem prod_univ_add {M : Type*} [CommMonoid M] {a b : ℕ} (f : Fin (a + b) → M) :
    (∏ i : Fin (a + b), f i) = (∏ i : Fin a, f (castAdd b i)) * ∏ i : Fin b, f (natAdd a i) := by
  rw [Fintype.prod_equiv finSumFinEquiv.symm f fun i => f (finSumFinEquiv.toFun i)]
  · apply Fintype.prod_sum_type
  · intro x
    simp only [Equiv.toFun_as_coe, Equiv.apply_symm_apply]

@[to_additive]
theorem prod_trunc {M : Type*} [CommMonoid M] {a b : ℕ} (f : Fin (a + b) → M)
    (hf : ∀ j : Fin b, f (natAdd a j) = 1) :
    (∏ i : Fin (a + b), f i) = ∏ i : Fin a, f (castLE (Nat.le.intro rfl) i) := by
  rw [prod_univ_add, Fintype.prod_eq_one _ hf, mul_one]
  rfl

lemma sum_neg_one_pow (R : Type*) [Ring R] (m : ℕ) :
    (∑ n : Fin m, (-1) ^ n.1 : R) = if Even m then 0 else 1 := by
  induction m with
  | zero => simp
  | succ n IH =>
    simp only [Fin.sum_univ_castSucc, Fin.coe_castSucc, IH, Fin.val_last,
      Nat.even_add_one, ← Nat.not_even_iff_odd, ite_not]
    split_ifs with h
    · simp [*]
    · simp [(Nat.not_even_iff_odd.mp h).neg_pow]

section PartialProd

variable [Monoid α] {n : ℕ}

/-- For `f = (a₁, ..., aₙ)` in `αⁿ`, `partialProd f` is `(1, a₁, a₁a₂, ..., a₁...aₙ)` in `αⁿ⁺¹`. -/
@[to_additive "For `f = (a₁, ..., aₙ)` in `αⁿ`, `partialSum f` is\n
`(0, a₁, a₁ + a₂, ..., a₁ + ... + aₙ)` in `αⁿ⁺¹`."]
def partialProd (f : Fin n → α) (i : Fin (n + 1)) : α :=
  ((List.ofFn f).take i).prod

@[to_additive (attr := simp)]
theorem partialProd_zero (f : Fin n → α) : partialProd f 0 = 1 := by simp [partialProd]

@[to_additive]
theorem partialProd_succ (f : Fin n → α) (j : Fin n) :
    partialProd f j.succ = partialProd f (Fin.castSucc j) * f j := by
  simp [partialProd, List.take_succ, List.ofFnNthVal, dif_pos j.is_lt]

@[to_additive]
theorem partialProd_succ' (f : Fin (n + 1) → α) (j : Fin (n + 1)) :
    partialProd f j.succ = f 0 * partialProd (Fin.tail f) j := by
  simp [partialProd]
  rfl

@[to_additive]
theorem partialProd_left_inv {G : Type*} [Group G] (f : Fin (n + 1) → G) :
    (f 0 • partialProd fun i : Fin n => (f i)⁻¹ * f i.succ) = f :=
  funext fun x => Fin.inductionOn x (by simp) fun x hx => by
    simp only [coe_eq_castSucc, Pi.smul_apply, smul_eq_mul] at hx ⊢
    rw [partialProd_succ, ← mul_assoc, hx, mul_inv_cancel_left]

@[to_additive]
theorem partialProd_right_inv {G : Type*} [Group G] (f : Fin n → G) (i : Fin n) :
    (partialProd f (Fin.castSucc i))⁻¹ * partialProd f i.succ = f i := by
  rw [partialProd_succ, inv_mul_cancel_left]

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

end PartialProd

section DivModSum

/-- Given a tuple of natural numbers `n : Fin m → ℕ` and a natural number `k`, return the first
index `i` such that `k` is smaller than `∑ j < i, n j`, and `none` otherwise.

This is defined en-route to `Fin.divSum`, which is the dependent version of `Fin.divNat`.
-/
def divSum? {m : ℕ} (n : Fin m → ℕ) (k : ℕ) : Option (Fin m) :=
  find (fun i => k < ∑ j : Fin i.val.succ, n (castLE i.isLt j))

theorem divSum?_is_some_iff_lt_sum {m : ℕ} {n : Fin m → ℕ} {k : ℕ} :
    (divSum? n k).isSome ↔ k < ∑ i, n i := by
  constructor
  · intro h
    simp only [divSum?, Nat.succ_eq_add_one, castLE, isSome_find_iff] at h
    obtain ⟨i, hi⟩ := h
    have : i.val + 1 + (m - i.val - 1) = m := by omega
    rw [← sum_congr' _ this, sum_univ_add]
    simp only [cast, coe_castAdd, coe_natAdd, gt_iff_lt]
    exact Nat.lt_add_right _ hi
  · intro isLt
    have : m ≠ 0 := fun h => by subst h; simp at isLt
    refine isSome_find_iff.mpr ?_
    have hm : (m - 1) + 1 = m := by omega
    refine ⟨cast hm (last (m - 1)), ?_⟩
    simp only [coe_cast, val_last, Nat.succ_eq_add_one, castLE_of_eq hm, sum_congr' n hm, isLt]

/-- The quotient of `k : Fin (∑ j, n j)` after "division" by `n : Fin m → ℕ`.

This is the dependent version of `Fin.divNat`. -/
def divSum {m : ℕ} {n : Fin m → ℕ} (k : Fin (∑ j, n j)) : Fin m :=
  (divSum? n k).get (divSum?_is_some_iff_lt_sum.mpr k.isLt)

theorem sum_le_of_divSum?_eq_some {m : ℕ} {n : Fin m → ℕ} {k : Fin (∑ j, n j)} {i : Fin m}
    (hi : divSum? n k = some i) : ∑ j : Fin i, n (castLE i.isLt.le j) ≤ k := by
  by_cases hi' : 0 = i.val
  · rw [← sum_congr' _ hi']
    simp only [univ_eq_empty, sum_empty, Nat.zero_le]
  · have : (i.val - 1) + 1 = i.val := by omega
    rw [← sum_congr' _ this]
    have := find_min (Option.mem_def.mp hi) (j := ⟨i.val - 1, by omega⟩) <| lt_def.mpr
      (by simp only [and_true]; omega)
    exact not_lt.mp this

/-- The remainder of `k : Fin (∑ j, n j)` after "division" by `n : Fin m → ℕ`, taking values in
`Fin (n (divSum k))`.

This is the dependent version of `Fin.modNat`. -/
def modSum {m : ℕ} {n : Fin m → ℕ} (k : Fin (∑ j, n j)) : Fin (n (divSum k)) :=
  ⟨k - ∑ j, n (castLE (divSum k).isLt.le j), by
    have divSum_mem : divSum k ∈ divSum? n k := by
      simp only [divSum, divSum?, Option.mem_def, Option.some_get]
    have hk : k < ∑ j, n (castLE (divSum k).isLt j) := find_spec _ divSum_mem
    simp only [sum_univ_succAbove _ (last (divSum k)), val_last, succAbove_last] at hk
    rw [Nat.sub_lt_iff_lt_add' (sum_le_of_divSum?_eq_some divSum_mem)]
    exact hk⟩

end DivModSum

end Fin

/-- Equivalence between `Fin n → Fin m` and `Fin (m ^ n)`. -/
@[simps!]
def finFunctionFinEquiv {m n : ℕ} : (Fin n → Fin m) ≃ Fin (m ^ n) :=
  .ofRightInverseOfCardLE (le_of_eq <| by simp_rw [Fintype.card_fun, Fintype.card_fin])
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
        rw [ih _ (Nat.div_lt_of_lt_mul ?_), Nat.mod_add_div]
        -- Porting note: replaces `a.is_lt` in the wildcard above.
        -- Caused by a refactor of the `npow` instance for `Fin`.
        exact a.is_lt.trans_eq (pow_succ' _ _)

theorem finFunctionFinEquiv_apply {m n : ℕ} (f : Fin n → Fin m) :
    (finFunctionFinEquiv f : ℕ) = ∑ i : Fin n, ↑(f i) * m ^ (i : ℕ) :=
  rfl

theorem finFunctionFinEquiv_single {m n : ℕ} [NeZero m] (i : Fin n) (j : Fin m) :
    (finFunctionFinEquiv (Pi.single i j) : ℕ) = j * m ^ (i : ℕ) := by
  rw [finFunctionFinEquiv_apply, Fintype.sum_eq_single i, Pi.single_eq_same]
  rintro x hx
  rw [Pi.single_eq_of_ne hx, Fin.val_zero', zero_mul]

/-- Equivalence between `(i : Fin m) × Fin (n i)` and `Fin (∑ i, n i)`. -/
def finSigmaFinEquiv {m : ℕ} {n : Fin m → ℕ} : (i : Fin m) × Fin (n i) ≃ Fin (∑ i, n i) :=
  .ofRightInverseOfCardLE (le_of_eq <| by simp_rw [Fintype.card_sigma, Fintype.card_fin])
    (fun ⟨i, j⟩ => ⟨∑ k, n (Fin.castLE i.isLt.le k) + j, by
      have hi : i.val + 1 + (m - i.val - 1) = m := by omega
      conv_rhs => rw [← Fin.sum_congr' n hi, Fin.sum_univ_add, Fin.sum_univ_add, add_assoc]
      have hk {k : Fin i} : Fin.castLE i.isLt.le k =
            Fin.cast hi (Fin.castAdd (m - i - 1) (Fin.castAdd 1 k)) := by
        simp only [Fin.castLE, Fin.cast, Fin.coe_castAdd]
      simp_rw [hk, Nat.add_lt_add_iff_left, univ_unique, sum_singleton]
      exact Nat.lt_add_right _ (by simp only [Fin.cast, Fin.coe_castAdd, Fin.coe_natAdd,
          Fin.val_eq_zero, add_zero, Fin.is_lt])⟩)
    (fun k => ⟨k.divSum, k.modSum⟩)
    (fun a => by
      induction n using Fin.consInduction with
      | h0 =>
        simp only [univ_eq_empty, sum_empty] at a
        exact Fin.elim0 a
      | h =>
        ext
        exact Nat.add_sub_cancel' (Fin.sum_le_of_divSum?_eq_some (Option.some_get _).symm))

@[simp]
theorem finSigmaFinEquiv_apply {m : ℕ} {n : Fin m → ℕ} (k : (i : Fin m) × Fin (n i)) :
    (finSigmaFinEquiv k : ℕ) = ∑ i : Fin k.1, n (Fin.castLE k.1.isLt.le i) + k.2 := rfl

theorem finSigmaFinEquiv_pair {m : ℕ} {n : Fin m → ℕ} (i : Fin m) (k : Fin (n i)) :
    (finSigmaFinEquiv ⟨i, k⟩ : ℕ) = ∑ j, n (Fin.castLE i.isLt.le j) + k := by
  simp only [finSigmaFinEquiv, ↓reduceDIte, Equiv.ofRightInverseOfCardLE_apply]

/-- Equivalence between `∀ i : Fin m, Fin (n i)` and `Fin (∏ i : Fin m, n i)`. -/
def finPiFinEquiv {m : ℕ} {n : Fin m → ℕ} : (∀ i : Fin m, Fin (n i)) ≃ Fin (∏ i : Fin m, n i) :=
  .ofRightInverseOfCardLE (le_of_eq <| by simp_rw [Fintype.card_pi, Fintype.card_fin])
    (fun f => ⟨∑ i, f i * ∏ j, n (Fin.castLE i.is_lt.le j), by
      induction m with
      | zero => simp
      | succ m ih =>
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
        dsimp only [Fin.val_zero]
        simp_rw [Fintype.prod_empty, Nat.div_one, mul_one, Fin.cons_zero, Fin.prod_univ_succ]
        change (_ + ∑ y : _, _ / (x * _) % _ * (x * _)) = _
        simp_rw [← Nat.div_div_eq_div_mul, mul_left_comm (_ % _ : ℕ), ← mul_sum]
        convert Nat.mod_add_div _ _
        refine (ih (a / x) (Nat.div_lt_of_lt_mul <| a.is_lt.trans_eq ?_))
        exact Fin.prod_univ_succ _)

theorem finPiFinEquiv_apply {m : ℕ} {n : Fin m → ℕ} (f : ∀ i : Fin m, Fin (n i)) :
    (finPiFinEquiv f : ℕ) = ∑ i, f i * ∏ j, n (Fin.castLE i.is_lt.le j) := rfl

theorem finPiFinEquiv_single {m : ℕ} {n : Fin m → ℕ} [∀ i, NeZero (n i)] (i : Fin m)
    (j : Fin (n i)) :
    (finPiFinEquiv (Pi.single i j : ∀ i : Fin m, Fin (n i)) : ℕ) =
      j * ∏ j, n (Fin.castLE i.is_lt.le j) := by
  rw [finPiFinEquiv_apply, Fintype.sum_eq_single i, Pi.single_eq_same]
  rintro x hx
  rw [Pi.single_eq_of_ne hx, Fin.val_zero', zero_mul]

/-- Equivalence between the Sigma type `(i : Fin m) × Fin (n i)` and `Fin (∑ i : Fin m, n i)`. -/
def finSigmaFinEquiv {m : ℕ} {n : Fin m → ℕ} : (i : Fin m) × Fin (n i) ≃ Fin (∑ i : Fin m, n i) :=
  match m with
  | 0 => @Equiv.equivOfIsEmpty _ _ _ (by simp; exact Fin.isEmpty')
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
  simp only [Equiv.coe_fn_mk, Equiv.sigmaCongrLeft, Equiv.coe_fn_symm_mk, Equiv.instTrans_trans,
    Equiv.trans_apply, finCongr_apply, Fin.coe_cast]
  conv  =>
    enter [1,1,3]
    apply Equiv.sumCongr_apply
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
  rw [finSigmaFinEquiv_apply, add_left_eq_self]
  apply @Finset.sum_of_isEmpty _ _ _ _ (by simpa using Fin.isEmpty')

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
        rw [take_of_length_le this, take_of_length_le (le_trans this (Nat.le_succ _))]
      have B : ∀ j : Fin n, ((j : ℕ) < i.succ) = ((j : ℕ) < i) := by
        intro j
        have : (j : ℕ) < i := lt_of_lt_of_le j.2 (not_lt.mp h)
        simp [this, lt_trans this (Nat.lt_succ_self _)]
      simp [← A, B, IH]

@[to_additive]
theorem prod_ofFn {n : ℕ} {f : Fin n → α} : (ofFn f).prod = ∏ i, f i :=
  Fin.prod_ofFn f

end CommMonoid

@[to_additive]
theorem alternatingProd_eq_finset_prod {G : Type*} [CommGroup G] :
    ∀ (L : List G), alternatingProd L = ∏ i : Fin L.length, L[i] ^ (-1 : ℤ) ^ (i : ℕ)
  | [] => by
    rw [alternatingProd, Finset.prod_eq_one]
    rintro ⟨i, ⟨⟩⟩
  | g::[] => by
    show g = ∏ i : Fin 1, [g][i] ^ (-1 : ℤ) ^ (i : ℕ)
    rw [Fin.prod_univ_succ]; simp
  | g::h::L =>
    calc g * h⁻¹ * L.alternatingProd
      = g * h⁻¹ * ∏ i : Fin L.length, L[i] ^ (-1 : ℤ) ^ (i : ℕ) :=
        congr_arg _ (alternatingProd_eq_finset_prod _)
    _ = ∏ i : Fin (L.length + 2), (g::h::L)[i] ^ (-1 : ℤ) ^ (i : ℕ) := by
        { rw [Fin.prod_univ_succ, Fin.prod_univ_succ, mul_assoc]
          simp [pow_add]}

end List
