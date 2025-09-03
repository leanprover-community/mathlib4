/-
Copyright (c) 2022 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Multinomial

This file defines the multinomial coefficient and several small lemma's for manipulating it.

## Main declarations

- `Nat.multinomial`: the multinomial coefficient

## Main results

- `Finset.sum_pow`: The expansion of `(s.sum x) ^ n` using multinomial coefficients

-/

open Finset
open scoped Nat

namespace Nat

variable {α : Type*} (s : Finset α) (f : α → ℕ) {a b : α} (n : ℕ)

/-- The multinomial coefficient. Gives the number of strings consisting of symbols
from `s`, where `c ∈ s` appears with multiplicity `f c`.

Defined as `(∑ i ∈ s, f i)! / ∏ i ∈ s, (f i)!`.
-/
def multinomial : ℕ :=
  (∑ i ∈ s, f i)! / ∏ i ∈ s, (f i)!

theorem multinomial_pos : 0 < multinomial s f :=
  Nat.div_pos (le_of_dvd (factorial_pos _) (prod_factorial_dvd_factorial_sum s f))
    (prod_factorial_pos s f)

theorem multinomial_spec : (∏ i ∈ s, (f i)!) * multinomial s f = (∑ i ∈ s, f i)! :=
  Nat.mul_div_cancel' (prod_factorial_dvd_factorial_sum s f)

@[simp] lemma multinomial_empty : multinomial ∅ f = 1 := by simp [multinomial]

variable {s f}

lemma multinomial_cons (ha : a ∉ s) (f : α → ℕ) :
    multinomial (s.cons a ha) f = (f a + ∑ i ∈ s, f i).choose (f a) * multinomial s f := by
  rw [multinomial, Nat.div_eq_iff_eq_mul_left _ (prod_factorial_dvd_factorial_sum _ _), prod_cons,
    multinomial, mul_assoc, mul_left_comm _ (f a)!,
    Nat.div_mul_cancel (prod_factorial_dvd_factorial_sum _ _), ← mul_assoc, Nat.choose_symm_add,
    Nat.add_choose_mul_factorial_mul_factorial, Finset.sum_cons]
  positivity

lemma multinomial_insert [DecidableEq α] (ha : a ∉ s) (f : α → ℕ) :
    multinomial (insert a s) f = (f a + ∑ i ∈ s, f i).choose (f a) * multinomial s f := by
  rw [← cons_eq_insert _ _ ha, multinomial_cons]

@[simp] lemma multinomial_singleton (a : α) (f : α → ℕ) : multinomial {a} f = 1 := by
  rw [← cons_empty, multinomial_cons]; simp

@[simp]
theorem multinomial_insert_one [DecidableEq α] (h : a ∉ s) (h₁ : f a = 1) :
    multinomial (insert a s) f = (s.sum f).succ * multinomial s f := by
  simp only [multinomial]
  rw [Finset.sum_insert h, Finset.prod_insert h, h₁, add_comm, ← succ_eq_add_one, factorial_succ]
  simp only [factorial, succ_eq_add_one, zero_add, mul_one, one_mul]
  rw [Nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum _ _)]

theorem multinomial_congr {f g : α → ℕ} (h : ∀ a ∈ s, f a = g a) :
    multinomial s f = multinomial s g := by
  simp only [multinomial]; congr 1
  · rw [Finset.sum_congr rfl h]
  · exact Finset.prod_congr rfl fun a ha => by rw [h a ha]

/-! ### Connection to binomial coefficients

When `Nat.multinomial` is applied to a `Finset` of two elements `{a, b}`, the
result a binomial coefficient. We use `binomial` in the names of lemmas that
involves `Nat.multinomial {a, b}`.
-/

theorem binomial_eq [DecidableEq α] (h : a ≠ b) :
    multinomial {a, b} f = (f a + f b)! / ((f a)! * (f b)!) := by
  simp [multinomial, Finset.sum_pair h, Finset.prod_pair h]

theorem binomial_eq_choose [DecidableEq α] (h : a ≠ b) :
    multinomial {a, b} f = (f a + f b).choose (f a) := by
  simp [binomial_eq h, choose_eq_factorial_div_factorial (Nat.le_add_right _ _)]

theorem binomial_spec [DecidableEq α] (hab : a ≠ b) :
    (f a)! * (f b)! * multinomial {a, b} f = (f a + f b)! := by
  simpa [Finset.sum_pair hab, Finset.prod_pair hab] using multinomial_spec {a, b} f

theorem binomial_one [DecidableEq α] (h : a ≠ b) (h₁ : f a = 1) :
    multinomial {a, b} f = (f b).succ := by
  simp [h, h₁]

theorem binomial_succ_succ [DecidableEq α] (h : a ≠ b) :
    multinomial {a, b} (Function.update (Function.update f a (f a).succ) b (f b).succ) =
      multinomial {a, b} (Function.update f a (f a).succ) +
      multinomial {a, b} (Function.update f b (f b).succ) := by
  simp only [binomial_eq_choose, Function.update_apply,
    h, Ne, ite_true, ite_false, not_false_eq_true]
  rw [if_neg h.symm]
  rw [add_succ, choose_succ_succ, succ_add_eq_add_succ]
  ring

theorem succ_mul_binomial [DecidableEq α] (h : a ≠ b) :
    (f a + f b).succ * multinomial {a, b} f =
      (f a).succ * multinomial {a, b} (Function.update f a (f a).succ) := by
  rw [binomial_eq_choose h, binomial_eq_choose h, mul_comm (f a).succ, Function.update_self,
    Function.update_of_ne h.symm]
  rw [succ_mul_choose_eq (f a + f b) (f a), succ_add (f a) (f b)]

/-! ### Simple cases -/


theorem multinomial_univ_two (a b : ℕ) :
    multinomial Finset.univ ![a, b] = (a + b)! / (a ! * b !) := by
  rw [multinomial, Fin.sum_univ_two, Fin.prod_univ_two]
  dsimp only [Matrix.cons_val]

theorem multinomial_univ_three (a b c : ℕ) :
    multinomial Finset.univ ![a, b, c] = (a + b + c)! / (a ! * b ! * c !) := by
  rw [multinomial, Fin.sum_univ_three, Fin.prod_univ_three]
  rfl

end Nat

/-! ### Alternative definitions -/


namespace Finsupp

variable {α : Type*}

/-- Alternative multinomial definition based on a finsupp, using the support
  for the big operations
-/
def multinomial (f : α →₀ ℕ) : ℕ :=
  (f.sum fun _ => id)! / f.prod fun _ n => n !

theorem multinomial_eq (f : α →₀ ℕ) : f.multinomial = Nat.multinomial f.support f :=
  rfl

theorem multinomial_update (a : α) (f : α →₀ ℕ) :
    f.multinomial = (f.sum fun _ => id).choose (f a) * (f.update a 0).multinomial := by
  simp only [multinomial_eq]
  classical
    by_cases h : a ∈ f.support
    · rw [← Finset.insert_erase h, Nat.multinomial_insert (Finset.notMem_erase a _),
        Finset.add_sum_erase _ f h, support_update_zero]
      congr 1
      exact Nat.multinomial_congr fun _ h ↦ (Function.update_of_ne (mem_erase.1 h).1 0 f).symm
    rw [notMem_support_iff] at h
    rw [h, Nat.choose_zero_right, one_mul, ← h, update_self]

end Finsupp

namespace Multiset

variable {α : Type*}

/-- Alternative definition of multinomial based on `Multiset` delegating to the
  finsupp definition
-/
def multinomial [DecidableEq α] (m : Multiset α) : ℕ :=
  m.toFinsupp.multinomial

theorem multinomial_filter_ne [DecidableEq α] (a : α) (m : Multiset α) :
    m.multinomial = m.card.choose (m.count a) * (m.filter (a ≠ ·)).multinomial := by
  dsimp only [multinomial]
  convert Finsupp.multinomial_update a _
  · rw [← Finsupp.card_toMultiset, m.toFinsupp_toMultiset]
  · ext1 a
    rw [toFinsupp_apply, count_filter, Finsupp.coe_update]
    split_ifs with h
    · rw [Function.update_of_ne h.symm, toFinsupp_apply]
    · rw [not_ne_iff.1 h, Function.update_self]

@[simp]
theorem multinomial_zero [DecidableEq α] : multinomial (0 : Multiset α) = 1 := by
  simp [multinomial, Finsupp.multinomial]

end Multiset

namespace Finset
open _root_.Nat

/-! ### Multinomial theorem -/

variable {α R : Type*} [DecidableEq α]

section Semiring
variable [Semiring R]

open scoped Function -- required for scoped `on` notation

-- TODO: Can we prove one of the following two from the other one?
/-- The **multinomial theorem**. -/
lemma sum_pow_eq_sum_piAntidiag_of_commute (s : Finset α) (f : α → R)
    (hc : (s : Set α).Pairwise (Commute on f)) (n : ℕ) :
    (∑ i ∈ s, f i) ^ n = ∑ k ∈ piAntidiag s n, multinomial s k *
      s.noncommProd (fun i ↦ f i ^ k i) (hc.mono' fun _ _ h ↦ h.pow_pow ..) := by
  classical
  induction' s using Finset.cons_induction with a s has ih generalizing n
  · cases n <;> simp
  rw [Finset.sum_cons, piAntidiag_cons, sum_disjiUnion]
  simp only [sum_map, Pi.add_apply, multinomial_cons,
    Pi.add_apply, if_true, Nat.cast_mul, noncommProd_cons,
    if_true, sum_add_distrib, sum_ite_eq', has, if_false, add_zero,
    addRightEmbedding_apply]
  suffices ∀ p : ℕ × ℕ, p ∈ antidiagonal n →
    ∑ g ∈ piAntidiag s p.2, ((g a + p.1 + s.sum g).choose (g a + p.1) : R) *
      multinomial s (g + fun i ↦ ite (i = a) p.1 0) *
        (f a ^ (g a + p.1) * s.noncommProd (fun i ↦ f i ^ (g i + ite (i = a) p.1 0))
          ((hc.mono (by simp)).mono' fun i j h ↦ h.pow_pow ..)) =
      ∑ g ∈ piAntidiag s p.2, n.choose p.1 * multinomial s g * (f a ^ p.1 *
        s.noncommProd (fun i ↦ f i ^ g i) ((hc.mono (by simp)).mono' fun i j h ↦ h.pow_pow ..)) by
    rw [sum_congr rfl this]
    simp only [Nat.antidiagonal_eq_map, sum_map, Function.Embedding.coeFn_mk]
    rw [(Commute.sum_right _ _ _ fun i hi ↦ hc (by simp) (by simp [hi])
      (by simpa [eq_comm] using ne_of_mem_of_not_mem hi has)).add_pow]
    simp only [ih (hc.mono (by simp)), sum_mul, mul_sum]
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun g _ ↦ ?_
    rw [← Nat.cast_comm, (Nat.commute_cast (f a ^ i) _).left_comm, mul_assoc]
  refine fun p hp ↦ sum_congr rfl fun f hf ↦ ?_
  rw [mem_piAntidiag] at hf
  rw [not_imp_comm.1 (hf.2 _) has, zero_add, hf.1]
  congr 2
  · rw [mem_antidiagonal.1 hp]
  · rw [multinomial_congr]
    intro t ht
    rw [Pi.add_apply, if_neg, add_zero]
    exact ne_of_mem_of_not_mem ht has
  refine noncommProd_congr rfl (fun t ht ↦ ?_) _
  rw [if_neg, add_zero]
  exact ne_of_mem_of_not_mem ht has

/-- The **multinomial theorem**. -/
theorem sum_pow_of_commute (x : α → R) (s : Finset α)
    (hc : (s : Set α).Pairwise (Commute on x)) :
    ∀ n,
      s.sum x ^ n =
        ∑ k : s.sym n,
          k.1.1.multinomial *
            (k.1.1.map <| x).noncommProd
              (Multiset.map_set_pairwise <| hc.mono <| mem_sym_iff.1 k.2) := by
  induction' s using Finset.induction with a s ha ih
  · rw [sum_empty]
    rintro (_ | n)
    · rw [_root_.pow_zero, Fintype.sum_subsingleton]
      swap
      · exact ⟨0, by simp [eq_iff_true_of_subsingleton]⟩
      convert (@one_mul R _ _).symm
      convert @Nat.cast_one R _
      simp
    · rw [_root_.pow_succ, mul_zero]
      haveI : IsEmpty (Finset.sym (∅ : Finset α) n.succ) := Finset.instIsEmpty
      apply (Fintype.sum_empty _).symm
  intro n; specialize ih (hc.mono <| s.subset_insert a)
  rw [sum_insert ha, (Commute.sum_right s _ _ _).add_pow, sum_range]; swap
  · exact fun _ hb => hc (mem_insert_self a s) (mem_insert_of_mem hb)
      (ne_of_mem_of_not_mem hb ha).symm
  · simp_rw [ih, mul_sum, sum_mul, sum_sigma', univ_sigma_univ]
    refine (Fintype.sum_equiv (symInsertEquiv ha) _ _ fun m => ?_).symm
    rw [m.1.1.multinomial_filter_ne a]
    conv in m.1.1.map _ => rw [← m.1.1.filter_add_not (a = ·), Multiset.map_add]
    simp_rw [Multiset.noncommProd_add, m.1.1.filter_eq, Multiset.map_replicate, m.1.2]
    rw [Multiset.noncommProd_eq_pow_card _ _ _ fun _ => Multiset.eq_of_mem_replicate]
    rw [Multiset.card_replicate, Nat.cast_mul, mul_assoc, Nat.cast_comm]
    congr 1; simp_rw [← mul_assoc, Nat.cast_comm]; rfl

end Semiring

section CommSemiring
variable [CommSemiring R] {f : α → R} {s : Finset α}

lemma sum_pow_eq_sum_piAntidiag (s : Finset α) (f : α → R) (n : ℕ) :
    (∑ i ∈ s, f i) ^ n = ∑ k ∈ piAntidiag s n, multinomial s k * ∏ i ∈ s, f i ^ k i := by
  simp_rw [← noncommProd_eq_prod]
  rw [← sum_pow_eq_sum_piAntidiag_of_commute _ _ fun _ _ _ _ _ ↦ Commute.all ..]

theorem sum_pow (x : α → R) (n : ℕ) :
    s.sum x ^ n = ∑ k ∈ s.sym n, k.val.multinomial * (k.val.map x).prod := by
  conv_rhs => rw [← sum_coe_sort]
  convert sum_pow_of_commute x s (fun _ _ _ _ _ ↦ Commute.all ..) n
  rw [Multiset.noncommProd_eq_prod]

end CommSemiring
end Finset

namespace Nat
variable {ι : Type*} {s : Finset ι} {f : ι → ℕ}

lemma multinomial_two_mul_le_mul_multinomial :
    multinomial s (fun i ↦ 2 * f i) ≤ ((∑ i ∈ s, f i) ^ ∑ i ∈ s, f i) * multinomial s f := by
  rw [multinomial, multinomial, ← mul_sum,
    ← Nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum ..)]
  refine Nat.div_le_div_of_mul_le_mul (by positivity)
    ((prod_factorial_dvd_factorial_sum ..).trans (Nat.dvd_mul_left ..)) ?_
  calc
    (2 * ∑ i ∈ s, f i)! * ∏ i ∈ s, (f i)!
      ≤ ((2 * ∑ i ∈ s, f i) ^ (∑ i ∈ s, f i) * (∑ i ∈ s, f i)!) * ∏ i ∈ s, (f i)! := by
      gcongr; exact Nat.factorial_two_mul_le _
    _ = ((∑ i ∈ s, f i) ^ ∑ i ∈ s, f i) * (∑ i ∈ s, f i)! * ∏ i ∈ s, 2 ^ f i * (f i)! := by
      rw [mul_pow, ← prod_pow_eq_pow_sum, prod_mul_distrib]; ring
    _ ≤ ((∑ i ∈ s, f i) ^ ∑ i ∈ s, f i) * (∑ i ∈ s, f i)! * ∏ i ∈ s, (2 * f i)! := by
      gcongr
      rw [← doubleFactorial_two_mul]
      exact doubleFactorial_le_factorial _

end Nat

namespace Sym

variable {n : ℕ} {α : Type*} [DecidableEq α]

theorem multinomial_coe_fill_of_notMem {m : Fin (n + 1)} {s : Sym α (n - m)} {x : α} (hx : x ∉ s) :
    (fill x m s : Multiset α).multinomial = n.choose m * (s : Multiset α).multinomial := by
  rw [Multiset.multinomial_filter_ne x]
  rw [← mem_coe] at hx
  refine congrArg₂ _ ?_ ?_
  · rw [card_coe, count_coe_fill_self_of_notMem hx]
  · refine congrArg _ ?_
    rw [coe_fill, coe_replicate, Multiset.filter_add]
    rw [Multiset.filter_eq_self.mpr]
    · rw [add_eq_left]
      rw [Multiset.filter_eq_nil]
      exact fun j hj ↦ by simp [Multiset.mem_replicate.mp hj]
    · exact fun j hj h ↦ hx <| by simpa [h] using hj

@[deprecated (since := "2025-05-23")]
alias multinomial_coe_fill_of_not_mem := multinomial_coe_fill_of_notMem

end Sym
