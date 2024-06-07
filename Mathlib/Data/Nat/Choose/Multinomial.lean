/-
Copyright (c) 2022 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Finsupp.Multiset

#align_import data.nat.choose.multinomial from "leanprover-community/mathlib"@"2738d2ca56cbc63be80c3bd48e9ed90ad94e947d"

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
#align nat.multinomial Nat.multinomial

theorem multinomial_pos : 0 < multinomial s f :=
  Nat.div_pos (le_of_dvd (factorial_pos _) (prod_factorial_dvd_factorial_sum s f))
    (prod_factorial_pos s f)
#align nat.multinomial_pos Nat.multinomial_pos

theorem multinomial_spec : (∏ i ∈ s, (f i)!) * multinomial s f = (∑ i ∈ s, f i)! :=
  Nat.mul_div_cancel' (prod_factorial_dvd_factorial_sum s f)
#align nat.multinomial_spec Nat.multinomial_spec

@[simp] lemma multinomial_empty : multinomial ∅ f = 1 := rfl
#align nat.multinomial_nil Nat.multinomial_empty

@[deprecated (since := "2024-06-01")] alias multinomial_nil := multinomial_empty

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
#align nat.multinomial_insert Nat.multinomial_insert

@[simp] lemma multinomial_singleton (a : α) (f : α → ℕ) : multinomial {a} f = 1 := by
  rw [← cons_empty, multinomial_cons]; simp
#align nat.multinomial_singleton Nat.multinomial_singleton

@[simp]
theorem multinomial_insert_one [DecidableEq α] (h : a ∉ s) (h₁ : f a = 1) :
    multinomial (insert a s) f = (s.sum f).succ * multinomial s f := by
  simp only [multinomial, one_mul, factorial]
  rw [Finset.sum_insert h, Finset.prod_insert h, h₁, add_comm, ← succ_eq_add_one, factorial_succ]
  simp only [factorial_one, one_mul, Function.comp_apply, factorial, mul_one, ← one_eq_succ_zero]
  rw [Nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum _ _)]
#align nat.multinomial_insert_one Nat.multinomial_insert_one

theorem multinomial_congr {f g : α → ℕ} (h : ∀ a ∈ s, f a = g a) :
    multinomial s f = multinomial s g := by
  simp only [multinomial]; congr 1
  · rw [Finset.sum_congr rfl h]
  · exact Finset.prod_congr rfl fun a ha => by rw [h a ha]
#align nat.multinomial_congr Nat.multinomial_congr

/-! ### Connection to binomial coefficients

When `Nat.multinomial` is applied to a `Finset` of two elements `{a, b}`, the
result a binomial coefficient. We use `binomial` in the names of lemmas that
involves `Nat.multinomial {a, b}`.
-/

theorem binomial_eq [DecidableEq α] (h : a ≠ b) :
    multinomial {a, b} f = (f a + f b)! / ((f a)! * (f b)!) := by
  simp [multinomial, Finset.sum_pair h, Finset.prod_pair h]
#align nat.binomial_eq Nat.binomial_eq

theorem binomial_eq_choose [DecidableEq α] (h : a ≠ b) :
    multinomial {a, b} f = (f a + f b).choose (f a) := by
  simp [binomial_eq h, choose_eq_factorial_div_factorial (Nat.le_add_right _ _)]
#align nat.binomial_eq_choose Nat.binomial_eq_choose

theorem binomial_spec [DecidableEq α] (hab : a ≠ b) :
    (f a)! * (f b)! * multinomial {a, b} f = (f a + f b)! := by
  simpa [Finset.sum_pair hab, Finset.prod_pair hab] using multinomial_spec {a, b} f
#align nat.binomial_spec Nat.binomial_spec

@[simp]
theorem binomial_one [DecidableEq α] (h : a ≠ b) (h₁ : f a = 1) :
    multinomial {a, b} f = (f b).succ := by
  simp [multinomial_insert_one (Finset.not_mem_singleton.mpr h) h₁]
#align nat.binomial_one Nat.binomial_one

theorem binomial_succ_succ [DecidableEq α] (h : a ≠ b) :
    multinomial {a, b} (Function.update (Function.update f a (f a).succ) b (f b).succ) =
      multinomial {a, b} (Function.update f a (f a).succ) +
      multinomial {a, b} (Function.update f b (f b).succ) := by
  simp only [binomial_eq_choose, Function.update_apply,
    h, Ne, ite_true, ite_false, not_false_eq_true]
  rw [if_neg h.symm]
  rw [add_succ, choose_succ_succ, succ_add_eq_add_succ]
  ring
#align nat.binomial_succ_succ Nat.binomial_succ_succ

theorem succ_mul_binomial [DecidableEq α] (h : a ≠ b) :
    (f a + f b).succ * multinomial {a, b} f =
      (f a).succ * multinomial {a, b} (Function.update f a (f a).succ) := by
  rw [binomial_eq_choose h, binomial_eq_choose h, mul_comm (f a).succ, Function.update_same,
    Function.update_noteq (ne_comm.mp h)]
  rw [succ_mul_choose_eq (f a + f b) (f a), succ_add (f a) (f b)]
#align nat.succ_mul_binomial Nat.succ_mul_binomial

/-! ### Simple cases -/


theorem multinomial_univ_two (a b : ℕ) :
    multinomial Finset.univ ![a, b] = (a + b)! / (a ! * b !) := by
  rw [multinomial, Fin.sum_univ_two, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
#align nat.multinomial_univ_two Nat.multinomial_univ_two

theorem multinomial_univ_three (a b c : ℕ) :
    multinomial Finset.univ ![a, b, c] = (a + b + c)! / (a ! * b ! * c !) := by
  rw [multinomial, Fin.sum_univ_three, Fin.prod_univ_three]
  rfl
#align nat.multinomial_univ_three Nat.multinomial_univ_three

end Nat

/-! ### Alternative definitions -/


namespace Finsupp

variable {α : Type*}

/-- Alternative multinomial definition based on a finsupp, using the support
  for the big operations
-/
def multinomial (f : α →₀ ℕ) : ℕ :=
  (f.sum fun _ => id)! / f.prod fun _ n => n !
#align finsupp.multinomial Finsupp.multinomial

theorem multinomial_eq (f : α →₀ ℕ) : f.multinomial = Nat.multinomial f.support f :=
  rfl
#align finsupp.multinomial_eq Finsupp.multinomial_eq

theorem multinomial_update (a : α) (f : α →₀ ℕ) :
    f.multinomial = (f.sum fun _ => id).choose (f a) * (f.update a 0).multinomial := by
  simp only [multinomial_eq]
  classical
    by_cases h : a ∈ f.support
    · rw [← Finset.insert_erase h, Nat.multinomial_insert (Finset.not_mem_erase a _),
        Finset.add_sum_erase _ f h, support_update_zero]
      congr 1
      exact Nat.multinomial_congr fun _ h ↦ (Function.update_noteq (mem_erase.1 h).1 0 f).symm
    rw [not_mem_support_iff] at h
    rw [h, Nat.choose_zero_right, one_mul, ← h, update_self]
#align finsupp.multinomial_update Finsupp.multinomial_update

end Finsupp

namespace Multiset

variable {α : Type*}

/-- Alternative definition of multinomial based on `Multiset` delegating to the
  finsupp definition
-/
def multinomial [DecidableEq α] (m : Multiset α) : ℕ :=
  m.toFinsupp.multinomial
#align multiset.multinomial Multiset.multinomial

theorem multinomial_filter_ne [DecidableEq α] (a : α) (m : Multiset α) :
    m.multinomial = m.card.choose (m.count a) * (m.filter (a ≠ ·)).multinomial := by
  dsimp only [multinomial]
  convert Finsupp.multinomial_update a _
  · rw [← Finsupp.card_toMultiset, m.toFinsupp_toMultiset]
  · ext1 a
    rw [toFinsupp_apply, count_filter, Finsupp.coe_update]
    split_ifs with h
    · rw [Function.update_noteq h.symm, toFinsupp_apply]
    · rw [not_ne_iff.1 h, Function.update_same]
#align multiset.multinomial_filter_ne Multiset.multinomial_filter_ne

@[simp]
theorem multinomial_zero [DecidableEq α] : multinomial (0 : Multiset α) = 1 := by
  simp [multinomial, Finsupp.multinomial]

end Multiset

namespace Finset

/-! ### Multinomial theorem -/

variable {α : Type*} [DecidableEq α] (s : Finset α) {R : Type*}

/-- The multinomial theorem

  Proof is by induction on the number of summands.
-/
theorem sum_pow_of_commute [Semiring R] (x : α → R)
    (hc : (s : Set α).Pairwise fun i j => Commute (x i) (x j)) :
    ∀ n,
      s.sum x ^ n =
        ∑ k : s.sym n,
          k.1.1.multinomial *
            (k.1.1.map <| x).noncommProd
              (Multiset.map_set_pairwise <| hc.mono <| mem_sym_iff.1 k.2) := by
  induction' s using Finset.induction with a s ha ih
  · rw [sum_empty]
    rintro (_ | n)
      -- Porting note: Lean cannot infer this instance by itself
    · haveI : Subsingleton (Sym α 0) := Unique.instSubsingleton
      rw [_root_.pow_zero, Fintype.sum_subsingleton]
      swap
        -- Porting note: Lean cannot infer this instance by itself
      · have : Zero (Sym α 0) := Sym.instZeroSym
        exact ⟨0, by simp [eq_iff_true_of_subsingleton]⟩
      convert (@one_mul R _ _).symm
      convert @Nat.cast_one R _
    · rw [_root_.pow_succ, mul_zero]
      -- Porting note: Lean cannot infer this instance by itself
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
#align finset.sum_pow_of_commute Finset.sum_pow_of_commute


theorem sum_pow [CommSemiring R] (x : α → R) (n : ℕ) :
    s.sum x ^ n = ∑ k ∈ s.sym n, k.val.multinomial * (k.val.map x).prod := by
  conv_rhs => rw [← sum_coe_sort]
  convert sum_pow_of_commute s x (fun _ _ _ _ _ => mul_comm _ _) n
  rw [Multiset.noncommProd_eq_prod]
#align finset.sum_pow Finset.sum_pow

end Finset

namespace Sym

variable {n : ℕ} {α : Type*} [DecidableEq α]

theorem multinomial_coe_fill_of_not_mem {m : Fin (n + 1)} {s : Sym α (n - m)} {x : α} (hx : x ∉ s) :
    (fill x m s : Multiset α).multinomial = n.choose m * (s : Multiset α).multinomial := by
  rw [Multiset.multinomial_filter_ne x]
  rw [← mem_coe] at hx
  refine congrArg₂ _ ?_ ?_
  · rw [card_coe, count_coe_fill_self_of_not_mem hx]
  · refine congrArg _ ?_
    rw [coe_fill, coe_replicate, Multiset.filter_add]
    rw [Multiset.filter_eq_self.mpr]
    · rw [add_right_eq_self]
      rw [Multiset.filter_eq_nil]
      exact fun j hj ↦ by simp [Multiset.mem_replicate.mp hj]
    · exact fun j hj h ↦ hx <| by simpa [h] using hj

end Sym
