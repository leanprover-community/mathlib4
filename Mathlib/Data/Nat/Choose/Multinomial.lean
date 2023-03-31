/-
Copyright (c) 2022 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte

! This file was ported from Lean 3 source module data.nat.choose.multinomial
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Fin
import Mathbin.Data.Nat.Choose.Sum
import Mathbin.Data.Nat.Factorial.BigOperators
import Mathbin.Data.Fin.VecNotation
import Mathbin.Data.Finset.Sym
import Mathbin.Data.Finsupp.Multiset

/-!
# Multinomial

This file defines the multinomial coefficient and several small lemma's for manipulating it.

## Main declarations

- `nat.multinomial`: the multinomial coefficient

## Main results

- `finest.sum_pow`: The expansion of `(s.sum x) ^ n` using multinomial coefficients

-/


open BigOperators Nat

open BigOperators

namespace Nat

variable {α : Type _} (s : Finset α) (f : α → ℕ) {a b : α} (n : ℕ)

/-- The multinomial coefficient. Gives the number of strings consisting of symbols
from `s`, where `c ∈ s` appears with multiplicity `f c`.

Defined as `(∑ i in s, f i)! / ∏ i in s, (f i)!`.
-/
def multinomial : ℕ :=
  (∑ i in s, f i)! / ∏ i in s, (f i)!
#align nat.multinomial Nat.multinomial

theorem multinomial_pos : 0 < multinomial s f :=
  Nat.div_pos (le_of_dvd (factorial_pos _) (prod_factorial_dvd_factorial_sum s f))
    (prod_factorial_pos s f)
#align nat.multinomial_pos Nat.multinomial_pos

theorem multinomial_spec : (∏ i in s, (f i)!) * multinomial s f = (∑ i in s, f i)! :=
  Nat.mul_div_cancel' (prod_factorial_dvd_factorial_sum s f)
#align nat.multinomial_spec Nat.multinomial_spec

@[simp]
theorem multinomial_nil : multinomial ∅ f = 1 :=
  rfl
#align nat.multinomial_nil Nat.multinomial_nil

@[simp]
theorem multinomial_singleton : multinomial {a} f = 1 := by
  simp [multinomial, Nat.div_self (factorial_pos (f a))]
#align nat.multinomial_singleton Nat.multinomial_singleton

@[simp]
theorem multinomial_insert_one [DecidableEq α] (h : a ∉ s) (h₁ : f a = 1) :
    multinomial (insert a s) f = (s.Sum f).succ * multinomial s f :=
  by
  simp only [multinomial, one_mul, factorial]
  rw [Finset.sum_insert h, Finset.prod_insert h, h₁, add_comm, ← succ_eq_add_one, factorial_succ]
  simp only [factorial_one, one_mul, Function.comp_apply, factorial]
  rw [Nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum _ _)]
#align nat.multinomial_insert_one Nat.multinomial_insert_one

theorem multinomial_insert [DecidableEq α] (h : a ∉ s) :
    multinomial (insert a s) f = (f a + s.Sum f).choose (f a) * multinomial s f :=
  by
  rw [choose_eq_factorial_div_factorial (le.intro rfl)]
  simp only [multinomial, Nat.add_sub_cancel_left, Finset.sum_insert h, Finset.prod_insert h,
    Function.comp_apply]
  rw [div_mul_div_comm ((f a).factorial_mul_factorial_dvd_factorial_add (s.sum f))
      (prod_factorial_dvd_factorial_sum _ _),
    mul_comm (f a)! (s.sum f)!, mul_assoc, mul_comm _ (s.sum f)!,
    Nat.mul_div_mul _ _ (factorial_pos _)]
#align nat.multinomial_insert Nat.multinomial_insert

theorem multinomial_congr {f g : α → ℕ} (h : ∀ a ∈ s, f a = g a) :
    multinomial s f = multinomial s g :=
  by
  simp only [multinomial]; congr 1
  · rw [Finset.sum_congr rfl h]
  · exact Finset.prod_congr rfl fun a ha => by rw [h a ha]
#align nat.multinomial_congr Nat.multinomial_congr

/-! ### Connection to binomial coefficients

When `nat.multinomial` is applied to a `finset` of two elements `{a, b}`, the
result a binomial coefficient. We use `binomial` in the names of lemmas that
involves `nat.multinomial {a, b}`.
-/


theorem binomial_eq [DecidableEq α] (h : a ≠ b) :
    multinomial {a, b} f = (f a + f b)! / ((f a)! * (f b)!) := by
  simp [multinomial, Finset.sum_pair h, Finset.prod_pair h]
#align nat.binomial_eq Nat.binomial_eq

theorem binomial_eq_choose [DecidableEq α] (h : a ≠ b) :
    multinomial {a, b} f = (f a + f b).choose (f a) := by
  simp [binomial_eq _ h, choose_eq_factorial_div_factorial (Nat.le_add_right _ _)]
#align nat.binomial_eq_choose Nat.binomial_eq_choose

theorem binomial_spec [DecidableEq α] (hab : a ≠ b) :
    (f a)! * (f b)! * multinomial {a, b} f = (f a + f b)! := by
  simpa [Finset.sum_pair hab, Finset.prod_pair hab] using multinomial_spec {a, b} f
#align nat.binomial_spec Nat.binomial_spec

@[simp]
theorem binomial_one [DecidableEq α] (h : a ≠ b) (h₁ : f a = 1) :
    multinomial {a, b} f = (f b).succ := by
  simp [multinomial_insert_one {b} f (finset.not_mem_singleton.mpr h) h₁]
#align nat.binomial_one Nat.binomial_one

theorem binomial_succ_succ [DecidableEq α] (h : a ≠ b) :
    multinomial {a, b} ((f.update a (f a).succ).update b (f b).succ) =
      multinomial {a, b} (f.update a (f a).succ) + multinomial {a, b} (f.update b (f b).succ) :=
  by
  simp only [binomial_eq_choose, Function.update_apply, Function.update_noteq, succ_add, add_succ,
    choose_succ_succ, h, Ne.def, not_false_iff, Function.update_same]
  rw [if_neg h.symm]
  ring
#align nat.binomial_succ_succ Nat.binomial_succ_succ

theorem succ_mul_binomial [DecidableEq α] (h : a ≠ b) :
    (f a + f b).succ * multinomial {a, b} f =
      (f a).succ * multinomial {a, b} (f.update a (f a).succ) :=
  by
  rw [binomial_eq_choose _ h, binomial_eq_choose _ h, mul_comm (f a).succ, Function.update_same,
    Function.update_noteq (ne_comm.mp h)]
  convert succ_mul_choose_eq (f a + f b) (f a)
  exact succ_add (f a) (f b)
#align nat.succ_mul_binomial Nat.succ_mul_binomial

/-! ### Simple cases -/


theorem multinomial_univ_two (a b : ℕ) : multinomial Finset.univ ![a, b] = (a + b)! / (a ! * b !) :=
  by simp [multinomial, Fin.sum_univ_two, Fin.prod_univ_two]
#align nat.multinomial_univ_two Nat.multinomial_univ_two

theorem multinomial_univ_three (a b c : ℕ) :
    multinomial Finset.univ ![a, b, c] = (a + b + c)! / (a ! * b ! * c !) := by
  simp [multinomial, Fin.sum_univ_three, Fin.prod_univ_three]
#align nat.multinomial_univ_three Nat.multinomial_univ_three

end Nat

/-! ### Alternative definitions -/


namespace Finsupp

variable {α : Type _}

/-- Alternative multinomial definition based on a finsupp, using the support
  for the big operations
-/
def multinomial (f : α →₀ ℕ) : ℕ :=
  (f.Sum fun _ => id)! / f.Prod fun _ n => n !
#align finsupp.multinomial Finsupp.multinomial

theorem multinomial_eq (f : α →₀ ℕ) : f.multinomial = Nat.multinomial f.support f :=
  rfl
#align finsupp.multinomial_eq Finsupp.multinomial_eq

theorem multinomial_update (a : α) (f : α →₀ ℕ) :
    f.multinomial = (f.Sum fun _ => id).choose (f a) * (f.update a 0).multinomial :=
  by
  simp only [multinomial_eq]
  classical
    by_cases a ∈ f.support
    · rw [← Finset.insert_erase h, Nat.multinomial_insert _ f (Finset.not_mem_erase a _),
        Finset.add_sum_erase _ f h, support_update_zero]
      congr 1
      exact
        Nat.multinomial_congr _ fun _ h => (Function.update_noteq (Finset.mem_erase.1 h).1 0 f).symm
    rw [not_mem_support_iff] at h
    rw [h, Nat.choose_zero_right, one_mul, ← h, update_self]
#align finsupp.multinomial_update Finsupp.multinomial_update

end Finsupp

namespace Multiset

variable {α : Type _}

/-- Alternative definition of multinomial based on `multiset` delegating to the
  finsupp definition
-/
noncomputable def multinomial (m : Multiset α) : ℕ :=
  m.toFinsupp.multinomial
#align multiset.multinomial Multiset.multinomial

theorem multinomial_filter_ne [DecidableEq α] (a : α) (m : Multiset α) :
    m.multinomial = m.card.choose (m.count a) * (m.filterₓ ((· ≠ ·) a)).multinomial :=
  by
  dsimp only [multinomial]
  convert Finsupp.multinomial_update a _
  · rw [← Finsupp.card_toMultiset, m.to_finsupp_to_multiset]
  · ext1 a'
    rw [to_finsupp_apply, count_filter, Finsupp.coe_update]
    split_ifs
    · rw [Function.update_noteq h.symm, to_finsupp_apply]
    · rw [not_ne_iff.1 h, Function.update_same]
#align multiset.multinomial_filter_ne Multiset.multinomial_filter_ne

end Multiset

namespace Finset

/-! ### Multinomial theorem -/


variable {α : Type _} [DecidableEq α] (s : Finset α) {R : Type _}

/-- The multinomial theorem

  Proof is by induction on the number of summands.
-/
theorem sum_pow_of_commute [Semiring R] (x : α → R)
    (hc : (s : Set α).Pairwise fun i j => Commute (x i) (x j)) :
    ∀ n,
      s.Sum x ^ n =
        ∑ k : s.Sym n,
          k.1.1.multinomial *
            (k.1.1.map <| x).noncommProd
              (Multiset.map_set_pairwise <| hc.mono <| mem_sym_iff.1 k.2) :=
  by
  induction' s using Finset.induction with a s ha ih
  · rw [sum_empty]
    rintro (_ | n)
    · rw [pow_zero, Fintype.sum_subsingleton]
      swap
      · exact ⟨0, Or.inl rfl⟩
      convert (one_mul _).symm
      apply Nat.cast_one
    · rw [pow_succ, zero_mul]
      apply (Fintype.sum_empty _).symm
      rw [sym_empty]
      infer_instance
  intro n; specialize ih (hc.mono <| s.subset_insert a)
  rw [sum_insert ha, (Commute.sum_right s _ _ fun b hb => _).add_pow, sum_range]; swap
  · exact hc (mem_insert_self a s) (mem_insert_of_mem hb) (ne_of_mem_of_not_mem hb ha).symm
  simp_rw [ih, mul_sum, sum_mul, sum_sigma', univ_sigma_univ]
  refine' (Fintype.sum_equiv (sym_insert_equiv ha) _ _ fun m => _).symm
  rw [m.1.1.multinomial_filter_ne a]
  conv in m.1.1.map _ => rw [← m.1.1.filter_add_not ((· = ·) a), Multiset.map_add]
  simp_rw [Multiset.noncommProd_add, m.1.1.filter_eq, Multiset.map_replicate, m.1.2]
  rw [Multiset.noncommProd_eq_pow_card _ _ _ fun _ => Multiset.eq_of_mem_replicate]
  rw [Multiset.card_replicate, Nat.cast_mul, mul_assoc, Nat.cast_comm]
  congr 1; simp_rw [← mul_assoc, Nat.cast_comm]; rfl
#align finset.sum_pow_of_commute Finset.sum_pow_of_commute

theorem sum_pow [CommSemiring R] (x : α → R) (n : ℕ) :
    s.Sum x ^ n = ∑ k in s.Sym n, k.val.multinomial * (k.val.map x).Prod :=
  by
  conv_rhs => rw [← sum_coe_sort]
  convert sum_pow_of_commute s x (fun _ _ _ _ _ => mul_comm _ _) n
  ext1; rw [Multiset.noncommProd_eq_prod]; rfl
#align finset.sum_pow Finset.sum_pow

end Finset

