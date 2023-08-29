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

- `Finest.sum_pow`: The expansion of `(s.sum x) ^ n` using multinomial coefficients

-/


open BigOperators Nat

open BigOperators

namespace Nat

variable {α : Type*} (s : Finset α) (f : α → ℕ) {a b : α} (n : ℕ)

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
theorem multinomial_nil : multinomial ∅ f = 1 := by
  dsimp [multinomial]
  -- ⊢ 1 / 1 = 1
  rfl
  -- 🎉 no goals
#align nat.multinomial_nil Nat.multinomial_nil

@[simp]
theorem multinomial_singleton : multinomial {a} f = 1 := by
  simp [multinomial, Nat.div_self (factorial_pos (f a))]
  -- 🎉 no goals
#align nat.multinomial_singleton Nat.multinomial_singleton

@[simp]
theorem multinomial_insert_one [DecidableEq α] (h : a ∉ s) (h₁ : f a = 1) :
    multinomial (insert a s) f = (s.sum f).succ * multinomial s f := by
  simp only [multinomial, one_mul, factorial]
  -- ⊢ (∑ i in insert a s, f i)! / ∏ i in insert a s, (f i)! = succ (Finset.sum s f …
  rw [Finset.sum_insert h, Finset.prod_insert h, h₁, add_comm, ← succ_eq_add_one, factorial_succ]
  -- ⊢ (∑ x in s, f x + 1) * (∑ x in s, f x)! / (1! * ∏ x in s, (f x)!) = succ (Fin …
  simp only [factorial_one, one_mul, Function.comp_apply, factorial, mul_one, ← one_eq_succ_zero]
  -- ⊢ (∑ x in s, f x + 1) * (∑ x in s, f x)! / ∏ x in s, (f x)! = succ (Finset.sum …
  rw [Nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum _ _)]
  -- 🎉 no goals
#align nat.multinomial_insert_one Nat.multinomial_insert_one

theorem multinomial_insert [DecidableEq α] (h : a ∉ s) :
    multinomial (insert a s) f = (f a + s.sum f).choose (f a) * multinomial s f := by
  rw [choose_eq_factorial_div_factorial (le.intro rfl)]
  -- ⊢ multinomial (insert a s) f = (f a + Finset.sum s f)! / ((f a)! * (f a + Fins …
  simp only [multinomial, Nat.add_sub_cancel_left, Finset.sum_insert h, Finset.prod_insert h,
    Function.comp_apply]
  rw [div_mul_div_comm ((f a).factorial_mul_factorial_dvd_factorial_add (s.sum f))
      (prod_factorial_dvd_factorial_sum _ _),
    mul_comm (f a)! (s.sum f)!, mul_assoc, mul_comm _ (s.sum f)!,
    Nat.mul_div_mul_left _ _ (factorial_pos _)]
#align nat.multinomial_insert Nat.multinomial_insert

theorem multinomial_congr {f g : α → ℕ} (h : ∀ a ∈ s, f a = g a) :
    multinomial s f = multinomial s g := by
  simp only [multinomial]; congr 1
  -- ⊢ (∑ i in s, f i)! / ∏ i in s, (f i)! = (∑ i in s, g i)! / ∏ i in s, (g i)!
                           -- ⊢ (∑ i in s, f i)! = (∑ i in s, g i)!
  · rw [Finset.sum_congr rfl h]
    -- 🎉 no goals
  · exact Finset.prod_congr rfl fun a ha => by rw [h a ha]
    -- 🎉 no goals
#align nat.multinomial_congr Nat.multinomial_congr

/-! ### Connection to binomial coefficients

When `Nat.multinomial` is applied to a `Finset` of two elements `{a, b}`, the
result a binomial coefficient. We use `binomial` in the names of lemmas that
involves `Nat.multinomial {a, b}`.
-/


theorem binomial_eq [DecidableEq α] (h : a ≠ b) :
    multinomial {a, b} f = (f a + f b)! / ((f a)! * (f b)!) := by
  simp [multinomial, Finset.sum_pair h, Finset.prod_pair h]
  -- 🎉 no goals
#align nat.binomial_eq Nat.binomial_eq

theorem binomial_eq_choose [DecidableEq α] (h : a ≠ b) :
    multinomial {a, b} f = (f a + f b).choose (f a) := by
  simp [binomial_eq _ h, choose_eq_factorial_div_factorial (Nat.le_add_right _ _)]
  -- 🎉 no goals
#align nat.binomial_eq_choose Nat.binomial_eq_choose

theorem binomial_spec [DecidableEq α] (hab : a ≠ b) :
    (f a)! * (f b)! * multinomial {a, b} f = (f a + f b)! := by
  simpa [Finset.sum_pair hab, Finset.prod_pair hab] using multinomial_spec {a, b} f
  -- 🎉 no goals
#align nat.binomial_spec Nat.binomial_spec

@[simp]
theorem binomial_one [DecidableEq α] (h : a ≠ b) (h₁ : f a = 1) :
    multinomial {a, b} f = (f b).succ := by
  simp [multinomial_insert_one {b} f (Finset.not_mem_singleton.mpr h) h₁]
  -- 🎉 no goals
#align nat.binomial_one Nat.binomial_one

theorem binomial_succ_succ [DecidableEq α] (h : a ≠ b) :
    multinomial {a, b} (Function.update (Function.update f a (f a).succ) b (f b).succ) =
      multinomial {a, b} (Function.update f a (f a).succ) +
      multinomial {a, b} (Function.update f b (f b).succ) := by
  simp only [binomial_eq_choose, Function.update_apply,
    h, Ne.def, ite_true, ite_false]
  rw [if_neg h.symm]
  -- ⊢ choose (succ (f a) + succ (f b)) (succ (f a)) = choose (succ (f a) + f b) (s …
  rw [add_succ, choose_succ_succ, succ_add_eq_succ_add]
  -- ⊢ choose (f a + succ (f b)) (f a) + choose (f a + succ (f b)) (succ (f a)) = c …
  ring
  -- 🎉 no goals
#align nat.binomial_succ_succ Nat.binomial_succ_succ

theorem succ_mul_binomial [DecidableEq α] (h : a ≠ b) :
    (f a + f b).succ * multinomial {a, b} f =
      (f a).succ * multinomial {a, b} (Function.update f a (f a).succ) := by
  rw [binomial_eq_choose _ h, binomial_eq_choose _ h, mul_comm (f a).succ, Function.update_same,
    Function.update_noteq (ne_comm.mp h)]
  rw [succ_mul_choose_eq (f a + f b) (f a), succ_add (f a) (f b)]
  -- 🎉 no goals
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
  -- ⊢ (Matrix.vecCons a ![b, c] 0 + Matrix.vecCons a ![b, c] 1 + Matrix.vecCons a  …
  rfl
  -- 🎉 no goals
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
  -- ⊢ Nat.multinomial f.support ↑f = choose (sum f fun x => id) (↑f a) * Nat.multi …
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

variable {α : Type*}

/-- Alternative definition of multinomial based on `Multiset` delegating to the
  finsupp definition
-/
def multinomial [DecidableEq α] (m : Multiset α) : ℕ :=
  m.toFinsupp.multinomial
#align multiset.multinomial Multiset.multinomial

theorem multinomial_filter_ne [DecidableEq α] (a : α) (m : Multiset α) :
    m.multinomial = m.card.choose (m.count a) * (m.filter ((· ≠ ·) a)).multinomial := by
  dsimp only [multinomial]
  -- ⊢ Finsupp.multinomial (↑toFinsupp m) = Nat.choose (↑card m) (count a m) * Fins …
  convert Finsupp.multinomial_update a _
  -- ⊢ ↑card m = Finsupp.sum (↑toFinsupp m) fun x => id
  · rw [← Finsupp.card_toMultiset, m.toFinsupp_toMultiset]
    -- 🎉 no goals
  · ext1 a
    -- ⊢ ↑(↑toFinsupp (filter (fun x => a✝ ≠ x) m)) a = ↑(Finsupp.update (↑toFinsupp  …
    rw [toFinsupp_apply, count_filter, Finsupp.coe_update]
    -- ⊢ (if a✝ ≠ a then count a m else 0) = Function.update (↑(↑toFinsupp m)) a✝ 0 a
    split_ifs with h
    -- ⊢ count a m = Function.update (↑(↑toFinsupp m)) a✝ 0 a
    · rw [Function.update_noteq h.symm, toFinsupp_apply]
      -- 🎉 no goals
    · rw [not_ne_iff.1 h, Function.update_same]
      -- 🎉 no goals
#align multiset.multinomial_filter_ne Multiset.multinomial_filter_ne

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
  -- ⊢ ∀ (n : ℕ), Finset.sum ∅ x ^ n = ∑ k : { x // x ∈ Finset.sym ∅ n }, ↑(Multise …
  · rw [sum_empty]
    -- ⊢ ∀ (n : ℕ), 0 ^ n = ∑ k : { x // x ∈ Finset.sym ∅ n }, ↑(Multiset.multinomial …
    rintro (_ | n)
    -- ⊢ 0 ^ zero = ∑ k : { x // x ∈ Finset.sym ∅ zero }, ↑(Multiset.multinomial ↑↑k) …
      -- Porting note : Lean cannot infer this instance by itself
    · haveI : Subsingleton (Sym α 0) := Unique.instSubsingleton
      -- ⊢ 0 ^ zero = ∑ k : { x // x ∈ Finset.sym ∅ zero }, ↑(Multiset.multinomial ↑↑k) …
      rw [_root_.pow_zero, Fintype.sum_subsingleton]
      -- ⊢ 1 = ↑(Multiset.multinomial ↑↑?empty.zero.a) * Multiset.noncommProd (Multiset …
      swap
      -- ⊢ { x // x ∈ Finset.sym ∅ zero }
        -- Porting note : Lean cannot infer this instance by itself
      · have : Zero (Sym α 0) := Sym.instZeroSym
        -- ⊢ { x // x ∈ Finset.sym ∅ zero }
        exact ⟨0, by simp⟩
        -- 🎉 no goals
      convert (@one_mul R _ _).symm
      -- ⊢ ↑(Multiset.multinomial
      dsimp only
      -- ⊢ ↑(Multiset.multinomial ↑0) = 1
      convert @Nat.cast_one R _
      -- 🎉 no goals
    · rw [_root_.pow_succ, zero_mul]
      -- ⊢ 0 = ∑ k : { x // x ∈ Finset.sym ∅ (succ n) }, ↑(Multiset.multinomial ↑↑k) *  …
      -- Porting note : Lean cannot infer this instance by itself
      haveI : IsEmpty (Finset.sym (∅ : Finset α) (succ n)) := Finset.instIsEmpty
      -- ⊢ 0 = ∑ k : { x // x ∈ Finset.sym ∅ (succ n) }, ↑(Multiset.multinomial ↑↑k) *  …
      apply (Fintype.sum_empty _).symm
      -- 🎉 no goals
  intro n; specialize ih (hc.mono <| s.subset_insert a)
  -- ⊢ Finset.sum (insert a s) x ^ n = ∑ k : { x // x ∈ Finset.sym (insert a s) n } …
           -- ⊢ Finset.sum (insert a s) x ^ n = ∑ k : { x // x ∈ Finset.sym (insert a s) n } …
  rw [sum_insert ha, (Commute.sum_right s _ _ _).add_pow, sum_range]; swap
  -- ⊢ ∑ i : Fin (n + 1), x a ^ ↑i * (∑ i in s, x i) ^ (n - ↑i) * ↑(Nat.choose n ↑i …
                                                                      -- ⊢ ∀ (i : α), i ∈ s → Commute (x a) (x i)
  · exact fun _ hb => hc (mem_insert_self a s) (mem_insert_of_mem hb)
      (ne_of_mem_of_not_mem hb ha).symm
  · simp_rw [ih, mul_sum, sum_mul, sum_sigma', univ_sigma_univ]
    -- ⊢ ∑ x_1 : (i : Fin (n + 1)) × { x // x ∈ Finset.sym s (n - ↑i) }, x a ^ ↑x_1.f …
    refine' (Fintype.sum_equiv (symInsertEquiv ha) _ _ fun m => _).symm
    -- ⊢ ↑(Multiset.multinomial ↑↑m) * Multiset.noncommProd (Multiset.map x ↑↑m) (_ : …
    rw [m.1.1.multinomial_filter_ne a]
    -- ⊢ ↑(Nat.choose (↑Multiset.card ↑↑m) (Multiset.count a ↑↑m) * Multiset.multinom …
    conv in m.1.1.map _ => rw [← m.1.1.filter_add_not ((· = ·) a), Multiset.map_add]
    -- ⊢ ↑(Nat.choose (↑Multiset.card ↑↑m) (Multiset.count a ↑↑m) * Multiset.multinom …
    simp_rw [Multiset.noncommProd_add, m.1.1.filter_eq, Multiset.map_replicate, m.1.2]
    -- ⊢ ↑(Nat.choose n (Multiset.count a ↑↑m) * Multiset.multinomial (Multiset.filte …
    rw [Multiset.noncommProd_eq_pow_card _ _ _ fun _ => Multiset.eq_of_mem_replicate]
    -- ⊢ ↑(Nat.choose n (Multiset.count a ↑↑m) * Multiset.multinomial (Multiset.filte …
    rw [Multiset.card_replicate, Nat.cast_mul, mul_assoc, Nat.cast_comm]
    -- ⊢ ↑(Multiset.multinomial (Multiset.filter (fun x => a ≠ x) ↑↑m)) * (x a ^ Mult …
    congr 1; simp_rw [← mul_assoc, Nat.cast_comm]; rfl
    -- ⊢ ↑(Multiset.multinomial (Multiset.filter (fun x => a ≠ x) ↑↑m)) * (x a ^ Mult …
             -- ⊢ x a ^ Multiset.count a ↑↑m * ↑(Multiset.multinomial (Multiset.filter (fun x  …
                                                   -- 🎉 no goals
#align finset.sum_pow_of_commute Finset.sum_pow_of_commute


theorem sum_pow [CommSemiring R] (x : α → R) (n : ℕ) :
    s.sum x ^ n = ∑ k in s.sym n, k.val.multinomial * (k.val.map x).prod := by
  conv_rhs => rw [← sum_coe_sort]
  -- ⊢ Finset.sum s x ^ n = ∑ i : { x // x ∈ Finset.sym s n }, ↑(Multiset.multinomi …
  convert sum_pow_of_commute s x (fun _ _ _ _ _ => mul_comm _ _) n
  -- ⊢ Multiset.prod (Multiset.map x ↑↑x✝) = Multiset.noncommProd (Multiset.map x ↑ …
  rw [Multiset.noncommProd_eq_prod]
  -- 🎉 no goals
#align finset.sum_pow Finset.sum_pow

end Finset
