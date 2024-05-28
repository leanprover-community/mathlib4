/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Nat.Prime
import Mathlib.Data.List.Prime
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Chain

#align_import data.nat.factors from "leanprover-community/mathlib"@"008205aa645b3f194c1da47025c5f110c8406eab"

/-!
# Prime numbers

This file deals with the factors of natural numbers.

## Important declarations

- `Nat.factors n`: the prime factorization of `n`
- `Nat.factors_unique`: uniqueness of the prime factorisation

-/

open Bool Subtype

open Nat

namespace Nat

attribute [instance 0] instBEqNat

/-- `factors n` is the prime factorization of `n`, listed in increasing order. -/
def factors : ℕ → List ℕ
  | 0 => []
  | 1 => []
  | k + 2 =>
    let m := minFac (k + 2)
    m :: factors ((k + 2) / m)
decreasing_by show (k + 2) / m < (k + 2); exact factors_lemma
#align nat.factors Nat.factors

@[simp]
theorem factors_zero : factors 0 = [] := by rw [factors]
#align nat.factors_zero Nat.factors_zero

@[simp]
theorem factors_one : factors 1 = [] := by rw [factors]
#align nat.factors_one Nat.factors_one

@[simp]
theorem factors_two : factors 2 = [2] := by simp [factors]

theorem prime_of_mem_factors {n : ℕ} : ∀ {p : ℕ}, (h : p ∈ factors n) → Prime p := by
  match n with
  | 0 => simp
  | 1 => simp
  | k + 2 =>
      intro p h
      let m := minFac (k + 2)
      have : (k + 2) / m < (k + 2) := factors_lemma
      have h₁ : p = m ∨ p ∈ factors ((k + 2) / m) :=
        List.mem_cons.1 (by rwa [factors] at h)
      exact Or.casesOn h₁ (fun h₂ => h₂.symm ▸ minFac_prime (by simp)) prime_of_mem_factors
#align nat.prime_of_mem_factors Nat.prime_of_mem_factors

theorem pos_of_mem_factors {n p : ℕ} (h : p ∈ factors n) : 0 < p :=
  Prime.pos (prime_of_mem_factors h)
#align nat.pos_of_mem_factors Nat.pos_of_mem_factors

theorem prod_factors : ∀ {n}, n ≠ 0 → List.prod (factors n) = n
  | 0 => by simp
  | 1 => by simp
  | k + 2 => fun _ =>
    let m := minFac (k + 2)
    have : (k + 2) / m < (k + 2) := factors_lemma
    show (factors (k + 2)).prod = (k + 2) by
      have h₁ : (k + 2) / m ≠ 0 := fun h => by
        have : (k + 2) = 0 * m := (Nat.div_eq_iff_eq_mul_left (minFac_pos _) (minFac_dvd _)).1 h
        rw [zero_mul] at this; exact (show k + 2 ≠ 0 by simp) this
      rw [factors, List.prod_cons, prod_factors h₁, Nat.mul_div_cancel' (minFac_dvd _)]
#align nat.prod_factors Nat.prod_factors

theorem factors_prime {p : ℕ} (hp : Nat.Prime p) : p.factors = [p] := by
  have : p = p - 2 + 2 := (tsub_eq_iff_eq_add_of_le hp.two_le).mp rfl
  rw [this, Nat.factors]
  simp only [Eq.symm this]
  have : Nat.minFac p = p := (Nat.prime_def_minFac.mp hp).2
  simp only [this, Nat.factors, Nat.div_self (Nat.Prime.pos hp)]
#align nat.factors_prime Nat.factors_prime

theorem factors_chain {n : ℕ} :
    ∀ {a}, (∀ p, Prime p → p ∣ n → a ≤ p) → List.Chain (· ≤ ·) a (factors n) := by
  match n with
  | 0 => simp
  | 1 => simp
  | k + 2 =>
      intro a h
      let m := minFac (k + 2)
      have : (k + 2) / m < (k + 2) := factors_lemma
      rw [factors]
      refine List.Chain.cons ((le_minFac.2 h).resolve_left (by simp)) (factors_chain ?_)
      exact fun p pp d => minFac_le_of_dvd pp.two_le (d.trans <| div_dvd_of_dvd <| minFac_dvd _)
#align nat.factors_chain Nat.factors_chain

theorem factors_chain_2 (n) : List.Chain (· ≤ ·) 2 (factors n) :=
  factors_chain fun _ pp _ => pp.two_le
#align nat.factors_chain_2 Nat.factors_chain_2

theorem factors_chain' (n) : List.Chain' (· ≤ ·) (factors n) :=
  @List.Chain'.tail _ _ (_ :: _) (factors_chain_2 _)
#align nat.factors_chain' Nat.factors_chain'

theorem factors_sorted (n : ℕ) : List.Sorted (· ≤ ·) (factors n) :=
  List.chain'_iff_pairwise.1 (factors_chain' _)
#align nat.factors_sorted Nat.factors_sorted

/-- `factors` can be constructed inductively by extracting `minFac`, for sufficiently large `n`. -/
theorem factors_add_two (n : ℕ) :
    factors (n + 2) = minFac (n + 2) :: factors ((n + 2) / minFac (n + 2)) := by rw [factors]
#align nat.factors_add_two Nat.factors_add_two

@[simp]
theorem factors_eq_nil (n : ℕ) : n.factors = [] ↔ n = 0 ∨ n = 1 := by
  constructor <;> intro h
  · rcases n with (_ | _ | n)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rw [factors] at h
      injection h
  · rcases h with (rfl | rfl)
    · exact factors_zero
    · exact factors_one
#align nat.factors_eq_nil Nat.factors_eq_nil

open scoped List in
theorem eq_of_perm_factors {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a.factors ~ b.factors) :
    a = b := by simpa [prod_factors ha, prod_factors hb] using List.Perm.prod_eq h
#align nat.eq_of_perm_factors Nat.eq_of_perm_factors

section

open List

theorem mem_factors_iff_dvd {n p : ℕ} (hn : n ≠ 0) (hp : Prime p) : p ∈ factors n ↔ p ∣ n :=
  ⟨fun h => prod_factors hn ▸ List.dvd_prod h, fun h =>
    mem_list_primes_of_dvd_prod (prime_iff.mp hp) (fun _ h => prime_iff.mp (prime_of_mem_factors h))
      ((prod_factors hn).symm ▸ h)⟩
#align nat.mem_factors_iff_dvd Nat.mem_factors_iff_dvd

theorem dvd_of_mem_factors {n p : ℕ} (h : p ∈ n.factors) : p ∣ n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · exact dvd_zero p
  · rwa [← mem_factors_iff_dvd hn.ne' (prime_of_mem_factors h)]
#align nat.dvd_of_mem_factors Nat.dvd_of_mem_factors

theorem mem_factors {n p} (hn : n ≠ 0) : p ∈ factors n ↔ Prime p ∧ p ∣ n :=
  ⟨fun h => ⟨prime_of_mem_factors h, dvd_of_mem_factors h⟩, fun ⟨hprime, hdvd⟩ =>
    (mem_factors_iff_dvd hn hprime).mpr hdvd⟩
#align nat.mem_factors Nat.mem_factors

@[simp] lemma mem_factors' {n p} : p ∈ n.factors ↔ p.Prime ∧ p ∣ n ∧ n ≠ 0 := by
  cases n <;> simp [mem_factors, *]

theorem le_of_mem_factors {n p : ℕ} (h : p ∈ n.factors) : p ≤ n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · rw [factors_zero] at h
    cases h
  · exact le_of_dvd hn (dvd_of_mem_factors h)
#align nat.le_of_mem_factors Nat.le_of_mem_factors

/-- **Fundamental theorem of arithmetic**-/
theorem factors_unique {n : ℕ} {l : List ℕ} (h₁ : prod l = n) (h₂ : ∀ p ∈ l, Prime p) :
    l ~ factors n := by
  refine perm_of_prod_eq_prod ?_ ?_ ?_
  · rw [h₁]
    refine (prod_factors ?_).symm
    rintro rfl
    rw [prod_eq_zero_iff] at h₁
    exact Prime.ne_zero (h₂ 0 h₁) rfl
  · simp_rw [← prime_iff]
    exact h₂
  · simp_rw [← prime_iff]
    exact fun p => prime_of_mem_factors
#align nat.factors_unique Nat.factors_unique

theorem Prime.factors_pow {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (p ^ n).factors = List.replicate n p := by
  symm
  rw [← List.replicate_perm]
  apply Nat.factors_unique (List.prod_replicate n p)
  intro q hq
  rwa [eq_of_mem_replicate hq]
#align nat.prime.factors_pow Nat.Prime.factors_pow

theorem eq_prime_pow_of_unique_prime_dvd {n p : ℕ} (hpos : n ≠ 0)
    (h : ∀ {d}, Nat.Prime d → d ∣ n → d = p) : n = p ^ n.factors.length := by
  set k := n.factors.length
  rw [← prod_factors hpos, ← prod_replicate k p,
    eq_replicate_of_mem fun d hd => h (prime_of_mem_factors hd) (dvd_of_mem_factors hd)]
#align nat.eq_prime_pow_of_unique_prime_dvd Nat.eq_prime_pow_of_unique_prime_dvd

/-- For positive `a` and `b`, the prime factors of `a * b` are the union of those of `a` and `b` -/
theorem perm_factors_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).factors ~ a.factors ++ b.factors := by
  refine (factors_unique ?_ ?_).symm
  · rw [List.prod_append, prod_factors ha, prod_factors hb]
  · intro p hp
    rw [List.mem_append] at hp
    cases' hp with hp' hp' <;> exact prime_of_mem_factors hp'
#align nat.perm_factors_mul Nat.perm_factors_mul

/-- For coprime `a` and `b`, the prime factors of `a * b` are the union of those of `a` and `b` -/
theorem perm_factors_mul_of_coprime {a b : ℕ} (hab : Coprime a b) :
    (a * b).factors ~ a.factors ++ b.factors := by
  rcases a.eq_zero_or_pos with (rfl | ha)
  · simp [(coprime_zero_left _).mp hab]
  rcases b.eq_zero_or_pos with (rfl | hb)
  · simp [(coprime_zero_right _).mp hab]
  exact perm_factors_mul ha.ne' hb.ne'
#align nat.perm_factors_mul_of_coprime Nat.perm_factors_mul_of_coprime

theorem factors_sublist_right {n k : ℕ} (h : k ≠ 0) : n.factors <+ (n * k).factors := by
  cases' n with hn
  · simp [zero_mul]
  apply sublist_of_subperm_of_sorted _ (factors_sorted _) (factors_sorted _)
  simp only [(perm_factors_mul (Nat.succ_ne_zero _) h).subperm_left]
  exact (sublist_append_left _ _).subperm
#align nat.factors_sublist_right Nat.factors_sublist_right

theorem factors_sublist_of_dvd {n k : ℕ} (h : n ∣ k) (h' : k ≠ 0) : n.factors <+ k.factors := by
  obtain ⟨a, rfl⟩ := h
  exact factors_sublist_right (right_ne_zero_of_mul h')
#align nat.factors_sublist_of_dvd Nat.factors_sublist_of_dvd

theorem factors_subset_right {n k : ℕ} (h : k ≠ 0) : n.factors ⊆ (n * k).factors :=
  (factors_sublist_right h).subset
#align nat.factors_subset_right Nat.factors_subset_right

theorem factors_subset_of_dvd {n k : ℕ} (h : n ∣ k) (h' : k ≠ 0) : n.factors ⊆ k.factors :=
  (factors_sublist_of_dvd h h').subset
#align nat.factors_subset_of_dvd Nat.factors_subset_of_dvd

theorem dvd_of_factors_subperm {a b : ℕ} (ha : a ≠ 0) (h : a.factors <+~ b.factors) : a ∣ b := by
  rcases b.eq_zero_or_pos with (rfl | hb)
  · exact dvd_zero _
  rcases a with (_ | _ | a)
  · exact (ha rfl).elim
  · exact one_dvd _
  -- Porting note: previous proof
  --use (b.factors.diff a.succ.succ.factors).prod
  use (@List.diff _ instBEqOfDecidableEq b.factors a.succ.succ.factors).prod
  nth_rw 1 [← Nat.prod_factors ha]
  rw [← List.prod_append,
    List.Perm.prod_eq <| List.subperm_append_diff_self_of_count_le <| List.subperm_ext_iff.mp h,
    Nat.prod_factors hb.ne']
#align nat.dvd_of_factors_subperm Nat.dvd_of_factors_subperm

theorem replicate_subperm_factors_iff {a b n : ℕ} (ha : Prime a) (hb : b ≠ 0) :
    replicate n a <+~ factors b ↔ a ^ n ∣ b := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    constructor
    · rw [List.subperm_iff]
      rintro ⟨u, hu1, hu2⟩
      rw [← Nat.prod_factors hb, ← hu1.prod_eq, ← prod_replicate]
      exact hu2.prod_dvd_prod
    · rintro ⟨c, rfl⟩
      rw [Ne, pow_succ', mul_assoc, mul_eq_zero, _root_.not_or] at hb
      rw [pow_succ', mul_assoc, replicate_succ, (Nat.perm_factors_mul hb.1 hb.2).subperm_left,
        factors_prime ha, singleton_append, subperm_cons, ih hb.2]
      exact dvd_mul_right _ _

end

theorem mem_factors_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) {p : ℕ} :
    p ∈ (a * b).factors ↔ p ∈ a.factors ∨ p ∈ b.factors := by
  rw [mem_factors (mul_ne_zero ha hb), mem_factors ha, mem_factors hb, ← and_or_left]
  simpa only [and_congr_right_iff] using Prime.dvd_mul
#align nat.mem_factors_mul Nat.mem_factors_mul

/-- The sets of factors of coprime `a` and `b` are disjoint -/
theorem coprime_factors_disjoint {a b : ℕ} (hab : a.Coprime b) :
    List.Disjoint a.factors b.factors := by
  intro q hqa hqb
  apply not_prime_one
  rw [← eq_one_of_dvd_coprimes hab (dvd_of_mem_factors hqa) (dvd_of_mem_factors hqb)]
  exact prime_of_mem_factors hqa
#align nat.coprime_factors_disjoint Nat.coprime_factors_disjoint

theorem mem_factors_mul_of_coprime {a b : ℕ} (hab : Coprime a b) (p : ℕ) :
    p ∈ (a * b).factors ↔ p ∈ a.factors ∪ b.factors := by
  rcases a.eq_zero_or_pos with (rfl | ha)
  · simp [(coprime_zero_left _).mp hab]
  rcases b.eq_zero_or_pos with (rfl | hb)
  · simp [(coprime_zero_right _).mp hab]
  rw [mem_factors_mul ha.ne' hb.ne', List.mem_union_iff]
#align nat.mem_factors_mul_of_coprime Nat.mem_factors_mul_of_coprime

open List

/-- If `p` is a prime factor of `a` then `p` is also a prime factor of `a * b` for any `b > 0` -/
theorem mem_factors_mul_left {p a b : ℕ} (hpa : p ∈ a.factors) (hb : b ≠ 0) :
    p ∈ (a * b).factors := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp at hpa
  apply (mem_factors_mul ha hb).2 (Or.inl hpa)
#align nat.mem_factors_mul_left Nat.mem_factors_mul_left

/-- If `p` is a prime factor of `b` then `p` is also a prime factor of `a * b` for any `a > 0` -/
theorem mem_factors_mul_right {p a b : ℕ} (hpb : p ∈ b.factors) (ha : a ≠ 0) :
    p ∈ (a * b).factors := by
  rw [mul_comm]
  exact mem_factors_mul_left hpb ha
#align nat.mem_factors_mul_right Nat.mem_factors_mul_right

theorem eq_two_pow_or_exists_odd_prime_and_dvd (n : ℕ) :
    (∃ k : ℕ, n = 2 ^ k) ∨ ∃ p, Nat.Prime p ∧ p ∣ n ∧ Odd p :=
  (eq_or_ne n 0).elim (fun hn => Or.inr ⟨3, prime_three, hn.symm ▸ dvd_zero 3, ⟨1, rfl⟩⟩) fun hn =>
    or_iff_not_imp_right.mpr fun H =>
      ⟨n.factors.length,
        eq_prime_pow_of_unique_prime_dvd hn fun {_} hprime hdvd =>
          hprime.eq_two_or_odd'.resolve_right fun hodd => H ⟨_, hprime, hdvd, hodd⟩⟩
#align nat.eq_two_pow_or_exists_odd_prime_and_dvd Nat.eq_two_pow_or_exists_odd_prime_and_dvd

theorem four_dvd_or_exists_odd_prime_and_dvd_of_two_lt {n : ℕ} (n2 : 2 < n) :
    4 ∣ n ∨ ∃ p, Prime p ∧ p ∣ n ∧ Odd p := by
  obtain ⟨_ | _ | k, rfl⟩ | ⟨p, hp, hdvd, hodd⟩ := n.eq_two_pow_or_exists_odd_prime_and_dvd
  · contradiction
  · contradiction
  · simp [Nat.pow_succ, mul_assoc]
  · exact Or.inr ⟨p, hp, hdvd, hodd⟩

end Nat

assert_not_exists Multiset
