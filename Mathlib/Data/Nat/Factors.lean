/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.Prime
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Perm.Subperm

/-!
# Prime numbers

This file deals with the factors of natural numbers.

## Important declarations

- `Nat.primeFactorsList n`: the prime factorization of `n`
- `Nat.primeFactorsList_unique`: uniqueness of the prime factorisation

-/

assert_not_exists Multiset

open Bool Subtype

open Nat

namespace Nat

/-- `primeFactorsList n` is the prime factorization of `n`, listed in increasing order. -/
def primeFactorsList : ℕ → List ℕ
  | 0 => []
  | 1 => []
  | k + 2 =>
    let m := minFac (k + 2)
    m :: primeFactorsList ((k + 2) / m)
decreasing_by exact factors_lemma

@[simp]
theorem primeFactorsList_zero : primeFactorsList 0 = [] := by rw [primeFactorsList]

@[simp]
theorem primeFactorsList_one : primeFactorsList 1 = [] := by rw [primeFactorsList]

@[simp]
theorem primeFactorsList_two : primeFactorsList 2 = [2] := by simp [primeFactorsList]

theorem prime_of_mem_primeFactorsList {n : ℕ} : ∀ {p : ℕ}, p ∈ primeFactorsList n → Prime p := by
  match n with
  | 0 => simp
  | 1 => simp
  | k + 2 =>
      intro p h
      let m := minFac (k + 2)
      have : (k + 2) / m < (k + 2) := factors_lemma
      have h₁ : p = m ∨ p ∈ primeFactorsList ((k + 2) / m) :=
        List.mem_cons.1 (by rwa [primeFactorsList] at h)
      exact Or.casesOn h₁ (fun h₂ => h₂.symm ▸ minFac_prime (by simp)) prime_of_mem_primeFactorsList

theorem pos_of_mem_primeFactorsList {n p : ℕ} (h : p ∈ primeFactorsList n) : 0 < p :=
  Prime.pos (prime_of_mem_primeFactorsList h)

theorem prod_primeFactorsList : ∀ {n}, n ≠ 0 → List.prod (primeFactorsList n) = n
  | 0 => by simp
  | 1 => by simp
  | k + 2 => fun _ =>
    let m := minFac (k + 2)
    have : (k + 2) / m < (k + 2) := factors_lemma
    show (primeFactorsList (k + 2)).prod = (k + 2) by
      have h₁ : (k + 2) / m ≠ 0 := fun h => by
        have : (k + 2) = 0 * m := (Nat.div_eq_iff_eq_mul_left (minFac_pos _) (minFac_dvd _)).1 h
        rw [zero_mul] at this; exact (show k + 2 ≠ 0 by simp) this
      rw [primeFactorsList, List.prod_cons, prod_primeFactorsList h₁,
        Nat.mul_div_cancel' (minFac_dvd _)]

theorem primeFactorsList_prime {p : ℕ} (hp : Nat.Prime p) : p.primeFactorsList = [p] := by
  have : p = p - 2 + 2 := Nat.eq_add_of_sub_eq hp.two_le rfl
  rw [this, primeFactorsList]
  simp only [Eq.symm this]
  have : Nat.minFac p = p := (Nat.prime_def_minFac.mp hp).2
  simp only [this, primeFactorsList, Nat.div_self (Nat.Prime.pos hp)]

theorem isChain_cons_primeFactorsList {n : ℕ} :
    ∀ {a}, (∀ p, Prime p → p ∣ n → a ≤ p) → List.IsChain (· ≤ ·) (a :: primeFactorsList n) := by
  match n with
  | 0 => simp
  | 1 => simp
  | k + 2 =>
      intro a h
      let m := minFac (k + 2)
      have : (k + 2) / m < (k + 2) := factors_lemma
      rw [primeFactorsList]
      refine List.IsChain.cons_cons
        ((le_minFac.2 h).resolve_left (by simp)) (isChain_cons_primeFactorsList ?_)
      exact fun p pp d => minFac_le_of_dvd pp.two_le (d.trans <| div_dvd_of_dvd <| minFac_dvd _)

@[deprecated (since := "2025-09-21")]
alias primeFactorsList_chain := isChain_cons_primeFactorsList

theorem isChain_two_cons_primeFactorsList (n) : List.IsChain (· ≤ ·) (2 :: primeFactorsList n) :=
  isChain_cons_primeFactorsList fun _ pp _ => pp.two_le

theorem isChain_primeFactorsList (n) : List.IsChain (· ≤ ·) (primeFactorsList n) :=
  (isChain_two_cons_primeFactorsList _).tail

@[deprecated (since := "2025-09-24")]
alias primeFactorsList_chain_2 := isChain_two_cons_primeFactorsList

@[deprecated (since := "2025-09-24")]
alias primeFactorsList_chain' := isChain_primeFactorsList

theorem primeFactorsList_sorted (n : ℕ) : List.Sorted (· ≤ ·) (primeFactorsList n) :=
  (isChain_primeFactorsList _).pairwise

/-- `primeFactorsList` can be constructed inductively by extracting `minFac`, for sufficiently
large `n`. -/
theorem primeFactorsList_add_two (n : ℕ) :
    primeFactorsList (n + 2) = minFac (n + 2) :: primeFactorsList ((n + 2) / minFac (n + 2)) := by
  rw [primeFactorsList]

@[simp]
theorem primeFactorsList_eq_nil (n : ℕ) : n.primeFactorsList = [] ↔ n = 0 ∨ n = 1 := by
  constructor <;> intro h
  · rcases n with (_ | _ | n)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rw [primeFactorsList] at h
      injection h
  · rcases h with (rfl | rfl)
    · exact primeFactorsList_zero
    · exact primeFactorsList_one

theorem primeFactorsList_ne_nil (n : ℕ) : n.primeFactorsList ≠ [] ↔ 1 < n := by
  simp [primeFactorsList_eq_nil n, one_lt_iff_ne_zero_and_ne_one]

open scoped List in
theorem eq_of_perm_primeFactorsList {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a.primeFactorsList ~ b.primeFactorsList) : a = b := by
  simpa [prod_primeFactorsList ha, prod_primeFactorsList hb] using List.Perm.prod_eq h

section

open List

theorem mem_primeFactorsList_iff_dvd {n p : ℕ} (hn : n ≠ 0) (hp : Prime p) :
    p ∈ primeFactorsList n ↔ p ∣ n where
  mp h := prod_primeFactorsList hn ▸ List.dvd_prod h
  mpr h := mem_list_primes_of_dvd_prod (prime_iff.mp hp)
    (fun _ h ↦ prime_iff.mp (prime_of_mem_primeFactorsList h)) ((prod_primeFactorsList hn).symm ▸ h)

theorem dvd_of_mem_primeFactorsList {n p : ℕ} (h : p ∈ n.primeFactorsList) : p ∣ n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · exact dvd_zero p
  · rwa [← mem_primeFactorsList_iff_dvd hn.ne' (prime_of_mem_primeFactorsList h)]

theorem mem_primeFactorsList {n p} (hn : n ≠ 0) : p ∈ primeFactorsList n ↔ Prime p ∧ p ∣ n :=
  ⟨fun h => ⟨prime_of_mem_primeFactorsList h, dvd_of_mem_primeFactorsList h⟩, fun ⟨hprime, hdvd⟩ =>
    (mem_primeFactorsList_iff_dvd hn hprime).mpr hdvd⟩

@[simp] lemma mem_primeFactorsList' {n p} : p ∈ n.primeFactorsList ↔ p.Prime ∧ p ∣ n ∧ n ≠ 0 := by
  cases n <;> simp [mem_primeFactorsList, *]

theorem le_of_mem_primeFactorsList {n p : ℕ} (h : p ∈ n.primeFactorsList) : p ≤ n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · rw [primeFactorsList_zero] at h
    cases h
  · exact le_of_dvd hn (dvd_of_mem_primeFactorsList h)

/-- **Fundamental theorem of arithmetic** -/
theorem primeFactorsList_unique {n : ℕ} {l : List ℕ} (h₁ : prod l = n) (h₂ : ∀ p ∈ l, Prime p) :
    l ~ primeFactorsList n := by
  refine perm_of_prod_eq_prod ?_ ?_ ?_
  · rw [h₁]
    refine (prod_primeFactorsList ?_).symm
    rintro rfl
    rw [prod_eq_zero_iff] at h₁
    exact Prime.ne_zero (h₂ 0 h₁) rfl
  · simp_rw [← prime_iff]
    exact h₂
  · simp_rw [← prime_iff]
    exact fun p => prime_of_mem_primeFactorsList

theorem Prime.primeFactorsList_pow {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (p ^ n).primeFactorsList = List.replicate n p := by
  symm
  rw [← List.replicate_perm]
  apply Nat.primeFactorsList_unique (List.prod_replicate n p)
  intro q hq
  rwa [eq_of_mem_replicate hq]

theorem eq_prime_pow_of_unique_prime_dvd {n p : ℕ} (hpos : n ≠ 0)
    (h : ∀ {d}, Nat.Prime d → d ∣ n → d = p) : n = p ^ n.primeFactorsList.length := by
  set k := n.primeFactorsList.length
  rw [← prod_primeFactorsList hpos, ← prod_replicate k p, eq_replicate_of_mem fun d hd =>
    h (prime_of_mem_primeFactorsList hd) (dvd_of_mem_primeFactorsList hd)]

/-- For positive `a` and `b`, the prime factors of `a * b` are the union of those of `a` and `b` -/
theorem perm_primeFactorsList_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).primeFactorsList ~ a.primeFactorsList ++ b.primeFactorsList := by
  refine (primeFactorsList_unique ?_ ?_).symm
  · rw [List.prod_append, prod_primeFactorsList ha, prod_primeFactorsList hb]
  · intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp' | hp' <;> exact prime_of_mem_primeFactorsList hp'

/-- For coprime `a` and `b`, the prime factors of `a * b` are the union of those of `a` and `b` -/
theorem perm_primeFactorsList_mul_of_coprime {a b : ℕ} (hab : Coprime a b) :
    (a * b).primeFactorsList ~ a.primeFactorsList ++ b.primeFactorsList := by
  rcases a.eq_zero_or_pos with (rfl | ha)
  · simp [(coprime_zero_left _).mp hab]
  rcases b.eq_zero_or_pos with (rfl | hb)
  · simp [(coprime_zero_right _).mp hab]
  exact perm_primeFactorsList_mul ha.ne' hb.ne'

theorem primeFactorsList_sublist_right {n k : ℕ} (h : k ≠ 0) :
    n.primeFactorsList <+ (n * k).primeFactorsList := by
  rcases n with - | hn
  · simp [zero_mul]
  apply sublist_of_subperm_of_sorted _ (primeFactorsList_sorted _) (primeFactorsList_sorted _)
  simp only [(perm_primeFactorsList_mul (Nat.succ_ne_zero _) h).subperm_left]
  exact (sublist_append_left _ _).subperm

theorem primeFactorsList_sublist_of_dvd {n k : ℕ} (h : n ∣ k) (h' : k ≠ 0) :
    n.primeFactorsList <+ k.primeFactorsList := by
  obtain ⟨a, rfl⟩ := h
  exact primeFactorsList_sublist_right (right_ne_zero_of_mul h')

theorem primeFactorsList_subset_right {n k : ℕ} (h : k ≠ 0) :
    n.primeFactorsList ⊆ (n * k).primeFactorsList :=
  (primeFactorsList_sublist_right h).subset

theorem primeFactorsList_subset_of_dvd {n k : ℕ} (h : n ∣ k) (h' : k ≠ 0) :
    n.primeFactorsList ⊆ k.primeFactorsList :=
  (primeFactorsList_sublist_of_dvd h h').subset

theorem dvd_of_primeFactorsList_subperm {a b : ℕ} (ha : a ≠ 0)
    (h : a.primeFactorsList <+~ b.primeFactorsList) : a ∣ b := by
  rcases b.eq_zero_or_pos with (rfl | hb)
  · exact dvd_zero _
  rcases a with (_ | _ | a)
  · exact (ha rfl).elim
  · exact one_dvd _
  use (b.primeFactorsList.diff a.succ.succ.primeFactorsList).prod
  nth_rw 1 [← Nat.prod_primeFactorsList ha]
  rw [← List.prod_append,
    List.Perm.prod_eq <| List.subperm_append_diff_self_of_count_le <| List.subperm_ext_iff.mp h,
    Nat.prod_primeFactorsList hb.ne']

theorem replicate_subperm_primeFactorsList_iff {a b n : ℕ} (ha : Prime a) (hb : b ≠ 0) :
    replicate n a <+~ primeFactorsList b ↔ a ^ n ∣ b := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    constructor
    · rw [List.subperm_iff]
      rintro ⟨u, hu1, hu2⟩
      rw [← Nat.prod_primeFactorsList hb, ← hu1.prod_eq, ← prod_replicate]
      exact hu2.prod_dvd_prod
    · rintro ⟨c, rfl⟩
      rw [Ne, pow_succ', mul_assoc, mul_eq_zero, _root_.not_or] at hb
      rw [pow_succ', mul_assoc, replicate_succ,
        (Nat.perm_primeFactorsList_mul hb.1 hb.2).subperm_left, primeFactorsList_prime ha,
        singleton_append, subperm_cons, ih hb.2]
      exact dvd_mul_right _ _

end

theorem mem_primeFactorsList_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) {p : ℕ} :
    p ∈ (a * b).primeFactorsList ↔ p ∈ a.primeFactorsList ∨ p ∈ b.primeFactorsList := by
  rw [mem_primeFactorsList (mul_ne_zero ha hb), mem_primeFactorsList ha, mem_primeFactorsList hb,
    ← and_or_left]
  simpa only [and_congr_right_iff] using Prime.dvd_mul

/-- The sets of factors of coprime `a` and `b` are disjoint -/
theorem coprime_primeFactorsList_disjoint {a b : ℕ} (hab : a.Coprime b) :
    List.Disjoint a.primeFactorsList b.primeFactorsList := by
  intro q hqa hqb
  apply not_prime_one
  rw [← eq_one_of_dvd_coprimes hab (dvd_of_mem_primeFactorsList hqa)
    (dvd_of_mem_primeFactorsList hqb)]
  exact prime_of_mem_primeFactorsList hqa

theorem mem_primeFactorsList_mul_of_coprime {a b : ℕ} (hab : Coprime a b) (p : ℕ) :
    p ∈ (a * b).primeFactorsList ↔ p ∈ a.primeFactorsList ∪ b.primeFactorsList := by
  rcases a.eq_zero_or_pos with (rfl | ha)
  · simp [(coprime_zero_left _).mp hab]
  rcases b.eq_zero_or_pos with (rfl | hb)
  · simp [(coprime_zero_right _).mp hab]
  rw [mem_primeFactorsList_mul ha.ne' hb.ne', List.mem_union_iff]

open List

/-- If `p` is a prime factor of `a` then `p` is also a prime factor of `a * b` for any `b > 0` -/
theorem mem_primeFactorsList_mul_left {p a b : ℕ} (hpa : p ∈ a.primeFactorsList) (hb : b ≠ 0) :
    p ∈ (a * b).primeFactorsList := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp at hpa
  apply (mem_primeFactorsList_mul ha hb).2 (Or.inl hpa)

/-- If `p` is a prime factor of `b` then `p` is also a prime factor of `a * b` for any `a > 0` -/
theorem mem_primeFactorsList_mul_right {p a b : ℕ} (hpb : p ∈ b.primeFactorsList) (ha : a ≠ 0) :
    p ∈ (a * b).primeFactorsList := by
  rw [mul_comm]
  exact mem_primeFactorsList_mul_left hpb ha

theorem eq_two_pow_or_exists_odd_prime_and_dvd (n : ℕ) :
    (∃ k : ℕ, n = 2 ^ k) ∨ ∃ p, Nat.Prime p ∧ p ∣ n ∧ Odd p :=
  (eq_or_ne n 0).elim (fun hn => Or.inr ⟨3, prime_three, hn.symm ▸ dvd_zero 3, ⟨1, rfl⟩⟩) fun hn =>
    or_iff_not_imp_right.mpr fun H =>
      ⟨n.primeFactorsList.length,
        eq_prime_pow_of_unique_prime_dvd hn fun {_} hprime hdvd =>
          hprime.eq_two_or_odd'.resolve_right fun hodd => H ⟨_, hprime, hdvd, hodd⟩⟩

theorem four_dvd_or_exists_odd_prime_and_dvd_of_two_lt {n : ℕ} (n2 : 2 < n) :
    4 ∣ n ∨ ∃ p, Prime p ∧ p ∣ n ∧ Odd p := by
  obtain ⟨_ | _ | k, rfl⟩ | ⟨p, hp, hdvd, hodd⟩ := n.eq_two_pow_or_exists_odd_prime_and_dvd
  · contradiction
  · contradiction
  · simp [Nat.pow_succ, mul_assoc]
  · exact Or.inr ⟨p, hp, hdvd, hodd⟩

end Nat
