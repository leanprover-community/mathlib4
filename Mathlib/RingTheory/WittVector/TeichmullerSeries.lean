/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/

import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.Teichmuller

/-!
# Teichmuller Series

Let `R` be a characteristic `p` perfect ring. In this file, we show that
every element `x` of the Witt vectors `𝕎 R` can be written as the
(`p`-adic) summation of Teichmuller series, namely
`∑ i, (teichmuller p
        (((frobeniusEquiv R p).symm ^ i) (x.coeff i)) * p ^ i)`

## Main theorems

* `WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff` : `p ^ (n + 1)` divides
`x` minus the summation of the first `n + 1` terms of the Teichmuller series.
* `WittVector.eq_of_apply_teichmuller_eq` : Given a ring `S` such that `p` is nilpotent in `S`
and two ring maps `f g : 𝕎 R →+* S`, if they coincide on the teichmuller representatives,
then they are equal.

## TODO
Show that the Teichmuller series is unique.
-/

open Ideal Quotient
namespace WittVector

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

local notation "𝕎" => WittVector p

variable {R : Type*} [CommRing R]

theorem sum_coeff_eq_coeff_sum {α : Type*} {S : Finset α} (x : α → 𝕎 R)
    (h : ∀ (n : ℕ), Subsingleton {r | r ∈ S ∧ (x r).coeff n ≠ 0}) (n : ℕ) :
    (∑ s ∈ S, x s).coeff n = ∑ (s ∈ S), (x s).coeff n := by
  classical
  revert n
  induction' S using Finset.induction with a S' ha hind
  · simp
  · intro n
    have : (∀ (n : ℕ), Subsingleton {r | r ∈ S' ∧ (x r).coeff n ≠ 0 }) := by
      refine fun n ↦ ⟨fun b c ↦ ?_⟩
      ext
      exact congrArg (fun x ↦ x.1) <|
          (h n).allEq ⟨b.1, S'.subset_insert a b.2.1, b.2.2⟩ ⟨c.1, S'.subset_insert a c.2.1, c.2.2⟩
    replace hind := hind this
    simp only [ha, not_false_eq_true, Finset.sum_insert]
    have : ∀ (n : ℕ), (x a).coeff n = 0 ∨ (∑ s ∈ S', x s).coeff n = 0 := by
      simp only [hind]
      by_contra! h
      obtain ⟨m, hma, hmS'⟩ := h
      have := Finset.sum_eq_zero.mt hmS'
      push_neg at this
      choose b hb hb' using this
      have : a = b :=
        congrArg (fun x ↦ x.1) <|
          (h m).allEq ⟨a, S'.mem_insert_self a, hma⟩ ⟨b, S'.mem_insert_of_mem hb, hb'⟩
      exact ha (this ▸ hb)
    rw [coeff_add_of_disjoint n _ _ this, hind n]

@[simp]
theorem teichmuller_mul_pow_coeff {R : Type*} [CommRing R] [CharP R p] (n : ℕ) (x : R) :
    (teichmuller p x * p ^ n).coeff n = x ^ p ^ n := by
  simpa using WittVector.mul_pow_charP_coeff_succ (teichmuller p x) (m := 0)

theorem teichmuller_mul_pow_coeff_of_ne {R : Type*} [CommRing R] [CharP R p] (x : R)
    {m n : ℕ} (h : m ≠ n) : (teichmuller p x * p ^ n).coeff m = 0 := by
  cases Nat.lt_or_lt_of_ne h with
  | inl h =>
     exact WittVector.mul_pow_charP_coeff_zero (teichmuller p x) h
  | inr h =>
    rw [← Nat.sub_add_cancel h.le, WittVector.mul_pow_charP_coeff_succ (teichmuller p x),
        WittVector.teichmuller_coeff_pos p x (m - n) (Nat.zero_lt_sub_of_lt h), zero_pow]
    simp [Prime.ne_zero <| Nat.Prime.prime Fact.out]

/--
`p ^ (n + 1)` divides
`x` minus the summation of the first `n + 1` terms of the Teichmuller series.
-/
theorem dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff
    {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p] (x : 𝕎 R) (n : ℕ) :
    (p : 𝕎 R) ^ (n + 1) ∣ x - ∑ (i ≤ n), (teichmuller p
        (((_root_.frobeniusEquiv R p).symm ^ i) (x.coeff i)) * p ^ i) := by
  rw [← Ideal.mem_span_singleton, mem_span_p_pow_iff_le_coeff_eq_zero,
      ← le_coeff_eq_iff_le_sub_coeff_eq_zero]
  intro i hi
  rw [WittVector.sum_coeff_eq_coeff_sum]
  · rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp hi))]
    let g := fun x : ℕ ↦ (0 : R)
    rw [Finset.sum_congr rfl (g := fun x : ℕ ↦ (0 : R))]
    · simp
    · intro b hb
      simp only [Finset.mem_sdiff, Finset.mem_Iic, Finset.mem_singleton] at hb
      exact teichmuller_mul_pow_coeff_of_ne _ (Ne.intro hb.2).symm
  · refine fun n ↦ ⟨fun ⟨a, _, ha⟩ ⟨b, _, hb⟩ ↦ ?_⟩
    ext
    dsimp only [ne_eq, Set.mem_setOf_eq]
    have := of_not_not ((teichmuller_mul_pow_coeff_of_ne _).mt ha)
    rw [← this]
    have := of_not_not ((teichmuller_mul_pow_coeff_of_ne _).mt hb)
    exact this

/--
Given a ring `S` such that `p` is nilpotent in `S`
and two ring maps `f g : 𝕎 R →+* S`, if they coincide on the teichmuller representatives,
then they are equal.
-/
theorem eq_of_apply_teichmuller_eq {R S : Type*} [CommRing R] [CommRing S] [CharP R p]
    [PerfectRing R p] (f g : 𝕎 R →+* S) (hp : IsNilpotent (p : S))
    (h : ∀ (x : R), f (teichmuller p x) = g (teichmuller p x)) : f = g := by
  obtain ⟨n, hn⟩ := hp
  ext x
  obtain ⟨c, hc⟩ := (dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x n)
  calc
    f x = f (x - ∑ (i ≤ n), teichmuller p (((_root_.frobeniusEquiv R p).symm ^ i)
        (x.coeff i)) * p ^ i) + f (∑ (i ≤ n), teichmuller p
        (((_root_.frobeniusEquiv R p).symm ^ i) (x.coeff i)) * p ^ i) := by simp
    _ = ∑ (i ≤ n), f (teichmuller p (((_root_.frobeniusEquiv R p).symm ^ i)
        (x.coeff i))) * p ^ i := by rw [hc]; simp [pow_succ, hn]
    _ = ∑ (i ≤ n), g (teichmuller p
        (((_root_.frobeniusEquiv R p).symm ^ i) (x.coeff i))) * p ^ i := by simp [h]
    _ = g (x - ∑ (i ≤ n), teichmuller p (((_root_.frobeniusEquiv R p).symm ^ i)
        (x.coeff i)) * p ^ i) + g (∑ (i ≤ n), teichmuller p (((_root_.frobeniusEquiv R p).symm ^ i)
        (x.coeff i)) * p ^ i) := by rw [hc]; simp [pow_succ, hn]
    _ = g x := by simp

end WittVector
