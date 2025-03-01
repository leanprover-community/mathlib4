/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best

! This file was ported from Lean 3 source module number_theory.cyclotomic.cyclotomic_units
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

noncomputable section

open scoped BigOperators nonZeroDivisors

open Polynomial Finset Module Units Submodule

universe u v w z

variable (n : ℕ+) (K : Type u) (L : Type v) (A : Type w) (B : Type z)

variable [CommRing A] [CommRing B] [Algebra A B]

variable [Field K] [Field L] [Algebra K L]

variable [IsDomain A] [Algebra A K] [IsFractionRing A K]

section CyclotomicUnit

variable {n}

namespace CyclotomicUnit

-- I don't want to bother Leo, but I wonder if this can be automated in Lean4
-- (if they were 0 < n → 1 < n, it would work already!)
theorem Nat.one_lt_of_ne : ∀ n : ℕ, n ≠ 0 → n ≠ 1 → 1 < n
  | 0, h, _ => absurd rfl h
  | 1, _, h => absurd rfl h
  | n + 2, _, _ => n.one_lt_succ_succ

-- this result holds for all primitive roots; dah.
theorem associated_one_sub_pow_primitive_root_of_coprime {n j k : ℕ} {ζ : A}
    (hζ : IsPrimitiveRoot ζ n) (hk : k.Coprime n) (hj : j.Coprime n) :
    Associated (1 - ζ ^ j) (1 - ζ ^ k) := by
  suffices ∀ {j : ℕ}, j.Coprime n → Associated (1 - ζ) (1 - ζ ^ j) by
    exact (this hj).symm.trans (this hk)
  clear k j hk hj
  intro j hj
  refine associated_of_dvd_dvd ⟨∑ i ∈ range j, ζ ^ i, by rw [← geom_sum_mul_neg, mul_comm]⟩ ?_
  -- is there an easier way to do this?
  rcases eq_or_ne n 0 with (rfl | hn')
  · simp [j.coprime_zero_right.mp hj]
  rcases eq_or_ne n 1 with (rfl | hn)
  · simp [IsPrimitiveRoot.one_right_iff.mp hζ]
  replace hn := Nat.one_lt_of_ne n hn' hn
  obtain ⟨m, hm⟩ := Nat.exists_mul_emod_eq_one_of_coprime hj hn
  use ∑ i ∈ range m, (ζ ^ j) ^ i
  have : ζ = (ζ ^ j) ^ m := by rw [← pow_mul, ←pow_mod_orderOf, ← hζ.eq_orderOf, hm, pow_one]
  nth_rw 1 [this]
  rw [← geom_sum_mul_neg, mul_comm]

theorem IsPrimitiveRoot.sum_pow_unit {n k : ℕ} {ζ : A} (hn : 2 ≤ n) (hk : k.Coprime n)
    (hζ : IsPrimitiveRoot ζ n) : IsUnit (∑ i ∈ range k, ζ ^ (i : ℕ)) := by
  have h1 : (1 : ℕ).Coprime n := Nat.coprime_one_left n
  have := associated_one_sub_pow_primitive_root_of_coprime _ hζ hk h1
  simp at this
  rw [Associated] at this
  have h2 := mul_neg_geom_sum ζ k
  obtain ⟨u, hu⟩ := this
  have := u.isUnit
  convert this
  rw [← hu] at h2
  simp at h2
  cases' h2 with h2 h2
  exact h2
  exfalso
  have hn1 : 1 < n := by linarith
  have hp := IsPrimitiveRoot.pow_ne_one_of_pos_of_lt hζ one_pos hn1
  simp at *
  rw [sub_eq_zero] at h2
  rw [← h2] at hp
  simp only [eq_self_iff_true, not_true] at hp

theorem IsPrimitiveRoot.zeta_pow_sub_eq_unit_zeta_sub_one {p i j : ℕ} {ζ : A} (hn : 2 ≤ p)
    (hp : p.Prime) (hi : i < p) (hj : j < p) (hij : i ≠ j) (hζ : IsPrimitiveRoot ζ p) :
    ∃ u : Aˣ, ζ ^ i - ζ ^ j = u * (1 - ζ) := by
  by_cases hilj : j < i
  have h1 : ζ ^ i - ζ ^ j = ζ ^ j * (ζ ^ (i - j) - 1) := by
    ring_nf
    rw [pow_mul_pow_sub _ hilj.le]
    rw [add_comm]
    ring
  rw [h1]
  have h2 := mul_neg_geom_sum ζ (i - j)
  have hic : (i - j).Coprime p := by
    rw [Nat.coprime_comm]; apply Nat.coprime_of_lt_prime _ _ hp
    apply Nat.sub_pos_of_lt hilj
    by_cases hj : 0 < j
    apply lt_trans _ hi
    apply Nat.sub_lt_of_pos_le hj hilj.le
    simp only [not_lt, _root_.le_zero_iff] at hj
    rw [hj]
    simp only [tsub_zero]
    exact hi
  have h3 : IsUnit (-ζ ^ j * ∑ k ∈ range (i - j), ζ ^ (k : ℕ)) := by
    apply IsUnit.mul _ (IsPrimitiveRoot.sum_pow_unit _ hn hic hζ); apply IsUnit.neg
    apply IsUnit.pow; apply hζ.isUnit hp.pos
  obtain ⟨v, hv⟩ := h3
  use v
  rw [hv]
  rw [mul_comm] at h2
  rw [mul_assoc]
  rw [h2]
  ring
  simp at *
  have h1 : ζ ^ i - ζ ^ j = ζ ^ i * (1 - ζ ^ (j - i)) := by
    ring_nf
    simp; rw [pow_mul_pow_sub _ hilj]
  rw [h1]
  have h2 := mul_neg_geom_sum ζ (j - i)
  have hjc : (j - i).Coprime p := by
    rw [Nat.coprime_comm]
    apply Nat.coprime_of_lt_prime _ _ hp
    have hilj' : i < j := by rw [lt_iff_le_and_ne]; simp [hij, hilj]
    apply Nat.sub_pos_of_lt hilj'
    by_cases hii : 0 < i
    apply lt_trans _ hj
    apply Nat.sub_lt_of_pos_le hii hilj
    simp only [not_lt, _root_.le_zero_iff] at hii
    rw [hii]
    simp only [tsub_zero]
    exact hj
  have h3 : IsUnit (ζ ^ i * ∑ k ∈ range (j - i), ζ ^ (k : ℕ)) := by
    apply IsUnit.mul _ (IsPrimitiveRoot.sum_pow_unit _ hn hjc hζ); apply IsUnit.pow
    apply hζ.isUnit hp.pos
  obtain ⟨v, hv⟩ := h3
  use v
  rw [hv]
  rw [mul_comm] at h2
  rw [mul_assoc]
  rw [h2]

end CyclotomicUnit

lemma IsPrimitiveRoot.associated_sub_one {A : Type*} [CommRing A] [IsDomain A]
    {p : ℕ} (hp : p.Prime) {ζ : A} (hζ : IsPrimitiveRoot ζ p) {η₁ : A}
    (hη₁ : η₁ ∈ nthRootsFinset p A) {η₂ : A} (hη₂ : η₂ ∈ nthRootsFinset p A) (e : η₁ ≠ η₂) :
    Associated (ζ - 1) (η₁ - η₂) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, ⟨hi, rfl⟩⟩ :=
    hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hp.pos).1 hη₁)
  obtain ⟨j, ⟨hj, rfl⟩⟩ :=
    hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hp.pos).1 hη₂)
  have : i ≠ j := ne_of_apply_ne _ e
  obtain ⟨u, h⟩ := CyclotomicUnit.IsPrimitiveRoot.zeta_pow_sub_eq_unit_zeta_sub_one A
    hp.two_le hp hi hj this hζ
  rw [h, associated_isUnit_mul_right_iff u.isUnit, ← associated_isUnit_mul_right_iff isUnit_one.neg,
    neg_one_mul, neg_sub]
  rfl

end CyclotomicUnit
