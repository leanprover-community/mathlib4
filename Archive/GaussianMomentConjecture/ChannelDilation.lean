/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Nat.Prime.Defs

/-!
# Dilation of multiplicity channels supported on a face

This file isolates the elementary transport used by the Frobenius step in
GMC(2).  A multiplicity vector on a face `F` is extended by zero to the full
index set and then multiplied by `p`.  The resulting channel has exactly
`p` times the mass, charge, height, and accumulated bidegree, while its
coefficient monomial is the `p`-th power of the face monomial.

The final statements identify the image inside the full antidiagonal: its
members are precisely the mass-`p*m` channels supported on `F` whose
multiplicities are divisible by `p`.  Nothing here uses primality except the
convenient prime-specialized injectivity corollary; positivity is the exact
hypothesis needed for cancellation.
-/

open Finset

namespace GMC2.ChannelDilation

variable {ι : Type*} [DecidableEq ι]

/-- Extend a multiplicity vector on the face `F` by zero to the full index
set. -/
def extendByZero (F : Finset ι) (s : ↥F → ℕ) : ι → ℕ :=
  fun i ↦ if hi : i ∈ F then s ⟨i, hi⟩ else 0

@[simp] theorem extendByZero_of_mem (F : Finset ι) (s : ↥F → ℕ)
    {i : ι} (hi : i ∈ F) :
    extendByZero F s i = s ⟨i, hi⟩ := by
  simp [extendByZero, hi]

@[simp] theorem extendByZero_of_notMem (F : Finset ι) (s : ↥F → ℕ)
    {i : ι} (hi : i ∉ F) :
    extendByZero F s i = 0 := by
  simp [extendByZero, hi]

@[simp] theorem extendByZero_subtype (F : Finset ι) (s : ↥F → ℕ)
    (i : ↥F) :
    extendByZero F s i = s i := by
  simp [extendByZero, i.property]

/-- The `p`-dilation of a face channel, regarded as a channel on the full
index set. -/
def dilate (p : ℕ) (F : Finset ι) (s : ↥F → ℕ) : ι → ℕ :=
  fun i ↦ p * extendByZero F s i

@[simp] theorem dilate_apply (p : ℕ) (F : Finset ι) (s : ↥F → ℕ)
    (i : ι) :
    dilate p F s i = p * extendByZero F s i := rfl

@[simp] theorem dilate_subtype (p : ℕ) (F : Finset ι) (s : ↥F → ℕ)
    (i : ↥F) :
    dilate p F s i = p * s i := by
  simp [dilate]

@[simp] theorem dilate_of_notMem (p : ℕ) (F : Finset ι) (s : ↥F → ℕ)
    {i : ι} (hi : i ∉ F) :
    dilate p F s i = 0 := by
  simp [dilate, hi]

section FiniteIndex

variable [Fintype ι]

/-- Additive extension-by-zero transport.  This is the common engine behind
mass, charge, height, and bidegree transport. -/
theorem sum_extendByZero {A : Type*} [AddCommMonoid A]
    (F : Finset ι) (s : ↥F → ℕ) (g : ι → ℕ → A)
    (hzero : ∀ i, g i 0 = 0) :
    ∑ i, g i (extendByZero F s i) = ∑ i : ↥F, g i (s i) := by
  calc
    ∑ i, g i (extendByZero F s i) =
        ∑ i, if hi : i ∈ F then g i (s ⟨i, hi⟩) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hiF : i ∈ F
          · simp [extendByZero, hiF]
          · simp [extendByZero, hiF, hzero]
    _ = ∑ i : ↥F, g i (s i) := by
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach_eq_sum_dite F (fun i : ↥F ↦ g i (s i))).symm

/-- Multiplicative extension-by-zero transport. -/
theorem prod_extendByZero {A : Type*} [CommMonoid A]
    (F : Finset ι) (s : ↥F → ℕ) (g : ι → ℕ → A)
    (hzero : ∀ i, g i 0 = 1) :
    ∏ i, g i (extendByZero F s i) = ∏ i : ↥F, g i (s i) := by
  calc
    ∏ i, g i (extendByZero F s i) =
        ∏ i, if hi : i ∈ F then g i (s ⟨i, hi⟩) else 1 := by
          apply Finset.prod_congr rfl
          intro i hi
          by_cases hiF : i ∈ F
          · simp [extendByZero, hiF]
          · simp [extendByZero, hiF, hzero]
    _ = ∏ i : ↥F, g i (s i) := by
      simpa only [Finset.univ_eq_attach] using
        (Finset.prod_attach_eq_prod_dite F (fun i : ↥F ↦ g i (s i))).symm

/-- Exact mass scaling under dilation. -/
theorem sum_dilate (p : ℕ) (F : Finset ι) (s : ↥F → ℕ) :
    ∑ i, dilate p F s i = p * ∑ i : ↥F, s i := by
  calc
    ∑ i, dilate p F s i = ∑ i, p * extendByZero F s i := rfl
    _ = p * ∑ i, extendByZero F s i := by rw [Finset.mul_sum]
    _ = p * ∑ i : ↥F, s i := by
      rw [sum_extendByZero F s (fun _ n ↦ n)]
      intro i
      rfl

/-- A dilation scales any accumulated additive weight by `p`. -/
theorem accumulated_dilate {A : Type*} [AddCommMonoid A]
    (p : ℕ) (F : Finset ι) (s : ↥F → ℕ) (weight : ι → A) :
    ∑ i, (dilate p F s i) • weight i =
      p • ∑ i : ↥F, (s i) • weight i := by
  calc
    ∑ i, (dilate p F s i) • weight i =
        ∑ i, p • ((extendByZero F s i) • weight i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [dilate, Nat.mul_comm, mul_nsmul]
    _ = p • ∑ i, (extendByZero F s i) • weight i := by
      rw [Finset.sum_nsmul]
    _ = p • ∑ i : ↥F, (s i) • weight i := by
      rw [sum_extendByZero F s (fun i n ↦ n • weight i)]
      intro i
      simp

/-- Exact integer-charge scaling. -/
theorem totalCharge_dilate (p : ℕ) (F : Finset ι) (s : ↥F → ℕ)
    (charge : ι → ℤ) :
    ∑ i, (dilate p F s i : ℤ) * charge i =
      (p : ℤ) * ∑ i : ↥F, (s i : ℤ) * charge i := by
  simpa [nsmul_eq_mul] using
    (accumulated_dilate p F s charge)

/-- Exact natural-height scaling. -/
theorem accumulatedHeight_dilate (p : ℕ) (F : Finset ι) (s : ↥F → ℕ)
    (height : ι → ℕ) :
    ∑ i, dilate p F s i * height i =
      p * ∑ i : ↥F, s i * height i := by
  simpa [nsmul_eq_mul] using
    (accumulated_dilate p F s height)

/-- Exact bidegree scaling for the exponent representation used by GMC(2). -/
theorem accumulatedBidegree_dilate
    (p : ℕ) (F : Finset ι) (s : ↥F → ℕ)
    (exponent : ι → Fin 2 →₀ ℕ) :
    ∑ i, (dilate p F s i) • exponent i =
      p • ∑ i : ↥F, (s i) • exponent i :=
  accumulated_dilate p F s exponent

/-- Coefficient monomials of dilated channels are exact `p`-th powers. -/
theorem coefficientProduct_dilate {A : Type*} [CommMonoid A]
    (p : ℕ) (F : Finset ι) (s : ↥F → ℕ) (coefficient : ι → A) :
    ∏ i, coefficient i ^ dilate p F s i =
      (∏ i : ↥F, coefficient i ^ s i) ^ p := by
  calc
    ∏ i, coefficient i ^ dilate p F s i =
        ∏ i, (coefficient i ^ extendByZero F s i) ^ p := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [dilate, Nat.mul_comm, pow_mul]
    _ = (∏ i, coefficient i ^ extendByZero F s i) ^ p := by
      rw [Finset.prod_pow]
    _ = (∏ i : ↥F, coefficient i ^ s i) ^ p := by
      rw [prod_extendByZero F s (fun i n ↦ coefficient i ^ n)]
      intro i
      simp

end FiniteIndex

/-- Positive dilation is injective on face multiplicity vectors. -/
theorem dilate_injective {p : ℕ} (hp : 0 < p) (F : Finset ι) :
    Function.Injective (dilate p F) := by
  intro s t hst
  funext i
  have hi := congrFun hst (i : ι)
  simp only [dilate_subtype] at hi
  exact Nat.eq_of_mul_eq_mul_left hp hi

/-- Prime dilation is injective; primality is stronger than necessary. -/
theorem dilate_injective_of_prime {p : ℕ} (hp : Nat.Prime p) (F : Finset ι) :
    Function.Injective (dilate p F) :=
  dilate_injective hp.pos F

/-- A full channel is a dilation of a face channel exactly when it vanishes
off the face and all its on-face multiplicities are divisible by `p`.  This
description is valid even at `p = 0`. -/
theorem exists_dilate_iff (p : ℕ) (F : Finset ι) (r : ι → ℕ) :
    (∃ s : ↥F → ℕ, dilate p F s = r) ↔
      (∀ i, i ∉ F → r i = 0) ∧ (∀ i, i ∈ F → p ∣ r i) := by
  constructor
  · rintro ⟨s, rfl⟩
    constructor
    · intro i hi
      simp [hi]
    · intro i hi
      refine ⟨s ⟨i, hi⟩, ?_⟩
      simp [dilate, hi]
  · rintro ⟨hoff, hdvd⟩
    refine ⟨fun i ↦ r i / p, ?_⟩
    funext i
    by_cases hi : i ∈ F
    · simpa [dilate, extendByZero, hi] using
        (Nat.mul_div_cancel' (hdvd i hi))
    · simp [dilate, extendByZero, hi, hoff i hi]

section AntidiagonalTransport

variable [Fintype ι]

/-- Dilation sends the mass-`m` face antidiagonal into the full
mass-`p*m` antidiagonal. -/
theorem dilate_mem_piAntidiag {p m : ℕ} (F : Finset ι) (s : ↥F → ℕ)
    (hs : s ∈ Finset.piAntidiag (Finset.univ : Finset ↥F) m) :
    dilate p F s ∈ Finset.piAntidiag (Finset.univ : Finset ι) (p * m) := by
  rw [Finset.mem_piAntidiag] at hs ⊢
  constructor
  · calc
      ∑ i, dilate p F s i = p * ∑ i : ↥F, s i := sum_dilate p F s
      _ = p * m := congrArg (fun n ↦ p * n) hs.1
  · simp

end AntidiagonalTransport

/-- The embedding used to reindex a finite family of face channels by their
positive dilations. -/
def dilationEmbedding (p : ℕ) (hp : 0 < p) (F : Finset ι) :
    (↥F → ℕ) ↪ (ι → ℕ) :=
  ⟨dilate p F, dilate_injective hp F⟩

section AntidiagonalImage

variable [Fintype ι]

/-- Exact image of the face antidiagonal under positive dilation. -/
theorem map_piAntidiag_dilation {p m : ℕ} (hp : 0 < p) (F : Finset ι) :
    (Finset.piAntidiag (Finset.univ : Finset ↥F) m).map
        (dilationEmbedding p hp F) =
      (Finset.piAntidiag (Finset.univ : Finset ι) (p * m)).filter
        (fun r ↦ (∀ i, i ∉ F → r i = 0) ∧ (∀ i, i ∈ F → p ∣ r i)) := by
  classical
  ext r
  simp only [Finset.mem_map, Finset.mem_filter]
  constructor
  · rintro ⟨s, hs, hsr⟩
    subst r
    refine ⟨dilate_mem_piAntidiag F s hs, ?_⟩
    exact (exists_dilate_iff p F (dilate p F s)).1 ⟨s, rfl⟩
  · rintro ⟨hr, hsupport⟩
    obtain ⟨s, hsr⟩ := (exists_dilate_iff p F r).2 hsupport
    refine ⟨s, ?_, hsr⟩
    have hdilated : dilate p F s ∈
        Finset.piAntidiag (Finset.univ : Finset ι) (p * m) := by
      simpa only [hsr] using hr
    rw [Finset.mem_piAntidiag] at hdilated ⊢
    constructor
    · apply Nat.eq_of_mul_eq_mul_left hp
      rw [← sum_dilate p F s]
      exact hdilated.1
    · simp

end AntidiagonalImage

/-- Finite sums over the dilation image reindex without multiplicity. -/
theorem sum_map_dilation {A : Type*} [AddCommMonoid A]
    {p m : ℕ} (hp : 0 < p) (F : Finset ι) (g : (ι → ℕ) → A) :
    ∑ r ∈ (Finset.piAntidiag (Finset.univ : Finset ↥F) m).map
        (dilationEmbedding p hp F), g r =
      ∑ s ∈ Finset.piAntidiag (Finset.univ : Finset ↥F) m,
        g (dilate p F s) := by
  exact Finset.sum_map _ _ _

end GMC2.ChannelDilation

