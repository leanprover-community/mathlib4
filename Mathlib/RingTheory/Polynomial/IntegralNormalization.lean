/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker, Andrew Yang, Yuyang Zhao
-/
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Theory of monic polynomials

We define `integralNormalization`, which relate arbitrary polynomials to monic ones.
-/


open Polynomial

namespace Polynomial

universe u v y

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

section IntegralNormalization

section Semiring

variable [Semiring R]

/-- If `p : R[X]` is a nonzero polynomial with root `z`, `integralNormalization p` is
a monic polynomial with root `leadingCoeff f * z`.

Moreover, `integralNormalization 0 = 0`.
-/
noncomputable def integralNormalization (p : R[X]) : R[X] :=
  p.sum fun i a ↦
    monomial i (if p.degree = i then 1 else a * p.leadingCoeff ^ (p.natDegree - 1 - i))

@[simp]
theorem integralNormalization_zero : integralNormalization (0 : R[X]) = 0 := by
  simp [integralNormalization]

@[simp]
theorem integralNormalization_C {x : R} (hx : x ≠ 0) : integralNormalization (C x) = 1 := by
  simp [integralNormalization, sum_def, support_C hx, degree_C hx]

variable {p : R[X]}

theorem integralNormalization_coeff {i : ℕ} :
    (integralNormalization p).coeff i =
      if p.degree = i then 1 else coeff p i * p.leadingCoeff ^ (p.natDegree - 1 - i) := by
  have : p.coeff i = 0 → p.degree ≠ i := fun hc hd => coeff_ne_zero_of_eq_degree hd hc
  simp +contextual [sum_def, integralNormalization, coeff_monomial, this,
    mem_support_iff]

theorem support_integralNormalization_subset :
    (integralNormalization p).support ⊆ p.support := by
  intro
  simp +contextual [sum_def, integralNormalization, coeff_monomial, mem_support_iff]

theorem integralNormalization_coeff_degree {i : ℕ} (hi : p.degree = i) :
    (integralNormalization p).coeff i = 1 := by rw [integralNormalization_coeff, if_pos hi]

theorem integralNormalization_coeff_natDegree (hp : p ≠ 0) :
    (integralNormalization p).coeff (natDegree p) = 1 :=
  integralNormalization_coeff_degree (degree_eq_natDegree hp)

theorem integralNormalization_coeff_degree_ne {i : ℕ} (hi : p.degree ≠ i) :
    coeff (integralNormalization p) i = coeff p i * p.leadingCoeff ^ (p.natDegree - 1 - i) := by
  rw [integralNormalization_coeff, if_neg hi]

theorem integralNormalization_coeff_ne_natDegree {i : ℕ} (hi : i ≠ natDegree p) :
    coeff (integralNormalization p) i = coeff p i * p.leadingCoeff ^ (p.natDegree - 1 - i) :=
  integralNormalization_coeff_degree_ne (degree_ne_of_natDegree_ne hi.symm)

theorem monic_integralNormalization (hp : p ≠ 0) : Monic (integralNormalization p) :=
  monic_of_degree_le p.natDegree
    (Finset.sup_le fun i h =>
      WithBot.coe_le_coe.2 <| le_natDegree_of_mem_supp i <| support_integralNormalization_subset h)
    (integralNormalization_coeff_natDegree hp)

theorem integralNormalization_coeff_mul_leadingCoeff_pow (i : ℕ) (hp : 1 ≤ natDegree p) :
    (integralNormalization p).coeff i * p.leadingCoeff ^ i =
      p.coeff i * p.leadingCoeff ^ (p.natDegree - 1) := by
  rw [integralNormalization_coeff]
  split_ifs with h
  · simp [natDegree_eq_of_degree_eq_some h, leadingCoeff,
      ← pow_succ', tsub_add_cancel_of_le (natDegree_eq_of_degree_eq_some h ▸ hp)]
  · simp only [mul_assoc, ← pow_add]
    by_cases h' : i < p.degree
    · rw [tsub_add_cancel_of_le]
      rw [le_tsub_iff_right hp, Nat.succ_le_iff]
      exact coe_lt_degree.mp h'
    · simp [coeff_eq_zero_of_degree_lt (lt_of_le_of_ne (le_of_not_gt h') h)]

theorem integralNormalization_mul_C_leadingCoeff (p : R[X]) :
    integralNormalization p * C p.leadingCoeff = scaleRoots p p.leadingCoeff := by
  ext i
  rw [coeff_mul_C, integralNormalization_coeff]
  split_ifs with h
  · simp [natDegree_eq_of_degree_eq_some h, leadingCoeff]
  · simp only [coeff_scaleRoots]
    by_cases h' : i < p.degree
    · rw [mul_assoc, ← pow_succ, tsub_right_comm, tsub_add_cancel_of_le]
      rw [le_tsub_iff_left (coe_lt_degree.mp h').le, Nat.succ_le_iff]
      exact coe_lt_degree.mp h'
    · simp [coeff_eq_zero_of_degree_lt (lt_of_le_of_ne (le_of_not_gt h') h)]

theorem integralNormalization_degree : (integralNormalization p).degree = p.degree := by
  apply le_antisymm
  · exact Finset.sup_mono p.support_integralNormalization_subset
  · rw [← degree_scaleRoots, ← integralNormalization_mul_C_leadingCoeff]
    exact (degree_mul_le _ _).trans (add_le_of_nonpos_right degree_C_le)

variable {A : Type*} [CommSemiring S] [Semiring A]

theorem leadingCoeff_smul_integralNormalization (p : S[X]) :
    p.leadingCoeff • integralNormalization p = scaleRoots p p.leadingCoeff := by
  rw [Algebra.smul_def, algebraMap_eq, mul_comm, integralNormalization_mul_C_leadingCoeff]

theorem integralNormalization_eval₂_leadingCoeff_mul_of_commute (h : 1 ≤ p.natDegree) (f : R →+* A)
    (x : A) (h₁ : Commute (f p.leadingCoeff) x) (h₂ : ∀ {r r'}, Commute (f r) (f r')) :
    (integralNormalization p).eval₂ f (f p.leadingCoeff * x) =
      f p.leadingCoeff ^ (p.natDegree - 1) * p.eval₂ f x := by
  rw [eval₂_eq_sum_range, eval₂_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr
  · rw [natDegree_eq_of_degree_eq p.integralNormalization_degree]
  intro n _hn
  rw [h₁.mul_pow, ← mul_assoc, ← f.map_pow, ← f.map_mul,
    integralNormalization_coeff_mul_leadingCoeff_pow _ h, f.map_mul, h₂.eq, f.map_pow, mul_assoc]

theorem integralNormalization_eval₂_leadingCoeff_mul (h : 1 ≤ p.natDegree) (f : R →+* S) (x : S) :
    (integralNormalization p).eval₂ f (f p.leadingCoeff * x) =
      f p.leadingCoeff ^ (p.natDegree - 1) * p.eval₂ f x :=
  integralNormalization_eval₂_leadingCoeff_mul_of_commute h _ _ (.all _ _) (.all _ _)

theorem integralNormalization_eval₂_eq_zero_of_commute {p : R[X]} (f : R →+* A) {z : A}
    (hz : eval₂ f z p = 0) (h₁ : Commute (f p.leadingCoeff) z) (h₂ : ∀ {r r'}, Commute (f r) (f r'))
    (inj : ∀ x : R, f x = 0 → x = 0) :
    eval₂ f (f p.leadingCoeff * z) (integralNormalization p) = 0 := by
  obtain (h | h) := p.natDegree.eq_zero_or_pos
  · by_cases h0 : coeff p 0 = 0
    · rw [eq_C_of_natDegree_eq_zero h]
      simp [h0]
    · rw [eq_C_of_natDegree_eq_zero h, eval₂_C] at hz
      exact absurd (inj _ hz) h0
  · rw [integralNormalization_eval₂_leadingCoeff_mul_of_commute h _ _ h₁ h₂, hz, mul_zero]

theorem integralNormalization_eval₂_eq_zero {p : R[X]} (f : R →+* S) {z : S} (hz : eval₂ f z p = 0)
    (inj : ∀ x : R, f x = 0 → x = 0) :
    eval₂ f (f p.leadingCoeff * z) (integralNormalization p) = 0 :=
  integralNormalization_eval₂_eq_zero_of_commute _ hz (.all _ _) (.all _ _) inj

theorem integralNormalization_aeval_eq_zero [Algebra S A] {f : S[X]} {z : A} (hz : aeval z f = 0)
    (inj : ∀ x : S, algebraMap S A x = 0 → x = 0) :
    aeval (algebraMap S A f.leadingCoeff * z) (integralNormalization f) = 0 :=
  integralNormalization_eval₂_eq_zero_of_commute (algebraMap S A) hz
    (Algebra.commute_algebraMap_left _ _) (.map (.all _ _) _) inj

end Semiring

section IsCancelMulZero

variable [Semiring R] [IsCancelMulZero R]

@[simp]
theorem support_integralNormalization {f : R[X]} :
    (integralNormalization f).support = f.support := by
  nontriviality R using Subsingleton.eq_zero
  have : IsDomain R := {}
  by_cases hf : f = 0; · simp [hf]
  ext i
  refine ⟨fun h => support_integralNormalization_subset h, ?_⟩
  simp only [integralNormalization_coeff, mem_support_iff]
  intro hfi
  split_ifs with hi <;> simp [hf, hfi]

end IsCancelMulZero

end IntegralNormalization

end Polynomial
