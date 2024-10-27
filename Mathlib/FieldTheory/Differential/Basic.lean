/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Differential Fields

This file defines the logarithmic derivative `Differential.logDeriv` and proves properties of it.
This is defined algebraically, compared to `logDeriv` which is analytical.
-/

namespace Differential

open algebraMap

variable {R : Type*} [Field R] [Differential R] (a b : R)

/--
The logarithmic derivative of a is a′ / a.
-/
def logDeriv : R := a′ / a

@[simp]
lemma logDeriv_zero : logDeriv (0 : R) = 0 := by
  simp [logDeriv]

@[simp]
lemma logDeriv_one : logDeriv (1 : R) = 0 := by
  simp [logDeriv]

lemma logDeriv_mul (ha : a ≠ 0) (hb : b ≠ 0) : logDeriv (a * b) = logDeriv a + logDeriv b := by
  unfold logDeriv
  field_simp
  ring

lemma logDeriv_div (ha : a ≠ 0) (hb : b ≠ 0) : logDeriv (a / b) = logDeriv a - logDeriv b := by
  unfold logDeriv
  field_simp [Derivation.leibniz_div, smul_sub]
  ring

@[simp]
lemma logDeriv_pow (n : ℕ) (a : R) : logDeriv (a ^ n) = n * logDeriv a := by
  induction n with
  | zero => simp
  | succ n h2 =>
    obtain rfl | hb := eq_or_ne a 0
    · simp
    · rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← h2, pow_succ, logDeriv_mul] <;>
      simp [hb]

lemma logDeriv_eq_zero : logDeriv a = 0 ↔ a′ = 0 :=
  ⟨fun h ↦ by simp only [logDeriv, div_eq_zero_iff] at h; rcases h with h|h <;> simp [h],
  fun h ↦ by unfold logDeriv at *; simp [h]⟩

lemma logDeriv_multisetProd {ι : Type*} (s : Multiset ι) {f : ι → R} (h : ∀ x ∈ s, f x ≠ 0) :
    logDeriv (s.map f).prod = (s.map fun x ↦ logDeriv (f x)).sum := by
  induction s using Multiset.induction_on
  · simp
  · rename_i h₂
    simp only [Function.comp_apply, Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons]
    rw [← h₂]
    · apply logDeriv_mul
      · simp [h]
      · simp_all
    · simp_all

lemma logDeriv_prod (ι : Type*) (s : Finset ι) (f : ι → R) (h : ∀ x ∈ s, f x ≠ 0) :
    logDeriv (∏ x ∈ s, f x) = ∑ x ∈ s, logDeriv (f x) := logDeriv_multisetProd _ h

lemma logDeriv_prod_of_eq_zero (ι : Type*) (s : Finset ι) (f : ι → R) (h : ∀ x ∈ s, f x = 0) :
    logDeriv (∏ x ∈ s, f x) = ∑ x ∈ s, logDeriv (f x) := by
  unfold logDeriv
  simp_all

lemma logDeriv_algebraMap {F K : Type*} [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K]
    (a : F) : logDeriv (algebraMap F K a) = algebraMap F K (logDeriv a) := by
  unfold logDeriv
  simp [deriv_algebraMap]

@[norm_cast]
lemma _root_.algebraMap.coe_logDeriv {F K : Type*} [Field F] [Field K] [Differential F]
    [Differential K] [Algebra F K] [DifferentialAlgebra F K]
    (a : F) : logDeriv a = logDeriv (a : K) := (logDeriv_algebraMap a).symm

end Differential
