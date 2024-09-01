/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.Algebra.Algebra.Field
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Data.Countable.Small
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Differential Fields

This file defines the logarithmic derivative `logd` and proves properties of it.
-/

open Differential algebraMap

variable {R : Type*} [Field R] [Differential R] (a b : R)

/--
The logarithmic derivative of a is a′ / a.
-/
def logd : R := a′ / a

@[simp]
lemma logd_zero : logd (0 : R) = 0 := by
  unfold logd
  simp

@[simp]
lemma logd_one : logd (1 : R) = 0 := by
  unfold logd
  simp

lemma logd_mul (h₁ : a ≠ 0) (h₂ : b ≠ 0) : logd (a * b) = logd a + logd b := by
  unfold logd
  field_simp
  ring

lemma logd_div (h₁ : a ≠ 0) (h₂ : b ≠ 0) : logd (a / b) = logd a - logd b := by
  unfold logd
  field_simp [Derivation.leibniz_div]
  ring

lemma logd_npow (a : ℕ) : logd (b ^ a) = a * logd b := by
  by_cases h : b = 0
  · cases a <;> simp [h]
  induction a with
  | zero => simp
  | succ a h2 =>
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← h2, pow_succ, logd_mul] <;>
  simp [h]

lemma logd_eq_zero_iff : logd a = 0 ↔ a′ = 0 :=
  ⟨fun h ↦ by simp only [logd, div_eq_zero_iff] at h; rcases h with h|h <;> simp [h],
  fun h ↦ by unfold logd at *; simp [h]⟩

lemma logd_multisetProd {ι : Type*} (s : Multiset ι) {f : ι → R} (h : ∀ x ∈ s, f x ≠ 0) :
    logd (s.map f).prod = (s.map fun x ↦ logd (f x)).sum := by
  induction s using Multiset.induction_on
  · simp
  · rename_i h₂
    simp only [Function.comp_apply, Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons]
    rw [← h₂]
    apply logd_mul
    simp [h]
    apply Multiset.prod_ne_zero
    all_goals simp_all

lemma logd_prod (ι : Type*) (s : Finset ι) (f : ι → R) (h : ∀ x ∈ s, f x ≠ 0) :
    logd (∏ x ∈ s, f x) = ∑ x ∈ s, logd (f x) := logd_multisetProd _ h

lemma logd_prod_of_zero (ι : Type*) (s : Finset ι) (f : ι → R) (h : ∀ x ∈ s, f x = 0) :
    logd (∏ x ∈ s, f x) = ∑ x ∈ s, logd (f x) := by
  unfold logd
  simp_all

lemma logd_algebraMap {F K : Type*} [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K]
    (a : F) : logd (algebraMap F K a) = algebraMap F K (logd a) := by
  unfold logd
  simp [deriv_algebraMap]

@[norm_cast]
lemma algebraMap.coe_logd {F K : Type*} [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K]
    (a : F) : logd a = logd (a : K) := (logd_algebraMap a).symm
