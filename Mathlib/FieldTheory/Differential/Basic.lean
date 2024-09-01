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
def logDeriv : R := a′ / a

@[simp]
lemma logDeriv_zero : logDeriv (0 : R) = 0 := by
  unfold logDeriv
  simp

@[simp]
lemma logDeriv_one : logDeriv (1 : R) = 0 := by
  unfold logDeriv
  simp

lemma logDeriv_mul (h₁ : a ≠ 0) (h₂ : b ≠ 0) : logDeriv (a * b) = logDeriv a + logDeriv b := by
  unfold logDeriv
  field_simp
  ring

lemma logDeriv_div (h₁ : a ≠ 0) (h₂ : b ≠ 0) : logDeriv (a / b) = logDeriv a - logDeriv b := by
  unfold logDeriv
  field_simp [Derivation.leibniz_div]
  ring

lemma logDeriv_npow (a : ℕ) : logDeriv (b ^ a) = a * logDeriv b := by
  by_cases h : b = 0
  · cases a <;> simp [h]
  induction a with
  | zero => simp
  | succ a h2 =>
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← h2, pow_succ, logDeriv_mul] <;>
  simp [h]

lemma logDeriv_eq_zero_iff : logDeriv a = 0 ↔ a′ = 0 :=
  ⟨fun h ↦ by simp only [logDeriv, div_eq_zero_iff] at h; rcases h with h|h <;> simp [h],
  fun h ↦ by unfold logDeriv at *; simp [h]⟩

lemma logDeriv_multisetProd {ι : Type*} (s : Multiset ι) {f : ι → R} (h : ∀ x ∈ s, f x ≠ 0) :
    logDeriv (s.map f).prod = (s.map fun x ↦ logDeriv (f x)).sum := by
  induction s using Multiset.induction_on
  · simp
  · rename_i h₂
    simp only [Function.comp_apply, Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons]
    rw [← h₂]
    apply logDeriv_mul
    simp [h]
    apply Multiset.prod_ne_zero
    all_goals simp_all

lemma logDeriv_prod (ι : Type*) (s : Finset ι) (f : ι → R) (h : ∀ x ∈ s, f x ≠ 0) :
    logDeriv (∏ x ∈ s, f x) = ∑ x ∈ s, logDeriv (f x) := logDeriv_multisetProd _ h

lemma logDeriv_prod_of_zero (ι : Type*) (s : Finset ι) (f : ι → R) (h : ∀ x ∈ s, f x = 0) :
    logDeriv (∏ x ∈ s, f x) = ∑ x ∈ s, logDeriv (f x) := by
  unfold logDeriv
  simp_all

lemma logDeriv_algebraMap {F K : Type*} [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K]
    (a : F) : logDeriv (algebraMap F K a) = algebraMap F K (logDeriv a) := by
  unfold logDeriv
  simp [deriv_algebraMap]

@[norm_cast]
lemma algebraMap.coe_logDeriv {F K : Type*} [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K]
    (a : F) : logDeriv a = logDeriv (a : K) := (logDeriv_algebraMap a).symm
