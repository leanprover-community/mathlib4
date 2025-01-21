/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-! # Properties of `rpow` and `sqrt` over C⋆-algebras

This file collects results about `CFC.rpow`, `CFC.nnrpow` and `CFC.sqrt` that use facts that
are specific to C⋆-algebras.

## Main theorems

* Various versions of `‖a ^ r‖ = ‖a‖ ^ r` and `‖CFC.sqrt a‖ = sqrt ‖a‖`.

## Tags

continuous functional calculus, rpow, sqrt
-/

open scoped NNReal

namespace CFC

section nonunital

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [NormedSpace ℝ A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A] [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

lemma nnnorm_nnrpow (a : A) (r : ℝ≥0) (hr : 0 < r) (ha : 0 ≤ a) : ‖a ^ r‖₊ = ‖a‖₊ ^ (r : ℝ) := by
  simp only [nnrpow_def]
  rw [MonotoneOn.nnnorm_cfcₙ _ _ (Monotone.monotoneOn (NNReal.monotone_nnrpow_const r) _)]

lemma norm_nnrpow (a : A) (r : ℝ≥0) (hr : 0 < r) (ha : 0 ≤ a) : ‖a ^ r‖ = ‖a‖ ^ (r : ℝ) := by
  have h₁ : ‖a ^ r‖ = (‖a ^ r‖₊ : ℝ) := rfl
  rw [h₁, nnnorm_nnrpow a r hr ha]
  rfl

lemma nnnorm_sqrt (a : A) (ha : 0 ≤ a) : ‖sqrt a‖₊ = NNReal.sqrt ‖a‖₊ := by
  rw [sqrt_eq_nnrpow]
  calc _ = ‖a‖₊ ^ (1 / 2 : ℝ) := by exact nnnorm_nnrpow a _ (by norm_num) ha
    _ = NNReal.sqrt ‖a‖₊ := Eq.symm (NNReal.sqrt_eq_rpow ‖a‖₊)

lemma norm_sqrt (a : A) (ha : 0 ≤ a) : ‖sqrt a‖ = Real.sqrt ‖a‖ := by
  have hmain : ‖sqrt a‖₊ = (⟨Real.sqrt ‖a‖, by positivity⟩ : ℝ≥0) := by
    calc _ = NNReal.sqrt ‖a‖₊ := nnnorm_sqrt a ha
      _ = _ := by rw [← norm_toNNReal]; rfl
  have h₁ : ‖sqrt a‖ = (‖sqrt a‖₊ : ℝ) := rfl
  rw [h₁, hmain]
  rfl

end nonunital

section unital

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

lemma nnnorm_rpow (a : A) (r : ℝ) (hr : 0 < r) (ha : 0 ≤ a) : ‖a ^ r‖₊ = ‖a‖₊ ^ r := by
  let r' : ℝ≥0 := ⟨r, by positivity⟩
  have hr' : 0 < r' := by exact_mod_cast hr
  show ‖a ^ (r' : ℝ)‖₊ = ‖a‖₊ ^ (r' : ℝ)
  rw [← nnrpow_eq_rpow hr', nnnorm_nnrpow a r' hr' ha]

lemma norm_rpow (a : A) (r : ℝ) (hr : 0 < r) (ha : 0 ≤ a) : ‖a ^ r‖ = ‖a‖ ^ r := by
  let r' : ℝ≥0 := ⟨r, by positivity⟩
  have hr' : 0 < r' := by exact_mod_cast hr
  show ‖a ^ (r' : ℝ)‖ = ‖a‖ ^ (r' : ℝ)
  rw [← nnrpow_eq_rpow hr', norm_nnrpow a r' hr' ha]

end unital

end CFC
