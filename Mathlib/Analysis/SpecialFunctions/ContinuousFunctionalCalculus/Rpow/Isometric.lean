/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-! # Properties of `rpow` and `sqrt` over an algebra with an isometric CFC

This file collects results about `CFC.rpow`, `CFC.nnrpow` and `CFC.sqrt` that use facts that
rely on an isometric continuous functional calculus.

## Main theorems

* Various versions of `‖a ^ r‖ = ‖a‖ ^ r` and `‖CFC.sqrt a‖ = sqrt ‖a‖`.

## Tags

continuous functional calculus, rpow, sqrt
-/

public section

open scoped NNReal

namespace CFC

section nonunital

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [NormedSpace ℝ A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A] [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

lemma nnnorm_nnrpow (a : A) {r : ℝ≥0} (hr : 0 < r) (ha : 0 ≤ a := by cfc_tac) :
    ‖a ^ r‖₊ = ‖a‖₊ ^ (r : ℝ) :=
  NNReal.monotone_nnrpow_const r |>.monotoneOn _ |>.nnnorm_cfcₙ _ _

lemma norm_nnrpow (a : A) {r : ℝ≥0} (hr : 0 < r) (ha : 0 ≤ a := by cfc_tac) :
    ‖a ^ r‖ = ‖a‖ ^ (r : ℝ) :=
  congr(NNReal.toReal $(nnnorm_nnrpow a hr ha))

lemma nnnorm_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) : ‖sqrt a‖₊ = NNReal.sqrt ‖a‖₊ := by
  rw [sqrt_eq_nnrpow, NNReal.sqrt_eq_rpow]
  exact nnnorm_nnrpow a (by simp) ha

lemma norm_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) : ‖sqrt a‖ = √‖a‖ := by
  simpa using congr(NNReal.toReal $(nnnorm_sqrt a ha))

variable [ContinuousStar A] [CompleteSpace A]

lemma continuousOn_sqrt : ContinuousOn sqrt {a : A | 0 ≤ a} :=
  continuousOn_id.cfcₙ_nnreal_of_mem_nhdsSet _ Filter.univ_mem

lemma continuousOn_nnrpow (r : ℝ≥0) : ContinuousOn (· ^ r) {a : A | 0 ≤ a} := by
  obtain (rfl | hr) := eq_zero_or_pos r
  · simpa using continuousOn_const
  · exact continuousOn_id.cfcₙ_nnreal_of_mem_nhdsSet _ Filter.univ_mem

end nonunital

section unital

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

lemma nnnorm_rpow (a : A) {r : ℝ} (hr : 0 < r) (ha : 0 ≤ a := by cfc_tac) :
    ‖a ^ r‖₊ = ‖a‖₊ ^ r := by
  lift r to ℝ≥0 using hr.le
  rw [← nnrpow_eq_rpow, ← nnnorm_nnrpow a]
  all_goals simpa

lemma norm_rpow (a : A) {r : ℝ} (hr : 0 < r) (ha : 0 ≤ a := by cfc_tac) :
    ‖a ^ r‖ = ‖a‖ ^ r :=
  congr(NNReal.toReal $(nnnorm_rpow a hr ha))

lemma continuousOn_rpow [ContinuousStar A] [CompleteSpace A] (r : ℝ) :
    ContinuousOn (· ^ r) {a : A | IsStrictlyPositive a} := by
  refine continuousOn_id.cfc_nnreal_of_mem_nhdsSet _ (s := {0}ᶜ) ?_
  simp_rw [nhdsSet_iUnion, Filter.mem_iSup, isOpen_compl_singleton.mem_nhdsSet]
  exact fun a ha ↦ by simpa using spectrum.zero_notMem _ ha.isUnit

end unital

end CFC
