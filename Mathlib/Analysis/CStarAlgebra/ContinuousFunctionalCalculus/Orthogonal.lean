/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Star.Orthogonal
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Star-orthogonality and the continuous functional calculus

If `a ⋆⟂ b`, then `cfcₙ f a ⋆⟂ b` whenever `f 0 = 0` (and `a` satisfies the predicate for the
relevant continuous functional calculus). This file provides these results for the `ℂ`, `ℝ` and
`ℝ≥0` non-unital continuous functional calculi.

## Main declarations

+ `IsStarOrtho.cfcₙ_complex_left`: if `a` is normal and `a ⋆⟂ b`, then `cfcₙ f a ⋆⟂ b`.
+ `IsStarOrtho.cfcₙ_real_left`: if `a` is selfadjoint and `a ⋆⟂ b`, then `cfcₙ f a ⋆⟂ b`.
+ `IsStarOrtho.cfcₙ_nnreal_left`: if `a` is nonnegative and `a ⋆⟂ b`, then `cfcₙ f a ⋆⟂ b`.
+ `isStarOrtho_sqrt_left_iff`: if `0 ≤ a`, then `CFC.sqrt a ⋆⟂ b ↔ a ⋆⟂ b`.
-/

public section

open scoped StarRing

variable {A : Type*} [NonUnitalRing A] [StarRing A] [TopologicalSpace A]
  [IsSemitopologicalRing A] [T2Space A] {a b : A}

namespace IsStarOrtho

section Complex

variable [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [IsProperStar A]
  [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal]

/-- If `a` is normal and `a ⋆⟂ b`, then `cfcₙ f a ⋆⟂ b`. -/
lemma cfcₙ_complex_left (f : ℂ → ℂ) (h : a ⋆⟂ b) (ha : IsStarNormal a := by cfc_tac)
    (hf : ContinuousOn f (quasispectrum ℂ a) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a ⋆⟂ b := by
  have := isCompact_iff_compactSpace.mp <|
    NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum (R := ℂ) (p := IsStarNormal) a
  have h' := h.star_left_of_isStarNormal ha
  rw [cfcₙ_apply f a]
  constructor
  · refine ContinuousMapZero.nonUnitalStarAlgHom_apply_mul_eq_zero _ _
      (by simpa using h.mul_star_eq_zero) ?_ (cfcₙHom_continuous ha) _
    simpa [map_star] using h'.mul_star_eq_zero
  · refine ContinuousMapZero.mul_nonUnitalStarAlgHom_apply_eq_zero _ _
      (by simpa using h.star_mul_eq_zero) ?_ (cfcₙHom_continuous ha) _
    simpa [map_star] using h'.star_mul_eq_zero

/-- If `b` is normal and `a ⋆⟂ b`, then `a ⋆⟂ cfcₙ f b`. -/
lemma cfcₙ_complex_right (f : ℂ → ℂ) (h : a ⋆⟂ b) (hb : IsStarNormal b := by cfc_tac)
    (hf : ContinuousOn f (quasispectrum ℂ b) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    a ⋆⟂ cfcₙ f b :=
  (h.symm.cfcₙ_complex_left f).symm

end Complex

section Real

variable [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- If `a` is selfadjoint and `a ⋆⟂ b`, then `cfcₙ f a ⋆⟂ b`. -/
lemma cfcₙ_real_left (f : ℝ → ℝ) (h : a ⋆⟂ b) (ha : IsSelfAdjoint a := by cfc_tac)
    (hf : ContinuousOn f (quasispectrum ℝ a) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a ⋆⟂ b := by
  have := isCompact_iff_compactSpace.mp <|
    NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum (R := ℝ) (p := IsSelfAdjoint) a
  rw [cfcₙ_apply f a]
  constructor
  · refine ContinuousMapZero.nonUnitalStarAlgHom_apply_mul_eq_zero _ _ ?_ ?_
      (cfcₙHom_continuous ha) _
    all_goals simpa [map_star, cfcₙHom_id ha, ha.star_eq] using h.mul_star_eq_zero
  · refine ContinuousMapZero.mul_nonUnitalStarAlgHom_apply_eq_zero _ _ ?_ ?_
      (cfcₙHom_continuous ha) _
    all_goals simpa [map_star, cfcₙHom_id ha, ha.star_eq] using h.star_mul_eq_zero

/-- If `b` is selfadjoint and `a ⋆⟂ b`, then `a ⋆⟂ cfcₙ f b`. -/
lemma cfcₙ_real_right (f : ℝ → ℝ) (h : a ⋆⟂ b) (hb : IsSelfAdjoint b := by cfc_tac)
    (hf : ContinuousOn f (quasispectrum ℝ b) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    a ⋆⟂ cfcₙ f b :=
  (h.symm.cfcₙ_real_left f).symm

variable [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]

open scoped NNReal

/-- If `a` is nonnegative and `a ⋆⟂ b`, then `cfcₙ f a ⋆⟂ b`. -/
lemma cfcₙ_nnreal_left (f : ℝ≥0 → ℝ≥0) (h : a ⋆⟂ b) (ha : 0 ≤ a := by cfc_tac)
    (hf : ContinuousOn f (quasispectrum ℝ≥0 a) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a ⋆⟂ b := by
  rw [cfcₙ_nnreal_eq_real f a]
  refine h.cfcₙ_real_left _ (.of_nonneg ha) ?_ (by simpa)
  refine NNReal.continuous_coe.comp_continuousOn <|
    hf.comp continuous_real_toNNReal.continuousOn fun x hx ↦ ?_
  rw [← (QuasispectrumRestricts.nnreal_of_nonneg ha).algebraMap_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa

/-- If `b` is nonnegative and `a ⋆⟂ b`, then `a ⋆⟂ cfcₙ f b`. -/
lemma cfcₙ_nnreal_right (f : ℝ≥0 → ℝ≥0) (h : a ⋆⟂ b) (hb : 0 ≤ b := by cfc_tac)
    (hf : ContinuousOn f (quasispectrum ℝ≥0 b) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    a ⋆⟂ cfcₙ f b :=
  (h.symm.cfcₙ_nnreal_left f).symm

open CFC

lemma _root_.isStarOrtho_sqrt_right_iff (ha : 0 ≤ a) : b ⋆⟂ sqrt a ↔ b ⋆⟂ a := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.cfcₙ_nnreal_right _⟩
  have := h.cfcₙ_nnreal_right (fun x ↦ x * x)
  rwa [cfcₙ_mul .., cfcₙ_id' .., sqrt_mul_sqrt_self _] at this

lemma _root_.isStarOrtho_sqrt_left_iff (ha : 0 ≤ a) : sqrt a ⋆⟂ b ↔ a ⋆⟂ b := by
  simpa [isStarOrtho_comm] using isStarOrtho_sqrt_right_iff ha

alias ⟨of_sqrt_right, sqrt_right⟩ := isStarOrtho_sqrt_right_iff
alias ⟨of_sqrt_left, sqrt_left⟩ := isStarOrtho_sqrt_left_iff

end Real

end IsStarOrtho
