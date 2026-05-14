/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import Batteries.Tactic.Trans
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!

# Lemmas about square of maximal ideal of local ring

-/

public section

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

variable (R) in
lemma IsLocalRing.maximalIdeal_sq_lt_maximalIdeal :
    maximalIdeal R ^ 2 < maximalIdeal R ↔ ¬ IsField R := by
  trans ¬ maximalIdeal R ^ 2 = maximalIdeal R
  · simp [lt_iff_le_and_ne, Ideal.pow_le_self]
  · rw [IsLocalRing.isField_iff_maximalIdeal_eq, pow_two]
    refine Iff.not ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
    exact Submodule.eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator (IsNoetherian.noetherian _)
      h.symm (maximalIdeal_le_jacobson _)

/-- In a Noetherian local ring of positive Krull dimension,
the square of the maximal ideal is strictly contained in the maximal ideal. -/
lemma IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero (h : ringKrullDim R ≠ 0) :
    (maximalIdeal R) ^ 2 < maximalIdeal R :=
  (maximalIdeal_sq_lt_maximalIdeal R).mpr (ringKrullDim_eq_zero_of_isField.mt h)

@[deprecated "Use `IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero` instead"
  (since := "2026-05-13")]
lemma IsLocalRing.maximalIdeal_sq_lt (h : 0 < ringKrullDim R) :
    (maximalIdeal R) ^ 2 < maximalIdeal R :=
  IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero h.ne.symm
