/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Algebra.Field.Opposite

/-!
# Star ring classes and facts about the star operation for primitive types, ℕ, ℤ, ℚ, ℚ≥0.

-/

open MulOpposite

universe u

variable {R : Type u}

@[simp, norm_cast]
lemma star_nnratCast [DivisionSemiring R] [StarRing R] (q : ℚ≥0) : star (q : R) = q :=
  (congr_arg unop <| map_nnratCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) q).trans (unop_nnratCast _)

@[simp, norm_cast]
theorem star_ratCast [DivisionRing R] [StarRing R] (r : ℚ) : star (r : R) = r :=
  (congr_arg unop <| map_ratCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) r).trans (unop_ratCast _)
#align star_rat_cast star_ratCast


instance Nat.instStarRing : StarRing ℕ := starRingOfComm
instance Int.instStarRing : StarRing ℤ := starRingOfComm
instance Rat.instStarRing : StarRing ℚ := starRingOfComm
instance NNRat.instStarRing : StarRing ℚ≥0 := starRingOfComm
instance Nat.instTrivialStar : TrivialStar ℕ := ⟨fun _ ↦ rfl⟩
instance Int.instTrivialStar : TrivialStar ℤ := ⟨fun _ ↦ rfl⟩
instance Rat.instTrivialStar : TrivialStar ℚ := ⟨fun _ ↦ rfl⟩
instance NNRat.instTrivialStar : TrivialStar ℚ≥0 := ⟨fun _ ↦ rfl⟩

instance StarAddMonoid.toStarModuleNat {α} [AddCommMonoid α] [StarAddMonoid α] : StarModule ℕ α :=
  ⟨fun n a ↦ by rw [star_nsmul, star_trivial n]⟩

