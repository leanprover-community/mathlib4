/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Field.Opposite
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Positivity.Basic

/-!
# *-ring structure on ℚ and ℚ≥0.
-/

instance Rat.instStarRing : StarRing ℚ := starRingOfComm
instance NNRat.instStarRing : StarRing ℚ≥0 := starRingOfComm
instance Rat.instTrivialStar : TrivialStar ℚ := ⟨fun _ ↦ rfl⟩
instance NNRat.instTrivialStar : TrivialStar ℚ≥0 := ⟨fun _ ↦ rfl⟩

variable {α R : Type*}

open MulOpposite

@[simp, norm_cast]
lemma star_nnratCast [DivisionSemiring R] [StarRing R] (q : ℚ≥0) : star (q : R) = q :=
  (congr_arg unop <| map_nnratCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) q).trans (unop_nnratCast _)

@[simp, norm_cast]
theorem star_ratCast [DivisionRing R] [StarRing R] (r : ℚ) : star (r : R) = r :=
  (congr_arg unop <| map_ratCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) r).trans (unop_ratCast _)

@[simp] lemma star_nnqsmul [AddCommMonoid α] [Module ℚ≥0 α] [StarAddMonoid α] (q : ℚ≥0) (a : α) :
    star (q • a) = q • star a := by
  refine MulAction.injective₀ (G₀ := ℚ≥0) (a := q.den) (by positivity) ?_
  dsimp
  rw [Nat.cast_smul_eq_nsmul, ← star_nsmul, ← Nat.cast_smul_eq_nsmul ℚ≥0, smul_smul, smul_smul,
    NNRat.den_mul_eq_num, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, star_nsmul]

@[simp] lemma star_qsmul [AddCommGroup α] [Module ℚ α] [StarAddMonoid α] (q : ℚ) (a : α) :
    star (q • a) = q • star a := by
  refine MulAction.injective₀ (G₀ := ℚ) (a := q.den) (by positivity) ?_
  dsimp
  rw [Nat.cast_smul_eq_nsmul, ← star_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_smul,
    Rat.den_mul_eq_num, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, star_zsmul]

instance StarAddMonoid.toStarModuleNNRat [AddCommMonoid α] [Module ℚ≥0 α] [StarAddMonoid α] :
    StarModule ℚ≥0 α where star_smul := star_nnqsmul

instance StarAddMonoid.toStarModuleRat [AddCommGroup α] [Module ℚ α] [StarAddMonoid α] :
    StarModule ℚ α where star_smul := star_qsmul
