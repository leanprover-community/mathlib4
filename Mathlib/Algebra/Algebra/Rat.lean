/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Algebra.Module.End
import Mathlib.Data.Rat.Cast.CharZero

/-!
# Further basic results about `Algebra`'s over `ℚ`.

This file could usefully be split further.
-/

assert_not_exists Subgroup

variable {F R S : Type*}

namespace RingHom

@[simp]
theorem map_rat_algebraMap [Semiring R] [Semiring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S)
    (r : ℚ) : f (algebraMap ℚ R r) = algebraMap ℚ S r :=
  RingHom.ext_iff.1 (Subsingleton.elim (f.comp (algebraMap ℚ R)) (algebraMap ℚ S)) r

end RingHom

namespace NNRat
variable [DivisionSemiring R] [CharZero R]

section Semiring
variable [Semiring S] [Module ℚ≥0 S]

variable (R) in
/-- `nnqsmul` is equal to any other module structure via a cast. -/
lemma cast_smul_eq_nnqsmul [Module R S] (q : ℚ≥0) (a : S) : (q : R) • a = q • a := by
  refine MulAction.injective₀ (G₀ := ℚ≥0) (Nat.cast_ne_zero.2 q.den_pos.ne') ?_
  dsimp
  rw [← mul_smul, den_mul_eq_num, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← smul_assoc,
    nsmul_eq_mul q.den, ← cast_natCast, ← cast_mul, den_mul_eq_num, cast_natCast,
    Nat.cast_smul_eq_nsmul]

end Semiring

section DivisionSemiring
variable [DivisionSemiring S] [CharZero S]

instance _root_.DivisionSemiring.toNNRatAlgebra : Algebra ℚ≥0 R where
  smul_def' := smul_def
  algebraMap := castHom _
  commutes' := cast_commute

instance _root_.RingHomClass.toLinearMapClassNNRat [FunLike F R S] [RingHomClass F R S] :
    LinearMapClass F ℚ≥0 R S where
  map_smulₛₗ f q a := by simp [smul_def, cast_id]

variable [SMul R S]

instance instSMulCommClass [SMulCommClass R S S] : SMulCommClass ℚ≥0 R S where
  smul_comm q a b := by simp [smul_def, mul_smul_comm]

instance instSMulCommClass' [SMulCommClass S R S] : SMulCommClass R ℚ≥0 S :=
  have := SMulCommClass.symm S R S; SMulCommClass.symm _ _ _

end DivisionSemiring
end NNRat

namespace Rat
variable [DivisionRing R] [CharZero R]

section Ring
variable [Ring S] [Module ℚ S]

variable (R) in
/-- `nnqsmul` is equal to any other module structure via a cast. -/
lemma cast_smul_eq_qsmul [Module R S] (q : ℚ) (a : S) : (q : R) • a = q • a := by
  refine MulAction.injective₀ (G₀ := ℚ) (Nat.cast_ne_zero.2 q.den_pos.ne') ?_
  dsimp
  rw [← mul_smul, den_mul_eq_num, Nat.cast_smul_eq_nsmul, Int.cast_smul_eq_zsmul, ← smul_assoc,
    nsmul_eq_mul q.den, ← cast_natCast, ← cast_mul, den_mul_eq_num, cast_intCast,
    Int.cast_smul_eq_zsmul]

end Ring

section DivisionRing
variable [DivisionRing S] [CharZero S]

instance _root_.DivisionRing.toRatAlgebra : Algebra ℚ R where
  smul_def' := smul_def
  algebraMap := castHom _
  commutes' := cast_commute

instance _root_.RingHomClass.toLinearMapClassRat [FunLike F R S] [RingHomClass F R S] :
    LinearMapClass F ℚ R S where
  map_smulₛₗ f q a := by simp [smul_def, cast_id]

variable [SMul R S]

instance instSMulCommClass [SMulCommClass R S S] : SMulCommClass ℚ R S where
  smul_comm q a b := by simp [smul_def, mul_smul_comm]

instance instSMulCommClass' [SMulCommClass S R S] : SMulCommClass R ℚ S :=
  have := SMulCommClass.symm S R S; SMulCommClass.symm _ _ _

end DivisionRing

instance algebra_rat_subsingleton {R} [Semiring R] : Subsingleton (Algebra ℚ R) :=
  ⟨fun x y => Algebra.algebra_ext x y <| RingHom.congr_fun <| Subsingleton.elim _ _⟩

end Rat
