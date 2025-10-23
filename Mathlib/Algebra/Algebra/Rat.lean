/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Module.Equiv.Defs
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
variable [DivisionSemiring R] [CharZero R] [DivisionSemiring S] [CharZero S]

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

end NNRat

namespace Rat
variable [DivisionRing R] [CharZero R] [DivisionRing S] [CharZero S]

instance _root_.DivisionRing.toRatAlgebra : Algebra ℚ R where
  smul_def' := smul_def
  algebraMap := castHom _
  commutes' := cast_commute

instance _root_.RingHomClass.toLinearMapClassRat [FunLike F R S] [RingHomClass F R S] :
    LinearMapClass F ℚ R S where
  map_smulₛₗ f q a := by simp [smul_def, cast_id]

instance _root_.RingEquivClass.toLinearEquivClassRat [EquivLike F R S] [RingEquivClass F R S] :
    LinearEquivClass F ℚ R S where
  map_smulₛₗ f c x := by simp [Algebra.smul_def]

variable [SMul R S]

instance instSMulCommClass [SMulCommClass R S S] : SMulCommClass ℚ R S where
  smul_comm q a b := by simp [smul_def, mul_smul_comm]

instance instSMulCommClass' [SMulCommClass S R S] : SMulCommClass R ℚ S :=
  have := SMulCommClass.symm S R S; SMulCommClass.symm _ _ _

instance algebra_rat_subsingleton {R} [Semiring R] : Subsingleton (Algebra ℚ R) :=
  ⟨fun x y => Algebra.algebra_ext x y <| RingHom.congr_fun <| Subsingleton.elim _ _⟩

end Rat
