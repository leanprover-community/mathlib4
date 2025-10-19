/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Ring.Opposite

/-!
# Actions by matrices on vectors through `*ᵥ` and `ᵥ*`, cast as `Module`s

This file provides the left- and right- module structures of square matrices on vectors, via
`Matrix.mulVec` and `Matrix.vecMul`.
-/

variable {n R S : Type*}

namespace Matrix

variable [Fintype n] [DecidableEq n] [Semiring R]

/-! ## `*ᵥ` as a left-module -/

section mulVec

instance : Module (Matrix n n R) (n → R) where
  smul := mulVec
  one_smul := one_mulVec
  mul_smul _ _ _ := (mulVec_mulVec _ _ _).symm
  zero_smul := zero_mulVec
  add_smul := add_mulVec
  smul_zero := mulVec_zero
  smul_add := mulVec_add

@[simp] lemma smul_eq_mulVec (A : Matrix n n R) (v : n → R) : A • v = A *ᵥ v := rfl

instance [DistribSMul S R] [SMulCommClass R S R] : SMulCommClass (Matrix n n R) S (n → R) where
  smul_comm := letI := SMulCommClass.symm; mulVec_smul

instance [DistribSMul S R] [SMulCommClass S R R] : SMulCommClass S (Matrix n n R) (n → R) where
  smul_comm s A v := (mulVec_smul A s v).symm

instance [DistribSMul S R] [IsScalarTower S R R] : IsScalarTower S (Matrix n n R) (n → R) where
  smul_assoc := smul_mulVec

end mulVec

/-! ## `*ᵥ` as a right-module -/

section vecMul

instance : Module (Matrix n n R)ᵐᵒᵖ (n → R) where
  smul A v := v ᵥ* A.unop
  one_smul := Matrix.vecMul_one
  mul_smul _ _ _ := (vecMul_vecMul _ _ _).symm
  zero_smul := vecMul_zero
  add_smul _ _ := vecMul_add _ _
  smul_zero _ := zero_vecMul _
  smul_add _ := add_vecMul _

@[simp] lemma op_smul_eq_vecMul (A : (Matrix n n R)ᵐᵒᵖ) (v : n → R) : A • v = v ᵥ* A.unop := rfl

instance [DistribSMul S R] [IsScalarTower S R R] : SMulCommClass (Matrix n n R)ᵐᵒᵖ S (n → R) where
  smul_comm A s v := smul_vecMul s v A.unop

instance [DistribSMul S R] [IsScalarTower S R R] : SMulCommClass S (Matrix n n R)ᵐᵒᵖ (n → R) where
  smul_comm s A v := (smul_vecMul s v A.unop).symm

instance [DistribSMul S R] [SMulCommClass S R R] : IsScalarTower S (Matrix n n R)ᵐᵒᵖ (n → R) where
  smul_assoc s A v := vecMul_smul v s A.unop

end vecMul

end Matrix
