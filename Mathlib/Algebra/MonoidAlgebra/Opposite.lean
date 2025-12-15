/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Data.Finsupp.Basic

/-!
# Monoid algebras and the opposite ring
-/

assert_not_exists NonUnitalAlgHom AlgEquiv

@[expose] public noncomputable section

open Finsupp MulOpposite

variable {R M : Type*} [Semiring R] [Mul M]

namespace MonoidAlgebra

/-- The opposite of a monoid algebra is equivalent as a ring to the opposite monoid algebra over the
opposite ring. -/
@[to_additive (dont_translate := R) (attr := simps! +simpRhs apply symm_apply)
/-- The opposite of a monoid algebra is equivalent as a ring to the opposite monoid algebra over the
opposite ring. -/]
protected noncomputable def opRingEquiv : R[M]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[Mᵐᵒᵖ] where
  toAddEquiv :=
    opAddEquiv.symm.trans <| (mapDomainAddEquiv _ opEquiv).trans <| mapRangeAddEquiv _ opAddEquiv
  map_mul' := by
    classical
    simp [-opEquiv_apply, coeff_mul, MonoidAlgebra.ext_iff, Finsupp.ext_iff, ← MulOpposite.unop_inj,
      sum_mapRange_index, apply_ite op, mapRangeAddEquiv]
    simpa using fun _ _ _ ↦ Finsupp.sum_comm ..

@[to_additive (dont_translate := R)]
lemma opRingEquiv_single (r : R) (x : M) :
    MonoidAlgebra.opRingEquiv (op (single x r)) = single (op x) (op r) := by ext; simp

@[to_additive (dont_translate := R)]
lemma opRingEquiv_symm_single (r : Rᵐᵒᵖ) (x : Mᵐᵒᵖ) :
    MonoidAlgebra.opRingEquiv.symm (single x r) = op (single x.unop r.unop) := by
  apply MulOpposite.unop_injective; ext; simp

end MonoidAlgebra
