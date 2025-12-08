/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
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
  __ := opAddEquiv.symm.trans <|
      (Finsupp.mapRange.addEquiv (opAddEquiv : R ≃+ Rᵐᵒᵖ)).trans <| Finsupp.domCongr opEquiv
  map_mul' := by
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    rw [Equiv.toFun_as_coe, AddEquiv.toEquiv_eq_coe]; erw [AddEquiv.coe_toEquiv]
    rw [← AddEquiv.coe_toAddMonoidHom]
    refine (AddMonoidHom.map_mul_iff (R := R[M]ᵐᵒᵖ) (S := Rᵐᵒᵖ[Mᵐᵒᵖ]) _).mpr ?_
    ext
    -- Porting note: `reducible` cannot be `local` so proof gets long.
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, singleAddHom_apply,
      AddMonoidHom.compr₂_apply, AddMonoidHom.coe_mul, AddMonoidHom.coe_mulLeft,
      AddMonoidHom.compl₂_apply, AddEquiv.toAddMonoidHom_eq_coe,
      AddEquiv.coe_addMonoidHom_trans]
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.trans_apply,
      MulOpposite.opAddEquiv_symm_apply]
    rw [MulOpposite.unop_mul (α := R[M])]
    simp

@[to_additive (dont_translate := R)]
lemma opRingEquiv_single (r : R) (x : M) :
    MonoidAlgebra.opRingEquiv (op (single x r)) = single (op x) (op r) := by simp

@[to_additive (dont_translate := R)]
lemma opRingEquiv_symm_single (r : Rᵐᵒᵖ) (x : Mᵐᵒᵖ) :
    MonoidAlgebra.opRingEquiv.symm (single x r) = op (single x.unop r.unop) := by simp

end MonoidAlgebra
