/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Data.Finsupp.Basic

/-!
# Monoid algebras and the opposite ring
-/

assert_not_exists NonUnitalAlgHom AlgEquiv

noncomputable section

open Finsupp hiding single

universe u₁ u₂ u₃ u₄

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S M : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra

variable {k G}

open Finsupp MulOpposite

variable [Semiring k]

/-- The opposite of a `MonoidAlgebra R I` equivalent as a ring to
the `MonoidAlgebra Rᵐᵒᵖ Iᵐᵒᵖ` over the opposite ring, taking elements to their opposite. -/
@[simps! +simpRhs apply symm_apply]
protected noncomputable def opRingEquiv [Mul G] :
    (MonoidAlgebra k G)ᵐᵒᵖ ≃+* MonoidAlgebra kᵐᵒᵖ Gᵐᵒᵖ :=
  { opAddEquiv.symm.trans <|
      (Finsupp.mapRange.addEquiv (opAddEquiv : k ≃+ kᵐᵒᵖ)).trans <| Finsupp.domCongr opEquiv with
    map_mul' := by
      -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
      rw [Equiv.toFun_as_coe, AddEquiv.toEquiv_eq_coe]; erw [AddEquiv.coe_toEquiv]
      rw [← AddEquiv.coe_toAddMonoidHom]
      refine Iff.mpr (AddMonoidHom.map_mul_iff (R := (MonoidAlgebra k G)ᵐᵒᵖ)
        (S := MonoidAlgebra kᵐᵒᵖ Gᵐᵒᵖ) _) ?_
      ext
      -- Porting note: `reducible` cannot be `local` so proof gets long.
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, singleAddHom_apply,
        AddMonoidHom.compr₂_apply, AddMonoidHom.coe_mul, AddMonoidHom.coe_mulLeft,
        AddMonoidHom.compl₂_apply, AddEquiv.toAddMonoidHom_eq_coe,
        AddEquiv.coe_addMonoidHom_trans]
      -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
      erw [AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.trans_apply,
        MulOpposite.opAddEquiv_symm_apply]
      rw [MulOpposite.unop_mul (α := MonoidAlgebra k G)]
      simp }

theorem opRingEquiv_single [Mul G] (r : k) (x : G) :
    MonoidAlgebra.opRingEquiv (op (single x r)) = single (op x) (op r) := by simp

theorem opRingEquiv_symm_single [Mul G] (r : kᵐᵒᵖ) (x : Gᵐᵒᵖ) :
    MonoidAlgebra.opRingEquiv.symm (single x r) = op (single x.unop r.unop) := by simp

end MonoidAlgebra

/-! ### Additive monoids -/

namespace AddMonoidAlgebra

variable {k G H}

open Finsupp MulOpposite

variable [Semiring k]

/-- The opposite of an `R[I]` is ring equivalent to
the `AddMonoidAlgebra Rᵐᵒᵖ I` over the opposite ring, taking elements to their opposite. -/
@[simps! +simpRhs apply symm_apply]
protected noncomputable def opRingEquiv [AddCommMagma G] :
    k[G]ᵐᵒᵖ ≃+* kᵐᵒᵖ[G] :=
  { opAddEquiv.symm.trans (mapRange.addEquiv (opAddEquiv : k ≃+ kᵐᵒᵖ)) with
    map_mul' := by
      let f : k[G]ᵐᵒᵖ ≃+ kᵐᵒᵖ[G] :=
        opAddEquiv.symm.trans (mapRange.addEquiv (opAddEquiv : k ≃+ kᵐᵒᵖ))
      change ∀ (x y : k[G]ᵐᵒᵖ), f (x * y) = f x * f y
      rw [← AddEquiv.coe_toAddMonoidHom, AddMonoidHom.map_mul_iff]
      ext i₁ r₁ i₂ r₂ : 6
      dsimp only [f, AddMonoidHom.compr₂_apply, AddMonoidHom.compl₂_apply,
        AddMonoidHom.comp_apply, AddMonoidHom.coe_coe,
        AddEquiv.toAddMonoidHom_eq_coe, AddEquiv.coe_addMonoidHom_trans,
        singleAddHom_apply, opAddEquiv_apply, opAddEquiv_symm_apply,
        AddMonoidHom.coe_mul, AddMonoidHom.coe_mulLeft, unop_mul, unop_op]
      -- Defeq abuse. Probably `k[G]` vs `G →₀ k`.
      erw [mapRange.addEquiv_apply, mapRange.addEquiv_apply, mapRange.addEquiv_apply]
      rw [single_mul_single, mapRange_single, mapRange_single, mapRange_single, single_mul_single]
      simp only [opAddEquiv_apply, op_mul, add_comm] }

-- Not `@[simp]` because the LHS simplifies further.
-- TODO: the LHS simplifies to `Finsupp.single`, which implies there's some defeq abuse going on.
theorem opRingEquiv_single [AddCommMagma G] (r : k) (x : G) :
    AddMonoidAlgebra.opRingEquiv (op (single x r)) = single x (op r) := by simp

theorem opRingEquiv_symm_single [AddCommMagma G] (r : kᵐᵒᵖ) (x : Gᵐᵒᵖ) :
    AddMonoidAlgebra.opRingEquiv.symm (single x r) = op (single x r.unop) := by simp

end AddMonoidAlgebra
