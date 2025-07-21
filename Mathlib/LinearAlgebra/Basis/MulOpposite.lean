/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Basis of an opposite space

This file defines the basis of an opposite space and shows
that the opposite space is finite-dimensional and free when the original space is.
-/

variable {R H : Type*}

namespace Basis

variable {ι : Type*} [Semiring R] [AddCommMonoid H] [Module R H]

/-- the mulOpposite of a basis: `b.mulOpposite i ↦ MulOpposite.op (b i)` -/
noncomputable def mulOpposite (b : Basis ι R H) : Basis ι R Hᵐᵒᵖ :=
  b.map (MulOpposite.opLinearEquiv R)

@[simp]
theorem mulOpposite_apply (b : Basis ι R H) (i : ι) :
    b.mulOpposite i = MulOpposite.op (b i) := rfl

theorem mulOpposite_repr_eq (b : Basis ι R H) :
    b.mulOpposite.repr = (MulOpposite.opLinearEquiv R).symm.trans b.repr := rfl

@[simp]
theorem mulOpposite_repr_unop (b : Basis ι R H) (x : Hᵐᵒᵖ) :
    b.repr (MulOpposite.unop x) = b.mulOpposite.repr x := rfl

@[simp]
theorem mulOpposite_repr_op (b : Basis ι R H) (x : H) :
    b.mulOpposite.repr (MulOpposite.op x) = b.repr x := rfl

end Basis

instance FiniteDimensional.mulOpposite [DivisionRing R] [AddCommGroup H] [Module R H]
    [FiniteDimensional R H] : FiniteDimensional R Hᵐᵒᵖ := FiniteDimensional.of_finite_basis
  (Basis.ofVectorSpace R H).mulOpposite
  (Basis.ofVectorSpaceIndex R H).toFinite

instance Module.Free.mulOpposite [Semiring R] [AddCommMonoid H] [Module R H]
    [Module.Free R H] : Module.Free R Hᵐᵒᵖ :=
  let ⟨b⟩ := exists_basis (R := R) (M := H)
  of_basis b.2.mulOpposite

theorem MulOpposite.finrank [DivisionRing R] [AddCommGroup H] [Module R H] :
    Module.finrank R Hᵐᵒᵖ = Module.finrank R H := by
  let b := Basis.ofVectorSpace R H
  rw [Module.finrank_eq_nat_card_basis b, Module.finrank_eq_nat_card_basis b.mulOpposite]

theorem MulOpposite.rank [Semiring R] [StrongRankCondition R] [AddCommMonoid H] [Module R H]
    [Module.Free R H] : Module.rank R Hᵐᵒᵖ = Module.rank R H :=
  LinearEquiv.nonempty_equiv_iff_rank_eq.mp ⟨(MulOpposite.opLinearEquiv R).symm⟩
