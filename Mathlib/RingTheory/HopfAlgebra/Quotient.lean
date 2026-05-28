/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Quotient
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Hopf algebra structure on `RingQuot`

A relation `r : A → A → Prop` on an `R`-Hopf algebra `A` is a *Hopf relation* when it is a
bialgebra relation and the antipode identifies related elements after projection to `RingQuot r`.
The quotient `RingQuot r` then inherits a Hopf algebra structure.

## Main definitions

* `IsHopfRel R r` — Hopf descent condition on a generating relation.

## Main results

* `HopfAlgebra R (RingQuot r)` instance from `[IsHopfRel R r]`.
-/

@[expose] public section

open Bialgebra Coalgebra LinearMap RingQuot TensorProduct

variable {R A : Type*} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

variable (R) in
/-- A relation `r` on an `R`-Hopf algebra `A` is a *Hopf relation* if it is a bialgebra
relation and the antipode identifies related elements after projection to `RingQuot r`. -/
class IsHopfRel (r : A → A → Prop) : Prop extends IsBialgebraRel R r where
  antipode_map_eq : ∀ ⦃x y : A⦄, r x y →
    mkAlgHom R r (HopfAlgebra.antipode R x) = mkAlgHom R r (HopfAlgebra.antipode R y)

namespace HopfAlgebra.Quotient

variable (r : A → A → Prop) [IsHopfRel R r]

noncomputable instance : HopfAlgebraStruct R (RingQuot r) where
  antipode := (MulOpposite.opLinearEquiv R).symm.toLinearMap.comp
    (liftAlgHom R ⟨
      { toFun a := MulOpposite.op (mkAlgHom R r (HopfAlgebra.antipode R a))
        map_one' := by simp [HopfAlgebra.antipode_one]
        map_mul' a b := by simp [HopfAlgebra.antipode_mul, map_mul, MulOpposite.op_mul]
        map_zero' := by simp
        map_add' a b := by simp [map_add]
        commutes' x := by
          show MulOpposite.op (mkAlgHom R r (HopfAlgebra.antipode R (algebraMap R A x))) =
            algebraMap R (RingQuot r)ᵐᵒᵖ x
          rw [Algebra.algebraMap_eq_smul_one, map_smul, HopfAlgebra.antipode_one, map_smul,
            map_one, ← Algebra.algebraMap_eq_smul_one]
          rfl },
      fun _ _ h ↦ congrArg MulOpposite.op (IsHopfRel.antipode_map_eq h)⟩).toLinearMap

@[simp]
lemma antipode_mkAlgHom (a : A) :
    HopfAlgebra.antipode R (mkAlgHom R r a) =
      mkAlgHom R r (HopfAlgebra.antipode R a) := by
  simp [HopfAlgebra.antipode]

@[simp]
lemma antipode_comp_mkAlgHom :
    (HopfAlgebra.antipode R).comp (mkAlgHom R r).toLinearMap =
      (mkAlgHom R r).toLinearMap ∘ₗ HopfAlgebra.antipode R := by ext; simp

omit [IsHopfRel R r] in
@[simp]
private lemma mul'_map_mkAlgHom (z : A ⊗[R] A) :
    mul' R (RingQuot r) (map (mkAlgHom R r).toLinearMap (mkAlgHom R r).toLinearMap z) =
      mkAlgHom R r (mul' R A z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [mul'_apply]
  | add x y hx hy => simp [map_add, hx, hy]

noncomputable instance : HopfAlgebra R (RingQuot r) where
  mul_antipode_rTensor_comul := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨a, rfl⟩ := mkAlgHom_surjective R r x
    simp only [coe_comp, Function.comp_apply, Bialgebra.Quotient.comul_mkAlgHom,
      Bialgebra.Quotient.counit_mkAlgHom, rTensor_map, antipode_comp_mkAlgHom, ← map_rTensor,
      mul'_map_mkAlgHom, HopfAlgebra.mul_antipode_rTensor_comul_apply]
    simp
  mul_antipode_lTensor_comul := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨a, rfl⟩ := mkAlgHom_surjective R r x
    simp only [coe_comp, Function.comp_apply, Bialgebra.Quotient.comul_mkAlgHom,
      Bialgebra.Quotient.counit_mkAlgHom, lTensor_map, antipode_comp_mkAlgHom, ← map_lTensor,
      mul'_map_mkAlgHom, HopfAlgebra.mul_antipode_lTensor_comul_apply]
    simp

end HopfAlgebra.Quotient
