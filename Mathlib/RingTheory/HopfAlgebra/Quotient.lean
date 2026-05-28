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

## Implementation notes

The antipode is an antihomomorphism, so lifting it through `RingQuot.liftAlgHom` routes through
`(RingQuot r)ᵐᵒᵖ`. Specifically, `a ↦ op (mkAlgHom R r (antipode a))` is an algebra hom
`A →ₐ[R] (RingQuot r)ᵐᵒᵖ` because the two antihomomorphisms compose to a homomorphism.
-/

@[expose] public section

open Bialgebra Coalgebra LinearMap RingQuot TensorProduct

variable {R A : Type*} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

variable (R) in
/-- A relation `r` on an `R`-Hopf algebra `A` is a *Hopf relation* if it is a bialgebra
relation and the antipode identifies related elements after projection to `RingQuot r`. -/
class IsHopfRel (r : A → A → Prop) : Prop extends IsBialgebraRel R r where
  antipode_map_eq : ∀ ⦃x y : A⦄, r x y →
    (mkAlgHom R r).toLinearMap (HopfAlgebra.antipode R x) =
      (mkAlgHom R r).toLinearMap (HopfAlgebra.antipode R y)

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
    HopfAlgebraStruct.antipode (A := RingQuot r) R (mkAlgHom R r a) =
      mkAlgHom R r (HopfAlgebra.antipode R a) := by
  simp [HopfAlgebraStruct.antipode]

@[simp]
lemma antipode_comp_mkAlgHom :
    (HopfAlgebraStruct.antipode (A := RingQuot r) R).comp (mkAlgHom R r).toLinearMap =
      (mkAlgHom R r).toLinearMap ∘ₗ HopfAlgebra.antipode R := by
  ext a; simp

omit [IsHopfRel R r] in
private lemma mul'_comp_map_mkAlgHom :
    mul' R (RingQuot r) ∘ₗ TensorProduct.map (mkAlgHom R r).toLinearMap
        (mkAlgHom R r).toLinearMap =
      (mkAlgHom R r).toLinearMap ∘ₗ mul' R A :=
  TensorProduct.ext (by ext; simp [mul'_apply])

private lemma antipode_rTensor_comp_map_mkAlgHom :
    (HopfAlgebraStruct.antipode (A := RingQuot r) R).rTensor (RingQuot r) ∘ₗ
      TensorProduct.map (mkAlgHom R r).toLinearMap (mkAlgHom R r).toLinearMap =
    TensorProduct.map (mkAlgHom R r).toLinearMap (mkAlgHom R r).toLinearMap ∘ₗ
        (HopfAlgebra.antipode R).rTensor A := by
  rw [rTensor, rTensor, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    antipode_comp_mkAlgHom, id_comp, comp_id]

private lemma antipode_lTensor_comp_map_mkAlgHom :
    (HopfAlgebraStruct.antipode (A := RingQuot r) R).lTensor (RingQuot r) ∘ₗ
      TensorProduct.map (mkAlgHom R r).toLinearMap (mkAlgHom R r).toLinearMap =
    TensorProduct.map (mkAlgHom R r).toLinearMap (mkAlgHom R r).toLinearMap ∘ₗ
        (HopfAlgebra.antipode R).lTensor A := by
  rw [lTensor, lTensor, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    antipode_comp_mkAlgHom, id_comp, comp_id]

noncomputable instance : HopfAlgebra R (RingQuot r) where
  mul_antipode_rTensor_comul := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨a, rfl⟩ := mkAlgHom_surjective R r x
    have hpush := LinearMap.congr_fun (antipode_rTensor_comp_map_mkAlgHom (R := R) r) (comul a)
    have hmul := LinearMap.congr_fun (mul'_comp_map_mkAlgHom (R := R) r)
      ((HopfAlgebra.antipode R).rTensor A (comul a))
    simp only [coe_comp, Function.comp_apply, Bialgebra.Quotient.comul_mkAlgHom,
      Bialgebra.Quotient.counit_mkAlgHom] at *
    rw [hpush, hmul, HopfAlgebra.mul_antipode_rTensor_comul_apply]
    simp
  mul_antipode_lTensor_comul := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨a, rfl⟩ := mkAlgHom_surjective R r x
    have hpush := LinearMap.congr_fun (antipode_lTensor_comp_map_mkAlgHom (R := R) r) (comul a)
    have hmul := LinearMap.congr_fun (mul'_comp_map_mkAlgHom (R := R) r)
      ((HopfAlgebra.antipode R).lTensor A (comul a))
    simp only [coe_comp, Function.comp_apply, Bialgebra.Quotient.comul_mkAlgHom,
      Bialgebra.Quotient.counit_mkAlgHom] at *
    rw [hpush, hmul, HopfAlgebra.mul_antipode_lTensor_comul_apply]
    simp

end HopfAlgebra.Quotient
