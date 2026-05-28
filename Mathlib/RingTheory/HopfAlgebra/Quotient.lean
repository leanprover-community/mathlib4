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

When a relation `r : A → A → Prop` on an `R`-Hopf algebra `A` is compatible with the counit and
comultiplication (`IsBialgebraRel`) and the antipode also descends along `RingQuot.mkAlgHom R r`,
the quotient `RingQuot r` inherits a Hopf algebra structure.

## Main definitions

* `IsHopfRel R r` — `IsBialgebraRel R r` together with descent of the antipode.

## Main results

* `HopfAlgebra R (RingQuot r)` instance from `[IsHopfRel R r]`.
-/

@[expose] public section

open Bialgebra Coalgebra LinearMap RingQuot TensorProduct

variable {R A : Type*} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

variable (R) in
/-- `IsBialgebraRel R r` together with descent of the antipode along `RingQuot.mkAlgHom R r`. -/
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

noncomputable instance : HopfAlgebra R (RingQuot r) where
  mul_antipode_rTensor_comul := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨a, rfl⟩ := mkAlgHom_surjective R r x
    convert! congr(mkAlgHom R r $(mul_antipode_rTensor_comul_apply (R := R) a)) using 1
    · simp only [coe_comp, Function.comp_apply, Bialgebra.Quotient.comul_mkAlgHom,
        rTensor_map, antipode_comp_mkAlgHom, ← map_rTensor]
      exact (LinearMap.congr_fun (AlgHom.comp_mul' (mkAlgHom R r)) _).symm
    · simp [Bialgebra.Quotient.counit_mkAlgHom]
  mul_antipode_lTensor_comul := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨a, rfl⟩ := mkAlgHom_surjective R r x
    convert! congr(mkAlgHom R r $(mul_antipode_lTensor_comul_apply (R := R) a)) using 1
    · simp only [coe_comp, Function.comp_apply, Bialgebra.Quotient.comul_mkAlgHom,
        lTensor_map, antipode_comp_mkAlgHom, ← map_lTensor]
      exact (LinearMap.congr_fun (AlgHom.comp_mul' (mkAlgHom R r)) _).symm
    · simp [Bialgebra.Quotient.counit_mkAlgHom]

end HopfAlgebra.Quotient
