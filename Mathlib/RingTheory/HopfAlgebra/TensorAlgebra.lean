/-
Copyright (c) 2025 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/
module

public import Mathlib.RingTheory.Bialgebra.TensorAlgebra
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Hopf algebra structure on `TensorAlgebra R M`

In this file we implement the natura Hopf algebra structure on `TensorAlgebra R M`.
The comultiplication is the unique algebra map satisfying `comul ((ι R) x) = (ι R) x ⊗ 1 + 1 ⊗ (ι R)
x` for all `x : M`.
`algebraMapInv` acts as the counit, and the antipode is the unique algebra map `antipode :
TensorAlgebra R M → (TensorAlgebra R M)ᵐᵒᵖ` induced by `fun x => op -(ι R) x`.
-/
@[expose] public section

namespace TensorAlgebra

open scoped RingTheory.LinearMap
open LinearMap TensorProduct

variable (R : Type*) [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

local notation "T[" M "]" => TensorAlgebra R M

/-- Antipode in `TensorAlgebra R M` as a linear map. -/
def antipode : T[M] →ₗ[R] T[M] := (MulOpposite.opLinearEquiv R).symm.comp
  (lift R <| (MulOpposite.opLinearEquiv R).comp <| -ι R).toLinearMap

@[simp]
lemma antipode_ι_apply (x : M) : antipode R (ι R x) = -ι R x := by
  simp [antipode]

@[simp]
theorem antipode_antihom_apply (x y : T[M]) : antipode R (x * y) = antipode R y * antipode R x := by
  simp [antipode]

@[simp]
theorem antipode_antihom : antipode R ∘ₗ mul' R T[M] =
    mul' R T[M] ∘ₗ TensorProduct.comm R T[M] T[M] ∘ₗ (antipode R ⊗ₘ antipode R) := by
  ext
  simp

@[simp]
lemma antipode_algebraMap_apply (r : R) :
    antipode R (algebraMap R T[M] r) = algebraMap R T[M] r := by
  simp [antipode]

open Algebra Bialgebra Coalgebra in
instance instHopfAlgebra : HopfAlgebra R T[M] where
  antipode := antipode R
  mul_antipode_rTensor_comul := by
    rw [LinearMap.rTensor]
    ext x
    induction x using induction with
    | algebraMap r => simp
    | add u v hu hv => rw [map_add, hu, hv, ← map_add]
    | ι u =>
        conv =>
          rhs
          rw [comp_apply, CoalgebraStruct.counit, instBialgebra, toCoalgebraStruct,
            toCoalgebra, ofAlgHom, mk', coe_coe, algebraMapInv_ι_apply, map_zero]
        conv =>
          lhs
          rw [CoalgebraStruct.comul, toCoalgebraStruct, toCoalgebra]
          unfold instBialgebra ofAlgHom mk'
          simp only [coe_semilinearMap, comp_apply, comul_apply, map_add, map_tmul,
            antipode_ι_apply, id_coe, id_eq, mul'_apply, mul_one]
          rw [← map_one (algebraMap R _), antipode_algebraMap_apply]
          simp
    | mul u v hu hv =>
        conv =>
          rhs
          rw [comp_apply, counit_mul]
        have assoc4 {Q} [Semiring Q] (a b c d : Q) : a * b * (c * d) = a * (b * c) * d := by
          rw [← mul_assoc, mul_assoc a b c]
        rw [comp_apply, comp_apply, comul_mul, ← Coalgebra.Repr.eq (ℛ R u),
          ← Coalgebra.Repr.eq (ℛ R v), Finset.sum_mul_sum, map_sum, map_sum] at *
        simp only [TensorProduct.tmul_mul_tmul, map_sum, map_tmul, antipode_antihom_apply, id_coe,
        id_eq, mul'_apply] at *
        conv =>
          lhs
          conv =>
            arg 2
            intro i
            conv =>
              arg 2
              intro j
              rw [assoc4]
        rw [Finset.sum_comm]
        conv =>
          lhs
          conv =>
            arg 2
            intro i
            rw [← Finset.sum_mul, ← Finset.mul_sum, hu, comp_apply, linearMap_apply,
              ← commutes, mul_assoc]
          rw [← Finset.mul_sum, hv, comp_apply, linearMap_apply, ← map_mul, ← linearMap_apply]
  mul_antipode_lTensor_comul := by
    rw [LinearMap.lTensor]
    ext x
    induction x using induction with
    | algebraMap r =>
        simp only [comp_apply, comul_algebraMap, TensorProduct.algebraMap_apply, map_tmul,
          id_coe, id_eq, mul'_apply, counit_algebraMap, ← map_one (algebraMap R
          T[M]), antipode_algebraMap_apply]
        simp
    | add u v hu hv => rw [map_add, hu, hv, ← map_add]
    | ι u =>
        conv =>
          rhs
          rw [comp_apply, CoalgebraStruct.counit, instBialgebra, toCoalgebraStruct,
            toCoalgebra, ofAlgHom, mk', coe_coe, algebraMapInv_ι_apply, map_zero]
        conv =>
          lhs
          rw [CoalgebraStruct.comul, toCoalgebraStruct, toCoalgebra]
          unfold instBialgebra ofAlgHom mk'
          simp only [coe_coe, comul_apply, map_add, map_tmul, antipode_ι_apply, id_coe, id_eq,
            mul'_apply, mul_one, ← map_one (algebraMap R T[M]), antipode_algebraMap_apply,
            coe_semilinearMap, comp_apply]
          rw [map_one, one_mul, mul_one, add_neg_cancel]
    | mul u v hu hv =>
        conv =>
          rhs
          rw [comp_apply, counit_mul]
        have assoc4 {Q} [Semiring Q] (a b c d : Q) : a * b * (c * d) = a * (b * c) * d := by
          rw [← mul_assoc, mul_assoc a b c]
        rw [comp_apply, comp_apply, comul_mul, ← Coalgebra.Repr.eq (ℛ R u),
          ← Coalgebra.Repr.eq (ℛ R v), Finset.sum_mul_sum, map_sum, map_sum] at *
        simp only [TensorProduct.tmul_mul_tmul, map_sum, map_tmul, antipode_antihom_apply, id_coe,
        id_eq, mul'_apply] at *
        conv =>
          lhs
          conv =>
            arg 2
            intro i
            conv =>
              arg 2
              intro j
              rw [assoc4]
        conv =>
          lhs
          conv =>
            arg 2
            intro i
            rw [← Finset.sum_mul, ← Finset.mul_sum, hv, comp_apply, linearMap_apply,
              ← Algebra.commutes, mul_assoc]
          rw [← Finset.mul_sum, hu, comp_apply, linearMap_apply, commutes, ← map_mul,
            ← linearMap_apply]

end TensorAlgebra
