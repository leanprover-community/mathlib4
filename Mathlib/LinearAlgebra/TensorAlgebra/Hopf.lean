/-
Copyright (c) 2025 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.Basic
public import Mathlib.RingTheory.Coalgebra.Convolution
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
open scoped TensorProduct RingTheory.LinearMap Coalgebra
open LinearMap TensorProduct

section Bialgebra

variable (R : Type*) [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]

local notation "T[" M "]" => TensorAlgebra R M

/-- Comultiplication in `TensorAlgebra R M` as an algebra map.
It is induced by the linear map sending `(m : M)` to `ι R m ⊗ₜ[R] 1 + 1 ⊗ₜ[R] ι R m`.
See `comul_apply`.
-/
def comul : T[M] →ₐ[R] T[M] ⊗[R] T[M] := lift R (
  (ι R ⊗ₘ Algebra.linearMap R T[M]) ∘ₗ (TensorProduct.rid R M).symm +
  (Algebra.linearMap R T[M] ⊗ₘ ι R) ∘ₗ (TensorProduct.lid R M).symm
  )

@[simp]
lemma comul_apply (m : M) : comul R (ι R m) = ι R m ⊗ₜ[R] 1 + 1 ⊗ₜ[R] ι R m := by
  simp [comul]

@[simp]
lemma algebraMapInv_ι_apply (m : M) : algebraMapInv (ι R m) = 0 := by
  simp [algebraMapInv]

@[simp]
lemma algebraMapInv_ι_eq_zero : algebraMapInv.toLinearMap ∘ₗ (ι R) = (0 : M →ₗ[R] R) :=
  LinearMap.ext <| algebraMapInv_ι_apply _

instance instBialgebra : Bialgebra R T[M] := Bialgebra.ofAlgHom (comul R) algebraMapInv
    (by ext; simpa [comul, Algebra.TensorProduct.one_def, add_tmul, tmul_add] using by abel)
    (by ext; simp [comul, algebraMapInv])
    (by ext; simp [comul, algebraMapInv])

end Bialgebra

section HopfAlgebra

variable (R : Type*) [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

local notation "T[" M "]" => TensorAlgebra R M

/-- Antipode in `TensorAlgebra R M` as an algebra map. -/
def antipode : T[M] →ₗ[R] T[M] := (MulOpposite.opLinearEquiv R).symm.comp
  (lift R ((MulOpposite.opLinearEquiv R).comp (-(ι R)))).toLinearMap

@[simp]
lemma antipode_ι_apply (x : M) : antipode R (ι R x) = -(ι R) x := by
  simp [antipode]

@[simp]
theorem antipode_antihom_apply (x y : T[M]) : antipode R (x * y) = antipode R y * antipode R x := by
  simp [antipode]

@[simp]
theorem antipode_antihom : antipode R ∘ₗ mul' R T[M] =
    mul' R T[M] ∘ₗ TensorProduct.comm R T[M] T[M] ∘ₗ ((antipode R) ⊗ₘ (antipode R)) := by
  ext
  simp

@[simp]
lemma antipode_algebraMap_apply (r : R) :
    antipode R ((algebraMap R T[M]) r) = algebraMap R T[M] r := by
  simp [antipode]

open Algebra Bialgebra Coalgebra in
instance instHopfAlgebra : HopfAlgebra R T[M] where
  antipode := antipode R
  mul_antipode_rTensor_comul := by
    rw [LinearMap.rTensor, ← LinearMap.convMul_def, ← convOne_def]
    ext x
    induction x using induction with
    | algebraMap r => simp
    | add u v hu hv => rw [map_add, hu, hv, ← map_add]
    | ι u =>
        conv =>
          rhs
          rw [convOne_def, comp_apply, CoalgebraStruct.counit, instBialgebra, toCoalgebraStruct,
            toCoalgebra, ofAlgHom, mk', coe_coe, algebraMapInv_ι_apply, map_zero]
        conv =>
          lhs
          rw [convMul_apply, CoalgebraStruct.comul, toCoalgebraStruct, toCoalgebra]
          unfold instBialgebra ofAlgHom mk'
          simp only [coe_coe, comul_apply, map_add, map_tmul, antipode_ι_apply, id_coe, id_eq,
            mul'_apply, mul_one, ← map_one (algebraMap R T[M]), antipode_algebraMap_apply]
          simp only [map_one, mul_one, one_mul, neg_add_cancel]
    | mul u v hu hv =>
        conv =>
          rhs
          rw [convOne_apply, counit_mul, map_mul, ← convOne_apply, ← convOne_apply]
        have assoc4 {Q} [Semiring Q] (a b c d : Q) : a * b * (c * d) = a * (b * c) * d := by
          rw [← mul_assoc, mul_assoc a b c]
        rw [convMul_apply, comul_mul, ← Coalgebra.Repr.eq (ℛ R u), ← Coalgebra.Repr.eq (ℛ R v),
          Finset.sum_mul_sum, map_sum, map_sum] at *
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
            rw [← Finset.sum_mul, ← Finset.mul_sum, hu, convOne_apply,
            ← Algebra.commutes, mul_assoc]
          rw [← Finset.mul_sum, hv, ← convOne_apply]
  mul_antipode_lTensor_comul := by
    rw [LinearMap.lTensor, ← LinearMap.convMul_def, ← convOne_def]
    ext x
    induction x using induction with
    | algebraMap r =>
        simp only [convMul_apply, comul_algebraMap, TensorProduct.algebraMap_apply, map_tmul,
          id_coe, id_eq, mul'_apply, convOne_apply, counit_algebraMap, ← map_one (algebraMap R
          T[M]), antipode_algebraMap_apply]
        simp
    | add u v hu hv => rw [map_add, hu, hv, ← map_add]
    | ι u =>
        conv =>
          rhs
          rw [convOne_def, comp_apply, CoalgebraStruct.counit, instBialgebra, toCoalgebraStruct,
            toCoalgebra, ofAlgHom, mk', coe_coe, algebraMapInv_ι_apply, map_zero]
        conv =>
          lhs
          rw [convMul_apply, CoalgebraStruct.comul, toCoalgebraStruct, toCoalgebra]
          unfold instBialgebra ofAlgHom mk'
          simp only [coe_coe, comul_apply, map_add, map_tmul, antipode_ι_apply, id_coe, id_eq,
            mul'_apply, mul_one, ← map_one (algebraMap R T[M]), antipode_algebraMap_apply]
          simp only [map_one, mul_one, one_mul, neg_add_cancel]
          abel_nf
    | mul u v hu hv =>
        conv =>
          rhs
          rw [convOne_apply, counit_mul, map_mul, Algebra.commutes, ← convOne_apply,
            ← convOne_apply]
        have assoc4 {Q} [Semiring Q] (a b c d : Q) : a * b * (c * d) = a * (b * c) * d := by
          rw [← mul_assoc, mul_assoc a b c]
        rw [convMul_apply, comul_mul, ← Coalgebra.Repr.eq (ℛ R u), ← Coalgebra.Repr.eq (ℛ R v),
          Finset.sum_mul_sum, map_sum, map_sum] at *
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
            rw [← Finset.sum_mul, ← Finset.mul_sum, hv, convOne_apply,
            ← Algebra.commutes, mul_assoc]
          rw [← Finset.mul_sum, hu, ← convOne_apply]

end HopfAlgebra

end TensorAlgebra
