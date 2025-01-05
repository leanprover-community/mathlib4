/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie
-/
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Definition of Azumaya Algebras

reference : Wikipedia, Noncommutative Algebra
-/

variable (R A : Type*) [CommRing R] [Ring A] [Algebra R A]

open TensorProduct MulOpposite

@[simps]
private abbrev moptoendo : A → Aᵐᵒᵖ →ₗ[R] Module.End R A :=
  fun a ↦ {
    toFun := fun b ↦ {
      toFun := fun x ↦ a * x * unop b,
      map_add' := fun _ _ ↦ by simp [mul_add, add_mul],
      map_smul' := fun _ _ ↦ by simp
    }
    map_add' := fun _ _ ↦ by ext; simp [mul_add]
    map_smul' := fun _ _ ↦ by ext; simp
  }

noncomputable abbrev endo : (A ⊗[R] Aᵐᵒᵖ) →ₐ[R] Module.End R A where
  toFun := TensorProduct.lift (R := R) (M := A) (N := Aᵐᵒᵖ) (P := Module.End R A)
    { toFun := moptoendo R A,
      map_add' := fun _ _ ↦ by ext; simp [add_mul]
      map_smul' := fun _ _ ↦ by ext; simp }
  map_one' := by ext; simp [Algebra.TensorProduct.one_def]
  map_mul' := fun x y ↦ by
    induction x using TensorProduct.induction_on with
    | zero =>
      simp
    | tmul x1 x2 =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul y1 y2 =>
        ext; simp [mul_assoc]
      | add y11 y22 h11 h22 =>
        simp_all [mul_add]
    | add x11 x22 h11 h22 =>
      simp_all [add_mul]
  map_zero' := rfl
  map_add' := map_add _
  commutes' := fun r ↦ by
    dsimp
    ext a
    simp [Algebra.algebraMap_eq_smul_one]

class IsAzumaya extends Module.Projective R A, FaithfulSMul R A : Prop where
    fg : Module.Finite R A
    bij : Function.Bijective <| endo R A
