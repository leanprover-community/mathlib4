/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
import Mathlib.Algebra.Azumaya.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Basic properties of Azumaya algebras

In this file we prove basic facts about Azumaya algebras such as `R` is an Azumaya algebra
over itself where `R` is a commutative ring.

## Main Results

- `IsAzumaya.Self`: `R` is an Azumaya algebra over itself.

- `IsAzumaya.ofAlgEquiv`: If `A` is an Azumaya algebra over `R` and `A` is isomorphic to `B`
  as an `R`-algebra, then `B` is an Azumaya algebra over `R`.

## Tags
Noncommutative algebra, Azumaya algebra, Brauer Group

-/

open scoped TensorProduct

open MulOpposite

namespace IsAzumaya

variable (R A B : Type*) [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/-- The "canonical" isomorphism between `R ⊗ Rᵒᵖ` and `End R R` which is equal
  to `AlgHom.mulLeftRight R R`. -/
noncomputable abbrev tensorEquivEnd : R ⊗[R] Rᵐᵒᵖ ≃ₐ[R] Module.End R R :=
  Algebra.TensorProduct.lid R Rᵐᵒᵖ|>.trans <|
  AlgEquiv.ofRingEquiv (f := Module.moduleEndSelf R) fun r ↦ by ext; simp

lemma tensorEquivEnd_eq_mulLeftRight: tensorEquivEnd R = AlgHom.mulLeftRight R R := by
  ext; simp

instance self : IsAzumaya R R where
  bij := by rw [← tensorEquivEnd_eq_mulLeftRight]; exact tensorEquivEnd R |>.bijective

/--
The following diagram commutes:
```
          e ⊗ eᵒᵖ
A ⊗ Aᵐᵒᵖ  ------------> B ⊗ Bᵐᵒᵖ
  |                        |
  |                        |
  | mulLeftRight R A       | mulLeftRight R B
  |                        |
  V                        V
End R A   ------------> End R B
          e.conj
```
-/
lemma small_comm_square (e : A ≃ₐ[R] B):
    (AlgHom.mulLeftRight R B).comp (Algebra.TensorProduct.congr e e.op).toAlgHom =
    (e.toLinearEquiv.algConj).toAlgHom.comp (AlgHom.mulLeftRight R A) := by
  apply AlgHom.ext
  intro a
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a a' =>
    ext; simp [AlgHom.mulLeftRight_apply, LinearEquiv.algConj, LinearEquiv.conj]
  | add _ _ _ _ => simp_all [map_add]

variable {R A B} in
lemma _root_.FaithfulSMul.ofAlgEquiv [FaithfulSMul R A] (e : A ≃ₐ[R] B) :
    FaithfulSMul R B where
  eq_of_smul_eq_smul {r1 r2} h12 := by
    specialize h12 1
    rw [← e.apply_symm_apply 1, ← map_smul, map_one e.symm, ← map_smul] at h12
    have : ∀ (a : A), r1 • a = r2 • a := fun a ↦ by
      rw [← one_mul a, ← smul_mul_assoc, e.injective h12, smul_mul_assoc]
    exact eq_of_smul_eq_smul this

theorem ofAlgEquiv (e : A ≃ₐ[R] B) (hA : IsAzumaya R A) : IsAzumaya R B :=
  let _ : Module.Projective R B := .of_equiv e.toLinearEquiv
  let _ : FaithfulSMul R B := .ofAlgEquiv e
  let _ : Module.Finite R B := .equiv e.toLinearEquiv
  ⟨Function.Bijective.of_comp_iff (AlgHom.mulLeftRight R B)
    (Algebra.TensorProduct.congr e e.op).bijective |>.1 <| by
    erw [← AlgHom.coe_comp, small_comm_square]
    simp [hA.bij]⟩

end IsAzumaya
