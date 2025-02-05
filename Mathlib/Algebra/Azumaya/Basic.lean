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

- `IsAzumaya.id`: `R` is an Azumaya algebra over itself.

- `IsAzumaya.ofAlgEquiv`: If `A` is an Azumaya algebra over `R` and `A` is isomorphic to `B`
  as an `R`-algebra, then `B` is an Azumaya algebra over `R`.

## Tags
Noncommutative algebra, Azumaya algebra, Brauer Group

-/

open scoped TensorProduct

open MulOpposite

namespace IsAzumaya

variable (R A B : Type*) [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

lemma AlgHom.mulLeftRight_bij [h : IsAzumaya R A] :
    Function.Bijective (AlgHom.mulLeftRight R A) := h.bij

/-- The "canonical" isomorphism between `R ⊗ Rᵒᵖ` and `End R R` which is equal
  to `AlgHom.mulLeftRight R R`. -/
noncomputable abbrev tensorEquivEnd : R ⊗[R] Rᵐᵒᵖ ≃ₐ[R] Module.End R R :=
  Algebra.TensorProduct.lid R Rᵐᵒᵖ|>.trans <|
  AlgEquiv.ofRingEquiv (f := Module.moduleEndSelf R) fun r ↦ by ext; simp

lemma coe_tensorEquivEnd: tensorEquivEnd R = AlgHom.mulLeftRight R R := by
  ext; simp

instance id : IsAzumaya R R where
  bij := by rw [← coe_tensorEquivEnd]; exact tensorEquivEnd R |>.bijective

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
lemma mulLeftRight_comp_congr (e : A ≃ₐ[R] B):
    (AlgHom.mulLeftRight R B).comp (Algebra.TensorProduct.congr e e.op).toAlgHom =
    (e.toLinearEquiv.algConj).toAlgHom.comp (AlgHom.mulLeftRight R A) := by
  apply AlgHom.ext
  intro a
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a a' =>
    ext; simp [AlgHom.mulLeftRight_apply, LinearEquiv.algConj, LinearEquiv.conj]
  | add _ _ _ _ => simp_all [map_add]

lemma _root_.FaithfulSMul.ofInjective {R M N : Type*} [SMul R M] [SMul R N]
    [Nonempty M] [FaithfulSMul R M] (f : @MulActionHom R R _root_.id M _ N _)
    (hf : Function.Injective f) :
    FaithfulSMul R N where
  eq_of_smul_eq_smul {r1 r2} h12 := by
    have : ∀ m : M, r1 • f m = r2 • f m := fun m ↦ h12 (f m)
    simp_rw [← map_smul] at this
    exact eq_of_smul_eq_smul <| fun m ↦ hf (this m)

theorem of_AlgEquiv (e : A ≃ₐ[R] B) [IsAzumaya R A] : IsAzumaya R B :=
  let _ : Module.Projective R B := .of_equiv e.toLinearEquiv
  let _ : FaithfulSMul R B := .ofInjective ⟨e, map_smul e⟩ e.injective
  let _ : Module.Finite R B := .equiv e.toLinearEquiv
  ⟨Function.Bijective.of_comp_iff (AlgHom.mulLeftRight R B)
    (Algebra.TensorProduct.congr e e.op).bijective |>.1 <| by
    erw [← AlgHom.coe_comp, mulLeftRight_comp_congr]
    simp [AlgHom.mulLeftRight_bij]⟩

end IsAzumaya
