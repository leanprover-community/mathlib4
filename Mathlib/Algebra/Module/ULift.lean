/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.GroupWithZero.ULift
import Mathlib.Algebra.Ring.ULift
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Data.ULift

/-!
# `ULift` instances for module and multiplicative actions

This file defines instances for module, mul_action and related structures on `ULift` types.

(Recall `ULift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `ULift.moduleEquiv : ULift M ≃ₗ[R] M`.
-/


namespace ULift

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}

@[to_additive]
instance smulLeft [SMul R M] : SMul (ULift R) M :=
  ⟨fun s x => s.down • x⟩

@[to_additive (attr := simp)]
theorem smul_def [SMul R M] (s : ULift R) (x : M) : s • x = s.down • x :=
  rfl

instance isScalarTower [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N] :
    IsScalarTower (ULift R) M N :=
  ⟨fun x y z => show (x.down • y) • z = x.down • y • z from smul_assoc _ _ _⟩

instance isScalarTower' [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N] :
    IsScalarTower R (ULift M) N :=
  ⟨fun x y z => show (x • y.down) • z = x • y.down • z from smul_assoc _ _ _⟩

instance isScalarTower'' [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N] :
    IsScalarTower R M (ULift N) :=
  ⟨fun x y z => show up ((x • y) • z.down) = ⟨x • y • z.down⟩ by rw [smul_assoc]⟩

instance [SMul R M] [SMul Rᵐᵒᵖ M] [IsCentralScalar R M] : IsCentralScalar R (ULift M) :=
  ⟨fun r m => congr_arg up <| op_smul_eq_smul r m.down⟩

@[to_additive]
instance mulAction [Monoid R] [MulAction R M] : MulAction (ULift R) M where
  mul_smul _ _ := mul_smul _ _
  one_smul := one_smul _

@[to_additive]
instance mulAction' [Monoid R] [MulAction R M] : MulAction R (ULift M) where
  mul_smul := fun _ _ _ => congr_arg ULift.up <| mul_smul _ _ _
  one_smul := fun _ => congr_arg ULift.up <| one_smul _ _

instance smulZeroClass [Zero M] [SMulZeroClass R M] : SMulZeroClass (ULift R) M :=
  { ULift.smulLeft with smul_zero := fun _ => smul_zero _ }

instance smulZeroClass' [Zero M] [SMulZeroClass R M] : SMulZeroClass R (ULift M) where
  smul_zero c := by { ext; simp [smul_zero] }

instance distribSMul [AddZeroClass M] [DistribSMul R M] : DistribSMul (ULift R) M where
  smul_add _ := smul_add _

instance distribSMul' [AddZeroClass M] [DistribSMul R M] : DistribSMul R (ULift M) where
  smul_add c f g := by
    ext
    simp [smul_add]

instance distribMulAction [Monoid R] [AddMonoid M] [DistribMulAction R M] :
    DistribMulAction (ULift R) M :=
  { ULift.mulAction, ULift.distribSMul with }

instance distribMulAction' [Monoid R] [AddMonoid M] [DistribMulAction R M] :
    DistribMulAction R (ULift M) :=
  { ULift.mulAction', ULift.distribSMul' with }

instance mulDistribMulAction [Monoid R] [Monoid M] [MulDistribMulAction R M] :
    MulDistribMulAction (ULift R) M where
  smul_one _ := smul_one _
  smul_mul _ := smul_mul' _

instance mulDistribMulAction' [Monoid R] [Monoid M] [MulDistribMulAction R M] :
    MulDistribMulAction R (ULift M) :=
  { ULift.mulAction' with
    smul_one := fun _ => by
      ext
      simp [smul_one]
    smul_mul := fun _ _ _ => by
      ext
      simp [smul_mul'] }

instance smulWithZero [Zero R] [Zero M] [SMulWithZero R M] : SMulWithZero (ULift R) M :=
  { ULift.smulLeft with
    smul_zero := fun _ => smul_zero _
    zero_smul := zero_smul _ }

instance smulWithZero' [Zero R] [Zero M] [SMulWithZero R M] : SMulWithZero R (ULift M) where
  smul_zero _ := ULift.ext _ _ <| smul_zero _
  zero_smul _ := ULift.ext _ _ <| zero_smul _ _

instance mulActionWithZero [MonoidWithZero R] [Zero M] [MulActionWithZero R M] :
    MulActionWithZero (ULift R) M :=
  { ULift.smulWithZero with
    one_smul := one_smul _
    mul_smul := mul_smul }

instance mulActionWithZero' [MonoidWithZero R] [Zero M] [MulActionWithZero R M] :
    MulActionWithZero R (ULift M) :=
  { ULift.smulWithZero' with
    one_smul := one_smul _
    mul_smul := mul_smul }

instance module [Semiring R] [AddCommMonoid M] [Module R M] : Module (ULift R) M :=
  { ULift.smulWithZero with
    add_smul := fun _ _ => add_smul _ _
    smul_add := smul_add
    one_smul := one_smul _
    mul_smul := mul_smul }

instance module' [Semiring R] [AddCommMonoid M] [Module R M] : Module R (ULift M) :=
  { ULift.smulWithZero' with
    add_smul := fun _ _ _ => ULift.ext _ _ <| add_smul _ _ _
    one_smul := one_smul _
    mul_smul := mul_smul
    smul_add := smul_add }

/-- The `R`-linear equivalence between `ULift M` and `M`.

This is a linear version of `AddEquiv.ulift`. -/
@[simps apply symm_apply]
def moduleEquiv [Semiring R] [AddCommMonoid M] [Module R M] : ULift.{w} M ≃ₗ[R] M where
  toFun := ULift.down
  invFun := ULift.up
  map_smul' _ _ := rfl
  __ := AddEquiv.ulift

end ULift
