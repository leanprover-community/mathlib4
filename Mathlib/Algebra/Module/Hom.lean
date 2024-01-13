/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Module.Pi

#align_import algebra.module.hom from "leanprover-community/mathlib"@"134625f523e737f650a6ea7f0c82a6177e45e622"

/-!
# Bundled Hom instances for module and multiplicative actions

This file defines instances for `Module`, `MulAction` and related structures on bundled `Hom` types.

These are analogous to the instances in `Algebra.Module.Pi`, but for bundled instead of unbundled
functions.

We also define bundled versions of `(c • ·)` and `(· • ·)` as `AddMonoidHom.smulLeft` and
`AddMonoidHom.smul`, respectively.
-/

set_option autoImplicit true

variable {R S A B : Type*}

namespace AddMonoidHom

section

instance distribSMul [AddZeroClass A] [AddCommMonoid B] [DistribSMul M B] :
    DistribSMul M (A →+ B) where
  smul_add _ _ _ := ext fun _ => smul_add _ _ _

variable [Monoid R] [Monoid S] [AddMonoid A] [AddCommMonoid B]

variable [DistribMulAction R B] [DistribMulAction S B]

instance distribMulAction : DistribMulAction R (A →+ B) where
  smul_zero := smul_zero
  smul_add := smul_add
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _
#align add_monoid_hom.distrib_mul_action AddMonoidHom.distribMulAction

@[simp] theorem coe_smul (r : R) (f : A →+ B) : ⇑(r • f) = r • ⇑f := rfl
#align add_monoid_hom.coe_smul AddMonoidHom.coe_smul

theorem smul_apply (r : R) (f : A →+ B) (x : A) : (r • f) x = r • f x :=
  rfl
#align add_monoid_hom.smul_apply AddMonoidHom.smul_apply

instance smulCommClass [SMulCommClass R S B] : SMulCommClass R S (A →+ B) :=
  ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩
#align add_monoid_hom.smul_comm_class AddMonoidHom.smulCommClass

instance isScalarTower [SMul R S] [IsScalarTower R S B] : IsScalarTower R S (A →+ B) :=
  ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩
#align add_monoid_hom.is_scalar_tower AddMonoidHom.isScalarTower

instance isCentralScalar [DistribMulAction Rᵐᵒᵖ B] [IsCentralScalar R B] :
    IsCentralScalar R (A →+ B) :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩
#align add_monoid_hom.is_central_scalar AddMonoidHom.isCentralScalar

end

/-- Scalar multiplication on the left as an additive monoid homomorphism. -/
@[simps! (config := .asFn)]
protected def smulLeft [Monoid M] [AddMonoid A] [DistribMulAction M A] (c : M) : A →+ A :=
  DistribMulAction.toAddMonoidHom _ c

/-- Scalar multiplication as a biadditive monoid homomorphism. We need `M` to be commutative
to have addition on `M →+ M`. -/
protected def smul [Semiring R] [AddCommMonoid M] [Module R M] : R →+ M →+ M :=
  (Module.toAddMonoidEnd R M).toAddMonoidHom

@[simp] theorem coe_smul' [Semiring R] [AddCommMonoid M] [Module R M] :
    ⇑(.smul : R →+ M →+ M) = AddMonoidHom.smulLeft := rfl

instance module [Semiring R] [AddMonoid A] [AddCommMonoid B] [Module R B] : Module R (A →+ B) :=
  { add_smul := fun _ _ _=> ext fun _ => add_smul _ _ _
    zero_smul := fun _ => ext fun _ => zero_smul _ _ }
#align add_monoid_hom.module AddMonoidHom.module

end AddMonoidHom

/-- The tautological action by `AddMonoid.End α` on `α`.

This generalizes `AddMonoid.End.applyDistribMulAction`. -/
instance AddMonoid.End.applyModule [AddCommMonoid A] : Module (AddMonoid.End A) A where
  add_smul _ _ _ := rfl
  zero_smul _ := rfl
