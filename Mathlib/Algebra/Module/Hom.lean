/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.module.hom
! leanprover-community/mathlib commit 134625f523e737f650a6ea7f0c82a6177e45e622
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Module.Pi

/-!
# Bundled Hom instances for module and multiplicative actions

This file defines instances for `Module`, `MulAction` and related structures on bundled `Hom` types.

These are analogous to the instances in `Algebra.Module.Pi`, but for bundled instead of unbundled
functions.

We also define bundled versions of `(c • ·)` and `(· • ·)` as `AddMonoidHom.smulLeft` and
`AddMonoidHom.smul`, respectively.
-/

variable {R S A B : Type _}

namespace AddMonoidHom

section

variable [Monoid R] [Monoid S] [AddMonoid A] [AddCommMonoid B]

variable [DistribMulAction R B] [DistribMulAction S B]

instance distribMulAction : DistribMulAction R (A →+ B) where
  smul r f :=
    { toFun := (fun a => r • (f a))
      map_zero' := by simp only [map_zero, smul_zero]
      map_add' := fun x y => by simp only [map_add, smul_add] }
  one_smul f := ext fun _ => MulAction.one_smul _
  mul_smul r s f := ext fun _ => MulAction.mul_smul _ _ _
  smul_add r f g := ext fun _ => smul_add _ _ _
  smul_zero r := ext fun _ => smul_zero _
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
@[simps (config := .asFn)]
protected def smulLeft [Monoid M] [AddMonoid A] [DistribMulAction M A] (c : M) : A →+ A where
  toFun := (c • ·)
  map_zero' := smul_zero c
  map_add' := smul_add c

/-- Scalar multiplication as a biadditive monoid homomorphism. We need `M` to be commutative
to have addition on `M →+ M`. -/
protected def smul [Semiring R] [AddCommMonoid M] [Module R M] : R →+ M →+ M where
  toFun := .smulLeft
  map_zero' := AddMonoidHom.ext <| zero_smul _
  map_add' _ _ := AddMonoidHom.ext <| add_smul _ _

@[simp] theorem coe_smul' [Semiring R] [AddCommMonoid M] [Module R M] :
    ⇑(.smul : R →+ M →+ M) = AddMonoidHom.smulLeft := rfl

instance module [Semiring R] [AddMonoid A] [AddCommMonoid B] [Module R B] : Module R (A →+ B) :=
  { add_smul := fun _ _ _=> ext fun _ => add_smul _ _ _
    zero_smul := fun _ => ext fun _ => zero_smul _ _ }
#align add_monoid_hom.module AddMonoidHom.module

end AddMonoidHom
