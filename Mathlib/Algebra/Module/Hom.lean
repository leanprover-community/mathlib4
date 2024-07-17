/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.GroupTheory.GroupAction.DomAct.Basic

#align_import algebra.module.hom from "leanprover-community/mathlib"@"134625f523e737f650a6ea7f0c82a6177e45e622"

/-!
# Bundled Hom instances for module and multiplicative actions

This file defines instances for `Module`, `MulAction` and related structures on bundled `Hom` types.

These are analogous to the instances in `Algebra.Module.Pi`, but for bundled instead of unbundled
functions.

We also define bundled versions of `(c • ·)` and `(· • ·)` as `AddMonoidHom.smulLeft` and
`AddMonoidHom.smul`, respectively.
-/

variable {R S M A B : Type*}

/-! ### Instances for `AddMonoidHom` -/

namespace AddMonoidHom

section

instance instDistribSMul [AddZeroClass A] [AddCommMonoid B] [DistribSMul M B] :
    DistribSMul M (A →+ B) where
  smul_add _ _ _ := ext fun _ => smul_add _ _ _

variable [Monoid R] [Monoid S] [AddMonoid A] [AddCommMonoid B]
variable [DistribMulAction R B] [DistribMulAction S B]

instance instDistribMulAction : DistribMulAction R (A →+ B) where
  smul_zero := smul_zero
  smul_add := smul_add
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _
#align add_monoid_hom.distrib_mul_action AddMonoidHom.instDistribMulAction

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

instance instModule [Semiring R] [AddMonoid A] [AddCommMonoid B] [Module R B] : Module R (A →+ B) :=
  { add_smul := fun _ _ _=> ext fun _ => add_smul _ _ _
    zero_smul := fun _ => ext fun _ => zero_smul _ _ }
#align add_monoid_hom.module AddMonoidHom.instModule

instance instDomMulActModule
    {S M M₂ : Type*} [Semiring S] [AddCommMonoid M] [AddCommMonoid M₂] [Module S M] :
    Module Sᵈᵐᵃ (M →+ M₂) where
  add_smul s s' f := AddMonoidHom.ext fun m ↦ by
    simp_rw [AddMonoidHom.add_apply, DomMulAct.smul_addMonoidHom_apply, ← map_add, ← add_smul]; rfl
  zero_smul _ := AddMonoidHom.ext fun _ ↦ by
    erw [DomMulAct.smul_addMonoidHom_apply, zero_smul, map_zero]; rfl

end AddMonoidHom

/-!
### Instances for `AddMonoid.End`

These are direct copies of the instances above.
-/

namespace AddMonoid.End

section

variable [Monoid R] [Monoid S] [AddCommMonoid A]

instance instDistribSMul [DistribSMul M A] : DistribSMul M (AddMonoid.End A) :=
  AddMonoidHom.instDistribSMul

variable [DistribMulAction R A] [DistribMulAction S A]

instance instDistribMulAction : DistribMulAction R (AddMonoid.End A) :=
  AddMonoidHom.instDistribMulAction

@[simp] theorem coe_smul (r : R) (f : AddMonoid.End A) : ⇑(r • f) = r • ⇑f := rfl

theorem smul_apply (r : R) (f : AddMonoid.End A) (x : A) : (r • f) x = r • f x :=
  rfl

instance smulCommClass [SMulCommClass R S A] : SMulCommClass R S (AddMonoid.End A) :=
  AddMonoidHom.smulCommClass

instance isScalarTower [SMul R S] [IsScalarTower R S A] : IsScalarTower R S (AddMonoid.End A) :=
  AddMonoidHom.isScalarTower

instance isCentralScalar [DistribMulAction Rᵐᵒᵖ A] [IsCentralScalar R A] :
    IsCentralScalar R (AddMonoid.End A) :=
  AddMonoidHom.isCentralScalar

end

instance instModule [Semiring R] [AddCommMonoid A] [Module R A] : Module R (AddMonoid.End A) :=
  AddMonoidHom.instModule

/-- The tautological action by `AddMonoid.End α` on `α`.

This generalizes `AddMonoid.End.applyDistribMulAction`. -/
instance applyModule [AddCommMonoid A] : Module (AddMonoid.End A) A where
  add_smul _ _ _ := rfl
  zero_smul _ := rfl

end AddMonoid.End

/-! ### Miscelaneous morphisms -/

namespace AddMonoidHom

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

end AddMonoidHom
