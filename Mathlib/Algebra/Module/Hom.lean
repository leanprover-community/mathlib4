/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Algebra.GroupWithZero.Action.End
import Mathlib.Algebra.GroupWithZero.Action.Hom
import Mathlib.Algebra.Module.End
import Mathlib.Algebra.Ring.Opposite
import Mathlib.GroupTheory.GroupAction.DomAct.Basic

/-!
# Bundled Hom instances for module and multiplicative actions

This file defines instances for `Module` on bundled `Hom` types.

These are analogous to the instances in `Algebra.Module.Pi`, but for bundled instead of unbundled
functions.

We also define bundled versions of `(c • ·)` and `(· • ·)` as `AddMonoidHom.smulLeft` and
`AddMonoidHom.smul`, respectively.
-/

variable {R S M A B : Type*}

namespace ZeroHom

instance instModule [Semiring R] [AddMonoid A] [AddCommMonoid B] [Module R B] :
    Module R (ZeroHom A B) where
  __ : MulActionWithZero _ _ := ZeroHom.instMulActionWithZero
  add_smul _ _ _ := ext fun _ => add_smul _ _ _
  smul_add _ _ _ := ext fun _ => smul_add _ _ _

end ZeroHom

/-! ### Instances for `AddMonoidHom` -/

namespace AddMonoidHom

instance instModule [Semiring R] [AddMonoid A] [AddCommMonoid B] [Module R B] :
    Module R (A →+ B) where
  add_smul _ _ _ := ext fun _ => add_smul _ _ _
  zero_smul _ := ext fun _ => zero_smul _ _

instance instDomMulActModule
    {S M M₂ : Type*} [Semiring S] [AddCommMonoid M] [AddCommMonoid M₂] [Module S M] :
    Module Sᵈᵐᵃ (M →+ M₂) where
  add_smul s s' f := AddMonoidHom.ext fun m ↦ by
    simp_rw [AddMonoidHom.add_apply, DomMulAct.smul_addMonoidHom_apply, ← map_add, ← add_smul]; rfl
  zero_smul _ := AddMonoidHom.ext fun _ ↦ by
    rw [DomMulAct.smul_addMonoidHom_apply]
    -- TODO there should be a simp lemma for `DomMulAct.mk.symm 0`
    simp [DomMulAct.mk, MulOpposite.opEquiv]

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
  AddMonoidHom.instSMulCommClass

instance isScalarTower [SMul R S] [IsScalarTower R S A] : IsScalarTower R S (AddMonoid.End A) :=
  AddMonoidHom.instIsScalarTower

instance isCentralScalar [DistribMulAction Rᵐᵒᵖ A] [IsCentralScalar R A] :
    IsCentralScalar R (AddMonoid.End A) :=
  AddMonoidHom.instIsCentralScalar

end

instance instModule [Semiring R] [AddCommMonoid A] [Module R A] : Module R (AddMonoid.End A) :=
  AddMonoidHom.instModule

/-- The tautological action by `AddMonoid.End α` on `α`.

This generalizes `AddMonoid.End.applyDistribMulAction`. -/
instance applyModule [AddCommMonoid A] : Module (AddMonoid.End A) A where
  add_smul _ _ _ := rfl
  zero_smul _ := rfl

end AddMonoid.End

/-! ### Miscellaneous morphisms -/

namespace AddMonoidHom

/-- Scalar multiplication on the left as an additive monoid homomorphism. -/
@[simps! -fullyApplied]
protected def smulLeft [Monoid M] [AddMonoid A] [DistribMulAction M A] (c : M) : A →+ A :=
  DistribMulAction.toAddMonoidHom _ c

/-- Scalar multiplication as a biadditive monoid homomorphism. We need `M` to be commutative
to have addition on `M →+ M`. -/
protected def smul [Semiring R] [AddCommMonoid M] [Module R M] : R →+ M →+ M :=
  (Module.toAddMonoidEnd R M).toAddMonoidHom

@[simp] theorem coe_smul' [Semiring R] [AddCommMonoid M] [Module R M] :
    ⇑(.smul : R →+ M →+ M) = AddMonoidHom.smulLeft := rfl

end AddMonoidHom
