/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.GroupTheory.GroupAction.Defs

#align_import group_theory.group_action.prod from "leanprover-community/mathlib"@"aba57d4d3dae35460225919dcd82fe91355162f9"

/-!
# Prod instances for additive and multiplicative actions
This file defines instances for binary product of additive and multiplicative actions and provides
scalar multiplication as a homomorphism from `α × β` to `β`.
## Main declarations
* `smulMulHom `/`smulMonoidHom `: Scalar multiplication bundled as a multiplicative/monoid
  homomorphism.
## See also
* `Mathlib.GroupTheory.GroupAction.Option`
* `Mathlib.GroupTheory.GroupAction.Pi`
* `Mathlib.GroupTheory.GroupAction.Sigma`
* `Mathlib.GroupTheory.GroupAction.Sum`

# Porting notes
The `to_additive` attribute can be used to generate both the `smul` and `vadd` lemmas
from the corresponding `pow` lemmas, as explained on zulip here:
https://leanprover.zulipchat.com/#narrow/near/316087838

This was not done as part of the port in order to stay as close as possible to the mathlib3 code.
-/

set_option autoImplicit true


variable {M N P E α β : Type*}

namespace Prod

section

variable [SMul M α] [SMul M β] [SMul N α] [SMul N β] (a : M) (x : α × β)

@[to_additive]
instance smul : SMul M (α × β) :=
  ⟨fun a p => (a • p.1, a • p.2)⟩

@[to_additive (attr := simp)]
theorem smul_fst : (a • x).1 = a • x.1 :=
  rfl
#align prod.smul_fst Prod.smul_fst
#align prod.vadd_fst Prod.vadd_fst

@[to_additive (attr := simp)]
theorem smul_snd : (a • x).2 = a • x.2 :=
  rfl
#align prod.smul_snd Prod.smul_snd
#align prod.vadd_snd Prod.vadd_snd

@[to_additive (attr := simp)]
theorem smul_mk (a : M) (b : α) (c : β) : a • (b, c) = (a • b, a • c) :=
  rfl
#align prod.smul_mk Prod.smul_mk
#align prod.vadd_mk Prod.vadd_mk

@[to_additive]
theorem smul_def (a : M) (x : α × β) : a • x = (a • x.1, a • x.2) :=
  rfl
#align prod.smul_def Prod.smul_def
#align prod.vadd_def Prod.vadd_def

@[to_additive (attr := simp)]
theorem smul_swap : (a • x).swap = a • x.swap :=
  rfl
#align prod.smul_swap Prod.smul_swap
#align prod.vadd_swap Prod.vadd_swap

theorem smul_zero_mk {α : Type*} [Monoid M] [AddMonoid α] [DistribMulAction M α] (a : M) (c : β) :
    a • ((0 : α), c) = (0, a • c) := by rw [Prod.smul_mk, smul_zero]
                                        -- 🎉 no goals
#align prod.smul_zero_mk Prod.smul_zero_mk

theorem smul_mk_zero {β : Type*} [Monoid M] [AddMonoid β] [DistribMulAction M β] (a : M) (b : α) :
    a • (b, (0 : β)) = (a • b, 0) := by rw [Prod.smul_mk, smul_zero]
                                        -- 🎉 no goals
#align prod.smul_mk_zero Prod.smul_mk_zero

variable [Pow α E] [Pow β E]

@[to_additive existing smul]
instance pow : Pow (α × β) E where pow p c := (p.1 ^ c, p.2 ^ c)
#align prod.has_pow Prod.pow
#align prod.has_smul Prod.smul

@[to_additive existing (attr := simp) (reorder := 6 7) smul_fst]
theorem pow_fst (p : α × β) (c : E) : (p ^ c).fst = p.fst ^ c :=
  rfl
#align prod.pow_fst Prod.pow_fst

@[to_additive existing (attr := simp) (reorder := 6 7) smul_snd]
theorem pow_snd (p : α × β) (c : E) : (p ^ c).snd = p.snd ^ c :=
  rfl
#align prod.pow_snd Prod.pow_snd

/- Note that the `c` arguments to this lemmas cannot be in the more natural right-most positions due
to limitations in `to_additive` and `to_additive_reorder`, which will silently fail to reorder more
than two adjacent arguments -/
@[to_additive existing (attr := simp) (reorder := 6 7) smul_mk]
theorem pow_mk (c : E) (a : α) (b : β) : Prod.mk a b ^ c = Prod.mk (a ^ c) (b ^ c) :=
  rfl
#align prod.pow_mk Prod.pow_mk

@[to_additive existing (reorder := 6 7) smul_def]
theorem pow_def (p : α × β) (c : E) : p ^ c = (p.1 ^ c, p.2 ^ c) :=
  rfl
#align prod.pow_def Prod.pow_def

@[to_additive existing (attr := simp) (reorder := 6 7) smul_swap]
theorem pow_swap (p : α × β) (c : E) : (p ^ c).swap = p.swap ^ c :=
  rfl
#align prod.pow_swap Prod.pow_swap

@[to_additive vaddAssocClass]
instance isScalarTower [SMul M N] [IsScalarTower M N α] [IsScalarTower M N β] :
    IsScalarTower M N (α × β) :=
  ⟨fun _ _ _ => mk.inj_iff.mpr ⟨smul_assoc _ _ _, smul_assoc _ _ _⟩⟩

@[to_additive]
instance smulCommClass [SMulCommClass M N α] [SMulCommClass M N β] :
    SMulCommClass M N (α × β) where
  smul_comm _ _ _ := mk.inj_iff.mpr ⟨smul_comm _ _ _, smul_comm _ _ _⟩

@[to_additive]
instance isCentralScalar [SMul Mᵐᵒᵖ α] [SMul Mᵐᵒᵖ β] [IsCentralScalar M α] [IsCentralScalar M β] :
    IsCentralScalar M (α × β) :=
  ⟨fun _ _ => Prod.ext (op_smul_eq_smul _ _) (op_smul_eq_smul _ _)⟩
#align prod.is_central_scalar Prod.isCentralScalar
#align prod.is_central_vadd Prod.isCentralVAdd

@[to_additive]
instance faithfulSMulLeft [FaithfulSMul M α] [Nonempty β] : FaithfulSMul M (α × β) :=
  ⟨fun h =>
    let ⟨b⟩ := ‹Nonempty β›
    eq_of_smul_eq_smul fun a : α => by injection h (a, b)⟩
                                       -- 🎉 no goals
#align prod.has_faithful_smul_left Prod.faithfulSMulLeft
#align prod.has_faithful_vadd_left Prod.faithfulVAddLeft

@[to_additive]
instance faithfulSMulRight [Nonempty α] [FaithfulSMul M β] : FaithfulSMul M (α × β) :=
  ⟨fun h =>
    let ⟨a⟩ := ‹Nonempty α›
    eq_of_smul_eq_smul fun b : β => by injection h (a, b)⟩
                                       -- 🎉 no goals
#align prod.has_faithful_smul_right Prod.faithfulSMulRight
#align prod.has_faithful_vadd_right Prod.faithfulVAddRight

end

@[to_additive]
instance smulCommClassBoth [Mul N] [Mul P] [SMul M N] [SMul M P] [SMulCommClass M N N]
    [SMulCommClass M P P] : SMulCommClass M (N × P) (N × P) :=
  ⟨fun c x y => by simp [smul_def, mul_def, mul_smul_comm]⟩
                   -- 🎉 no goals
#align prod.smul_comm_class_both Prod.smulCommClassBoth
#align prod.vadd_comm_class_both Prod.vaddCommClassBoth

instance isScalarTowerBoth [Mul N] [Mul P] [SMul M N] [SMul M P] [IsScalarTower M N N]
    [IsScalarTower M P P] : IsScalarTower M (N × P) (N × P) :=
  ⟨fun c x y => by simp [smul_def, mul_def, smul_mul_assoc]⟩
                   -- 🎉 no goals
#align prod.is_scalar_tower_both Prod.isScalarTowerBoth

@[to_additive]
instance mulAction [Monoid M] [MulAction M α] [MulAction M β] : MulAction M (α × β) where
  mul_smul _ _ _ := mk.inj_iff.mpr ⟨mul_smul _ _ _, mul_smul _ _ _⟩
  one_smul := fun ⟨_, _⟩ => mk.inj_iff.mpr ⟨one_smul _ _, one_smul _ _⟩

instance smulZeroClass {R M N : Type*} [Zero M] [Zero N] [SMulZeroClass R M] [SMulZeroClass R N] :
    SMulZeroClass R (M × N) where smul_zero _ := mk.inj_iff.mpr ⟨smul_zero _, smul_zero _⟩

instance distribSMul {R M N : Type*} [AddZeroClass M] [AddZeroClass N] [DistribSMul R M]
    [DistribSMul R N] : DistribSMul R (M × N) where
  smul_add _ _ _ := mk.inj_iff.mpr ⟨smul_add _ _ _, smul_add _ _ _⟩

instance distribMulAction [Monoid R] [AddMonoid M] [AddMonoid N]
    [DistribMulAction R M] [DistribMulAction R N] : DistribMulAction R (M × N) :=
  { Prod.mulAction, Prod.distribSMul with }

instance mulDistribMulAction [Monoid R] [Monoid M] [Monoid N]
    [MulDistribMulAction R M] [MulDistribMulAction R N] : MulDistribMulAction R (M × N) where
  smul_mul _ _ _ := mk.inj_iff.mpr ⟨smul_mul' _ _ _, smul_mul' _ _ _⟩
  smul_one _ := mk.inj_iff.mpr ⟨smul_one _, smul_one _⟩

end Prod

/-! ### Scalar multiplication as a homomorphism -/

section BundledSMul

/-- Scalar multiplication as a multiplicative homomorphism. -/
@[simps]
def smulMulHom [Monoid α] [Mul β] [MulAction α β] [IsScalarTower α β β] [SMulCommClass α β β] :
    α × β →ₙ* β where
  toFun a := a.1 • a.2
  map_mul' _ _ := (smul_mul_smul _ _ _ _).symm
#align smul_mul_hom smulMulHom
#align smul_mul_hom_apply smulMulHom_apply

/-- Scalar multiplication as a monoid homomorphism. -/
@[simps]
def smulMonoidHom [Monoid α] [MulOneClass β] [MulAction α β] [IsScalarTower α β β]
    [SMulCommClass α β β] : α × β →* β :=
  { smulMulHom with map_one' := one_smul _ _ }
#align smul_monoid_hom smulMonoidHom
#align smul_monoid_hom_apply smulMonoidHom_apply

end BundledSMul
