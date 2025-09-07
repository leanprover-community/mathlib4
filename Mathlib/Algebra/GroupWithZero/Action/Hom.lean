/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Group.Hom.Instances

/-! # Zero-related `•` instances on group-like morphisms -/

variable {M N A B C : Type*}

namespace AddMonoidHom

section
variable [AddZeroClass A] [AddZeroClass B] [AddZeroClass C]

instance [DistribSMul M B] : SMulZeroClass M (A →+ B) where
  smul r f :=
    { toFun a := r • f a
      map_zero' := by simp only [map_zero, smul_zero]
      map_add' _ _ := by simp only [map_add, smul_add] }
  smul_zero _ := ext fun _ => smul_zero _

@[norm_cast] theorem coe_smul [DistribSMul M B] (m : M) (f : A →+ B) : ⇑(m • f) = m • f := rfl

@[simp] theorem smul_apply [DistribSMul M B] (m : M) (f : A →+ B) (a : A) : (m • f) a = m • f a :=
  rfl

theorem smul_comp [DistribSMul M C] (m : M) (g : B →+ C) (f : A →+ B) :
    (m • g).comp f = m • g.comp f := rfl

instance [DistribSMul M B] [DistribSMul N B] [SMulCommClass M N B] :
    SMulCommClass M N (A →+ B) where
  smul_comm _ _ _ := ext fun _ => smul_comm _ _ _

instance [SMul M N] [DistribSMul M B] [DistribSMul N B] [IsScalarTower M N B] :
    IsScalarTower M N (A →+ B) where
  smul_assoc _ _ _ := ext fun _ => smul_assoc _ _ _

instance [DistribSMul M B] [DistribSMul Mᵐᵒᵖ B] [IsCentralScalar M B] :
    IsCentralScalar M (A →+ B) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

end

variable [AddZeroClass A] [AddCommMonoid B]

instance [DistribSMul M B] : DistribSMul M (A →+ B) where
  smul_add _ _ _ := ext fun _ => smul_add _ _ _

instance [Monoid M] [DistribMulAction M B] : DistribMulAction M (A →+ B) where
  __ : DistribSMul _ _ := inferInstance
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ :=  ext fun _ => mul_smul _ _ _

end AddMonoidHom
