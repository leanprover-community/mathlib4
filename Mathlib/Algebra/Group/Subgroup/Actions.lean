/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.GroupTheory.Subgroup.Center

#align_import group_theory.subgroup.actions from "leanprover-community/mathlib"@"f93c11933efbc3c2f0299e47b8ff83e9b539cbf6"

/-!
# Actions by `Subgroup`s

These are just copies of the definitions about `Submonoid` starting from `Submonoid.mulAction`.

## Tags
subgroup, subgroups

-/


namespace Subgroup
variable {G α β : Type*} [Group G]

section MulAction
variable [MulAction G α] {S : Subgroup G}

/-- The action by a subgroup is the action by the underlying group. -/
@[to_additive "The additive action by an add_subgroup is the action by the underlying `AddGroup`. "]
instance instMulAction : MulAction S α := inferInstanceAs (MulAction S.toSubmonoid α)

@[to_additive] lemma smul_def (g : S) (m : α) : g • m = (g : G) • m := rfl
#align subgroup.smul_def Subgroup.smul_def
#align add_subgroup.vadd_def AddSubgroup.vadd_def

@[to_additive (attr := simp)]
lemma mk_smul (g : G) (hg : g ∈ S) (a : α) : (⟨g, hg⟩ : S) • a = g • a := rfl

end MulAction

@[to_additive]
instance smulCommClass_left [MulAction G β] [SMul α β] [SMulCommClass G α β] (S : Subgroup G) :
    SMulCommClass S α β :=
  S.toSubmonoid.smulCommClass_left
#align subgroup.smul_comm_class_left Subgroup.smulCommClass_left
#align add_subgroup.vadd_comm_class_left AddSubgroup.vaddCommClass_left

@[to_additive]
instance smulCommClass_right [SMul α β] [MulAction G β] [SMulCommClass α G β] (S : Subgroup G) :
    SMulCommClass α S β :=
  S.toSubmonoid.smulCommClass_right
#align subgroup.smul_comm_class_right Subgroup.smulCommClass_right
#align add_subgroup.vadd_comm_class_right AddSubgroup.vaddCommClass_right

/-- Note that this provides `IsScalarTower S G G` which is needed by `smul_mul_assoc`. -/
instance [SMul α β] [MulAction G α] [MulAction G β] [IsScalarTower G α β] (S : Subgroup G) :
    IsScalarTower S α β :=
  inferInstanceAs (IsScalarTower S.toSubmonoid α β)

instance [MulAction G α] [FaithfulSMul G α] (S : Subgroup G) : FaithfulSMul S α :=
  inferInstanceAs (FaithfulSMul S.toSubmonoid α)

/-- The action by a subgroup is the action by the underlying group. -/
instance [AddMonoid α] [DistribMulAction G α] (S : Subgroup G) : DistribMulAction S α :=
  inferInstanceAs (DistribMulAction S.toSubmonoid α)

/-- The action by a subgroup is the action by the underlying group. -/
instance [Monoid α] [MulDistribMulAction G α] (S : Subgroup G) : MulDistribMulAction S α :=
  inferInstanceAs (MulDistribMulAction S.toSubmonoid α)

/-- The center of a group acts commutatively on that group. -/
instance center.smulCommClass_left : SMulCommClass (center G) G G :=
  Submonoid.center.smulCommClass_left
#align subgroup.center.smul_comm_class_left Subgroup.center.smulCommClass_left

/-- The center of a group acts commutatively on that group. -/
instance center.smulCommClass_right : SMulCommClass G (center G) G :=
  Submonoid.center.smulCommClass_right
#align subgroup.center.smul_comm_class_right Subgroup.center.smulCommClass_right

end Subgroup
