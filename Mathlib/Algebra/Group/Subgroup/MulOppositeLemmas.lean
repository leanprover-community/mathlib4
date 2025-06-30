/-
Copyright (c) 2022 Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Eric Wieser
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.MulOpposite
import Mathlib.Algebra.Group.Submonoid.MulOpposite
import Mathlib.Logic.Encodable.Basic

/-!
# Mul-opposite subgroups

This file contains a somewhat arbitrary assortment of results on the opposite subgroup `H.op`
that rely on further theory to define. As such it is a somewhat arbitrary assortment of results,
which might be organized and split up further.

## Tags
subgroup, subgroups

-/

variable {ι : Sort*} {G : Type*} [Group G]

namespace Subgroup

/- We redeclare this instance to get keys
`SMul (@Subtype (MulOpposite _) (@Membership.mem (MulOpposite _)
  (Subgroup (MulOpposite _) _) _ (@Subgroup.op _ _ _))) _`
compared to the keys for `Submonoid.smul`
`SMul (@Subtype _ (@Membership.mem _ (Submonoid _ _) _ _)) _` -/
@[to_additive] instance instSMul (H : Subgroup G) : SMul H.op G := Submonoid.smul ..

/-! ### Lattice results -/

@[to_additive (attr := simp)]
theorem op_bot : (⊥ : Subgroup G).op = ⊥ := opEquiv.map_bot

@[to_additive (attr := simp)]
theorem op_eq_bot {S : Subgroup G} : S.op = ⊥ ↔ S = ⊥ := op_injective.eq_iff' op_bot

@[to_additive (attr := simp)]
theorem unop_bot : (⊥ : Subgroup Gᵐᵒᵖ).unop = ⊥ := opEquiv.symm.map_bot

@[to_additive (attr := simp)]
theorem unop_eq_bot {S : Subgroup Gᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥ := unop_injective.eq_iff' unop_bot

@[to_additive (attr := simp)]
theorem op_top : (⊤ : Subgroup G).op = ⊤ := rfl

@[to_additive (attr := simp)]
theorem op_eq_top {S : Subgroup G} : S.op = ⊤ ↔ S = ⊤ := op_injective.eq_iff' op_top

@[to_additive (attr := simp)]
theorem unop_top : (⊤ : Subgroup Gᵐᵒᵖ).unop = ⊤ := rfl

@[to_additive (attr := simp)]
theorem unop_eq_top {S : Subgroup Gᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤ := unop_injective.eq_iff' unop_top

@[to_additive]
theorem op_sup (S₁ S₂ : Subgroup G) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op :=
  opEquiv.map_sup _ _

@[to_additive]
theorem unop_sup (S₁ S₂ : Subgroup Gᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop :=
  opEquiv.symm.map_sup _ _

@[to_additive]
theorem op_inf (S₁ S₂ : Subgroup G) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := rfl

@[to_additive]
theorem unop_inf (S₁ S₂ : Subgroup Gᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop := rfl

@[to_additive]
theorem op_sSup (S : Set (Subgroup G)) : (sSup S).op = sSup (.unop ⁻¹' S) :=
  opEquiv.map_sSup_eq_sSup_symm_preimage _

@[to_additive]
theorem unop_sSup (S : Set (Subgroup Gᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) :=
  opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

@[to_additive]
theorem op_sInf (S : Set (Subgroup G)) : (sInf S).op = sInf (.unop ⁻¹' S) :=
  opEquiv.map_sInf_eq_sInf_symm_preimage _

@[to_additive]
theorem unop_sInf (S : Set (Subgroup Gᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) :=
  opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

@[to_additive]
theorem op_iSup (S : ι → Subgroup G) : (iSup S).op = ⨆ i, (S i).op := opEquiv.map_iSup _

@[to_additive]
theorem unop_iSup (S : ι → Subgroup Gᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop :=
  opEquiv.symm.map_iSup _

@[to_additive]
theorem op_iInf (S : ι → Subgroup G) : (iInf S).op = ⨅ i, (S i).op := opEquiv.map_iInf _

@[to_additive]
theorem unop_iInf (S : ι → Subgroup Gᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop :=
  opEquiv.symm.map_iInf _

@[to_additive]
theorem op_closure (s : Set G) : (closure s).op = closure (MulOpposite.unop ⁻¹' s) := by
  simp_rw [closure, op_sInf, Set.preimage_setOf_eq, Subgroup.coe_unop]
  congr with a
  exact MulOpposite.unop_surjective.forall

@[to_additive]
theorem unop_closure (s : Set Gᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by
  rw [← op_inj, op_unop, op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

@[to_additive]
instance (H : Subgroup G) [Encodable H] : Encodable H.op :=
  Encodable.ofEquiv H H.equivOp.symm

@[to_additive]
instance (H : Subgroup G) [Countable H] : Countable H.op :=
  Countable.of_equiv H H.equivOp

@[to_additive]
theorem smul_opposite_mul {H : Subgroup G} (x g : G) (h : H.op) :
    h • (g * x) = g * h • x :=
  mul_assoc _ _ _

@[to_additive (attr := simp)]
theorem normal_op {H : Subgroup G} : H.op.Normal ↔ H.Normal := by
  simp only [← normalizer_eq_top_iff, ← op_normalizer, op_eq_top]

@[to_additive] alias ⟨Normal.of_op, Normal.op⟩ := normal_op

@[to_additive]
instance op.instNormal {H : Subgroup G} [H.Normal] : H.op.Normal := .op ‹_›

@[to_additive (attr := simp)]
theorem normal_unop {H : Subgroup Gᵐᵒᵖ} : H.unop.Normal ↔ H.Normal := by
  rw [← normal_op, op_unop]

@[to_additive] alias ⟨Normal.of_unop, Normal.unop⟩ := normal_unop

@[to_additive]
instance unop.instNormal {H : Subgroup Gᵐᵒᵖ} [H.Normal] : H.unop.Normal := .unop ‹_›

end Subgroup
