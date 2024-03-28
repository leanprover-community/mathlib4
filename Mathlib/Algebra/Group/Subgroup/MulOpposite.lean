/-
Copyright (c) 2022 Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Eric Wieser
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Submonoid.MulOpposite
import Mathlib.Logic.Encodable.Basic

#align_import group_theory.subgroup.mul_opposite from "leanprover-community/mathlib"@"f93c11933efbc3c2f0299e47b8ff83e9b539cbf6"

/-!
# Mul-opposite subgroups

## Tags
subgroup, subgroups

-/


variable {ι : Sort*} {G : Type*} [Group G]

namespace Subgroup

/-- Pull a subgroup back to an opposite subgroup along `MulOpposite.unop`-/
@[to_additive (attr := simps)
"Pull an additive subgroup back to an opposite additive subgroup along `AddOpposite.unop`"]
protected def op (H : Subgroup G) : Subgroup Gᵐᵒᵖ where
  carrier := MulOpposite.unop ⁻¹' (H : Set G)
  one_mem' := H.one_mem
  mul_mem' ha hb := H.mul_mem hb ha
  inv_mem' := H.inv_mem

@[to_additive (attr := simp)]
theorem mem_op {x : Gᵐᵒᵖ} {S : Subgroup G} : x ∈ S.op ↔ x.unop ∈ S := Iff.rfl

@[to_additive (attr := simp)] lemma op_toSubmonoid (H : Subgroup G) :
    H.op.toSubmonoid = H.toSubmonoid.op :=
  rfl

/-- Pull an opposite subgroup back to a subgroup along `MulOpposite.op`-/
@[to_additive (attr := simps)
"Pull an opposite additive subgroup back to an additive subgroup along `AddOpposite.op`"]
protected def unop (H : Subgroup Gᵐᵒᵖ) : Subgroup G where
  carrier := MulOpposite.op ⁻¹' (H : Set Gᵐᵒᵖ)
  one_mem' := H.one_mem
  mul_mem' := fun ha hb => H.mul_mem hb ha
  inv_mem' := H.inv_mem

@[to_additive (attr := simp)]
theorem mem_unop {x : G} {S : Subgroup Gᵐᵒᵖ} : x ∈ S.unop ↔ MulOpposite.op x ∈ S := Iff.rfl

@[to_additive (attr := simp)] lemma unop_toSubmonoid (H : Subgroup Gᵐᵒᵖ) :
    H.unop.toSubmonoid = H.toSubmonoid.unop :=
  rfl

@[to_additive (attr := simp)]
theorem unop_op (S : Subgroup G) : S.op.unop = S := rfl

@[to_additive (attr := simp)]
theorem op_unop (S : Subgroup Gᵐᵒᵖ) : S.unop.op = S := rfl

/-! ### Lattice results -/

@[to_additive]
theorem op_le_iff {S₁ : Subgroup G} {S₂ : Subgroup Gᵐᵒᵖ} : S₁.op ≤ S₂ ↔ S₁ ≤ S₂.unop :=
  MulOpposite.op_surjective.forall

@[to_additive]
theorem le_op_iff {S₁ : Subgroup Gᵐᵒᵖ} {S₂ : Subgroup G} : S₁ ≤ S₂.op ↔ S₁.unop ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]
theorem op_le_op_iff {S₁ S₂ : Subgroup G} : S₁.op ≤ S₂.op ↔ S₁ ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]
theorem unop_le_unop_iff {S₁ S₂ : Subgroup Gᵐᵒᵖ} : S₁.unop ≤ S₂.unop ↔ S₁ ≤ S₂ :=
  MulOpposite.unop_surjective.forall

/-- A subgroup `H` of `G` determines a subgroup `H.op` of the opposite group `Gᵐᵒᵖ`. -/
@[to_additive (attr := simps) "An additive subgroup `H` of `G` determines an additive subgroup
`H.op` of the opposite additive group `Gᵃᵒᵖ`."]
def opEquiv : Subgroup G ≃o Subgroup Gᵐᵒᵖ where
  toFun := Subgroup.op
  invFun := Subgroup.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff
#align subgroup.opposite Subgroup.opEquiv
#align add_subgroup.opposite AddSubgroup.opEquiv

@[to_additive (attr := simp)]
theorem op_bot : (⊥ : Subgroup G).op = ⊥ := opEquiv.map_bot

@[to_additive (attr := simp)]
theorem unop_bot : (⊥ : Subgroup Gᵐᵒᵖ).unop = ⊥ := opEquiv.symm.map_bot

@[to_additive (attr := simp)]
theorem op_top : (⊤ : Subgroup G).op = ⊤ := opEquiv.map_top

@[to_additive (attr := simp)]
theorem unop_top : (⊤ : Subgroup Gᵐᵒᵖ).unop = ⊤ := opEquiv.symm.map_top

@[to_additive]
theorem op_sup (S₁ S₂ : Subgroup G) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op :=
  opEquiv.map_sup _ _

@[to_additive]
theorem unop_sup (S₁ S₂ : Subgroup Gᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop :=
  opEquiv.symm.map_sup _ _

@[to_additive]
theorem op_inf (S₁ S₂ : Subgroup G) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := opEquiv.map_inf _ _

@[to_additive]
theorem unop_inf (S₁ S₂ : Subgroup Gᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop :=
  opEquiv.symm.map_inf _ _

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
  simp_rw [closure, op_sInf, Set.preimage_setOf_eq, Subgroup.unop_coe]
  congr with a
  exact MulOpposite.unop_surjective.forall

@[to_additive]
theorem unop_closure (s : Set Gᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by
  simp_rw [closure, unop_sInf, Set.preimage_setOf_eq, Subgroup.op_coe]
  congr with a
  exact MulOpposite.op_surjective.forall

/-- Bijection between a subgroup `H` and its opposite. -/
@[to_additive (attr := simps!) "Bijection between an additive subgroup `H` and its opposite."]
def equivOp (H : Subgroup G) : H ≃ H.op :=
  MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl
#align subgroup.opposite_equiv Subgroup.equivOp
#align add_subgroup.opposite_equiv AddSubgroup.equivOp
#align subgroup.opposite_equiv_symm_apply_coe Subgroup.equivOp_symm_apply_coe

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
#align subgroup.smul_opposite_mul Subgroup.smul_opposite_mul
#align add_subgroup.vadd_opposite_add AddSubgroup.vadd_opposite_add

end Subgroup
