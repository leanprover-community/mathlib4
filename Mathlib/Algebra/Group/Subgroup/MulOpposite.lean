/-
Copyright (c) 2022 Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Eric Wieser
-/
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.MulOpposite

/-!
# Mul-opposite subgroups

## Tags
subgroup, subgroups

-/

variable {ι : Sort*} {G : Type*} [Group G]

namespace Subgroup

/-- Pull a subgroup back to an opposite subgroup along `MulOpposite.unop` -/
@[to_additive (attr := simps)
/-- Pull an additive subgroup back to an opposite additive subgroup along `AddOpposite.unop` -/]
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

/-- Pull an opposite subgroup back to a subgroup along `MulOpposite.op` -/
@[to_additive (attr := simps)
/-- Pull an opposite additive subgroup back to an additive subgroup along `AddOpposite.op` -/]
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
@[to_additive (attr := simps) /-- An additive subgroup `H` of `G` determines an additive subgroup
`H.op` of the opposite additive group `Gᵃᵒᵖ`. -/]
def opEquiv : Subgroup G ≃o Subgroup Gᵐᵒᵖ where
  toFun := Subgroup.op
  invFun := Subgroup.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[to_additive]
theorem op_injective : (@Subgroup.op G _).Injective := opEquiv.injective

@[to_additive]
theorem unop_injective : (@Subgroup.unop G _).Injective := opEquiv.symm.injective

@[to_additive (attr := simp)]
theorem op_inj {S T : Subgroup G} : S.op = T.op ↔ S = T := opEquiv.eq_iff_eq

@[to_additive (attr := simp)]
theorem unop_inj {S T : Subgroup Gᵐᵒᵖ} : S.unop = T.unop ↔ S = T := opEquiv.symm.eq_iff_eq

/-- Bijection between a subgroup `H` and its opposite. -/
@[to_additive (attr := simps!) /-- Bijection between an additive subgroup `H` and its opposite. -/]
def equivOp (H : Subgroup G) : H ≃ H.op :=
  MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl

@[to_additive]
theorem op_normalizer (H : Subgroup G) : H.normalizer.op = H.op.normalizer := by
  ext x
  simp [mem_normalizer_iff', iff_comm]

@[to_additive]
theorem unop_normalizer (H : Subgroup Gᵐᵒᵖ) : H.normalizer.unop = H.unop.normalizer := by
  rw [← op_inj, op_unop, op_normalizer, op_unop]

end Subgroup
