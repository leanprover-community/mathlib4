/-
Copyright (c) 2025 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
module

public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Subsemigroup.Basic

/-!
# Subsemigroup of opposite semigroups

For every semigroup `M`, we construct an equivalence between subsemigroups of `M` and that of
`Mᵐᵒᵖ`.

-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {ι : Sort*} {M : Type*} [Mul M]

namespace Subsemigroup

/-- Pull a subsemigroup back to an opposite subsemigroup along `MulOpposite.unop` -/
@[to_additive (attr := simps) /-- Pull an additive subsemigroup back to an opposite subsemigroup
  along `AddOpposite.unop` -/]
protected def op (x : Subsemigroup M) : Subsemigroup Mᵐᵒᵖ where
  carrier := MulOpposite.unop ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha

@[to_additive (attr := simp)]
theorem mem_op {x : Mᵐᵒᵖ} {S : Subsemigroup M} : x ∈ S.op ↔ x.unop ∈ S := Iff.rfl

/-- Pull an opposite subsemigroup back to a subsemigroup along `MulOpposite.op` -/
@[to_additive (attr := simps) /-- Pull an opposite additive subsemigroup back to a subsemigroup
  along `AddOpposite.op` -/]
protected def unop (x : Subsemigroup Mᵐᵒᵖ) : Subsemigroup M where
  carrier := MulOpposite.op ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha

@[to_additive (attr := simp)]
theorem mem_unop {x : M} {S : Subsemigroup Mᵐᵒᵖ} : x ∈ S.unop ↔ MulOpposite.op x ∈ S := Iff.rfl

@[to_additive (attr := simp)]
theorem unop_op (S : Subsemigroup M) : S.op.unop = S := rfl

@[to_additive (attr := simp)]
theorem op_unop (S : Subsemigroup Mᵐᵒᵖ) : S.unop.op = S := rfl

/-! ### Lattice results -/

@[to_additive]
theorem op_le_iff {S₁ : Subsemigroup M} {S₂ : Subsemigroup Mᵐᵒᵖ} : S₁.op ≤ S₂ ↔ S₁ ≤ S₂.unop :=
  MulOpposite.op_surjective.forall

@[to_additive]
theorem le_op_iff {S₁ : Subsemigroup Mᵐᵒᵖ} {S₂ : Subsemigroup M} : S₁ ≤ S₂.op ↔ S₁.unop ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]
theorem op_le_op_iff {S₁ S₂ : Subsemigroup M} : S₁.op ≤ S₂.op ↔ S₁ ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]
theorem unop_le_unop_iff {S₁ S₂ : Subsemigroup Mᵐᵒᵖ} : S₁.unop ≤ S₂.unop ↔ S₁ ≤ S₂ :=
  MulOpposite.unop_surjective.forall

/-- A subsemigroup `H` of `M` determines a subsemigroup `H.op` of the opposite semigroup `Mᵐᵒᵖ`. -/
@[to_additive (attr := simps) /-- An additive subsemigroup `H` of `M` determines an additive
  subsemigroup `H.op` of the opposite semigroup `Mᵐᵒᵖ`. -/]
def opEquiv : Subsemigroup M ≃o Subsemigroup Mᵐᵒᵖ where
  toFun := Subsemigroup.op
  invFun := Subsemigroup.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[to_additive]
theorem op_injective : (@Subsemigroup.op M _).Injective := opEquiv.injective

@[to_additive]
theorem unop_injective : (@Subsemigroup.unop M _).Injective := opEquiv.symm.injective

@[to_additive (attr := simp)]
theorem op_inj {S T : Subsemigroup M} : S.op = T.op ↔ S = T := opEquiv.eq_iff_eq

@[to_additive (attr := simp)]
theorem unop_inj {S T : Subsemigroup Mᵐᵒᵖ} : S.unop = T.unop ↔ S = T := opEquiv.symm.eq_iff_eq

@[to_additive (attr := simp)]
theorem op_bot : (⊥ : Subsemigroup M).op = ⊥ := opEquiv.map_bot

@[to_additive (attr := simp)]
theorem op_eq_bot {S : Subsemigroup M} : S.op = ⊥ ↔ S = ⊥ := op_injective.eq_iff' op_bot

@[to_additive (attr := simp)]
theorem unop_bot : (⊥ : Subsemigroup Mᵐᵒᵖ).unop = ⊥ := opEquiv.symm.map_bot

@[to_additive (attr := simp)]
theorem unop_eq_bot {S : Subsemigroup Mᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥ := unop_injective.eq_iff' unop_bot

@[to_additive (attr := simp)]
theorem op_top : (⊤ : Subsemigroup M).op = ⊤ := rfl

@[to_additive (attr := simp)]
theorem op_eq_top {S : Subsemigroup M} : S.op = ⊤ ↔ S = ⊤ := op_injective.eq_iff' op_top

@[to_additive (attr := simp)]
theorem unop_top : (⊤ : Subsemigroup Mᵐᵒᵖ).unop = ⊤ := rfl

@[to_additive (attr := simp)]
theorem unop_eq_top {S : Subsemigroup Mᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤ := unop_injective.eq_iff' unop_top

@[to_additive]
theorem op_sup (S₁ S₂ : Subsemigroup M) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op :=
  opEquiv.map_sup _ _

@[to_additive]
theorem unop_sup (S₁ S₂ : Subsemigroup Mᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop :=
  opEquiv.symm.map_sup _ _

@[to_additive]
theorem op_inf (S₁ S₂ : Subsemigroup M) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := rfl

@[to_additive]
theorem unop_inf (S₁ S₂ : Subsemigroup Mᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop := rfl

@[to_additive]
theorem op_sSup (S : Set (Subsemigroup M)) : (sSup S).op = sSup (.unop ⁻¹' S) :=
  opEquiv.map_sSup_eq_sSup_symm_preimage _

@[to_additive]
theorem unop_sSup (S : Set (Subsemigroup Mᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) :=
  opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

@[to_additive]
theorem op_sInf (S : Set (Subsemigroup M)) : (sInf S).op = sInf (.unop ⁻¹' S) :=
  opEquiv.map_sInf_eq_sInf_symm_preimage _

@[to_additive]
theorem unop_sInf (S : Set (Subsemigroup Mᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) :=
  opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

@[to_additive]
theorem op_iSup (S : ι → Subsemigroup M) : (iSup S).op = ⨆ i, (S i).op := opEquiv.map_iSup _

@[to_additive]
theorem unop_iSup (S : ι → Subsemigroup Mᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop :=
  opEquiv.symm.map_iSup _

@[to_additive]
theorem op_iInf (S : ι → Subsemigroup M) : (iInf S).op = ⨅ i, (S i).op := opEquiv.map_iInf _

@[to_additive]
theorem unop_iInf (S : ι → Subsemigroup Mᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop :=
  opEquiv.symm.map_iInf _

@[to_additive]
theorem op_closure (s : Set M) : (closure s).op = closure (MulOpposite.unop ⁻¹' s) := by
  simp_rw [closure, op_sInf, Set.preimage_setOf_eq, Subsemigroup.coe_unop]
  congr with a
  exact MulOpposite.unop_surjective.forall

@[to_additive]
theorem unop_closure (s : Set Mᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by
  rw [← op_inj, op_unop, op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

/-- Bijection between a subsemigroup `H` and its opposite. -/
@[to_additive (attr := simps!) /-- Bijection between an additive subsemigroup `H` and its opposite.
  -/]
def equivOp (H : Subsemigroup M) : H ≃ H.op :=
  MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl

end Subsemigroup
