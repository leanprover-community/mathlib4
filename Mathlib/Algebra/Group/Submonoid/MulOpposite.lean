/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jujian Zhang
-/
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Group.Submonoid.Basic

/-!
# Submonoid of opposite monoids

For every monoid `M`, we construct an equivalence between submonoids of `M` and that of `Mᵐᵒᵖ`.

-/

assert_not_exists MonoidWithZero

variable {ι : Sort*} {M : Type*} [MulOneClass M]

namespace Submonoid

/-- Pull a submonoid back to an opposite submonoid along `MulOpposite.unop`-/
@[to_additive (attr := simps) "Pull an additive submonoid back to an opposite submonoid along
`AddOpposite.unop`"]
protected def op (x : Submonoid M) : Submonoid Mᵐᵒᵖ where
  carrier := MulOpposite.unop ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha
  one_mem' := Submonoid.one_mem' _

@[to_additive (attr := simp)]
theorem mem_op {x : Mᵐᵒᵖ} {S : Submonoid M} : x ∈ S.op ↔ x.unop ∈ S := Iff.rfl

/-- Pull an opposite submonoid back to a submonoid along `MulOpposite.op`-/
@[to_additive (attr := simps) "Pull an opposite additive submonoid back to a submonoid along
`AddOpposite.op`"]
protected def unop (x : Submonoid Mᵐᵒᵖ) : Submonoid M where
  carrier := MulOpposite.op ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha
  one_mem' := Submonoid.one_mem' _

@[to_additive (attr := simp)]
theorem mem_unop {x : M} {S : Submonoid Mᵐᵒᵖ} : x ∈ S.unop ↔ MulOpposite.op x ∈ S := Iff.rfl

@[to_additive (attr := simp)]
theorem unop_op (S : Submonoid M) : S.op.unop = S := rfl

@[to_additive (attr := simp)]
theorem op_unop (S : Submonoid Mᵐᵒᵖ) : S.unop.op = S := rfl

/-! ### Lattice results -/

@[to_additive]
theorem op_le_iff {S₁ : Submonoid M} {S₂ : Submonoid Mᵐᵒᵖ} : S₁.op ≤ S₂ ↔ S₁ ≤ S₂.unop :=
  MulOpposite.op_surjective.forall

@[to_additive]
theorem le_op_iff {S₁ : Submonoid Mᵐᵒᵖ} {S₂ : Submonoid M} : S₁ ≤ S₂.op ↔ S₁.unop ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]
theorem op_le_op_iff {S₁ S₂ : Submonoid M} : S₁.op ≤ S₂.op ↔ S₁ ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]
theorem unop_le_unop_iff {S₁ S₂ : Submonoid Mᵐᵒᵖ} : S₁.unop ≤ S₂.unop ↔ S₁ ≤ S₂ :=
  MulOpposite.unop_surjective.forall

/-- A submonoid `H` of `G` determines a submonoid `H.op` of the opposite group `Gᵐᵒᵖ`. -/
@[to_additive (attr := simps) "A additive submonoid `H` of `G` determines an additive submonoid
`H.op` of the opposite group `Gᵐᵒᵖ`."]
def opEquiv : Submonoid M ≃o Submonoid Mᵐᵒᵖ where
  toFun := Submonoid.op
  invFun := Submonoid.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[to_additive (attr := simp)]
theorem op_bot : (⊥ : Submonoid M).op = ⊥ := opEquiv.map_bot

@[to_additive (attr := simp)]
theorem unop_bot : (⊥ : Submonoid Mᵐᵒᵖ).unop = ⊥ := opEquiv.symm.map_bot

@[to_additive (attr := simp)]
theorem op_top : (⊤ : Submonoid M).op = ⊤ := opEquiv.map_top

@[to_additive (attr := simp)]
theorem unop_top : (⊤ : Submonoid Mᵐᵒᵖ).unop = ⊤ := opEquiv.symm.map_top

@[to_additive]
theorem op_sup (S₁ S₂ : Submonoid M) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op :=
  opEquiv.map_sup _ _

@[to_additive]
theorem unop_sup (S₁ S₂ : Submonoid Mᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop :=
  opEquiv.symm.map_sup _ _

@[to_additive]
theorem op_inf (S₁ S₂ : Submonoid M) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := opEquiv.map_inf _ _

@[to_additive]
theorem unop_inf (S₁ S₂ : Submonoid Mᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop :=
  opEquiv.symm.map_inf _ _

@[to_additive]
theorem op_sSup (S : Set (Submonoid M)) : (sSup S).op = sSup (.unop ⁻¹' S) :=
  opEquiv.map_sSup_eq_sSup_symm_preimage _

@[to_additive]
theorem unop_sSup (S : Set (Submonoid Mᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) :=
  opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

@[to_additive]
theorem op_sInf (S : Set (Submonoid M)) : (sInf S).op = sInf (.unop ⁻¹' S) :=
  opEquiv.map_sInf_eq_sInf_symm_preimage _

@[to_additive]
theorem unop_sInf (S : Set (Submonoid Mᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) :=
  opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

@[to_additive]
theorem op_iSup (S : ι → Submonoid M) : (iSup S).op = ⨆ i, (S i).op := opEquiv.map_iSup _

@[to_additive]
theorem unop_iSup (S : ι → Submonoid Mᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop :=
  opEquiv.symm.map_iSup _

@[to_additive]
theorem op_iInf (S : ι → Submonoid M) : (iInf S).op = ⨅ i, (S i).op := opEquiv.map_iInf _

@[to_additive]
theorem unop_iInf (S : ι → Submonoid Mᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop :=
  opEquiv.symm.map_iInf _

@[to_additive]
theorem op_closure (s : Set M) : (closure s).op = closure (MulOpposite.unop ⁻¹' s) := by
  simp_rw [closure, op_sInf, Set.preimage_setOf_eq, Submonoid.unop_coe]
  congr with a
  exact MulOpposite.unop_surjective.forall

@[to_additive]
theorem unop_closure (s : Set Mᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by
  simp_rw [closure, unop_sInf, Set.preimage_setOf_eq, Submonoid.op_coe]
  congr with a
  exact MulOpposite.op_surjective.forall

/-- Bijection between a submonoid `H` and its opposite. -/
@[to_additive (attr := simps!) "Bijection between an additive submonoid `H` and its opposite."]
def equivOp (H : Submonoid M) : H ≃ H.op :=
  MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl

end Submonoid
