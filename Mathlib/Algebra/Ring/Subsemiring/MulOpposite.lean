/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.Group.Submonoid.MulOpposite
import Mathlib.Algebra.Ring.Subsemiring.Basic

/-!

# Subsemiring of opposite semirings

For every semiring `R`, we construct an equivalence between subsemirings of `R` and that of `Rᵐᵒᵖ`.

-/

namespace Subsemiring

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

/-- Pull a subsemiring back to an opposite subsemiring along `MulOpposite.unop` -/
@[simps toSubmonoid]
protected def op (S : Subsemiring R) : Subsemiring Rᵐᵒᵖ where
  toSubmonoid := S.toSubmonoid.op
  add_mem' {x} {y} hx hy := add_mem (show x.unop ∈ S from hx) (show y.unop ∈ S from hy)
  zero_mem' := zero_mem S

@[simp, norm_cast]
theorem op_coe (S : Subsemiring R) : S.op = MulOpposite.unop ⁻¹' (S : Set R) := rfl

@[simp]
theorem mem_op {x : Rᵐᵒᵖ} {S : Subsemiring R} : x ∈ S.op ↔ x.unop ∈ S := Iff.rfl

/-- Pull an opposite subsemiring back to a subsemiring along `MulOpposite.op` -/
@[simps toSubmonoid]
protected def unop (S : Subsemiring Rᵐᵒᵖ) : Subsemiring R where
  toSubmonoid := S.toSubmonoid.unop
  add_mem' {x} {y} hx hy := add_mem
    (show MulOpposite.op x ∈ S from hx) (show MulOpposite.op y ∈ S from hy)
  zero_mem' := zero_mem S

@[simp, norm_cast]
theorem unop_coe (S : Subsemiring Rᵐᵒᵖ) : S.unop = MulOpposite.op ⁻¹' (S : Set Rᵐᵒᵖ) := rfl

@[simp]
theorem mem_unop {x : R} {S : Subsemiring Rᵐᵒᵖ} : x ∈ S.unop ↔ MulOpposite.op x ∈ S := Iff.rfl

@[simp]
theorem unop_op (S : Subsemiring R) : S.op.unop = S := rfl

@[simp]
theorem op_unop (S : Subsemiring Rᵐᵒᵖ) : S.unop.op = S := rfl

/-! ### Lattice results -/

theorem op_le_iff {S₁ : Subsemiring R} {S₂ : Subsemiring Rᵐᵒᵖ} : S₁.op ≤ S₂ ↔ S₁ ≤ S₂.unop :=
  MulOpposite.op_surjective.forall

theorem le_op_iff {S₁ : Subsemiring Rᵐᵒᵖ} {S₂ : Subsemiring R} : S₁ ≤ S₂.op ↔ S₁.unop ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[simp]
theorem op_le_op_iff {S₁ S₂ : Subsemiring R} : S₁.op ≤ S₂.op ↔ S₁ ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[simp]
theorem unop_le_unop_iff {S₁ S₂ : Subsemiring Rᵐᵒᵖ} : S₁.unop ≤ S₂.unop ↔ S₁ ≤ S₂ :=
  MulOpposite.unop_surjective.forall

/-- A subsemiring `S` of `R` determines a subsemiring `S.op` of the opposite ring `Rᵐᵒᵖ`. -/
@[simps]
def opEquiv : Subsemiring R ≃o Subsemiring Rᵐᵒᵖ where
  toFun := Subsemiring.op
  invFun := Subsemiring.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[simp]
theorem op_bot : (⊥ : Subsemiring R).op = ⊥ := opEquiv.map_bot

@[simp]
theorem unop_bot : (⊥ : Subsemiring Rᵐᵒᵖ).unop = ⊥ := opEquiv.symm.map_bot

@[simp]
theorem op_top : (⊤ : Subsemiring R).op = ⊤ := opEquiv.map_top

@[simp]
theorem unop_top : (⊤ : Subsemiring Rᵐᵒᵖ).unop = ⊤ := opEquiv.symm.map_top

theorem op_sup (S₁ S₂ : Subsemiring R) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op :=
  opEquiv.map_sup _ _

theorem unop_sup (S₁ S₂ : Subsemiring Rᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop :=
  opEquiv.symm.map_sup _ _

theorem op_inf (S₁ S₂ : Subsemiring R) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := opEquiv.map_inf _ _

theorem unop_inf (S₁ S₂ : Subsemiring Rᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop :=
  opEquiv.symm.map_inf _ _

theorem op_sSup (S : Set (Subsemiring R)) : (sSup S).op = sSup (.unop ⁻¹' S) :=
  opEquiv.map_sSup_eq_sSup_symm_preimage _

theorem unop_sSup (S : Set (Subsemiring Rᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) :=
  opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

theorem op_sInf (S : Set (Subsemiring R)) : (sInf S).op = sInf (.unop ⁻¹' S) :=
  opEquiv.map_sInf_eq_sInf_symm_preimage _

theorem unop_sInf (S : Set (Subsemiring Rᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) :=
  opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

theorem op_iSup (S : ι → Subsemiring R) : (iSup S).op = ⨆ i, (S i).op := opEquiv.map_iSup _

theorem unop_iSup (S : ι → Subsemiring Rᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop :=
  opEquiv.symm.map_iSup _

theorem op_iInf (S : ι → Subsemiring R) : (iInf S).op = ⨅ i, (S i).op := opEquiv.map_iInf _

theorem unop_iInf (S : ι → Subsemiring Rᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop :=
  opEquiv.symm.map_iInf _

theorem op_closure (s : Set R) : (closure s).op = closure (MulOpposite.unop ⁻¹' s) := by
  simp_rw [closure, op_sInf, Set.preimage_setOf_eq, unop_coe]
  congr with a
  exact MulOpposite.unop_surjective.forall

theorem unop_closure (s : Set Rᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by
  simp_rw [closure, unop_sInf, Set.preimage_setOf_eq, op_coe]
  congr with a
  exact MulOpposite.op_surjective.forall

/-- Bijection between a subsemiring `S` and its opposite. -/
@[simps!]
def addEquivOp (S : Subsemiring R) : S ≃+ S.op where
  toEquiv := S.toSubmonoid.equivOp
  map_add' _ _ := rfl

-- TODO: Add this for `[Add]Submonoid` and `[Add]Subgroup`
/-- Bijection between a subsemiring `S` and `MulOpposite` of its opposite. -/
@[simps!]
def ringEquivOpMop (S : Subsemiring R) : S ≃+* (S.op)ᵐᵒᵖ where
  __ := S.addEquivOp.trans MulOpposite.opAddEquiv
  map_mul' _ _ := rfl

-- TODO: Add this for `[Add]Submonoid` and `[Add]Subgroup`
/-- Bijection between `MulOpposite` of a subsemiring `S` and its opposite. -/
@[simps!]
def mopRingEquivOp (S : Subsemiring R) : Sᵐᵒᵖ ≃+* S.op where
  __ := MulOpposite.opAddEquiv.symm.trans S.addEquivOp
  map_mul' _ _ := rfl

end Subsemiring
