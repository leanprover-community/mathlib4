/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.Ring.Subsemiring.MulOpposite
import Mathlib.Algebra.Ring.Subring.Basic

/-!

# Subring of opposite rings

For every ring `R`, we construct an equivalence between subrings of `R` and that of `Rᵐᵒᵖ`.

-/

namespace Subring

variable {ι : Sort*} {R : Type*} [Ring R]

/-- Pull a subring back to an opposite subring along `MulOpposite.unop` -/
@[simps toSubsemiring]
protected def op (S : Subring R) : Subring Rᵐᵒᵖ where
  toSubsemiring := S.toSubsemiring.op
  neg_mem' {x} hx := neg_mem (show x.unop ∈ S from hx)

@[simp, norm_cast]
theorem op_coe (S : Subring R) : S.op = MulOpposite.unop ⁻¹' (S : Set R) := rfl

@[simp]
theorem mem_op {x : Rᵐᵒᵖ} {S : Subring R} : x ∈ S.op ↔ x.unop ∈ S := Iff.rfl

/-- Pull an opposite subring back to a subring along `MulOpposite.op` -/
@[simps toSubsemiring]
protected def unop (S : Subring Rᵐᵒᵖ) : Subring R where
  toSubsemiring := S.toSubsemiring.unop
  neg_mem' {x} hx := neg_mem (show MulOpposite.op x ∈ S from hx)

@[simp, norm_cast]
theorem unop_coe (S : Subring Rᵐᵒᵖ) : S.unop = MulOpposite.op ⁻¹' (S : Set Rᵐᵒᵖ) := rfl

@[simp]
theorem mem_unop {x : R} {S : Subring Rᵐᵒᵖ} : x ∈ S.unop ↔ MulOpposite.op x ∈ S := Iff.rfl

@[simp]
theorem unop_op (S : Subring R) : S.op.unop = S := rfl

@[simp]
theorem op_unop (S : Subring Rᵐᵒᵖ) : S.unop.op = S := rfl

/-! ### Lattice results -/

theorem op_le_iff {S₁ : Subring R} {S₂ : Subring Rᵐᵒᵖ} : S₁.op ≤ S₂ ↔ S₁ ≤ S₂.unop :=
  MulOpposite.op_surjective.forall

theorem le_op_iff {S₁ : Subring Rᵐᵒᵖ} {S₂ : Subring R} : S₁ ≤ S₂.op ↔ S₁.unop ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[simp]
theorem op_le_op_iff {S₁ S₂ : Subring R} : S₁.op ≤ S₂.op ↔ S₁ ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[simp]
theorem unop_le_unop_iff {S₁ S₂ : Subring Rᵐᵒᵖ} : S₁.unop ≤ S₂.unop ↔ S₁ ≤ S₂ :=
  MulOpposite.unop_surjective.forall

/-- A subring `S` of `R` determines a subring `S.op` of the opposite ring `Rᵐᵒᵖ`. -/
@[simps]
def opEquiv : Subring R ≃o Subring Rᵐᵒᵖ where
  toFun := Subring.op
  invFun := Subring.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[simp]
theorem op_bot : (⊥ : Subring R).op = ⊥ := opEquiv.map_bot

@[simp]
theorem unop_bot : (⊥ : Subring Rᵐᵒᵖ).unop = ⊥ := opEquiv.symm.map_bot

@[simp]
theorem op_top : (⊤ : Subring R).op = ⊤ := opEquiv.map_top

@[simp]
theorem unop_top : (⊤ : Subring Rᵐᵒᵖ).unop = ⊤ := opEquiv.symm.map_top

theorem op_sup (S₁ S₂ : Subring R) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op :=
  opEquiv.map_sup _ _

theorem unop_sup (S₁ S₂ : Subring Rᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop :=
  opEquiv.symm.map_sup _ _

theorem op_inf (S₁ S₂ : Subring R) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := opEquiv.map_inf _ _

theorem unop_inf (S₁ S₂ : Subring Rᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop :=
  opEquiv.symm.map_inf _ _

theorem op_sSup (S : Set (Subring R)) : (sSup S).op = sSup (.unop ⁻¹' S) :=
  opEquiv.map_sSup_eq_sSup_symm_preimage _

theorem unop_sSup (S : Set (Subring Rᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) :=
  opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

theorem op_sInf (S : Set (Subring R)) : (sInf S).op = sInf (.unop ⁻¹' S) :=
  opEquiv.map_sInf_eq_sInf_symm_preimage _

theorem unop_sInf (S : Set (Subring Rᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) :=
  opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

theorem op_iSup (S : ι → Subring R) : (iSup S).op = ⨆ i, (S i).op := opEquiv.map_iSup _

theorem unop_iSup (S : ι → Subring Rᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop :=
  opEquiv.symm.map_iSup _

theorem op_iInf (S : ι → Subring R) : (iInf S).op = ⨅ i, (S i).op := opEquiv.map_iInf _

theorem unop_iInf (S : ι → Subring Rᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop :=
  opEquiv.symm.map_iInf _

theorem op_closure (s : Set R) : (closure s).op = closure (MulOpposite.unop ⁻¹' s) := by
  simp_rw [closure, op_sInf, Set.preimage_setOf_eq, unop_coe]
  congr with a
  exact MulOpposite.unop_surjective.forall

theorem unop_closure (s : Set Rᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by
  simp_rw [closure, unop_sInf, Set.preimage_setOf_eq, op_coe]
  congr with a
  exact MulOpposite.op_surjective.forall

/-- Bijection between a subring `S` and its opposite. -/
@[simps!]
def addEquivOp (S : Subring R) : S ≃+ S.op := S.toSubsemiring.addEquivOp

/-- Bijection between a subring `S` and `MulOpposite` of its opposite. -/
@[simps!]
def ringEquivOpMop (S : Subring R) : S ≃+* (S.op)ᵐᵒᵖ := S.toSubsemiring.ringEquivOpMop

/-- Bijection between `MulOpposite` of a subring `S` and its opposite. -/
@[simps!]
def mopRingEquivOp (S : Subring R) : Sᵐᵒᵖ ≃+* S.op := S.toSubsemiring.mopRingEquivOp

end Subring
