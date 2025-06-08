/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Ring.Subring.MulOpposite

/-!

# Subalgebras of opposite rings

For every ring `A` over a commutative ring `R`, we construct an equivalence between
subalgebras of `A / R` and that of `Aᵐᵒᵖ / R`.

-/

namespace Subalgebra

section Semiring

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- Pull a subalgebra back to an opposite subalgebra along `MulOpposite.unop` -/
@[simps! coe toSubsemiring]
protected def op (S : Subalgebra R A) : Subalgebra R Aᵐᵒᵖ where
  toSubsemiring := S.toSubsemiring.op
  algebraMap_mem' := S.algebraMap_mem

attribute [norm_cast] coe_op

@[simp]
theorem mem_op {x : Aᵐᵒᵖ} {S : Subalgebra R A} : x ∈ S.op ↔ x.unop ∈ S := Iff.rfl

/-- Pull an subalgebra subring back to a subalgebra along `MulOpposite.op` -/
@[simps! coe toSubsemiring]
protected def unop (S : Subalgebra R Aᵐᵒᵖ) : Subalgebra R A where
  toSubsemiring := S.toSubsemiring.unop
  algebraMap_mem' := S.algebraMap_mem

attribute [norm_cast] coe_unop

@[simp]
theorem mem_unop {x : A} {S : Subalgebra R Aᵐᵒᵖ} : x ∈ S.unop ↔ MulOpposite.op x ∈ S := Iff.rfl

@[simp]
theorem unop_op (S : Subalgebra R A) : S.op.unop = S := rfl

@[simp]
theorem op_unop (S : Subalgebra R Aᵐᵒᵖ) : S.unop.op = S := rfl

/-! ### Lattice results -/

theorem op_le_iff {S₁ : Subalgebra R A} {S₂ : Subalgebra R Aᵐᵒᵖ} : S₁.op ≤ S₂ ↔ S₁ ≤ S₂.unop :=
  MulOpposite.op_surjective.forall

theorem le_op_iff {S₁ : Subalgebra R Aᵐᵒᵖ} {S₂ : Subalgebra R A} : S₁ ≤ S₂.op ↔ S₁.unop ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[simp]
theorem op_le_op_iff {S₁ S₂ : Subalgebra R A} : S₁.op ≤ S₂.op ↔ S₁ ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[simp]
theorem unop_le_unop_iff {S₁ S₂ : Subalgebra R Aᵐᵒᵖ} : S₁.unop ≤ S₂.unop ↔ S₁ ≤ S₂ :=
  MulOpposite.unop_surjective.forall

/-- A subalgebra `S` of `A / R` determines a subring `S.op` of the opposite ring `Aᵐᵒᵖ / R`. -/
@[simps]
def opEquiv : Subalgebra R A ≃o Subalgebra R Aᵐᵒᵖ where
  toFun := Subalgebra.op
  invFun := Subalgebra.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[simp]
theorem op_bot : (⊥ : Subalgebra R A).op = ⊥ := opEquiv.map_bot

@[simp]
theorem unop_bot : (⊥ : Subalgebra R Aᵐᵒᵖ).unop = ⊥ := opEquiv.symm.map_bot

@[simp]
theorem op_top : (⊤ : Subalgebra R A).op = ⊤ := opEquiv.map_top

@[simp]
theorem unop_top : (⊤ : Subalgebra R Aᵐᵒᵖ).unop = ⊤ := opEquiv.symm.map_top

theorem op_sup (S₁ S₂ : Subalgebra R A) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op :=
  opEquiv.map_sup _ _

theorem unop_sup (S₁ S₂ : Subalgebra R Aᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop :=
  opEquiv.symm.map_sup _ _

theorem op_inf (S₁ S₂ : Subalgebra R A) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := opEquiv.map_inf _ _

theorem unop_inf (S₁ S₂ : Subalgebra R Aᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop :=
  opEquiv.symm.map_inf _ _

theorem op_sSup (S : Set (Subalgebra R A)) : (sSup S).op = sSup (.unop ⁻¹' S) :=
  opEquiv.map_sSup_eq_sSup_symm_preimage _

theorem unop_sSup (S : Set (Subalgebra R Aᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) :=
  opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

theorem op_sInf (S : Set (Subalgebra R A)) : (sInf S).op = sInf (.unop ⁻¹' S) :=
  opEquiv.map_sInf_eq_sInf_symm_preimage _

theorem unop_sInf (S : Set (Subalgebra R Aᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) :=
  opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

theorem op_iSup (S : ι → Subalgebra R A) : (iSup S).op = ⨆ i, (S i).op := opEquiv.map_iSup _

theorem unop_iSup (S : ι → Subalgebra R Aᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop :=
  opEquiv.symm.map_iSup _

theorem op_iInf (S : ι → Subalgebra R A) : (iInf S).op = ⨅ i, (S i).op := opEquiv.map_iInf _

theorem unop_iInf (S : ι → Subalgebra R Aᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop :=
  opEquiv.symm.map_iInf _

theorem op_adjoin (s : Set A) :
    (Algebra.adjoin R s).op = Algebra.adjoin R (MulOpposite.unop ⁻¹' s) := by
  apply toSubsemiring_injective
  simp_rw [Algebra.adjoin, op_toSubsemiring, Subsemiring.op_closure, Set.preimage_union]
  congr with x
  simp_rw [Set.mem_preimage, Set.mem_range, MulOpposite.algebraMap_apply]
  congr!
  rw [← MulOpposite.op_injective.eq_iff (b := x.unop), MulOpposite.op_unop]

theorem unop_adjoin (s : Set Aᵐᵒᵖ) :
    (Algebra.adjoin R s).unop = Algebra.adjoin R (MulOpposite.op ⁻¹' s) := by
  apply toSubsemiring_injective
  simp_rw [Algebra.adjoin, unop_toSubsemiring, Subsemiring.unop_closure, Set.preimage_union]
  congr with x
  simp

/-- Bijection between a subalgebra `S` and its opposite. -/
@[simps!]
def linearEquivOp (S : Subalgebra R A) : S ≃ₗ[R] S.op where
  __ := S.toSubsemiring.addEquivOp
  map_smul' _ _ := rfl

/-- Bijection between a subalgebra `S` and `MulOpposite` of its opposite. -/
@[simps!]
def algEquivOpMop (S : Subalgebra R A) : S ≃ₐ[R] (S.op)ᵐᵒᵖ where
  __ := S.toSubsemiring.ringEquivOpMop
  commutes' _ := rfl

/-- Bijection between `MulOpposite` of a subalgebra `S` and its opposite. -/
@[simps!]
def mopAlgEquivOp (S : Subalgebra R A) : Sᵐᵒᵖ ≃ₐ[R] S.op where
  __ := S.toSubsemiring.mopRingEquivOp
  commutes' _ := rfl

end Semiring

section Ring

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

@[simp]
theorem op_toSubring (S : Subalgebra R A) : S.op.toSubring = S.toSubring.op := rfl

@[simp]
theorem unop_toSubring (S : Subalgebra R Aᵐᵒᵖ) : S.unop.toSubring = S.toSubring.unop := rfl

end Ring

end Subalgebra
