/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Field.Defs

/-!
# Ordered vector spaces
-/

open OrderDual

variable {𝕜 G : Type*}

section LinearOrderedSemifield
variable [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup G] [PartialOrder G]

-- See note [lower instance priority]
instance (priority := 100) PosSMulMono.toPosSMulReflectLE [MulAction 𝕜 G] [PosSMulMono 𝕜 G] :
    PosSMulReflectLE 𝕜 G where
  elim _a ha b₁ b₂ h := by
    simpa [ha.ne'] using smul_le_smul_of_nonneg_left h <| inv_nonneg.2 ha.le

-- See note [lower instance priority]
instance (priority := 100) PosSMulStrictMono.toPosSMulReflectLT [MulActionWithZero 𝕜 G]
    [PosSMulStrictMono 𝕜 G] : PosSMulReflectLT 𝕜 G :=
  PosSMulReflectLT.of_pos fun a ha b₁ b₂ h ↦ by
    simpa [ha.ne'] using smul_lt_smul_of_pos_left h <| inv_pos.2 ha

end LinearOrderedSemifield

section Field
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G] [Module 𝕜 G] {a : 𝕜} {b₁ b₂ : G}

section PosSMulMono
variable [PosSMulMono 𝕜 G]

lemma inv_smul_le_iff_of_neg (h : a < 0) : a⁻¹ • b₁ ≤ b₂ ↔ a • b₂ ≤ b₁ := by
  rw [← smul_le_smul_iff_of_neg_left h, smul_inv_smul₀ h.ne]

lemma smul_inv_le_iff_of_neg (h : a < 0) : b₁ ≤ a⁻¹ • b₂ ↔ b₂ ≤ a • b₁ := by
  rw [← smul_le_smul_iff_of_neg_left h, smul_inv_smul₀ h.ne]

variable (G)

/-- Left scalar multiplication as an order isomorphism. -/
@[simps!]
def OrderIso.smulRightDual (ha : a < 0) : G ≃o Gᵒᵈ where
  toEquiv := (Equiv.smulRight ha.ne).trans toDual
  map_rel_iff' := (@OrderDual.toDual_le_toDual G).trans <| smul_le_smul_iff_of_neg_left ha

end PosSMulMono

variable [PosSMulStrictMono 𝕜 G]

lemma inv_smul_lt_iff_of_neg (h : a < 0) : a⁻¹ • b₁ < b₂ ↔ a • b₂ < b₁ := by
  rw [← smul_lt_smul_iff_of_neg_left h, smul_inv_smul₀ h.ne]

lemma smul_inv_lt_iff_of_neg (h : a < 0) : b₁ < a⁻¹ • b₂ ↔ b₂ < a • b₁ := by
  rw [← smul_lt_smul_iff_of_neg_left h, smul_inv_smul₀ h.ne]

end Field
