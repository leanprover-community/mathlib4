import Mathlib.GroupTheory.QuotientGroup

open Set

open scoped Pointwise

variable (G : Type _) [Group G] (Γ : Subgroup G) [Subgroup.Normal Γ]

theorem QuotientGroup.sound [Subgroup.Normal Γ] (U : Set (G ⧸ Γ)) (g : (Subgroup.opposite Γ)) :
    g • (QuotientGroup.mk' Γ) ⁻¹' U = (QuotientGroup.mk' Γ) ⁻¹' U := by
  rw [QuotientGroup.coe_mk']
  ext x
  simp only [mem_preimage]
  have := @Set.mem_inv_smul_set_iff (x := x) (A := (mk' Γ) ⁻¹' U) (a := g⁻¹) _ _
  simp only [inv_inv, coe_mk', mem_preimage] at this
  convert this using 2
  apply @Quotient.sound (a := x) (s := (QuotientGroup.leftRel Γ)) (b := g⁻¹ • x)
  use g
  simp
