/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.group_ring_action.invariant
! leanprover-community/mathlib commit e7bab9a85e92cf46c02cb4725a7be2f04691e3a7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.GroupAction
import Mathbin.RingTheory.Subring.Pointwise

/-! # Subrings invariant under an action -/


section Ring

variable (M R : Type _) [Monoid M] [Ring R] [MulSemiringAction M R]

variable (S : Subring R)

open MulAction

variable {R}

/-- A typeclass for subrings invariant under a `mul_semiring_action`. -/
class IsInvariantSubring : Prop where
  smul_mem : ∀ (m : M) {x : R}, x ∈ S → m • x ∈ S
#align is_invariant_subring IsInvariantSubring

instance IsInvariantSubring.toMulSemiringAction [IsInvariantSubring M S] : MulSemiringAction M S
    where
  smul m x := ⟨m • x, IsInvariantSubring.smul_mem m x.2⟩
  one_smul s := Subtype.eq <| one_smul M s
  mul_smul m₁ m₂ s := Subtype.eq <| mul_smul m₁ m₂ s
  smul_add m s₁ s₂ := Subtype.eq <| smul_add m s₁ s₂
  smul_zero m := Subtype.eq <| smul_zero m
  smul_one m := Subtype.eq <| smul_one m
  smul_mul m s₁ s₂ := Subtype.eq <| smul_mul' m s₁ s₂
#align is_invariant_subring.to_mul_semiring_action IsInvariantSubring.toMulSemiringAction

end Ring

section

variable (M : Type _) [Monoid M]

variable {R' : Type _} [Ring R'] [MulSemiringAction M R']

variable (U : Subring R') [IsInvariantSubring M U]

/-- The canonical inclusion from an invariant subring. -/
def IsInvariantSubring.subtypeHom : U →+*[M] R' :=
  { U.Subtype with map_smul' := fun m s => rfl }
#align is_invariant_subring.subtype_hom IsInvariantSubring.subtypeHom

@[simp]
theorem IsInvariantSubring.coeSubtype_hom : (IsInvariantSubring.subtypeHom M U : U → R') = coe :=
  rfl
#align is_invariant_subring.coe_subtype_hom IsInvariantSubring.coeSubtype_hom

@[simp]
theorem IsInvariantSubring.coe_subtype_hom' :
    (IsInvariantSubring.subtypeHom M U : U →+* R') = U.Subtype :=
  rfl
#align is_invariant_subring.coe_subtype_hom' IsInvariantSubring.coe_subtype_hom'

end

