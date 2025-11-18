/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Algebra.Ring.Subring.Defs

/-! # Subrings invariant under an action

If a monoid acts on a ring via a `MulSemiringAction`, then `IsInvariantSubring` is
a predicate on subrings asserting that the subring is fixed elementwise by the
action.

-/

assert_not_exists RelIso

section Ring

variable (M R : Type*) [Monoid M] [Ring R] [MulSemiringAction M R]
variable (S : Subring R)

open MulAction

variable {R}

/-- A typeclass for subrings invariant under a `MulSemiringAction`. -/
class IsInvariantSubring : Prop where
  smul_mem : ∀ (m : M) {x : R}, x ∈ S → m • x ∈ S

instance IsInvariantSubring.toMulSemiringAction [IsInvariantSubring M S] :
    MulSemiringAction M S where
  smul m x := ⟨m • ↑x, IsInvariantSubring.smul_mem m x.2⟩
  one_smul s := Subtype.ext <| one_smul M (s : R)
  mul_smul m₁ m₂ s := Subtype.ext <| mul_smul m₁ m₂ (s : R)
  smul_add m s₁ s₂ := Subtype.ext <| smul_add m (s₁ : R) (s₂ : R)
  smul_zero m := Subtype.ext <| smul_zero m
  smul_one m := Subtype.ext <| smul_one m
  smul_mul m s₁ s₂ := Subtype.ext <| smul_mul' m (s₁ : R) (s₂ : R)

end Ring

section

variable (M : Type*) [Monoid M]
variable {R' : Type*} [Ring R'] [MulSemiringAction M R']
variable (U : Subring R') [IsInvariantSubring M U]

/-- The canonical inclusion from an invariant subring. -/
def IsInvariantSubring.subtypeHom : U →+*[M] R' :=
  { U.subtype with map_smul' := fun _ _ ↦ rfl }

@[simp]
theorem IsInvariantSubring.coe_subtypeHom :
    (IsInvariantSubring.subtypeHom M U : U → R') = Subtype.val := rfl

@[simp]
theorem IsInvariantSubring.coe_subtypeHom' :
    ((IsInvariantSubring.subtypeHom M U) : U →+* R') = U.subtype := rfl

end
