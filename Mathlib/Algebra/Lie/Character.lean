/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.Solvable
import Mathlib.LinearAlgebra.Dual

#align_import algebra.lie.character from "leanprover-community/mathlib"@"132328c4dd48da87adca5d408ca54f315282b719"

/-!
# Characters of Lie algebras

A character of a Lie algebra `L` over a commutative ring `R` is a morphism of Lie algebras `L → R`,
where `R` is regarded as a Lie algebra over itself via the ring commutator. For an Abelian Lie
algebra (e.g., a Cartan subalgebra of a semisimple Lie algebra) a character is just a linear form.

## Main definitions

  * `LieAlgebra.LieCharacter`
  * `LieAlgebra.lieCharacterEquivLinearDual`

## Tags

lie algebra, lie character
-/


universe u v w w₁

namespace LieAlgebra

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A character of a Lie algebra is a morphism to the scalars. -/
abbrev LieCharacter :=
  L →ₗ⁅R⁆ R
#align lie_algebra.lie_character LieAlgebra.LieCharacter

variable {R L}

-- @[simp] -- Porting note: simp normal form is the LHS of `lieCharacter_apply_lie'`
theorem lieCharacter_apply_lie (χ : LieCharacter R L) (x y : L) : χ ⁅x, y⁆ = 0 := by
  rw [LieHom.map_lie, LieRing.of_associative_ring_bracket, mul_comm, sub_self]
#align lie_algebra.lie_character_apply_lie LieAlgebra.lieCharacter_apply_lie

@[simp]
theorem lieCharacter_apply_lie' (χ : LieCharacter R L) (x y : L) : ⁅χ x, χ y⁆ = 0 := by
  rw [LieRing.of_associative_ring_bracket, mul_comm, sub_self]

theorem lieCharacter_apply_of_mem_derived (χ : LieCharacter R L) {x : L}
    (h : x ∈ derivedSeries R L 1) : χ x = 0 := by
  rw [derivedSeries_def, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero, ←
    LieSubmodule.mem_coeSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span] at h
  refine Submodule.span_induction h ?_ ?_ ?_ ?_
  · rintro y ⟨⟨z, hz⟩, ⟨⟨w, hw⟩, rfl⟩⟩; apply lieCharacter_apply_lie
  · exact χ.map_zero
  · intro y z hy hz; rw [LieHom.map_add, hy, hz, add_zero]
  · intro t y hy; rw [LieHom.map_smul, hy, smul_zero]
#align lie_algebra.lie_character_apply_of_mem_derived LieAlgebra.lieCharacter_apply_of_mem_derived

/-- For an Abelian Lie algebra, characters are just linear forms. -/
@[simps! apply symm_apply]
def lieCharacterEquivLinearDual [IsLieAbelian L] : LieCharacter R L ≃ Module.Dual R L where
  toFun χ := (χ : L →ₗ[R] R)
  invFun ψ :=
    { ψ with
      map_lie' := fun {x y} => by
        rw [LieModule.IsTrivial.trivial, LieRing.of_associative_ring_bracket, mul_comm, sub_self,
          LinearMap.toFun_eq_coe, LinearMap.map_zero] }
  left_inv χ := by ext; rfl
  right_inv ψ := by ext; rfl
#align lie_algebra.lie_character_equiv_linear_dual LieAlgebra.lieCharacterEquivLinearDual

end LieAlgebra
