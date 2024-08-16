/-
Copyright (c) 2024 Lucas Whitfield. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Whitfield
-/
import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Lie.AltWeights

/-!
# Lie's theorem for Solvable Lie algebras.

Lie's theorem asserts that Lie modules of solvable Lie algebras over fields of characteristic 0
have a common eigenvector for the action of all elements of the Lie algebra.
This result is named `LieModule.exists_forall_lie_eq_smul_of_Solvable`.
-/

section

variable {k : Type*} [Field k]
variable {L : Type*} [LieRing L] [LieAlgebra k L]
variable {V : Type*} [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]
variable [CharZero k] [Module.Finite k V]

open LieAlgebra

-- This lemma is the central inductive argument in the proof of Lie's theorem below.
-- The statement is identical to `LieModule.exists_forall_lie_eq_smul_of_isSolvable`
-- except that it additionally assumes a finiteness hypothesis.
private lemma LieModule.exists_forall_lie_eq_smul_of_isSolvable_of_finite [Nontrivial V]
    (L : Type*) [LieRing L] [LieAlgebra k L] [LieRingModule L V] [LieModule k L V]
    [IsSolvable k L] [LieModule.IsTriangularizable k L V] [Module.Finite k L] :
    ∃ χ : Module.Dual k L, ∃ v : V, v ≠ 0 ∧ ∀ x : L, ⁅x, v⁆ = χ x • v := by
  obtain H|⟨A, hA, hAL⟩ := eq_top_or_exists_le_coatom (derivedSeries k L 1).toSubmodule
  · obtain _inst|_inst := subsingleton_or_nontrivial L
    · use 0
      simpa using exists_ne _
    · rw [LieSubmodule.coeSubmodule_eq_top_iff] at H
      exact ((derivedSeries_lt_top_of_solvable k L).ne H).elim
  lift A to LieIdeal k L
  · intros
    exact hAL <| LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _)
  change LieIdeal k L at A -- remove this line when bug in `lift` is fixed (#15865)
  obtain ⟨χ', v, hv, hvA⟩ := exists_forall_lie_eq_smul_of_isSolvable_of_finite A
  exact extend_weight A hA χ' v hv hvA
termination_by FiniteDimensional.finrank k L
decreasing_by
  simp_wf
  rw [← finrank_top k L]
  apply Submodule.finrank_lt_finrank_of_lt
  exact hA.lt_top

local notation "π" => LieModule.toEnd k L V

-- If `L` is solvable, we can find a non-zero eigenvector
theorem LieModule.exists_forall_lie_eq_smul_of_isSolvable [Nontrivial V]
    [IsSolvable k L] [LieModule.IsTriangularizable k L V] :
    ∃ χ : Module.Dual k L, ∃ v : V, v ≠ 0 ∧ ∀ x : L, ⁅x, v⁆ = χ x • v := by
  let imL := (π).range
  have hdim : FiniteDimensional k imL := Submodule.finiteDimensional_of_le (le_top)
  suffices h : ∃ χ : Module.Dual k imL, ∃ v : V, v ≠ 0 ∧ ∀ x : imL, ⁅x, v⁆ = χ x • v by
    rcases h with ⟨χ', v, hv, hχ'⟩
    let toEndo : L →ₗ[k] imL := LinearMap.codRestrict imL.toSubmodule π
        (fun x ↦ LinearMap.mem_range.mpr ⟨x, rfl⟩ : ∀ x : L, π x ∈ imL)
    use χ'.comp toEndo, v, hv
    intro x
    have : ⁅x, v⁆ = ⁅toEndo x, v⁆ := rfl
    rw [LinearMap.comp_apply, this, hχ' (toEndo x)]
  have : IsSolvable k imL := LieHom.isSolvable_range π
  apply exists_forall_lie_eq_smul_of_isSolvable_of_finite (L := imL)

end

