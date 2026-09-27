/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
public import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
public import Mathlib.Topology.Algebra.Group.DiscontinuousSubgroup

/-!
# Arithmetic subgroups act properly discontinuously
-/

public section

open Matrix

open scoped MatrixGroups UpperHalfPlane

instance properlyDiscontinuousSL2ZRange : ProperlyDiscontinuousSMul 𝒮ℒ ℍ := by
  let 𝒮ℒ' : Subgroup SL(2, ℝ) := (SpecialLinearGroup.map (Int.castRingHom ℝ)).range
  have : ProperlyDiscontinuousSMul 𝒮ℒ' ℍ := inferInstance
  simp only [Subgroup.properlyDiscontinuousSMul_iff] at this ⊢
  refine fun K L hK hL ↦ ((this hK hL).map SpecialLinearGroup.toGL).subset fun g ↦ ?_
  rintro ⟨⟨γ, rfl⟩, hγ⟩
  exact ⟨γ, ⟨by simp [𝒮ℒ'], hγ⟩, rfl⟩

/-- Arithmetic subgroups of `GL(2, ℝ)` act properly discontinuously on `ℍ`. -/
instance Subgroup.IsArithmetic.properlyDiscontinuous {𝒢 : Subgroup (GL (Fin 2) ℝ)}
    [IsArithmetic 𝒢] : ProperlyDiscontinuousSMul 𝒢 ℍ := by
  rw [is_commensurable.properlyDiscontinuousSMul_iff]
  infer_instance

end
