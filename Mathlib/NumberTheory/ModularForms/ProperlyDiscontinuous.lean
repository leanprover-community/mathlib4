/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Group.DiscontinuousSubgroup

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
