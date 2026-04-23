/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Order.BoundedOrder.Lattice
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Semisimple operators on inner product spaces

This file is a place to gather results related to semisimplicity of linear operators on inner
product spaces.

-/

public section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace LinearMap.IsSymmetric

variable {T : Module.End 𝕜 E} {p : Submodule 𝕜 E} (hT : T.IsSymmetric)

include hT

/-- The orthogonal complement of an invariant submodule is invariant. -/
lemma orthogonalComplement_mem_invtSubmodule (hp : p ∈ T.invtSubmodule) :
    pᗮ ∈ T.invtSubmodule :=
  fun x hx y hy ↦ hT y x ▸ hx (T y) (hp hy)

/-- Symmetric operators are semisimple on finite-dimensional subspaces. -/
theorem isFinitelySemisimple :
    T.IsFinitelySemisimple := by
  refine Module.End.isFinitelySemisimple_iff.mpr fun p hp₁ hp₂ q hq₁ hq₂ ↦
    ⟨qᗮ ⊓ p, inf_le_right, Module.End.invtSubmodule.inf_mem ?_ hp₁, ?_, ?_⟩
  · exact orthogonalComplement_mem_invtSubmodule hT hq₁
  · simp [disjoint_iff, ← inf_assoc, Submodule.inf_orthogonal_eq_bot q]
  · suffices q ⊔ qᗮ = ⊤ by rw [← sup_inf_assoc_of_le _ hq₂, this, top_inf_eq p]
    replace hp₂ : Module.Finite 𝕜 q := Submodule.finiteDimensional_of_le hq₂
    exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

end LinearMap.IsSymmetric
