/-
Copyright (c) 2025 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Oliver Nash
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
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
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!

# One-point compactification of Euclidean space is homeomorphic to the sphere.

-/

@[expose] public section

open Function Metric Module Set Submodule

noncomputable section

/-- A homeomorphism from the one-point compactification of a hyperplane in Euclidean space to the
sphere. -/
def onePointHyperplaneHomeoUnitSphere
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {v : E} (hv : ‖v‖ = 1) :
    OnePoint (ℝ ∙ v)ᗮ ≃ₜ sphere (0 : E) 1 :=
  OnePoint.equivOfIsEmbeddingOfRangeEq _ _
    (isOpenEmbedding_stereographic_symm hv).toIsEmbedding (range_stereographic_symm hv)

/-- A homeomorphism from the one-point compactification of a finite-dimensional real vector space to
the sphere. -/
def onePointEquivSphereOfFinrankEq {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    (h : finrank ℝ V + 1 = Fintype.card ι) :
    OnePoint V ≃ₜ sphere (0 : EuclideanSpace ℝ ι) 1 := by
  classical
  have : Nonempty ι := Fintype.card_pos_iff.mp <| by lia
  let v : EuclideanSpace ℝ ι := .single (Classical.arbitrary ι) 1
  have hv : ‖v‖ = 1 := by simp [v]
  have hv₀ : v ≠ 0 := fun contra ↦ by simp [contra] at hv
  have : Fact (finrank ℝ (EuclideanSpace ℝ ι) = finrank ℝ V + 1) := ⟨by simp [h]⟩
  have hV : finrank ℝ V = finrank ℝ (ℝ ∙ v)ᗮ := (finrank_orthogonal_span_singleton hv₀).symm
  letI e : V ≃ₜ (ℝ ∙ v)ᗮ := (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq hV).some
  exact e.onePointCongr.trans <| onePointHyperplaneHomeoUnitSphere hv
