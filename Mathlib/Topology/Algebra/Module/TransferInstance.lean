/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Algebra.Module.Shrink
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Instances.Shrink
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Transfer topological algebraic structures across `Equiv`s

In this file, we construct a continuous linear equivalence `α ≃L[R] β` from an equivalence `α ≃ β`,
where the continuous `R`-module structure on `α` is the one obtained by transporting an
`R`-module structure on `β` back along `e`.
We also specialize this construction to `Shrink α`.

This continues the pattern set in `Mathlib/Algebra/Module/TransferInstance.lean`.
-/

@[expose] public section

variable {R α β : Type*}

namespace Equiv

variable (e : α ≃ β)

variable [TopologicalSpace β] [AddCommMonoid β] [Semiring R] [Module R β]

variable (R) in
/-- An equivalence `e : α ≃ β` gives a continuous linear equivalence `α ≃L[R] β`
where the continuous `R`-module structure on `α` is the one obtained by transporting an
`R`-module structure on `β` back along `e`.

This is `e.linearEquiv` as a continuous linear equivalence. -/
def continuousLinearEquiv (e : α ≃ β) :
    letI := e.topologicalSpace
    letI := e.addCommMonoid
    letI := e.module R
    α ≃L[R] β :=
  letI := e.topologicalSpace
  letI := e.addCommMonoid
  letI := e.module R
  { toLinearEquiv := e.linearEquiv _
    continuous_toFun := continuous_induced_dom
    continuous_invFun := by
      simp +instances only [Equiv.topologicalSpace, ← @coinduced_symm]
      exact continuous_coinduced_rng }

@[simp]
lemma toLinearEquiv_continuousLinearEquiv (e : α ≃ β) :
    letI := e.topologicalSpace
    letI := e.addCommMonoid
    letI := e.module R
    (e.continuousLinearEquiv R).toLinearEquiv = e.linearEquiv R := rfl

end Equiv

section ContinuousLinearEquiv

variable [Semiring R]

/-- Given a continuous additive equivalence `e : α ≃ₜ+ β`, if `β` is a topological additive group,
then so is `α`. -/
@[to_additive]
lemma ContinuousMulEquiv.isTopologicalGroup
    [TopologicalSpace β] [Group β] [IsTopologicalGroup β] [TopologicalSpace α] [Group α]
    (e : α ≃ₜ* β) : IsTopologicalGroup α where
  continuous_mul := by
    let f := (fun q ↦ q.1 * q.2 : β × β → β)
    have : Continuous (fun p ↦ e.symm <| f (e p.1, e p.2) : (α × α → α)) := by fun_prop
    exact this.congr <| fun p ↦ by simp [f]
  continuous_inv := by
    have : Continuous (e.symm ∘ (fun q ↦ q⁻¹) ∘ e) := by fun_prop
    exact this.congr (fun p ↦ by simp)

/-- Given a continuous linear equivalence `e : α ≃L[R] β`, if scalar multiplication on `β` is
continuous, then so is it for `α`. -/
lemma ContinuousLinearEquiv.continuousSMul
    [TopologicalSpace β] [AddCommGroup β] [Module R β] [TopologicalSpace R] [ContinuousSMul R β]
    [TopologicalSpace α] [AddCommGroup α] [Module R α]
    (e : α ≃L[R] β) :
    ContinuousSMul R α where
  continuous_smul := by
    let f : R × α → α := fun p ↦ e.symm <| p.1 • (e p.2)
    have : Continuous f := by fun_prop
    exact this.congr (fun p ↦ by simp [f])

end ContinuousLinearEquiv

universe v

variable (R α) in
/-- Shrinking `α` to a smaller universe preserves the continuous module structure. -/
@[simps!]
noncomputable def Shrink.continuousLinearEquiv
    [Small.{v} α] [AddCommMonoid α] [TopologicalSpace α] [Semiring R] [Module R α] :
    Shrink.{v} α ≃L[R] α :=
  (equivShrink α).symm.continuousLinearEquiv R
