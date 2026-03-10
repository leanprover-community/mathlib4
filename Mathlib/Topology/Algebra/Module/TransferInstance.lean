/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Algebra.Module.Shrink
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Instances.Shrink
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.MetricSpace.Bounded

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

/-- Given a continuous linear equivalence `e : α ≃L[R] β`, if `β` is a topological additive group,
then so is `α`. -/
@[implicit_reducible]
def ContinuousLinearEquiv.IsTopologicalAddGroup
    [TopologicalSpace β] [AddCommGroup β] [IsTopologicalAddGroup β] [Module R β]
    [TopologicalSpace α] [AddCommGroup α] [Module R α]
    (e : α ≃L[R] β) : IsTopologicalAddGroup α where
  continuous_add := by
    let f := (fun q ↦ q.1 + q.2 : β × β → β)
    have : Continuous (fun p ↦ e.symm <| f (e p.1, e p.2) : (α × α → α)) := by fun_prop
    exact this.congr <| fun p ↦ by simp [f]
  continuous_neg := by
    have : Continuous (e.symm ∘ (fun q ↦ -q) ∘ e) := by fun_prop
    exact this.congr (fun p ↦ by simp)

/- TODO: should there be the following version instead, deducing the instances for α
-- from the ones for β? Currently, the statement errors for reasons I don't understand yet.
def Equiv.IsTopologicalAddGroup
    [TopologicalSpace β] [AddCommGroup β] [IsTopologicalAddGroup β] [Module R β]
    (e : α ≃ β) :
    letI := e.topologicalSpace
    letI := e.addCommGroup
    letI := e.module R
    IsTopologicalAddGroup α where
  continuous_add := by
    let f := (fun q ↦ q.1 + q.2 : β × β → β)
    have : Continuous (fun p ↦ e.symm <| f (e p.1, e p.2) : (α × α → α)) := by fun_prop
    exact this.congr <| fun p ↦ by simp [f]
  continuous_neg := by
    have : Continuous (e.symm ∘ (fun q ↦ -q) ∘ e) := by fun_prop
    exact this.congr (fun p ↦ by simp)
-/

-- TODO: should the instances for α be deduced from the ones for β?
/-- Given a continuous linear equivalence `e : α ≃L[R] β`, if scalar multiplication on `β` is
continuous, then so is it for `α`. -/
@[implicit_reducible]
def ContinuousLinearEquiv.continuousSMul
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
