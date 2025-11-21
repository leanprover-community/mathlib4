/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Transfer algebraic structures across `Equiv`s

In this file, we transfer a topological space and continuous linear equivalence structure
across an equivalence.
This continues the pattern set in `Mathlib/Algebra/Normed/Module/TransferInstance.lean`.
-/

@[expose] public section

variable {R α β : Type*}

namespace Equiv

variable (e : α ≃ β)

-- XXX: will this cause diamonds with the metric space instance above?
/-- Transfer a `TopologicalSpace` across an `Equiv` -/
protected abbrev topologicalSpace (e : α ≃ β) : ∀ [TopologicalSpace β], TopologicalSpace α := by
  intros
  exact {
    -- Is there a more elegant construction?
    IsOpen s := IsOpen (e.symm ⁻¹' s)
    isOpen_univ := by simp
    isOpen_inter s t hs ht := by simpa using hs.inter ht
    isOpen_sUnion S hS := by simpa using isOpen_biUnion hS
  }

variable [TopologicalSpace β] [AddCommMonoid β] [Semiring R] [Module R β]

-- XXX: using `letI` make TC synthesis in the proof fail, but the current proof term is not nice
-- What's the best way to solve this?
variable (R) in
/-- An equivalence `e : α ≃ β` gives a continuous linear equivalence `α ≃L[R] β`
where the continuous `R`-module structure on `α` is the one obtained by transporting an
`R`-module structure on `β` back along `e`.

This is `e.linearEquiv` as a continuous linear equivalence. -/
def continuousLinearEquiv (e : α ≃ β) :
    let _ := e.topologicalSpace
    let _ := e.addCommMonoid
    let _ := e.module R
    α ≃L[R] β := by
  intros
  exact {
    toLinearEquiv := e.linearEquiv R
    continuous_toFun := by
      rw [continuous_def]
      intro t ht
      have : IsOpen (e.symm ⁻¹' (e ⁻¹' t)) := by convert ht; simp
      exact this
    continuous_invFun := by
      rw [continuous_def]
      exact fun s hs ↦ hs
  }

@[simp]
lemma continuousLinearEquiv_toLinearEquiv (e : α ≃ β) :
    let _ := e.topologicalSpace
    let _ := e.addCommMonoid
    let _ := e.module R
    (e.continuousLinearEquiv R).toLinearEquiv = e.linearEquiv R := by rfl

end Equiv
