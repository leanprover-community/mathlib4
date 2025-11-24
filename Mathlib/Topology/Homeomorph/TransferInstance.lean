/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Topology.Homeomorph.Defs

/-!
# Transfer topological structure across `Equiv`s

We show that transferring a topological space structure across an `Equiv` yields a homeomorphism
between the original space and the transported topology.

-/

@[expose] public section

variable {R α β : Type*}

namespace Equiv

variable [TopologicalSpace β]
/-- An equivalence `e : α ≃ β` gives a homeomorphism `α ≃ₜ β` where the topological space structure
on `α` is the one obtained by transporting the topological space structure on `β` back along `e`. -/
def homeomorph (e : α ≃ β) [TopologicalSpace β] :
    letI := e.topologicalSpace
    α ≃ₜ β :=
  letI := e.topologicalSpace
  { e with
    continuous_toFun := continuous_induced_dom
    continuous_invFun := by
      -- was: convert continuous_coinduced_rng; exact e.coinduced_symm.symm, TODO fix!
      sorry }

end Equiv
