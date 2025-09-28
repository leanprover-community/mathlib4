/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.CompHausLike.Limits
import Mathlib.Topology.Category.LightProfinite.Basic
/-!

# Explicit limits and colimits

This file applies the general API for explicit limits and colimits in `CompHausLike P` (see
the file `Mathlib/Topology/Category/CompHausLike/Limits.lean`) to the special case of
`LightProfinite`.
-/

namespace LightProfinite

universe u w

open CategoryTheory Limits CompHausLike

instance : HasExplicitPullbacks
    (fun Y ↦ TotallyDisconnectedSpace Y ∧ SecondCountableTopology Y) where
  hasProp _ _ := {
    hasProp := ⟨show TotallyDisconnectedSpace {_xy : _ | _} from inferInstance,
      show SecondCountableTopology {_xy : _ | _} from inferInstance⟩ }

instance : HasExplicitFiniteCoproducts.{w, u}
    (fun Y ↦ TotallyDisconnectedSpace Y ∧ SecondCountableTopology Y) where
  hasProp _ := { hasProp :=
    ⟨show TotallyDisconnectedSpace (Σ (_a : _), _) from inferInstance,
      show SecondCountableTopology (Σ (_a : _), _) from inferInstance⟩ }

/-- A one-element space is terminal in `Profinite` -/
abbrev isTerminalPUnit : IsTerminal (LightProfinite.of PUnit.{u + 1}) :=
  CompHausLike.isTerminalPUnit

example : FinitaryExtensive LightProfinite.{u} := inferInstance

noncomputable example : PreservesFiniteCoproducts lightProfiniteToCompHaus.{u} := inferInstance

end LightProfinite
