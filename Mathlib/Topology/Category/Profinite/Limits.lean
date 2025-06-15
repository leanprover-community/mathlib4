/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson
-/
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.CompHausLike.Limits
/-!

# Explicit limits and colimits

This file applies the general API for explicit limits and colimits in `CompHausLike P` (see
the file `Mathlib/Topology/Category/CompHausLike/Limits.lean`) to the special case of `Profinite`.
-/

namespace Profinite

universe u w

open CategoryTheory Limits CompHausLike

instance : HasExplicitPullbacks (fun Y ↦ TotallyDisconnectedSpace Y) where
  hasProp _ _ := { hasProp :=
    show TotallyDisconnectedSpace {_xy : _ | _} from inferInstance}

instance : HasExplicitFiniteCoproducts.{w, u} (fun Y ↦ TotallyDisconnectedSpace Y) where
  hasProp _ := { hasProp :=
    show TotallyDisconnectedSpace (Σ (_a : _), _) from inferInstance}

/-- A one-element space is terminal in `Profinite` -/
abbrev isTerminalPUnit : IsTerminal (Profinite.of PUnit.{u + 1}) := CompHausLike.isTerminalPUnit

example : FinitaryExtensive Profinite.{u} := inferInstance

noncomputable example : PreservesFiniteCoproducts profiniteToCompHaus := inferInstance

end Profinite
