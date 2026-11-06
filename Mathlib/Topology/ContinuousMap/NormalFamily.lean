/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Normal families

This file defines `IsNormalFamily` for families of continuous maps to a one-point compactification.
A family is normal if its closure in the compact-open topology is compact.

## Tags

normal family, compact-open topology, one-point compactification
-/

@[expose] public section

/-- A family of continuous maps to the one-point compactification of `Y` is normal if its closure
in the compact-open topology is compact. -/
def IsNormalFamily {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (F : Set C(X, OnePoint Y)) : Prop :=
  IsCompact (closure F)
