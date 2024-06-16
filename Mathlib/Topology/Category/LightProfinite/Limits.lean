/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.CompHausLike.Limits
import Mathlib.Topology.Category.LightProfinite.Basic
/-!

# Explicit limits and colimits

This file collects some constructions of explicit limits and colimits in `LightProfinite`,
which may be useful due to their definitional properties.

## Main definitions

* `LightProfinite.pullback`: Explicit pullback, defined in the "usual" way as a subset of the
  product.

* `LightProfinite.finiteCoproduct`: Explicit finite coproducts, defined as a disjoint union.

-/

namespace LightProfinite

universe u w

/-
Previously, this had accidentally been made a global instance,
and we now turn it on locally when convenient.
-/
attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike

open CategoryTheory Limits

instance : FinitaryExtensive LightProfinite := by
  apply CompHausLike.finitaryExtensive
  · intro α _ X
    constructor
    · exact show TotallyDisconnectedSpace (Σ (a : α), X a) from inferInstance
    · exact show SecondCountableTopology (Σ (a : α), X a) from inferInstance
  · intro X Y _ _ _ _
    constructor
    · exact show TotallyDisconnectedSpace {xy : X × Y | _} from inferInstance
    · exact show SecondCountableTopology {xy : X × Y | _} from inferInstance

noncomputable instance : PreservesFiniteCoproducts lightProfiniteToCompHaus := by
  apply CompHausLike.preservesFiniteCoproducts'
  intro α _ X
  constructor
  · exact show TotallyDisconnectedSpace (Σ (a : α), X a) from inferInstance
  · exact show SecondCountableTopology (Σ (a : α), X a) from inferInstance

end LightProfinite
