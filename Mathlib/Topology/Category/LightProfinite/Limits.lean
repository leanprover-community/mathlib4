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

open CategoryTheory Limits CompHausLike

set_option linter.unusedVariables false in
instance : HasExplicitPullbacks
    (fun Y ↦ TotallyDisconnectedSpace Y ∧ SecondCountableTopology Y) where
  hasExplicitPullbacks _ _ := {
    hasProp := ⟨show TotallyDisconnectedSpace {xy : _ | _} from inferInstance, show SecondCountableTopology {xy : _ | _} from inferInstance⟩ }

set_option linter.unusedVariables false in
instance : HasExplicitFiniteCoproducts
    (fun Y ↦ TotallyDisconnectedSpace Y ∧ SecondCountableTopology Y) where
  hasProp _ := { hasProp :=
    ⟨show TotallyDisconnectedSpace (Σ (a : _), _) from inferInstance,
      show SecondCountableTopology (Σ (a : _), _) from inferInstance⟩ }

example : FinitaryExtensive LightProfinite := inferInstance

noncomputable example : PreservesFiniteCoproducts lightProfiniteToCompHaus := inferInstance

end LightProfinite
