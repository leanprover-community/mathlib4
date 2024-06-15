/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.Topology.Category.CompHausLike.Limits

/-!

# Explicit limits and colimits

This file collects some constructions of explicit limits and colimits in `Profinite`,
which may be useful due to their definitional properties.

## Main definitions

- `Profinite.pullback`: Explicit pullback, defined in the "usual" way as a subset of the product.
- `Profinite.finiteCoproduct`: Explicit finite coproducts, defined as a disjoint union.

-/

namespace Profinite

universe u w

/-
Previously, this had accidentally been made a global instance,
and we now turn it on locally when convenient.
-/
attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike

open CategoryTheory Limits

instance : FinitaryExtensive Profinite := by
  apply CompHausLike.finitaryExtensive
  · intro α _ X
    exact show TotallyDisconnectedSpace (Σ (a : α), X a) from inferInstance
  · intro X Y _ _ _ _
    exact show TotallyDisconnectedSpace {xy : X × Y | _} from inferInstance

noncomputable instance : PreservesFiniteCoproducts profiniteToCompHaus := by
  apply CompHausLike.preservesFiniteCoproducts'
  intro α _ X
  exact show TotallyDisconnectedSpace (Σ (a : α), X a) from inferInstance

end Profinite
