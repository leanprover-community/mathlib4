/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.Topology.Order

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Topology on `ZMod N`

We equip `ZMod N` with the discrete topology.
-/

public section

namespace ZMod

variable {N : ℕ}

/-- The discrete topology (every set is open). -/
instance : TopologicalSpace (ZMod N) := ⊥

instance : DiscreteTopology (ZMod N) := ⟨rfl⟩

end ZMod
