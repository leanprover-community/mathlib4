/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Topology.Instances.ZMod
import Mathlib.MeasureTheory.MeasurableSpace.Basic
/-!
# Measure-space instance on `ZMod N`

We equip `ZMod N` with the discrete measure-space structure.
-/

variable {N : ℕ}

namespace ZMod

/-- The discrete measurable space structure (every set is measurable). -/
instance : MeasurableSpace (ZMod N) := ⊤

end ZMod
