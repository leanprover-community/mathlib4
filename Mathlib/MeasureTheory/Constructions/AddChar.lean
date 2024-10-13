/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.AddChar
import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# Measurable space instance for additive characters

This file endows `AddChar A M` with the discrete measurable space structure whenever `A` and `M`
are themselves discrete measurable spaces.

## TODO

Give the definition in the correct generality.
-/

namespace AddChar
variable {A M : Type*} [AddMonoid A] [Monoid M]
  [MeasurableSpace A] [DiscreteMeasurableSpace A] [MeasurableSpace M] [DiscreteMeasurableSpace M]

instance instMeasurableSpace : MeasurableSpace (AddChar A M) := ⊤
instance instDiscreteMeasurableSpace : DiscreteMeasurableSpace (AddChar A M) := ⟨fun _ ↦ trivial⟩

end AddChar
