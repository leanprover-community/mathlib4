/-
Copyright (c) 2025 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated

/-!
Some doc
-/

universe u

variable {α : Type u}

namespace MeasurableSpace

variable {m : MeasurableSpace α}

/--
`m.SigmaAlgebra` is *the* σ-algebra of `m`-measurable sets, packaged as
a plain `Set (Set α)`, so you can write `A ∈ m.SigmaAlgebra`.
-/
def SigmaAlgebra : Set (Set α) := m.MeasurableSet'

@[simp]
lemma mem_SigmaAlgebra {s : Set α} :
    s ∈ m.SigmaAlgebra ↔ (MeasurableSet s) :=
  Iff.rfl

instance instBooleanAlgebra : BooleanAlgebra m.SigmaAlgebra :=
  MeasurableSet.Subtype.instBooleanAlgebra

end MeasurableSpace
