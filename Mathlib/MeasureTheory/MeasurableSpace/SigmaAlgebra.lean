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

open MeasureTheory

/--
`m.SigmaAlgebra` is *the* σ-algebra of `m`-measurable sets, packaged as
a plain `Set (Set α)`, so you can write `A ∈ m.SigmaAlgebra`.
-/
def SigmaAlgebra : Set (Set α) := m.MeasurableSet'

@[simp]
lemma mem_SigmaAlgebra {s : Set α} : s ∈ m.SigmaAlgebra ↔ (MeasurableSet s) :=
  Iff.rfl

/-- Boolean algebra on `m.SigmaAlgebra`, inherited from
`MeasurableSet.Subtype.instBooleanAlgebra`. -/
instance instBooleanAlgebra : BooleanAlgebra m.SigmaAlgebra :=
  MeasurableSet.Subtype.instBooleanAlgebra

lemma generateFrom_sigmaAlgebra_eq : generateFrom m.SigmaAlgebra = m :=
  le_antisymm
    ((generateFrom_le_iff _).2 fun _ hs => mem_SigmaAlgebra.1 hs)
    fun _ hs => measurableSet_generateFrom hs

/-- `IsSigmaAlgebra 𝒜` holds iff `𝒜` equals the σ-algebra it generates. -/
def IsSigmaAlgebra (𝒜 : Set (Set α)) : Prop := (generateFrom 𝒜).SigmaAlgebra = 𝒜

/-- Every measurable space yields a σ-algebra as a plain set-of-sets. -/
lemma IsSigmaAlgebra_of_measurableSpace :
    IsSigmaAlgebra m.SigmaAlgebra :=
  congrArg (fun t : MeasurableSpace α => t.SigmaAlgebra) generateFrom_sigmaAlgebra_eq



end MeasurableSpace
