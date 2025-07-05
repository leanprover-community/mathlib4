/-
Copyright (c) 2025 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated

/-!
### σ-algebra helpers

This file provides lightweight wrappers around `MeasurableSpace` so that you can
work with σ‑algebras *as plain sets of sets* when that is more convenient.

* **`m.SigmaAlgebra`** — the collection of all `m`‑measurable sets, exposed as a
  value of type `Set (Set α)`.  This lets you write `s ∈ m.SigmaAlgebra` instead
  of the longer `MeasurableSet[m] s`.
* **`IsSigmaAlgebra F`** — a predicate saying that a family of sets F is already
  a σ‑algebra, implemented by the equality
  `(generateFrom F).SigmaAlgebra = F`.
* **`generateFrom_sigmaAlgebra_eq`** — closing a σ‑algebra  under
  `generateFrom` does nothing: `generateFrom m.SigmaAlgebra = m`.
* A `BooleanAlgebra` instance on `m.SigmaAlgebra`, inherited from the existing
  instance on `{s // MeasurableSet[m] s}`.
* Small bridges between the un‑bundled view (`Set (Set α)`) and the bundled
  subtype `{s // MeasurableSet[m] s}`.

All definitions are mere *re‑exposures* of the standard `MeasurableSet` API; no
new mathematical theory is introduced.
-/

variable {α : Type*} {m : MeasurableSpace α}

namespace MeasurableSpace

/-- The set of all `m`‑measurable subsets of `α`. -/
def SigmaAlgebra : Set (Set α) := m.MeasurableSet'

@[simp]
lemma mem_SigmaAlgebra {s : Set α} : s ∈ m.SigmaAlgebra ↔ (MeasurableSet s) :=
  Iff.rfl

/-- Boolean algebra on `m.SigmaAlgebra`, alias of `Subtype.instBooleanAlgebra`. -/
instance instBooleanAlgebra : BooleanAlgebra m.SigmaAlgebra :=
  MeasurableSet.Subtype.instBooleanAlgebra

lemma generateFrom_sigmaAlgebra_eq : generateFrom m.SigmaAlgebra = m :=
  le_antisymm
    ((generateFrom_le_iff _).2 fun _ hs => mem_SigmaAlgebra.1 hs)
    fun _ hs => measurableSet_generateFrom hs

/-- `IsSigmaAlgebra F` holds iff F equals the σ-algebra it generates. -/
def IsSigmaAlgebra (F : Set (Set α)) : Prop := (generateFrom F).SigmaAlgebra = F

lemma IsSigmaAlgebra_of_measurableSpace :
    IsSigmaAlgebra m.SigmaAlgebra :=
  congrArg (fun t : MeasurableSpace α => t.SigmaAlgebra) generateFrom_sigmaAlgebra_eq

/-- Any bundled measurable set is, by definition, a member of `m.SigmaAlgebra`. -/
@[simp]
lemma Subtype.mem_sigma {s : {t : Set α // MeasurableSet t}} :
    (s : Set α) ∈ m.SigmaAlgebra :=
  mem_SigmaAlgebra.2 s.property

/-- Wrap a membership proof into the *predicate* subtype. -/
def Set.toMeasurableSubtype {s : Set α} (h : s ∈ m.SigmaAlgebra) :
    {t : Set α // MeasurableSet t} :=
  ⟨s, mem_SigmaAlgebra.1 h⟩

end MeasurableSpace
