import Mathlib.SetTheory.Ordinal.Family

/-!
# Regression tests for `Ordinal.lift_iSup`

The content of the lemma is universe-crossing, so these pin the two universe positions that a
same-universe statement would silently satisfy.
-/

universe u v

/-- A small index type drawn from a strictly larger universe: this is what fails if the
statement is accidentally restricted to a same-universe index. -/
example {ι : Type v} [Small.{u} ι] (f : ι → Ordinal.{u}) :
    Ordinal.lift.{v} (⨆ i, f i) = ⨆ i, Ordinal.lift.{v} (f i) :=
  Ordinal.lift_iSup f

/-- A `ULift`ed index type: the required `Small` instance must be available without manual
setup. -/
example {ι : Type u} (f : ULift.{v} ι → Ordinal.{u}) :
    Ordinal.lift.{v} (⨆ i, f i) = ⨆ i, Ordinal.lift.{v} (f i) :=
  Ordinal.lift_iSup f
