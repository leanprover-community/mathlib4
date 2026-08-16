import Mathlib.SetTheory.Ordinal.Family

/-!
# Regression tests for `Ordinal.lift_iSup`

The lemma's content is universe-crossing, so the tests exercise the universe positions that a
same-universe statement would silently satisfy: an empty index type, an index type strictly
smaller than the value universe, and a `ULift`ed one.
-/

universe u v

/-- The empty index type: both sides are `0`, and the `Small` side condition must still fire. -/
example : Ordinal.lift.{v} (⨆ _ : (∅ : Set ℕ), (0 : Ordinal.{u}))
    = ⨆ _ : (∅ : Set ℕ), Ordinal.lift.{v} 0 :=
  Ordinal.lift_iSup _

/-- Index in `Type u`, values in `Ordinal.{u}`, lifted to `Ordinal.{max u v}`. -/
example {ι : Type u} (f : ι → Ordinal.{u}) :
    Ordinal.lift.{v} (⨆ i, f i) = ⨆ i, Ordinal.lift.{v} (f i) :=
  Ordinal.lift_iSup f

/-- A small index type drawn from a strictly larger universe. -/
example {ι : Type v} [Small.{u} ι] (f : ι → Ordinal.{u}) :
    Ordinal.lift.{v} (⨆ i, f i) = ⨆ i, Ordinal.lift.{v} (f i) :=
  Ordinal.lift_iSup f

/-- A `ULift`ed index type. -/
example {ι : Type u} (f : ULift.{v} ι → Ordinal.{u}) :
    Ordinal.lift.{v} (⨆ i, f i) = ⨆ i, Ordinal.lift.{v} (f i) :=
  Ordinal.lift_iSup f

/-- Lifting to the same universe is the identity on both sides. -/
example {ι : Type u} (f : ι → Ordinal.{u}) :
    Ordinal.lift.{u} (⨆ i, f i) = ⨆ i, Ordinal.lift.{u} (f i) :=
  Ordinal.lift_iSup f

/-- The `le` forms. -/
example {ι : Type u} {f : ι → Ordinal.{u}} {a : Ordinal.{max u v}}
    (h : ∀ i, Ordinal.lift.{v} (f i) ≤ a) : Ordinal.lift.{v} (⨆ i, f i) ≤ a :=
  Ordinal.lift_iSup_le h

example {ι : Type u} {f : ι → Ordinal.{u}} {a : Ordinal.{max u v}} :
    Ordinal.lift.{v} (⨆ i, f i) ≤ a ↔ ∀ i, Ordinal.lift.{v} (f i) ≤ a :=
  Ordinal.lift_iSup_le_iff
