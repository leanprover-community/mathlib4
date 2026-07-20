/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.IndexedSequenceOrderFormula
public import Mathlib.SetTheory.ZFC.Constructible.IndexedSequenceValidity

/-!
# Lookup semantics for represented indexed sequences

The access formula checks both that the requested index is below the recorded
length and that the corresponding graph pair is present.  Thus irrelevant
extra graph elements allowed by `Represents` cannot create out-of-range
lookups, and lookup is exactly equivalent to retrieving an entry of the
represented Lean list.
-/

@[expose] public section

universe u

namespace Constructible.IndexedSequenceZF

open FiniteSequenceZF

/-- A represented sequence exposes its entry at every in-range index. -/
theorem satisfies_valueAtFormula_of_represents
    {sequence : ZFSet.{u}} {xs : List ZFSet.{u}}
    (hrep : Represents sequence xs) (k : Nat) (hk : k < xs.length) :
    FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
      ![sequence, natCode k, xs.get ⟨k, hk⟩] := by
  exact (satisfies_valueAt_represents_iff hrep k _).mpr ⟨hk, rfl⟩

/--
At a fixed in-range index, a represented sequence has exactly the represented
list value.
-/
theorem satisfies_valueAtFormula_iff_of_represents_at
    {sequence : ZFSet.{u}} {xs : List ZFSet.{u}}
    (hrep : Represents sequence xs) (k : Nat) (hk : k < xs.length)
    (value : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        ![sequence, natCode k, value] <->
      value = xs.get ⟨k, hk⟩ := by
  rw [satisfies_valueAt_represents_iff hrep]
  constructor
  · rintro ⟨hk', hvalue⟩
    simpa using hvalue
  · intro hvalue
    exact ⟨hk, hvalue⟩

/-- Lookup has exact list semantics for every represented indexed sequence. -/
theorem satisfies_valueAtFormula_iff_of_represents
    {sequence : ZFSet.{u}} {xs : List ZFSet.{u}}
    (hrep : Represents sequence xs) (k : Nat) (value : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        ![sequence, natCode k, value] <->
      ∃ hk : k < xs.length, value = xs.get ⟨k, hk⟩ :=
  satisfies_valueAt_represents_iff hrep k value

/-- The representability invariant always proves the sound lookup direction. -/
theorem satisfies_valueAtFormula_of_exists_lt_of_represents
    {sequence : ZFSet.{u}} {xs : List ZFSet.{u}}
    (hrep : Represents sequence xs) (k : Nat) (value : ZFSet.{u})
    (hvalue : ∃ hk : k < xs.length, value = xs.get ⟨k, hk⟩) :
    FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
      ![sequence, natCode k, value] := by
  exact (satisfies_valueAtFormula_iff_of_represents hrep k value).mpr
    hvalue

/--
For a genuine indexed sequence code, whose graph has no extra entries, lookup
has the unrestricted exact semantics.
-/
theorem satisfies_valueAtFormula_sequenceCode_iff
    (xs : List ZFSet.{u}) (k : Nat) (value : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        ![sequenceCode xs, natCode k, value] <->
      ∃ hk : k < xs.length, value = xs.get ⟨k, hk⟩ :=
  satisfies_valueAt_sequenceCode_iff xs k value

end Constructible.IndexedSequenceZF
