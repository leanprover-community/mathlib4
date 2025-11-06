/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Pairwise
import Mathlib.Data.Set.Subsingleton

/-!
# Lattice operations on encodable types

Lemmas about lattice and set operations on encodable types

## Implementation Notes

This is a separate file, to avoid unnecessary imports in basic files.

Previously some of these results were in the `MeasureTheory` folder.
-/

open Set

namespace Encodable

variable {α : Type*} {β : Type*} [Encodable β]

theorem iSup_decode₂ [CompleteLattice α] (f : β → α) :
    ⨆ (i : ℕ) (b ∈ decode₂ β i), f b = (⨆ b, f b) := by
  rw [iSup_comm]
  simp only [mem_decode₂, iSup_iSup_eq_right]

theorem iUnion_decode₂ (f : β → Set α) : ⋃ (i : ℕ) (b ∈ decode₂ β i), f b = ⋃ b, f b :=
  iSup_decode₂ f

@[elab_as_elim]
theorem iUnion_decode₂_cases {f : β → Set α} {C : Set α → Prop} (H0 : C ∅) (H1 : ∀ b, C (f b)) {n} :
    C (⋃ b ∈ decode₂ β n, f b) :=
  match decode₂ β n with
  | none => by
    simp only [Option.mem_def, iUnion_of_empty, iUnion_empty, reduceCtorEq]
    apply H0
  | some b => by
    convert H1 b
    simp

open scoped Function in -- required for scoped `on` notation
theorem iUnion_decode₂_disjoint_on {f : β → Set α} (hd : Pairwise (Disjoint on f)) :
    Pairwise (Disjoint on fun i => ⋃ b ∈ decode₂ β i, f b) := by
  rintro i j ij
  refine disjoint_left.mpr fun x => ?_
  suffices ∀ a, encode a = i → x ∈ f a → ∀ b, encode b = j → x ∉ f b by simpa [decode₂_eq_some]
  rintro a rfl ha b rfl hb
  exact (hd (mt (congr_arg encode) ij)).le_bot ⟨ha, hb⟩

end Encodable
