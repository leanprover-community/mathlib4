/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module logic.encodable.lattice
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Pairwise

/-!
# Lattice operations on encodable types

Lemmas about lattice and set operations on encodable types

## Implementation Notes

This is a separate file, to avoid unnecessary imports in basic files.

Previously some of these results were in the `measure_theory` folder.
-/

open Set

namespace Encodable

variable {α : Type _} {β : Type _} [Encodable β]

theorem supr_decode₂ [CompleteLattice α] (f : β → α) :
    (⨆ (i : ℕ) (b ∈ decode₂ β i), f b) = (⨆ b, f b) := by
  rw [supᵢ_comm]
  simp only [mem_decode₂, supᵢ_supᵢ_eq_right]
#align encodable.supr_decode₂ Encodable.supr_decode₂

theorem Union_decode₂ (f : β → Set α) : (⋃ (i : ℕ) (b ∈ decode₂ β i), f b) = ⋃ b, f b :=
  supr_decode₂ f
#align encodable.Union_decode₂ Encodable.Union_decode₂

/- Porting note: Not sure what to make of error
`unexpected eliminator resulting type`
  `C (unionᵢ fun b => unionᵢ fun h => f b)`
I'm just commenting it out for now in the hopes that that's what we want. -/
--@[elab_as_elim]
theorem Union_decode₂_cases {f : β → Set α} {C : Set α → Prop} (H0 : C ∅) (H1 : ∀ b, C (f b)) {n} :
    C (⋃ b ∈ decode₂ β n, f b) :=
  match decode₂ β n with
  | none => by
    simp
    apply H0
  | some b => by
    convert H1 b
    simp [ext_iff]
#align encodable.Union_decode₂_cases Encodable.Union_decode₂_cases

theorem Union_decode₂_disjoint_on {f : β → Set α} (hd : Pairwise (Disjoint on f)) :
    Pairwise (Disjoint on fun i => ⋃ b ∈ decode₂ β i, f b) :=
  by
  rintro i j ij
  refine' disjoint_left.mpr fun x => _
  suffices ∀ a, encode a = i → x ∈ f a → ∀ b, encode b = j → x ∉ f b by simpa [decode₂_eq_some]
  rintro a rfl ha b rfl hb
  exact (hd (mt (congr_arg encode) ij)).le_bot ⟨ha, hb⟩
#align encodable.Union_decode₂_disjoint_on Encodable.Union_decode₂_disjoint_on

end Encodable
