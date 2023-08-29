/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Pairwise

#align_import logic.encodable.lattice from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

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
  -- ⊢ ⨆ (j : β) (i : ℕ) (_ : j ∈ decode₂ β i), f j = ⨆ (b : β), f b
  simp only [mem_decode₂, iSup_iSup_eq_right]
  -- 🎉 no goals
#align encodable.supr_decode₂ Encodable.iSup_decode₂

theorem iUnion_decode₂ (f : β → Set α) : ⋃ (i : ℕ) (b ∈ decode₂ β i), f b = ⋃ b, f b :=
  iSup_decode₂ f
#align encodable.Union_decode₂ Encodable.iUnion_decode₂

/- Porting note: `@[elab_as_elim]` gives `unexpected eliminator resulting type`. -/
--@[elab_as_elim]
theorem iUnion_decode₂_cases {f : β → Set α} {C : Set α → Prop} (H0 : C ∅) (H1 : ∀ b, C (f b)) {n} :
    C (⋃ b ∈ decode₂ β n, f b) :=
  match decode₂ β n with
  | none => by
    simp
    -- ⊢ C ∅
    apply H0
    -- 🎉 no goals
  | some b => by
    convert H1 b
    -- ⊢ ⋃ (b_1 : β) (_ : b_1 ∈ some b), f b_1 = f b
    simp [ext_iff]
    -- 🎉 no goals
#align encodable.Union_decode₂_cases Encodable.iUnion_decode₂_cases

theorem iUnion_decode₂_disjoint_on {f : β → Set α} (hd : Pairwise (Disjoint on f)) :
    Pairwise (Disjoint on fun i => ⋃ b ∈ decode₂ β i, f b) := by
  rintro i j ij
  -- ⊢ (Disjoint on fun i => ⋃ (b : β) (_ : b ∈ decode₂ β i), f b) i j
  refine' disjoint_left.mpr fun x => _
  -- ⊢ x ∈ (fun i => ⋃ (b : β) (_ : b ∈ decode₂ β i), f b) i → ¬x ∈ (fun i => ⋃ (b  …
  suffices ∀ a, encode a = i → x ∈ f a → ∀ b, encode b = j → x ∉ f b by simpa [decode₂_eq_some]
  -- ⊢ ∀ (a : β), encode a = i → x ∈ f a → ∀ (b : β), encode b = j → ¬x ∈ f b
  rintro a rfl ha b rfl hb
  -- ⊢ False
  exact (hd (mt (congr_arg encode) ij)).le_bot ⟨ha, hb⟩
  -- 🎉 no goals
#align encodable.Union_decode₂_disjoint_on Encodable.iUnion_decode₂_disjoint_on

end Encodable
