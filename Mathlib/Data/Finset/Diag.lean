/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Yury Kudryashov
-/
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card

#align_import data.finset.prod from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# Diagonal finset

In this file we define `Finset.diag s`
to be the `Finset (α × α)` of pairs `(a, a)` with `a ∈ s`.
-/

namespace Finset

section

variable {α : Type*} {s t : Finset α}

/-- Given a finite set `s`, the diagonal,
`Finset.diag s` is the set of pairs of the form `(a, a)` for `a ∈ s`. -/
def diag (s : Finset α) : Finset (α × α) :=
  s.map ⟨fun x ↦ (x, x), fun _ _ h ↦ congr_arg Prod.fst h⟩
#align finset.diag Finset.diag

theorem diag_eq_map (s : Finset α) :
    diag s = map ⟨fun x ↦ (x, x), fun _ _ h ↦ congr_arg Prod.fst h⟩ s :=
  rfl

theorem coe_diag (s : Finset α) : ↑(diag s) = Set.diagonal α ∩ (↑s ×ˢ ↑s) := by
  simp_rw [diag_eq_map, coe_map, Function.Embedding.coeFn_mk, Set.diag_image]

@[simp]
theorem mem_diag {x : α × α} : x ∈ diag s ↔ x.1 ∈ s ∧ x.1 = x.2 := by
  cases x; simp (config := {contextual := true}) [diag_eq_map, eq_comm]
#align finset.mem_diag Finset.mem_diag

@[simp]
theorem card_diag : (diag s).card = s.card := by simp [diag_eq_map]
#align finset.diag_card Finset.card_diag

@[deprecated] alias diag_card := card_diag -- 2024-03-23

@[simp] theorem diag_subset_diag : diag s ⊆ diag t ↔ s ⊆ t := map_subset_map
@[simp] theorem diag_ssubset_diag : diag s ⊂ diag t ↔ s ⊂ t := map_ssubset_map

theorem diag_mono : Monotone (diag : Finset α → Finset (α × α)) := fun _ _ ↦ diag_subset_diag.2
#align finset.diag_mono Finset.diag_mono

theorem diag_strictMono : StrictMono (diag : Finset α → Finset (α × α)) := fun _ _ ↦
  diag_ssubset_diag.2

@[simp] theorem diag_eq_empty : diag s = ∅ ↔ s = ∅ := map_eq_empty
@[simp] theorem diag_nonempty : (diag s).Nonempty ↔ s.Nonempty := map_nonempty
@[simp] theorem diag_nontrivial : (diag s).Nontrivial ↔ s.Nontrivial := map_nontrivial
@[simp] theorem disjoint_diag_diag : Disjoint (diag s) (diag t) ↔ Disjoint s t := disjoint_map _

@[simp] theorem diag_empty : diag (∅ : Finset α) = ∅ := map_empty _
#align finset.diag_empty Finset.diag_empty

@[simp] theorem diag_singleton (a : α) : diag {a} = {(a, a)} := map_singleton _ _
#align finset.diag_singleton Finset.diag_singleton

@[simp]
theorem diag_cons {a : α} (h : a ∉ s) : diag (cons a s h) = cons (a, a) (diag s) (by simpa) :=
  map_cons ..

@[simp]
theorem diag_disjUnion (h : Disjoint s t) :
    diag (disjUnion s t h) = disjUnion (diag s) (diag t) (disjoint_diag_diag.2 h) :=
  map_disjUnion ..

end

variable {α : Type*} [DecidableEq α] {s t : Finset α}

@[simp] theorem diag_union (s t : Finset α) : diag (s ∪ t) = diag s ∪ diag t := map_union ..
#align finset.diag_union Finset.diag_union

@[simp] theorem diag_inter (s t : Finset α) : diag (s ∩ t) = diag s ∩ diag t := map_inter ..
#align finset.diag_inter Finset.diag_inter

@[simp]
theorem diag_insert (a : α) (s : Finset α) : diag (insert a s) = insert (a, a) (diag s) :=
  map_insert ..
#align finset.diag_insert Finset.diag_insert

end Finset
