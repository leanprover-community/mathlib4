/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Mario Carneiro, Sean Leather
-/
import Mathlib.Data.Finset.Card

#align_import data.finset.option from "leanprover-community/mathlib"@"c227d107bbada5d0d9d20287e3282c0a7f1651a0"

/-!
# Finite sets in `Option α`

In this file we define

* `Option.toFinset`: construct an empty or singleton `Finset α` from an `Option α`;
* `Finset.insertNone`: given `s : Finset α`, lift it to a finset on `Option α` using `Option.some`
  and then insert `Option.none`;
* `Finset.eraseNone`: given `s : Finset (Option α)`, returns `t : Finset α` such that
  `x ∈ t ↔ some x ∈ s`.

Then we prove some basic lemmas about these definitions.

## Tags

finset, option
-/


variable {α β : Type*}

open Function

namespace Option

/-- Construct an empty or singleton finset from an `Option` -/
def toFinset (o : Option α) : Finset α :=
  o.elim ∅ singleton
#align option.to_finset Option.toFinset

@[simp]
theorem toFinset_none : none.toFinset = (∅ : Finset α) :=
  rfl
#align option.to_finset_none Option.toFinset_none

@[simp]
theorem toFinset_some {a : α} : (some a).toFinset = {a} :=
  rfl
#align option.to_finset_some Option.toFinset_some

@[simp]
theorem mem_toFinset {a : α} {o : Option α} : a ∈ o.toFinset ↔ a ∈ o := by
  cases o <;> simp [eq_comm]
  -- ⊢ a ∈ toFinset none ↔ a ∈ none
              -- 🎉 no goals
              -- 🎉 no goals
#align option.mem_to_finset Option.mem_toFinset

theorem card_toFinset (o : Option α) : o.toFinset.card = o.elim 0 1 := by cases o <;> rfl
                                                                          -- ⊢ Finset.card (toFinset none) = Option.elim none 0 1
                                                                                      -- 🎉 no goals
                                                                                      -- 🎉 no goals
#align option.card_to_finset Option.card_toFinset

end Option

namespace Finset

/-- Given a finset on `α`, lift it to being a finset on `Option α`
using `Option.some` and then insert `Option.none`. -/
def insertNone : Finset α ↪o Finset (Option α) :=
  (OrderEmbedding.ofMapLEIff fun s => cons none (s.map Embedding.some) <| by simp) fun s t => by
                                                                             -- 🎉 no goals
    rw [le_iff_subset, cons_subset_cons, map_subset_map, le_iff_subset]
    -- 🎉 no goals
#align finset.insert_none Finset.insertNone

@[simp]
theorem mem_insertNone {s : Finset α} : ∀ {o : Option α}, o ∈ insertNone s ↔ ∀ a ∈ o, a ∈ s
  | none => iff_of_true (Multiset.mem_cons_self _ _) fun a h => by cases h
                                                                   -- 🎉 no goals
  | some a => Multiset.mem_cons.trans <| by simp
                                            -- 🎉 no goals
#align finset.mem_insert_none Finset.mem_insertNone

theorem some_mem_insertNone {s : Finset α} {a : α} : some a ∈ insertNone s ↔ a ∈ s := by simp
                                                                                         -- 🎉 no goals
#align finset.some_mem_insert_none Finset.some_mem_insertNone

@[simp]
theorem card_insertNone (s : Finset α) : s.insertNone.card = s.card + 1 := by simp [insertNone]
                                                                              -- 🎉 no goals
#align finset.card_insert_none Finset.card_insertNone

/-- Given `s : Finset (Option α)`, `eraseNone s : Finset α` is the set of `x : α` such that
`some x ∈ s`. -/
def eraseNone : Finset (Option α) →o Finset α :=
  (Finset.mapEmbedding (Equiv.optionIsSomeEquiv α).toEmbedding).toOrderHom.comp
    ⟨Finset.subtype _, subtype_mono⟩
#align finset.erase_none Finset.eraseNone

@[simp]
theorem mem_eraseNone {s : Finset (Option α)} {x : α} : x ∈ eraseNone s ↔ some x ∈ s := by
  simp [eraseNone]
  -- 🎉 no goals
#align finset.mem_erase_none Finset.mem_eraseNone

theorem eraseNone_eq_biUnion [DecidableEq α] (s : Finset (Option α)) :
    eraseNone s = s.biUnion Option.toFinset := by
  ext
  -- ⊢ a✝ ∈ ↑eraseNone s ↔ a✝ ∈ Finset.biUnion s Option.toFinset
  simp
  -- 🎉 no goals
#align finset.erase_none_eq_bUnion Finset.eraseNone_eq_biUnion

@[simp]
theorem eraseNone_map_some (s : Finset α) : eraseNone (s.map Embedding.some) = s := by
  ext
  -- ⊢ a✝ ∈ ↑eraseNone (map Embedding.some s) ↔ a✝ ∈ s
  simp
  -- 🎉 no goals
#align finset.erase_none_map_some Finset.eraseNone_map_some

@[simp]
theorem eraseNone_image_some [DecidableEq (Option α)] (s : Finset α) :
    eraseNone (s.image some) = s := by simpa only [map_eq_image] using eraseNone_map_some s
                                       -- 🎉 no goals
#align finset.erase_none_image_some Finset.eraseNone_image_some

@[simp]
theorem coe_eraseNone (s : Finset (Option α)) : (eraseNone s : Set α) = some ⁻¹' s :=
  Set.ext fun _ => mem_eraseNone
#align finset.coe_erase_none Finset.coe_eraseNone

@[simp]
theorem eraseNone_union [DecidableEq (Option α)] [DecidableEq α] (s t : Finset (Option α)) :
    eraseNone (s ∪ t) = eraseNone s ∪ eraseNone t := by
  ext
  -- ⊢ a✝ ∈ ↑eraseNone (s ∪ t) ↔ a✝ ∈ ↑eraseNone s ∪ ↑eraseNone t
  simp
  -- 🎉 no goals
#align finset.erase_none_union Finset.eraseNone_union

@[simp]
theorem eraseNone_inter [DecidableEq (Option α)] [DecidableEq α] (s t : Finset (Option α)) :
    eraseNone (s ∩ t) = eraseNone s ∩ eraseNone t := by
  ext
  -- ⊢ a✝ ∈ ↑eraseNone (s ∩ t) ↔ a✝ ∈ ↑eraseNone s ∩ ↑eraseNone t
  simp
  -- 🎉 no goals
#align finset.erase_none_inter Finset.eraseNone_inter

@[simp]
theorem eraseNone_empty : eraseNone (∅ : Finset (Option α)) = ∅ := by
  ext
  -- ⊢ a✝ ∈ ↑eraseNone ∅ ↔ a✝ ∈ ∅
  simp
  -- 🎉 no goals
#align finset.erase_none_empty Finset.eraseNone_empty

@[simp]
theorem eraseNone_none : eraseNone ({none} : Finset (Option α)) = ∅ := by
  ext
  -- ⊢ a✝ ∈ ↑eraseNone {none} ↔ a✝ ∈ ∅
  simp
  -- 🎉 no goals
#align finset.erase_none_none Finset.eraseNone_none

@[simp]
theorem image_some_eraseNone [DecidableEq (Option α)] (s : Finset (Option α)) :
    (eraseNone s).image some = s.erase none := by ext (_ | x) <;> simp
                                                  -- ⊢ none ∈ image some (↑eraseNone s) ↔ none ∈ erase s none
                                                                  -- 🎉 no goals
                                                                  -- 🎉 no goals
#align finset.image_some_erase_none Finset.image_some_eraseNone

@[simp]
theorem map_some_eraseNone [DecidableEq (Option α)] (s : Finset (Option α)) :
    (eraseNone s).map Embedding.some = s.erase none := by
  rw [map_eq_image, Embedding.some_apply, image_some_eraseNone]
  -- 🎉 no goals
#align finset.map_some_erase_none Finset.map_some_eraseNone

@[simp]
theorem insertNone_eraseNone [DecidableEq (Option α)] (s : Finset (Option α)) :
    insertNone (eraseNone s) = insert none s := by ext (_ | x) <;> simp
                                                   -- ⊢ none ∈ ↑insertNone (↑eraseNone s) ↔ none ∈ insert none s
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
#align finset.insert_none_erase_none Finset.insertNone_eraseNone

@[simp]
theorem eraseNone_insertNone (s : Finset α) : eraseNone (insertNone s) = s := by
  ext
  -- ⊢ a✝ ∈ ↑eraseNone (↑insertNone s) ↔ a✝ ∈ s
  simp
  -- 🎉 no goals
#align finset.erase_none_insert_none Finset.eraseNone_insertNone

end Finset
