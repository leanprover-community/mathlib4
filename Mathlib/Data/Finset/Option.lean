/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Mario Carneiro, Sean Leather

! This file was ported from Lean 3 source module data.finset.option
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Card
import Mathbin.Order.Hom.Basic

/-!
# Finite sets in `option α`

In this file we define

* `option.to_finset`: construct an empty or singleton `finset α` from an `option α`;
* `finset.insert_none`: given `s : finset α`, lift it to a finset on `option α` using `option.some`
  and then insert `option.none`;
* `finset.erase_none`: given `s : finset (option α)`, returns `t : finset α` such that
  `x ∈ t ↔ some x ∈ s`.

Then we prove some basic lemmas about these definitions.

## Tags

finset, option
-/


variable {α β : Type _}

open Function

namespace Option

/-- Construct an empty or singleton finset from an `option` -/
def toFinset (o : Option α) : Finset α :=
  o.elim ∅ singleton
#align option.to_finset Option.toFinset

@[simp]
theorem to_finset_none : none.toFinset = (∅ : Finset α) :=
  rfl
#align option.to_finset_none Option.to_finset_none

@[simp]
theorem to_finset_some {a : α} : (some a).toFinset = {a} :=
  rfl
#align option.to_finset_some Option.to_finset_some

@[simp]
theorem mem_to_finset {a : α} {o : Option α} : a ∈ o.toFinset ↔ a ∈ o := by
  cases o <;> simp [eq_comm]
#align option.mem_to_finset Option.mem_to_finset

theorem card_to_finset (o : Option α) : o.toFinset.card = o.elim 0 1 := by cases o <;> rfl
#align option.card_to_finset Option.card_to_finset

end Option

namespace Finset

/-- Given a finset on `α`, lift it to being a finset on `option α`
using `option.some` and then insert `option.none`. -/
def insertNone : Finset α ↪o Finset (Option α) :=
  (OrderEmbedding.ofMapLeIff fun s => cons none (s.map Embedding.some) <| by simp) fun s t =>
    cons_subset_cons.trans map_subset_map
#align finset.insert_none Finset.insertNone

/-⟨none ::ₘ s.1.map some, multiset.nodup_cons.2
  ⟨by simp, s.nodup.map $ λ a b, option.some.inj⟩⟩-/
@[simp]
theorem mem_insert_none {s : Finset α} : ∀ {o : Option α}, o ∈ s.insertNone ↔ ∀ a ∈ o, a ∈ s
  | none => iff_of_true (Multiset.mem_cons_self _ _) fun a h => by cases h
  | some a => Multiset.mem_cons.trans <| by simp <;> rfl
#align finset.mem_insert_none Finset.mem_insert_none

theorem some_mem_insert_none {s : Finset α} {a : α} : some a ∈ s.insertNone ↔ a ∈ s := by simp
#align finset.some_mem_insert_none Finset.some_mem_insert_none

@[simp]
theorem card_insert_none (s : Finset α) : s.insertNone.card = s.card + 1 := by simp [insert_none]
#align finset.card_insert_none Finset.card_insert_none

/-- Given `s : finset (option α)`, `s.erase_none : finset α` is the set of `x : α` such that
`some x ∈ s`. -/
def eraseNone : Finset (Option α) →o Finset α :=
  (Finset.mapEmbedding (Equiv.optionIsSomeEquiv α).toEmbedding).toOrderHom.comp
    ⟨Finset.subtype _, subtype_mono⟩
#align finset.erase_none Finset.eraseNone

@[simp]
theorem mem_erase_none {s : Finset (Option α)} {x : α} : x ∈ s.eraseNone ↔ some x ∈ s := by
  simp [erase_none]
#align finset.mem_erase_none Finset.mem_erase_none

theorem erase_none_eq_bUnion [DecidableEq α] (s : Finset (Option α)) :
    s.eraseNone = s.bUnion Option.toFinset := by
  ext
  simp
#align finset.erase_none_eq_bUnion Finset.erase_none_eq_bUnion

@[simp]
theorem erase_none_map_some (s : Finset α) : (s.map Embedding.some).eraseNone = s :=
  by
  ext
  simp
#align finset.erase_none_map_some Finset.erase_none_map_some

@[simp]
theorem erase_none_image_some [DecidableEq (Option α)] (s : Finset α) :
    (s.image some).eraseNone = s := by simpa only [map_eq_image] using erase_none_map_some s
#align finset.erase_none_image_some Finset.erase_none_image_some

@[simp]
theorem coe_erase_none (s : Finset (Option α)) : (s.eraseNone : Set α) = some ⁻¹' s :=
  Set.ext fun x => mem_erase_none
#align finset.coe_erase_none Finset.coe_erase_none

@[simp]
theorem erase_none_union [DecidableEq (Option α)] [DecidableEq α] (s t : Finset (Option α)) :
    (s ∪ t).eraseNone = s.eraseNone ∪ t.eraseNone :=
  by
  ext
  simp
#align finset.erase_none_union Finset.erase_none_union

@[simp]
theorem erase_none_inter [DecidableEq (Option α)] [DecidableEq α] (s t : Finset (Option α)) :
    (s ∩ t).eraseNone = s.eraseNone ∩ t.eraseNone :=
  by
  ext
  simp
#align finset.erase_none_inter Finset.erase_none_inter

@[simp]
theorem erase_none_empty : (∅ : Finset (Option α)).eraseNone = ∅ :=
  by
  ext
  simp
#align finset.erase_none_empty Finset.erase_none_empty

@[simp]
theorem erase_none_none : ({none} : Finset (Option α)).eraseNone = ∅ :=
  by
  ext
  simp
#align finset.erase_none_none Finset.erase_none_none

@[simp]
theorem image_some_erase_none [DecidableEq (Option α)] (s : Finset (Option α)) :
    s.eraseNone.image some = s.erase none := by ext (_ | x) <;> simp
#align finset.image_some_erase_none Finset.image_some_erase_none

@[simp]
theorem map_some_erase_none [DecidableEq (Option α)] (s : Finset (Option α)) :
    s.eraseNone.map Embedding.some = s.erase none := by
  rw [map_eq_image, embedding.some_apply, image_some_erase_none]
#align finset.map_some_erase_none Finset.map_some_erase_none

@[simp]
theorem insert_none_erase_none [DecidableEq (Option α)] (s : Finset (Option α)) :
    insertNone (eraseNone s) = insert none s := by ext (_ | x) <;> simp
#align finset.insert_none_erase_none Finset.insert_none_erase_none

@[simp]
theorem erase_none_insert_none (s : Finset α) : eraseNone (insertNone s) = s :=
  by
  ext
  simp
#align finset.erase_none_insert_none Finset.erase_none_insert_none

end Finset

