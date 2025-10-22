/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Set.Image
import Mathlib.Data.List.Defs

/-!
# Lemmas about `List`s and `Set.range`

In this file we prove lemmas about range of some operations on lists.
-/


open List

variable {α β : Type*} (l : List α)

namespace Set

theorem range_list_map (f : α → β) : range (map f) = { l | ∀ x ∈ l, x ∈ range f } := by
  refine antisymm (range_subset_iff.2 fun l => forall_mem_map.2 fun y _ => mem_range_self _)
      fun l hl => ?_
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a l ihl =>
    rcases ihl fun x hx => hl x <| subset_cons_self _ _ hx with ⟨l, rfl⟩
    rcases hl a mem_cons_self with ⟨a, rfl⟩
    exact ⟨a :: l, map_cons⟩

theorem range_list_map_coe (s : Set α) : range (map ((↑) : s → α)) = { l | ∀ x ∈ l, x ∈ s } := by
  rw [range_list_map, Subtype.range_coe]

@[simp]
theorem range_list_get : range l.get = { x | x ∈ l } := by
  ext x
  rw [mem_setOf_eq, mem_iff_get, mem_range]

theorem range_list_getElem? :
    range (l[·]? : ℕ → Option α) = insert none (some '' { x | x ∈ l }) := by
  rw [← range_list_get, ← range_comp]
  refine (range_subset_iff.2 fun n => ?_).antisymm (insert_subset_iff.2 ⟨?_, ?_⟩)
  · exact (le_or_gt l.length n).imp getElem?_eq_none_iff.mpr
      (fun hlt => ⟨⟨_, hlt⟩, (getElem?_eq_getElem hlt).symm⟩)
  · exact ⟨_, getElem?_eq_none_iff.mpr le_rfl⟩
  · exact range_subset_iff.2 fun k => ⟨_, getElem?_eq_getElem _⟩

@[simp]
theorem range_list_getD (d : α) : (range fun n : Nat => l[n]?.getD d) = insert d { x | x ∈ l } :=
  calc
    (range fun n => l[n]?.getD d) = (fun o : Option α => o.getD d) '' range (l[·]?) := by
      simp only [← range_comp, Function.comp_def]
      rfl
    _ = insert d { x | x ∈ l } := by
      simp only [Option.getD, range_list_getElem?, image_insert_eq, image_image, image_id']

@[simp]
theorem range_list_getI [Inhabited α] (l : List α) :
    range l.getI = insert default { x | x ∈ l } := by
  unfold List.getI
  simp

end Set

/-- If each element of a list can be lifted to some type, then the whole list can be
lifted to this type. -/
instance List.canLift (c) (p) [CanLift α β c p] :
    CanLift (List α) (List β) (List.map c) fun l => ∀ x ∈ l, p x where
  prf l H := by
    rw [← Set.mem_range, Set.range_list_map]
    exact fun a ha => CanLift.prf a (H a ha)
