/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Data.Vector.Basic

/-!
# Theorems about membership of elements in vectors

This file contains theorems for membership in a `v.toList` for a vector `v`.
Having the length available in the type allows some of the lemmas to be
  simpler and more general than the original version for lists.
In particular we can avoid some assumptions about types being `Inhabited`,
  and make more general statements about `head` and `tail`.
-/

namespace List

namespace Vector

variable {α β : Type*} {n : ℕ} (a a' : α)

@[simp]
theorem get_mem (i : Fin n) (v : Vector α n) : v.get i ∈ v.toList := List.get_mem _ _

theorem mem_iff_get (v : Vector α n) : a ∈ v.toList ↔ ∃ i, v.get i = a := by
  simp only [List.mem_iff_get, Fin.exists_iff, Vector.get_eq_get_toList]
  exact
    ⟨fun ⟨i, hi, h⟩ => ⟨i, by rwa [toList_length] at hi, h⟩, fun ⟨i, hi, h⟩ =>
      ⟨i, by rwa [toList_length], h⟩⟩

theorem notMem_nil : a ∉ (Vector.nil : Vector α 0).toList := by
  unfold Vector.nil
  simp

@[deprecated (since := "2025-05-23")] alias not_mem_nil := notMem_nil

theorem notMem_zero (v : Vector α 0) : a ∉ v.toList :=
  (Vector.eq_nil v).symm ▸ notMem_nil a

@[deprecated (since := "2025-05-23")] alias not_mem_zero := notMem_zero

theorem mem_cons_iff (v : Vector α n) : a' ∈ (a ::ᵥ v).toList ↔ a' = a ∨ a' ∈ v.toList := by
  rw [Vector.toList_cons, List.mem_cons]

theorem mem_succ_iff (v : Vector α (n + 1)) : a ∈ v.toList ↔ a = v.head ∨ a ∈ v.tail.toList := by
  obtain ⟨a', v', h⟩ := exists_eq_cons v
  simp_rw [h, Vector.mem_cons_iff, Vector.head_cons, Vector.tail_cons]

theorem mem_cons_self (v : Vector α n) : a ∈ (a ::ᵥ v).toList :=
  (Vector.mem_iff_get a (a ::ᵥ v)).2 ⟨0, Vector.get_cons_zero a v⟩

@[simp]
theorem head_mem (v : Vector α (n + 1)) : v.head ∈ v.toList :=
  (Vector.mem_iff_get v.head v).2 ⟨0, Vector.get_zero v⟩

theorem mem_cons_of_mem (v : Vector α n) (ha' : a' ∈ v.toList) : a' ∈ (a ::ᵥ v).toList :=
  (Vector.mem_cons_iff a a' v).2 (Or.inr ha')

theorem mem_of_mem_tail (v : Vector α n) (ha : a ∈ v.tail.toList) : a ∈ v.toList := by
  induction n with
  | zero => exact False.elim (Vector.notMem_zero a v.tail ha)
  | succ n _ => exact (mem_succ_iff a v).2 (Or.inr ha)

theorem mem_map_iff (b : β) (v : Vector α n) (f : α → β) :
    b ∈ (v.map f).toList ↔ ∃ a : α, a ∈ v.toList ∧ f a = b := by
  rw [Vector.toList_map, List.mem_map]

theorem notMem_map_zero (b : β) (v : Vector α 0) (f : α → β) : b ∉ (v.map f).toList := by
  simpa only [Vector.eq_nil v, Vector.map_nil, Vector.toList_nil] using List.not_mem_nil

@[deprecated (since := "2025-05-23")] alias not_mem_map_zero := notMem_map_zero

theorem mem_map_succ_iff (b : β) (v : Vector α (n + 1)) (f : α → β) :
    b ∈ (v.map f).toList ↔ f v.head = b ∨ ∃ a : α, a ∈ v.tail.toList ∧ f a = b := by
  rw [mem_succ_iff, head_map, tail_map, mem_map_iff, @eq_comm _ b]

end Vector

end List
