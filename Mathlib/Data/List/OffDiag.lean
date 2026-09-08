/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

import Mathlib.Data.List.Count
import Mathlib.Data.List.Enum
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Nat.Notation

/-!
# Definition and basic properties of `List.offDiagonal`

In this file we define `List.offDiagonal l` to be the product `l.product l`
with the diagonal removed.
The actual definition is more complicated to avoid assuming that equality on `α` is decidable.
-/

@[expose] public section

assert_not_exists Preorder

namespace List

variable {α : Type*} {l : List α}

/-- `List.offDiagonal l` is the product `l.product l` with the diagonal removed. -/
def offDiagonal (l : List α) : List (α × α) :=
  l.zipIdx.flatMap fun (x, n) ↦ map (Prod.mk x) <| l.eraseIdx n

@[deprecated (since := "2026-09-06")] alias offDiag := offDiagonal

@[simp]
theorem offDiagonal_nil : offDiagonal ([] : List α) = [] := rfl

@[deprecated (since := "2026-09-06")] alias offDiag_nil := offDiagonal_nil

theorem offDiagonal_cons_perm (a : α) (l : List α) :
    offDiagonal (a :: l) ~ map (a, ·) l ++ map (·, a) l ++ l.offDiagonal := by
  simp only [offDiagonal, zipIdx_cons']
  have : map (fun x ↦ (x.fst, a)) l.zipIdx = map (·, a) l := by
    conv_rhs => rw [← zipIdx_map_fst 0 l, map_map, Function.comp_def]
  simp [append_assoc, perm_append_left_iff, flatMap_map,
    ← (map_append_flatMap_perm _ _ _).congr_left, this]

@[deprecated (since := "2026-09-06")] alias offDiag_cons_perm := offDiagonal_cons_perm

@[simp]
theorem offDiagonal_singleton (a : α) : offDiagonal [a] = [] := rfl

@[deprecated (since := "2026-09-06")] alias offDiag_singleton := offDiagonal_singleton

theorem length_offDiagonal' (l : List α) : length l.offDiagonal = length l * (length l - 1) := by
  have : ∀ x ∈ l.zipIdx, length (eraseIdx l x.2) = length l - 1 := fun x hx ↦
    length_eraseIdx_of_lt <| snd_lt_of_mem_zipIdx hx
  simp [offDiagonal, map_congr_left this]

@[deprecated (since := "2026-09-06")] alias length_offDiag' := length_offDiagonal'

@[simp]
theorem length_offDiagonal (l : List α) : length l.offDiagonal = length l ^ 2 - length l := by
  simp [length_offDiagonal', Nat.mul_sub, Nat.pow_two]

@[deprecated (since := "2026-09-06")] alias length_offDiag := length_offDiagonal

theorem mem_offDiagonal_iff_getElem {x : α × α} :
    x ∈ l.offDiagonal ↔ ∃ (i : ℕ) (_ : i < l.length) (j : ℕ) (_ : j < l.length),
      i ≠ j ∧ l[i] = x.1 ∧ l[j] = x.2 := by
  rcases x with ⟨x, y⟩
  simp only [offDiagonal, exists_mem_zipIdx, mem_eraseIdx_iff_getElem, mem_flatMap, mem_map,
    Nat.zero_add, Prod.ext_iff, ← exists_and_right, exists_and_left, @exists_comm α, and_assoc,
    exists_eq_left', ne_comm]

@[deprecated (since := "2026-09-06")] alias mem_offDiag_iff_getElem := mem_offDiagonal_iff_getElem

theorem count_offDiagonal_eq_mul_sub_ite [DecidableEq α] (l : List α) (a b : α) :
    count (a, b) l.offDiagonal = count a l * count b l - if a = b then count a l else 0 := by
  induction l with
  | nil => simp
  | cons c l ihl =>
    have H₁ {x y z : α} : count (x, y) (map (z, ·) l) = if z = x then count y l else 0 := by
      split_ifs with h
      · rw [h, count_map_of_injective l (x, ·) (by simp [Function.Injective])]
      · simp [count_eq_zero, h]
    have H₂ {x y z : α} : count (x, y) (map (·, z) l) = if z = y then count x l else 0 := by
      split_ifs with h
      · rw [h, count_map_of_injective l (·, y) (by simp [Function.Injective])]
      · simp [count_eq_zero, h]
    simp only [(offDiagonal_cons_perm _ _).count_eq, count_append, ihl, H₁, H₂, count_cons,
      beq_iff_eq]
    have := Nat.le_mul_self (count c l)
    split_ifs <;> simp_all <;> grind

@[deprecated (since := "2026-09-06")]
alias count_offDiag_eq_mul_sub_ite := count_offDiagonal_eq_mul_sub_ite

@[gcongr]
protected theorem Perm.offDiagonal {l₁ l₂ : List α} (h : l₁ ~ l₂) :
    l₁.offDiagonal ~ l₂.offDiagonal := by
  classical simp_all [perm_iff_count, count_offDiagonal_eq_mul_sub_ite]

@[deprecated (since := "2026-09-06")] alias Perm.offDiag := Perm.offDiagonal

protected theorem Nodup.offDiagonal (h : l.Nodup) : l.offDiagonal.Nodup := by
  let := Classical.decEq α
  rw [nodup_iff_count_le_one]
  rintro ⟨x, y⟩
  rw [count_offDiagonal_eq_mul_sub_ite l x y]
  grind

@[deprecated (since := "2026-09-06")] alias Nodup.offDiag := Nodup.offDiagonal

protected theorem Nodup.of_offDiagonal (h : l.offDiagonal.Nodup) : l.Nodup := by
  let := Classical.decEq α
  simp only [nodup_iff_count_le_one, Prod.forall, count_offDiagonal_eq_mul_sub_ite] at *
  intro a
  specialize h a a
  contrapose h
  rw [Nat.not_le] at h
  suffices 1 + l.count a < l.count a * l.count a by simpa
  calc
    1 + l.count a < l.count a + l.count a := by simpa
    _ ≤ l.count a * l.count a := by
      rw [← Nat.two_mul]
      exact Nat.mul_le_mul_right _ h

@[deprecated (since := "2026-09-06")] alias Nodup.of_offDiag := Nodup.of_offDiagonal

/-- `List.offDiagonal l` has no duplicates iff the original list has no duplicates. -/
@[simp]
theorem nodup_offDiagonal : l.offDiagonal.Nodup ↔ l.Nodup := ⟨.of_offDiagonal, .offDiagonal⟩

@[deprecated (since := "2026-09-06")] alias nodup_offDiag := nodup_offDiagonal

/-- If `l : List α` is a list with no duplicates, then `x : α × α` belongs to `List.offDiagonal l`
iff both components of `x` belong to `l` and they are not equal. -/
theorem Nodup.mem_offDiagonal (h : l.Nodup) {x : α × α} :
    x ∈ l.offDiagonal ↔ x.1 ∈ l ∧ x.2 ∈ l ∧ x.1 ≠ x.2 := by
  rcases x with ⟨x, y⟩
  simp_rw [mem_offDiagonal_iff_getElem, mem_iff_getElem, Ne]
  constructor
  · rintro ⟨i, hi, j, hj, hne, rfl, rfl⟩
    exact ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩, mt h.getElem_inj_iff.1 hne⟩
  · rintro ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩, hne⟩
    exact ⟨i, hi, j, hj, mt h.getElem_inj_iff.2 hne, rfl, rfl⟩

@[deprecated (since := "2026-09-06")] alias Nodup.mem_offDiag := Nodup.mem_offDiagonal

theorem map_prodMap_offDiagonal {β : Type*} (f : α → β) (l : List α) :
    map (Prod.map f f) l.offDiagonal = (map f l).offDiagonal := by
  simp [offDiagonal, map_flatMap, zipIdx_map, flatMap_map, eraseIdx_map, Function.comp_def]

@[deprecated (since := "2026-09-06")] alias map_prodMap_offDiag := map_prodMap_offDiagonal

end List
