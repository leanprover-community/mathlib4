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
# Definition and basic properties of `List.offDiag`

In this file we define `List.offDiag l` to be the product `l.product l`
with the diagonal removed.
The actual definition is more complicated to avoid assuming that equality on `α` is decidable.
-/

@[expose] public section

assert_not_exists Preorder

namespace List

variable {α : Type*} {l : List α}

/-- List.offDiag l` is the product `l.product l` with the diagonal removed. -/
def offDiag (l : List α) : List (α × α) :=
  l.zipIdx.flatMap fun (x, n) ↦ map (Prod.mk x) <| l.eraseIdx n

@[simp]
theorem offDiag_nil : offDiag ([] : List α) = [] := rfl

theorem offDiag_cons_perm (a : α) (l : List α) :
    offDiag (a :: l) ~ map (a, ·) l ++ map (·, a) l ++ l.offDiag := by
  simp only [offDiag, zipIdx_cons']
  have : map (fun x ↦ (x.fst, a)) l.zipIdx = map (·, a) l := by
    conv_rhs => rw [← zipIdx_map_fst 0 l, map_map, Function.comp_def]
  simp [append_assoc, perm_append_left_iff, flatMap_map,
    ← (map_append_flatMap_perm _ _ _).congr_left, this]

@[simp]
theorem offDiag_singleton (a : α) : offDiag [a] = [] := rfl

theorem length_offDiag' (l : List α) : length l.offDiag = length l * (length l - 1) := by
  have : ∀ x ∈ l.zipIdx, length (eraseIdx l x.2) = length l - 1 := fun x hx ↦
    length_eraseIdx_of_lt <| snd_lt_of_mem_zipIdx hx
  simp [offDiag, map_congr_left this]

@[simp]
theorem length_offDiag (l : List α) : length l.offDiag = length l ^ 2 - length l := by
  simp [length_offDiag', Nat.mul_sub, Nat.pow_two]

theorem mem_offDiag_iff_getElem {x : α × α} :
    x ∈ l.offDiag ↔ ∃ (i : ℕ) (_ : i < l.length) (j : ℕ) (_ : j < l.length),
      i ≠ j ∧ l[i] = x.1 ∧ l[j] = x.2 := by
  rcases x with ⟨x, y⟩
  simp only [offDiag, exists_mem_zipIdx, mem_eraseIdx_iff_getElem, mem_flatMap, mem_map,
    Nat.zero_add, Prod.ext_iff, ← exists_and_right, exists_and_left, @exists_comm α, and_assoc,
    exists_eq_left', ne_comm]

theorem count_offDiag_eq_mul_sub_ite [DecidableEq α] (l : List α) (a b : α) :
    count (a, b) l.offDiag = count a l * count b l - if a = b then count a l else 0 := by
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
    simp only [(offDiag_cons_perm _ _).count_eq, count_append, ihl, H₁, H₂, count_cons, beq_iff_eq]
    have := Nat.le_mul_self (count c l)
    split_ifs <;> simp_all <;> grind

@[gcongr]
protected theorem Perm.offDiag {l₁ l₂ : List α} (h : l₁ ~ l₂) : l₁.offDiag ~ l₂.offDiag := by
  classical simp_all [perm_iff_count, count_offDiag_eq_mul_sub_ite]

protected theorem Nodup.offDiag (h : l.Nodup) : l.offDiag.Nodup := by
  letI := Classical.decEq α
  rw [nodup_iff_count_le_one]
  rintro ⟨x, y⟩
  rw [count_offDiag_eq_mul_sub_ite l x y]
  grind

protected theorem Nodup.of_offDiag (h : l.offDiag.Nodup) : l.Nodup := by
  letI := Classical.decEq α
  simp only [nodup_iff_count_le_one, Prod.forall, count_offDiag_eq_mul_sub_ite] at *
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

/-- `List.offDiag l` has no duplicates iff the original list has no duplicates. -/
@[simp]
theorem nodup_offDiag : l.offDiag.Nodup ↔ l.Nodup := ⟨.of_offDiag, .offDiag⟩

/-- If `l : List α` is a list with no duplicates, then `x : α × α` belongs to `List.offDiag l`
iff both components of `x` belong to `l` and they are not equal. -/
theorem Nodup.mem_offDiag (h : l.Nodup) {x : α × α} :
    x ∈ l.offDiag ↔ x.1 ∈ l ∧ x.2 ∈ l ∧ x.1 ≠ x.2 := by
  rcases x with ⟨x, y⟩
  simp_rw [mem_offDiag_iff_getElem, mem_iff_getElem, Ne]
  constructor
  · rintro ⟨i, hi, j, hj, hne, rfl, rfl⟩
    exact ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩, mt h.getElem_inj_iff.1 hne⟩
  · rintro ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩, hne⟩
    exact ⟨i, hi, j, hj, mt h.getElem_inj_iff.2 hne, rfl, rfl⟩

theorem map_prodMap_offDiag {β : Type*} (f : α → β) (l : List α) :
    map (Prod.map f f) l.offDiag = (map f l).offDiag := by
  simp [offDiag, map_flatMap, zipIdx_map, flatMap_map, eraseIdx_map, Function.comp_def]

end List
