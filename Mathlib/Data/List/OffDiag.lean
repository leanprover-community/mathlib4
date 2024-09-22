/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.Data.List.Join
import Mathlib.Data.List.Enum

/-!
# Definition and basic properties of `List.offDiag`

In this file we define `List.offDiag l` to be the product `l.product l`
with the diagonal removed.
-/

namespace List

variable {α : Type*} {l : List α}

/-- List.offDiag l` is the product `l.product l` with the diagonal removed. -/
def offDiag (l : List α) : List (α × α) :=
  l.enum.bind fun nx ↦ map (Prod.mk nx.2) <| l.eraseIdx nx.1

@[simp]
theorem offDiag_nil : offDiag ([] : List α) = [] := rfl

@[simp]
theorem offDiag_singleton (a : α) : offDiag [a] = [] := rfl

theorem length_offDiag' (l : List α) : length l.offDiag = (length l - 1) * length l := by
  have : ∀ x ∈ enum l, length (eraseIdx l x.1) = length l - 1 := fun x hx ↦
    length_eraseIdx <| fst_lt_of_mem_enum hx
  simp [offDiag, map_congr_left this, Function.comp_def, map_const', mul_comm]

@[simp]
theorem length_offDiag (l : List α) : length l.offDiag = length l ^ 2 - length l := by
  simp [length_offDiag', Nat.mul_sub_right_distrib, sq]

theorem mem_offDiag_iff_getElem {x : α × α} :
    x ∈ l.offDiag ↔ ∃ (i : ℕ) (_ : i < l.length) (j : ℕ) (_ : j < l.length),
      i ≠ j ∧ l[i] = x.1 ∧ l[j] = x.2 := by
  rcases x with ⟨x, y⟩
  simp only [offDiag, exists_mem_enum, mem_eraseIdx_iff_getElem, mem_bind, mem_map, Prod.ext_iff,
    ← exists_and_right, exists_and_left, @exists_comm α, and_assoc, exists_eq_left', ne_comm]

theorem count_offDiag_of_ne [BEq α] [LawfulBEq α] (l : List α) {a b : α} (h : a ≠ b) :
    count (a, b) l.offDiag = count a l * count b l := by
  simp_rw [offDiag, count_bind, Function.comp_def]

/-- `List.offDiag l` has no duplicates iff the original list has no duplicates. -/
@[simp]
theorem nodup_offDiag : l.offDiag.Nodup ↔ l.Nodup := by
  simp_rw [offDiag, nodup_bind, forall_mem_iff_getElem, getElem_enum]
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun i _ ↦ (Pairwise.map _ ?_ (h.sublist <| eraseIdx_sublist ..)), ?_⟩⟩
  · replace h := h.2
    simp only [Nodup, pairwise_iff_getElem, getElem_enum] at h ⊢
    intro i j hi hj hlt heq
    specialize h (i.cast enum_length.symm) (j.cast enum_length.symm) hlt
    simp only [Fin.cast_trans, Fin.cast_eq_self, Fin.coe_cast, heq] at h
    exact h.of_map (mem_eraseIdx_iff_get.2 ⟨j, ne_of_gt hlt, rfl⟩)
      (mem_eraseIdx_iff_get.2 ⟨i, ne_of_lt hlt, heq⟩)
  · intro a b h
    simp [*]
  · simp_rw [pairwise_iff_get, Disjoint, mem_map, get_enum]
    rintro i j hlt _ ⟨a, -, rfl⟩ ⟨b, -, hab⟩
    simp [h.get_inj_iff, Fin.cast, Fin.val_inj, hlt.ne'] at hab

protected alias ⟨Nodup.of_offDiag, Nodup.offDiag⟩ := nodup_offDiag

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

end List
