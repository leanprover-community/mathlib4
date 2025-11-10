/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.List.Count
import Mathlib.Data.List.Enum
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Nodup

/-!
# Definition and basic properties of `List.offDiag`

In this file we define `List.offDiag l` to be the product `l.product l`
with the diagonal removed.
-/

assert_not_exists ne_of_gt

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
  simp [append_assoc, perm_append_left_iff, flatMap_map,
    ← (map_append_flatMap_perm _ _ _).congr_left, map_fun_fst_zipIdx _ (·, a)]

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

theorem count_offDiag [BEq α] [LawfulBEq α] (l : List α) (a b : α) :
    count (a, b) l.offDiag = count a l * count b l - bif a == b then count a l else 0 := by
  induction l with
  | nil => simp
  | cons c l ihl =>
    letI : DecidableEq α := instDecidableEqOfLawfulBEq
    have H₁ {x y z : α} : count (x, y) (map (z, ·) l) = if z = x then count y l else 0 := by
      split_ifs with h
      · rw [h, count_map_of_injective l (x, ·) (by simp [Function.Injective])]
      · simp [count_eq_zero, h]
    have H₂ {x y z : α} : count (x, y) (map (·, z) l) = if z = y then count x l else 0 := by
      split_ifs with h
      · rw [h, count_map_of_injective l (·, y) (by simp [Function.Injective])]
      · simp [count_eq_zero, h]
    simp only [(offDiag_cons_perm _ _).count_eq, count_append, ihl, H₁, H₂]
    split_ifs with h₁ h₂ h₂
    · have := Nat.le_mul_self (count c l)
      simp_all
      grind
    · simp_all [Bool.beq_eq_decide_eq]
      grind
    · simp [Bool.beq_eq_decide_eq, Ne.symm h₁, ← h₂, h₁]
      grind
    · simp [h₁, h₂]

/-- `List.offDiag l` has no duplicates iff the original list has no duplicates. -/
@[simp]
theorem nodup_offDiag : l.offDiag.Nodup ↔ l.Nodup := by
  simp_rw [offDiag, nodup_flatMap, forall_mem_iff_getElem, getElem_zipIdx]
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun i _ ↦ (Pairwise.map _ ?_ (h.sublist <| eraseIdx_sublist ..)), ?_⟩⟩
  · replace h := h.2
    simp only [Nodup, pairwise_iff_getElem, getElem_zipIdx] at h ⊢
    intro i j hi hj hlt heq
    specialize h i j (by simpa) (by simpa) hlt
    simp only [Function.onFun, heq, Nat.zero_add] at h
    exact h.of_map (mem_eraseIdx_iff_getElem.2 ⟨j, hj, ne_of_gt hlt, rfl⟩)
      (mem_eraseIdx_iff_getElem.2 ⟨i, hi, ne_of_lt hlt, heq⟩)
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
