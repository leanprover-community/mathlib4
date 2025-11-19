/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.List.Count
import Mathlib.Data.List.Enum
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.ProdSigma

/-!
# Definition and basic properties of `List.offDiag`

In this file we define `List.offDiag l` to be the product `l.product l`
with the diagonal removed.
-/

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

@[gcongr]
protected theorem Perm.offDiag {l₁ l₂ : List α} (h : l₁ ~ l₂) : l₁.offDiag ~ l₂.offDiag := by
  induction h with
  | nil => simp
  | cons x h ih => grw [offDiag_cons_perm, offDiag_cons_perm, ih, h]
  | swap x y l =>
    grw [offDiag_cons_perm, offDiag_cons_perm, offDiag_cons_perm, offDiag_cons_perm]
    simp only [map_cons, cons_append, append_assoc]
    grw [perm_middle, perm_middle, Perm.swap, perm_append_comm_assoc _ (l.map (x, ·)),
      perm_append_comm_assoc _ (l.map (x, ·)), perm_append_comm_assoc _ (l.map (·, x)),
      perm_append_comm_assoc _ (l.map (·, x))]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem mem_offDiag_iff_getElem {x : α × α} :
    x ∈ l.offDiag ↔ ∃ (i : ℕ) (_ : i < l.length) (j : ℕ) (_ : j < l.length),
      i ≠ j ∧ l[i] = x.1 ∧ l[j] = x.2 := by
  rcases x with ⟨x, y⟩
  simp only [offDiag, exists_mem_zipIdx, mem_eraseIdx_iff_getElem, mem_flatMap, mem_map,
    Nat.zero_add, Prod.ext_iff, ← exists_and_right, exists_and_left, @exists_comm α, and_assoc,
    exists_eq_left', ne_comm]

theorem count_offDiag_eq_mul_sub_bif [BEq α] [LawfulBEq α] (l : List α) (a b : α) :
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

protected theorem Nodup.offDiag (h : l.Nodup) : l.offDiag.Nodup := by
  letI := Classical.decEq α
  rw [nodup_iff_count_le_one]
  rintro ⟨x, y⟩
  rw [count_offDiag_eq_mul_sub_bif l x y]
  grind

protected theorem Nodup.of_offDiag (h : l.offDiag.Nodup) : l.Nodup := by
  letI := Classical.decEq α
  simp only [nodup_iff_count_le_one, Prod.forall, count_offDiag_eq_mul_sub_bif] at *
  intro a
  specialize h a a
  contrapose! h
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

end List
