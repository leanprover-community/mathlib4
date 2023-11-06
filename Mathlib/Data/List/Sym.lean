/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Data.Sym.Sym2

/-! # Unordered tuples of elements of a list

Defines `List.sym` and the specialized `List.sym2` for computing lists of all unordered n-tuples
from a given list. These are list versions of `Nat.multichoose`.

## Main declarations

* `List.sym`: `xs.sym n` is a list of all unordered n-tuples of elements from `xs`,
  with mulitplicity. The list's values are in `Sym α n`.
* `List.sym2`: `xs.sym2` is a list of all unordered pairs of elements from `xs`,
  with multiplicity. The list's values are in `Sym2 α`.

-/

namespace List

variable {α : Type*}

section Sym

/-- `xs.sym n` is all unordered `n`-tuples from the list `xs` in some order. -/
protected def sym : (n : Nat) → List α → List (Sym α n)
  | 0, _ => [.nil]
  | _, [] => []
  | n + 1, x :: xs => ((x :: xs).sym n |>.map fun p => x ::ₛ p) ++ xs.sym (n + 1)
termination_by _ n xs => n + xs.length

theorem sym_one_eq {xs : List α} : xs.sym 1 = xs.map (· ::ₛ .nil) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [map_cons, ← ih, List.sym, List.sym, map_singleton, singleton_append]

-- theorem first_mem_of_mem_sym {xs : List α} {n : ℕ} {a : α} {as : Sym α n}
--     (h : a ::ₛ as ∈ xs.sym (n + 1)) : a ∈ xs := by
--   sorry

-- protected theorem Perm.sym2 {xs ys : List α} (h : xs ~ ys) {n : ℕ} :
--     xs.sym n ~ ys.sym n := by
--   sorry

end Sym

section Sym2

/-- `xs.sym2` is a list of all unordered pairs of elements from `xs`.
If `xs` has no duplicates then neither does `xs.sym2`. -/
protected def sym2 : List α → List (Sym2 α)
  | [] => []
  | x::xs => ((x::xs).map fun y => Quotient.mk _ (x, y)) ++ xs.sym2

theorem sym2_eq_sym {xs : List α} : xs.sym2.map (Sym2.equivSym α) = xs.sym 2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.sym, ← ih, sym_one_eq, map_map, List.sym2, map_append, map_map]
    rfl

theorem left_mem_of_mem_sym2 {xs : List α} {a b : α}
    (h : Quotient.mk _ (a, b) ∈ xs.sym2) : a ∈ xs := by
  induction xs generalizing a b with
  | nil => exact (not_mem_nil _ h).elim
  | cons x xs ih =>
    rw [mem_cons]
    simp only [List.sym2, map_cons, cons_append, mem_cons, mem_append, mem_map] at h
    obtain (h | h) := h
    · rw [Sym2.eq_iff, ← and_or_left] at h
      left; exact h.1
    · obtain (⟨c, hc, h⟩ | h) := h
      · rw [Sym2.eq_iff] at h
        obtain (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) := h
        · left; rfl
        · right; exact hc
      · right; exact ih h

theorem right_mem_of_mem_sym2 {xs : List α} {a b : α}
    (h : Quotient.mk _ (a, b) ∈ xs.sym2) : b ∈ xs := by
  rw [Sym2.eq_swap] at h
  exact left_mem_of_mem_sym2 h

theorem mem_sym2 {xs : List α} {a b : α} (ha : a ∈ xs) (hb : b ∈ xs) :
    Quotient.mk _ (a, b) ∈ xs.sym2 := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.sym2, List.map_cons]
    rw [mem_cons] at ha hb
    obtain (rfl | ha) := ha <;> obtain (rfl | hb) := hb
    · apply List.mem_append_left
      apply List.mem_cons_self
    · apply List.mem_append_left
      apply List.mem_cons_of_mem
      rw [List.mem_map]
      use b
    · apply List.mem_append_left
      apply List.mem_cons_of_mem
      rw [Sym2.eq_swap, List.mem_map]
      use a
    · apply List.mem_append_right
      exact ih ha hb

theorem mk_mem_sym2_iff {xs : List α} {a b : α} :
    Quotient.mk _ (a, b) ∈ xs.sym2 ↔ a ∈ xs ∧ b ∈ xs := by
  constructor
  · intro h
    exact ⟨left_mem_of_mem_sym2 h, right_mem_of_mem_sym2 h⟩
  · rintro ⟨ha, hb⟩
    exact mem_sym2 ha hb

protected theorem Nodup.sym2 {xs : List α} (h : xs.Nodup) : xs.sym2.Nodup := by
  induction xs with
  | nil => simp [List.sym2]
  | cons x xs ih =>
    rw [List.sym2, List.map]
    have := ih (Nodup.of_cons h)
    rw [nodup_cons] at h
    apply Nodup.append _ this
    · intro z hz hz'
      simp only [mem_cons, mem_map] at hz
      obtain (rfl | ⟨_, _, rfl⟩) := hz
        <;> simp [left_mem_of_mem_sym2 hz'] at h
    apply Nodup.cons
    · intro h'
      simp only [mem_map, Sym2.eq_iff, true_and, or_self, exists_eq_right] at h'
      simp [h'] at h
    apply Nodup.map
    · intro a b
      simp only [Sym2.eq_iff, true_and]
      rintro (rfl | ⟨rfl, rfl⟩) <;> rfl
    · exact h.2

protected theorem Perm.sym2 {xs ys : List α} (h : xs ~ ys) :
    xs.sym2 ~ ys.sym2 := by
  induction h with
  | nil => rfl
  | cons x h ih =>
    simp only [List.sym2, map_cons, cons_append, perm_cons]
    exact (h.map _).append ih
  | swap x y xs =>
    simp only [List.sym2, map_cons, cons_append]
    refine Perm.trans (Perm.swap ..) (Perm.trans ?_ (Perm.swap ..))
    rw [Sym2.eq_swap]
    apply Perm.cons
    simp only [← Multiset.coe_eq_coe, ← Multiset.cons_coe,
      ← Multiset.coe_add, ← Multiset.singleton_add]
    simp only [add_assoc, add_left_comm]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

@[simp]
theorem sym2_eq_nil {xs : List α} : xs.sym2 = [] ↔ xs = [] := by
  cases xs <;> simp [List.sym2]

end Sym2

end List
