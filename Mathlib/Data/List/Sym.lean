/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Sym.Sym2

/-! # Unordered tuples of elements of a list

Defines `List.sym` and the specialized `List.sym2` for computing lists of all unordered n-tuples
from a given list. These are list versions of `Nat.multichoose`.

## Main declarations

* `List.sym`: `xs.sym n` is a list of all unordered n-tuples of elements from `xs`,
  with multiplicity. The list's values are in `Sym α n`.
* `List.sym2`: `xs.sym2` is a list of all unordered pairs of elements from `xs`,
  with multiplicity. The list's values are in `Sym2 α`.

## Todo

* Prove `protected theorem Perm.sym (n : ℕ) {xs ys : List α} (h : xs ~ ys) : xs.sym n ~ ys.sym n`
  and lift the result to `Multiset` and `Finset`.

-/

namespace List

variable {α : Type*}

section Sym2

/-- `xs.sym2` is a list of all unordered pairs of elements from `xs`.
If `xs` has no duplicates then neither does `xs.sym2`. -/
protected def sym2 : List α → List (Sym2 α)
  | [] => []
  | x :: xs => (x :: xs).map (fun y => s(x, y)) ++ xs.sym2

theorem mem_sym2_cons_iff {x : α} {xs : List α} {z : Sym2 α} :
    z ∈ (x :: xs).sym2 ↔ z = s(x, x) ∨ (∃ y, y ∈ xs ∧ z = s(x, y)) ∨ z ∈ xs.sym2 := by
  simp only [List.sym2, map_cons, cons_append, mem_cons, mem_append, mem_map]
  simp only [eq_comm]

@[simp]
theorem sym2_eq_nil_iff {xs : List α} : xs.sym2 = [] ↔ xs = [] := by
  cases xs <;> simp [List.sym2]

theorem left_mem_of_mk_mem_sym2 {xs : List α} {a b : α}
    (h : s(a, b) ∈ xs.sym2) : a ∈ xs := by
  induction xs with
  | nil => exact (not_mem_nil _ h).elim
  | cons x xs ih =>
    rw [mem_cons]
    rw [mem_sym2_cons_iff] at h
    obtain (h | ⟨c, hc, h⟩ | h) := h
    · rw [Sym2.eq_iff, ← and_or_left] at h
      exact .inl h.1
    · rw [Sym2.eq_iff] at h
      obtain (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) := h <;> simp [hc]
    · exact .inr <| ih h

theorem right_mem_of_mk_mem_sym2 {xs : List α} {a b : α}
    (h : s(a, b) ∈ xs.sym2) : b ∈ xs := by
  rw [Sym2.eq_swap] at h
  exact left_mem_of_mk_mem_sym2 h

theorem mk_mem_sym2 {xs : List α} {a b : α} (ha : a ∈ xs) (hb : b ∈ xs) :
    s(a, b) ∈ xs.sym2 := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rw [mem_sym2_cons_iff]
    rw [mem_cons] at ha hb
    obtain (rfl | ha) := ha <;> obtain (rfl | hb) := hb
    · left; rfl
    · right; left; use b
    · right; left; rw [Sym2.eq_swap]; use a
    · right; right; exact ih ha hb

theorem mk_mem_sym2_iff {xs : List α} {a b : α} :
    s(a, b) ∈ xs.sym2 ↔ a ∈ xs ∧ b ∈ xs := by
  constructor
  · intro h
    exact ⟨left_mem_of_mk_mem_sym2 h, right_mem_of_mk_mem_sym2 h⟩
  · rintro ⟨ha, hb⟩
    exact mk_mem_sym2 ha hb

theorem mem_sym2_iff {xs : List α} {z : Sym2 α} :
    z ∈ xs.sym2 ↔ ∀ y ∈ z, y ∈ xs := by
  refine z.ind (fun a b => ?_)
  simp [mk_mem_sym2_iff]

protected theorem Nodup.sym2 {xs : List α} (h : xs.Nodup) : xs.sym2.Nodup := by
  induction xs with
  | nil => simp only [List.sym2, nodup_nil]
  | cons x xs ih =>
    rw [List.sym2]
    specialize ih h.of_cons
    rw [nodup_cons] at h
    refine Nodup.append (Nodup.cons ?notmem (h.2.map ?inj)) ih ?disj
    case disj =>
      intro z hz hz'
      simp only [mem_cons, mem_map] at hz
      obtain ⟨_, (rfl | _), rfl⟩ := hz
        <;> simp [left_mem_of_mk_mem_sym2 hz'] at h
    case notmem =>
      intro h'
      simp only [h.1, mem_map, Sym2.eq_iff, true_and, or_self, exists_eq_right] at h'
    case inj =>
      intro a b
      simp only [Sym2.eq_iff, true_and]
      rintro (rfl | ⟨rfl, rfl⟩) <;> rfl

protected theorem Perm.sym2 {xs ys : List α} (h : xs ~ ys) :
    xs.sym2 ~ ys.sym2 := by
  induction h with
  | nil => rfl
  | cons x h ih =>
    simp only [List.sym2, map_cons, cons_append, perm_cons]
    exact (h.map _).append ih
  | swap x y xs =>
    simp only [List.sym2, map_cons, cons_append]
    conv => enter [1,2,1]; rw [Sym2.eq_swap]
    -- Explicit permutation to speed up simps that follow.
    refine Perm.trans (Perm.swap ..) (Perm.trans (Perm.cons _ ?_) (Perm.swap ..))
    simp only [← Multiset.coe_eq_coe, ← Multiset.cons_coe,
      ← Multiset.coe_add, ← Multiset.singleton_add]
    simp only [add_assoc, add_left_comm]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

protected theorem Sublist.sym2 {xs ys : List α} (h : xs <+ ys) : xs.sym2 <+ ys.sym2 := by
  induction h with
  | slnil => apply slnil
  | cons a h ih =>
    simp only [List.sym2]
    exact Sublist.append (nil_sublist _) ih
  | cons₂ a h ih =>
    simp only [List.sym2, map_cons, cons_append]
    exact cons₂ _ (append (Sublist.map _ h) ih)

protected theorem Subperm.sym2 {xs ys : List α} (h : xs <+~ ys) : xs.sym2 <+~ ys.sym2 := by
  obtain ⟨xs', hx, h⟩ := h
  exact hx.sym2.symm.subperm.trans h.sym2.subperm

theorem length_sym2 {xs : List α} : xs.sym2.length = Nat.choose (xs.length + 1) 2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.sym2, length_append, length_map, length_cons,
        Nat.choose_succ_succ, ← ih, Nat.choose_one_right]

end Sym2

section Sym

/-- `xs.sym n` is all unordered `n`-tuples from the list `xs` in some order. -/
protected def sym : (n : ℕ) → List α → List (Sym α n)
  | 0, _ => [.nil]
  | _, [] => []
  | n + 1, x :: xs => ((x :: xs).sym n |>.map fun p => x ::ₛ p) ++ xs.sym (n + 1)

variable {xs ys : List α} {n : ℕ}

theorem sym_one_eq : xs.sym 1 = xs.map (· ::ₛ .nil) := by
  induction xs with
  | nil => simp only [List.sym, Nat.succ_eq_add_one, Nat.reduceAdd, map_nil]
  | cons x xs ih =>
    rw [map_cons, ← ih, List.sym, List.sym, map_singleton, singleton_append]

theorem sym2_eq_sym_two : xs.sym2.map (Sym2.equivSym α) = xs.sym 2 := by
  induction xs with
  | nil => simp only [List.sym, map_eq_nil, sym2_eq_nil_iff]
  | cons x xs ih =>
    rw [List.sym, ← ih, sym_one_eq, map_map, List.sym2, map_append, map_map]
    rfl

theorem sym_map {β : Type*} (f : α → β) (n : ℕ) (xs : List α) :
    (xs.map f).sym n = (xs.sym n).map (Sym.map f) :=
  match n, xs with
  | 0, _ => by simp only [List.sym]; rfl
  | n + 1, [] => by simp [List.sym]
  | n + 1, x :: xs => by
    rw [map_cons, List.sym, ← map_cons, sym_map f n (x :: xs), sym_map f (n + 1) xs]
    simp only [map_map, List.sym, map_append, append_cancel_right_eq]
    congr
    ext s
    simp only [Function.comp_apply, Sym.map_cons]

protected theorem Sublist.sym (n : ℕ) {xs ys : List α} (h : xs <+ ys) : xs.sym n <+ ys.sym n :=
  match n, h with
  | 0, _ => by simp [List.sym]
  | n + 1, .slnil => by simp only [refl]
  | n + 1, .cons a h => by
    rw [List.sym, ← nil_append (List.sym (n + 1) xs)]
    apply Sublist.append (nil_sublist _)
    exact h.sym (n + 1)
  | n + 1, .cons₂ a h => by
    rw [List.sym, List.sym]
    apply Sublist.append
    · exact ((cons₂ a h).sym n).map _
    · exact h.sym (n + 1)

theorem sym_sublist_sym_cons {a : α} : xs.sym n <+ (a :: xs).sym n :=
  (sublist_cons a xs).sym n

theorem mem_of_mem_of_mem_sym {n : ℕ} {xs : List α} {a : α} {z : Sym α n}
    (ha : a ∈ z) (hz : z ∈ xs.sym n) : a ∈ xs :=
  match n, xs with
  | 0, xs => by
    cases Sym.eq_nil_of_card_zero z
    simp at ha
  | n + 1, [] => by simp [List.sym] at hz
  | n + 1, x :: xs => by
    rw [List.sym, mem_append, mem_map] at hz
    obtain ⟨z, hz, rfl⟩ | hz := hz
    · rw [Sym.mem_cons] at ha
      obtain rfl | ha := ha
      · simp
      · exact mem_of_mem_of_mem_sym ha hz
    · rw [mem_cons]
      right
      exact mem_of_mem_of_mem_sym ha hz

theorem first_mem_of_cons_mem_sym {xs : List α} {n : ℕ} {a : α} {z : Sym α n}
    (h : a ::ₛ z ∈ xs.sym (n + 1)) : a ∈ xs :=
  mem_of_mem_of_mem_sym (Sym.mem_cons_self a z) h

protected theorem Nodup.sym (n : ℕ) {xs : List α} (h : xs.Nodup) : (xs.sym n).Nodup :=
  match n, xs with
  | 0, _ => by simp [List.sym]
  | n + 1, [] => by simp [List.sym]
  | n + 1, x :: xs => by
    rw [List.sym]
    refine Nodup.append (Nodup.map ?inj (Nodup.sym n h)) (Nodup.sym (n + 1) h.of_cons) ?disj
    case inj =>
      intro z z'
      simp
    case disj =>
      intro z hz hz'
      rw [mem_map] at hz
      obtain ⟨z, _hz, rfl⟩ := hz
      have := first_mem_of_cons_mem_sym hz'
      simp only [nodup_cons, this, not_true_eq_false, false_and] at h

theorem length_sym {n : ℕ} {xs : List α} :
    (xs.sym n).length = Nat.multichoose xs.length n :=
  match n, xs with
  | 0, _ => by rw [List.sym, Nat.multichoose]; rfl
  | n + 1, [] => by simp [List.sym]
  | n + 1, x :: xs => by
    rw [List.sym, length_append, length_map, length_cons]
    rw [@length_sym n (x :: xs), @length_sym (n + 1) xs]
    rw [Nat.multichoose_succ_succ, length_cons, add_comm]

end Sym

end List
