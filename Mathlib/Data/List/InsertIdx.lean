/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.Data.List.Basic

/-!
# insertIdx

Proves various lemmas about `List.insertIdx`.
-/

assert_not_exists Set.range

open Function

open Nat hiding one_pos

namespace List

universe u v

variable {α : Type u} {β : Type v}

section InsertIdx

variable {a : α}

@[simp]
theorem sublist_insertIdx (l : List α) (n : ℕ) (a : α) : l <+ (l.insertIdx n a) := by
  simpa only [eraseIdx_insertIdx] using eraseIdx_sublist (l.insertIdx n a) n

@[simp]
theorem subset_insertIdx (l : List α) (n : ℕ) (a : α) : l ⊆ l.insertIdx n a :=
  (sublist_insertIdx ..).subset

/-- Erasing `n`th element of a list, then inserting `a` at the same place
is the same as setting `n`th element to `a`.

We assume that `n ≠ length l`, because otherwise LHS equals `l ++ [a]` while RHS equals `l`. -/
@[simp]
theorem insertIdx_eraseIdx {l : List α} {n : ℕ} (hn : n ≠ length l) (a : α) :
    (l.eraseIdx n).insertIdx n a = l.set n a := by
  induction n generalizing l <;> cases l <;> simp_all

theorem insertIdx_eraseIdx_getElem {l : List α} {n : ℕ} (hn : n < length l) :
    (l.eraseIdx n).insertIdx n l[n] = l := by
  simp [hn.ne]

theorem eq_or_mem_of_mem_insertIdx {l : List α} {n : ℕ} {a b : α} (h : a ∈ l.insertIdx n b) :
    a = b ∨ a ∈ l := by
  cases Nat.lt_or_ge (length l) n with
  | inl hn =>
    rw [insertIdx_of_length_lt hn] at h
    exact .inr h
  | inr hn =>
    rwa [mem_insertIdx hn] at h

theorem insertIdx_subset_cons (n : ℕ) (a : α) (l : List α) : l.insertIdx n a ⊆ a :: l := by
  intro b hb
  simpa using eq_or_mem_of_mem_insertIdx hb

theorem insertIdx_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} {a : α} {n : ℕ}
    (hl : ∀ x ∈ l, p x) (ha : p a) :
    (l.pmap f hl).insertIdx n (f a ha) = (l.insertIdx n a).pmap f
      (fun _ h ↦ (eq_or_mem_of_mem_insertIdx h).elim (fun heq ↦ heq ▸ ha) (hl _)) := by
  induction n generalizing l with
  | zero => cases l <;> simp
  | succ n ihn => cases l <;> simp_all

theorem map_insertIdx (f : α → β) (l : List α) (n : ℕ) (a : α) :
    (l.insertIdx n a).map f = (l.map f).insertIdx n (f a) := by
  simpa only [pmap_eq_map] using (insertIdx_pmap (fun a _ ↦ f a) (fun _ _ ↦ trivial) trivial).symm

theorem eraseIdx_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (hl : ∀ a ∈ l, p a) (n : ℕ) :
    (pmap f l hl).eraseIdx n = (l.eraseIdx n).pmap f fun a ha ↦ hl a (eraseIdx_subset ha) :=
  match l, hl, n with
  | [], _, _ => rfl
  | a :: _, _, 0 => rfl
  | a :: as, h, n + 1 => by rw [forall_mem_cons] at h; simp [eraseIdx_pmap f h.2 n]

/-- Erasing an index commutes with `List.map`. -/
theorem eraseIdx_map (f : α → β) (l : List α) (n : ℕ) :
    (map f l).eraseIdx n = (l.eraseIdx n).map f := by
  simpa only [pmap_eq_map] using eraseIdx_pmap (fun a _ ↦ f a) (fun _ _ ↦ trivial) n

theorem get_insertIdx_of_lt (l : List α) (x : α) (n k : ℕ) (hn : k < n) (hk : k < l.length)
    (hk' : k < (l.insertIdx n x).length := hk.trans_le length_le_length_insertIdx) :
    (l.insertIdx n x).get ⟨k, hk'⟩ = l.get ⟨k, hk⟩ := by
  simp_all [getElem_insertIdx_of_lt]

theorem get_insertIdx_self (l : List α) (x : α) (n : ℕ) (hn : n ≤ l.length)
    (hn' : n < (l.insertIdx n x).length :=
      (by rwa [length_insertIdx_of_le_length hn, Nat.lt_succ_iff])) :
    (l.insertIdx n x).get ⟨n, hn'⟩ = x := by
  simp [hn, hn']

theorem getElem_insertIdx_add_succ (l : List α) (x : α) (n k : ℕ) (hk' : n + k < l.length)
    (hk : n + k + 1 < (l.insertIdx n x).length := (by
      rwa [length_insertIdx_of_le_length (by omega), Nat.succ_lt_succ_iff])) :
    (l.insertIdx n x)[n + k + 1] = l[n + k] := by
  rw [getElem_insertIdx_of_gt (by omega)]
  simp only [Nat.add_one_sub_one]

theorem get_insertIdx_add_succ (l : List α) (x : α) (n k : ℕ) (hk' : n + k < l.length)
    (hk : n + k + 1 < (l.insertIdx n x).length := (by
      rwa [length_insertIdx_of_le_length (by omega), Nat.succ_lt_succ_iff])) :
    (l.insertIdx n x).get ⟨n + k + 1, hk⟩ = get l ⟨n + k, hk'⟩ := by
  simp [getElem_insertIdx_add_succ, hk, hk']

set_option linter.unnecessarySimpa false in
theorem insertIdx_injective (n : ℕ) (x : α) :
    Function.Injective (fun l : List α => l.insertIdx n x) := by
  induction n with
  | zero => simp
  | succ n IH => rintro (_ | ⟨a, as⟩) (_ | ⟨b, bs⟩) h <;> simpa [IH.eq_iff] using h

@[deprecated (since := "2024-10-21")] alias insertNth_zero := insertIdx_zero
@[deprecated (since := "2024-10-21")] alias insertNth_succ_nil := insertIdx_succ_nil
@[deprecated (since := "2024-10-21")] alias insertNth_succ_cons := insertIdx_succ_cons
@[deprecated (since := "2024-10-21")] alias length_insertNth := length_insertIdx
@[deprecated (since := "2024-10-21")] alias removeNth_insertIdx := eraseIdx_insertIdx
@[deprecated (since := "2024-10-21")] alias insertNth_eraseIdx_of_ge := insertIdx_eraseIdx_of_ge
@[deprecated (since := "2024-10-21")] alias insertNth_eraseIdx_of_le := insertIdx_eraseIdx_of_le
@[deprecated (since := "2024-10-21")] alias insertNth_comm := insertIdx_comm
@[deprecated (since := "2024-10-21")] alias mem_insertNth := mem_insertIdx
@[deprecated (since := "2024-10-21")] alias insertNth_of_length_lt := insertIdx_of_length_lt
@[deprecated (since := "2024-10-21")] alias insertNth_length_self := insertIdx_length_self
@[deprecated (since := "2024-10-21")] alias length_le_length_insertNth := length_le_length_insertIdx
@[deprecated (since := "2024-10-21")] alias length_insertNth_le_succ := length_insertIdx_le_succ
@[deprecated (since := "2024-10-21")] alias getElem_insertNth_of_lt := getElem_insertIdx_of_lt
@[deprecated (since := "2024-10-21")] alias get_insertNth_of_lt := get_insertIdx_of_lt
@[deprecated (since := "2024-10-21")] alias getElem_insertNth_self := getElem_insertIdx_self
@[deprecated (since := "2024-10-21")] alias get_insertNth_self := get_insertIdx_self
@[deprecated (since := "2024-10-21")] alias getElem_insertNth_add_succ := getElem_insertIdx_add_succ
@[deprecated (since := "2024-10-21")] alias get_insertNth_add_succ := get_insertIdx_add_succ
@[deprecated (since := "2024-10-21")] alias insertNth_injective := insertIdx_injective

end InsertIdx

end List
