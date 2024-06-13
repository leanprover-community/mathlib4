/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yakov Pechersky, Eric Wieser
-/
import Mathlib.Data.List.Basic

/-!
# Properties of `List.enum`
-/

namespace List

variable {α β : Type*}

#align list.length_enum_from List.enumFrom_length
#align list.length_enum List.enum_length

@[simp]
theorem get?_enumFrom :
    ∀ n (l : List α) m, get? (enumFrom n l) m = (get? l m).map fun a => (n + m, a)
  | n, [], m => rfl
  | n, a :: l, 0 => rfl
  | n, a :: l, m + 1 => (get?_enumFrom (n + 1) l m).trans <| by rw [Nat.add_right_comm]; rfl
#align list.enum_from_nth List.get?_enumFrom

@[deprecated (since := "2024-04-06")] alias enumFrom_get? := get?_enumFrom

@[simp]
theorem get?_enum (l : List α) (n) : get? (enum l) n = (get? l n).map fun a => (n, a) := by
  rw [enum, get?_enumFrom, Nat.zero_add]
#align list.enum_nth List.get?_enum

@[deprecated (since := "2024-04-06")] alias enum_get? := get?_enum

@[simp]
theorem enumFrom_map_snd : ∀ (n) (l : List α), map Prod.snd (enumFrom n l) = l
  | _, [] => rfl
  | _, _ :: _ => congr_arg (cons _) (enumFrom_map_snd _ _)
#align list.enum_from_map_snd List.enumFrom_map_snd

@[simp]
theorem enum_map_snd (l : List α) : map Prod.snd (enum l) = l :=
  enumFrom_map_snd _ _
#align list.enum_map_snd List.enum_map_snd

@[simp]
theorem get_enumFrom (l : List α) (n) (i : Fin (l.enumFrom n).length) :
    (l.enumFrom n).get i = (n + i, l.get (i.cast enumFrom_length)) := by
  simp [get_eq_get?]
#align list.nth_le_enum_from List.get_enumFrom

@[simp]
theorem get_enum (l : List α) (i : Fin l.enum.length) :
    l.enum.get i = (i.1, l.get (i.cast enum_length)) := by
  simp [enum]
#align list.nth_le_enum List.get_enum

theorem mk_add_mem_enumFrom_iff_get? {n i : ℕ} {x : α} {l : List α} :
    (n + i, x) ∈ enumFrom n l ↔ l.get? i = x := by
  simp [mem_iff_get?]

theorem mk_mem_enumFrom_iff_le_and_get?_sub {n i : ℕ} {x : α} {l : List α} :
    (i, x) ∈ enumFrom n l ↔ n ≤ i ∧ l.get? (i - n) = x := by
  if h : n ≤ i then
    rcases Nat.exists_eq_add_of_le h with ⟨i, rfl⟩
    simp [mk_add_mem_enumFrom_iff_get?, Nat.add_sub_cancel_left]
  else
    have : ∀ k, n + k ≠ i := by rintro k rfl; simp at h
    simp [h, mem_iff_get?, this]

theorem mk_mem_enum_iff_get? {i : ℕ} {x : α} {l : List α} : (i, x) ∈ enum l ↔ l.get? i = x := by
  simp [enum, mk_mem_enumFrom_iff_le_and_get?_sub]

theorem mem_enum_iff_get? {x : ℕ × α} {l : List α} : x ∈ enum l ↔ l.get? x.1 = x.2 :=
  mk_mem_enum_iff_get?

theorem le_fst_of_mem_enumFrom {x : ℕ × α} {n : ℕ} {l : List α} (h : x ∈ enumFrom n l) :
    n ≤ x.1 :=
  (mk_mem_enumFrom_iff_le_and_get?_sub.1 h).1

theorem fst_lt_add_of_mem_enumFrom {x : ℕ × α} {n : ℕ} {l : List α} (h : x ∈ enumFrom n l) :
    x.1 < n + length l := by
  rcases mem_iff_get.1 h with ⟨i, rfl⟩
  simpa using i.is_lt

theorem fst_lt_of_mem_enum {x : ℕ × α} {l : List α} (h : x ∈ enum l) : x.1 < length l := by
  simpa using fst_lt_add_of_mem_enumFrom h

theorem snd_mem_of_mem_enumFrom {x : ℕ × α} {n : ℕ} {l : List α} (h : x ∈ enumFrom n l) : x.2 ∈ l :=
  enumFrom_map_snd n l ▸ mem_map_of_mem _ h

theorem snd_mem_of_mem_enum {x : ℕ × α} {l : List α} (h : x ∈ enum l) : x.2 ∈ l :=
  snd_mem_of_mem_enumFrom h

theorem mem_enumFrom {x : α} {i j : ℕ} (xs : List α) (h : (i, x) ∈ xs.enumFrom j) :
    j ≤ i ∧ i < j + xs.length ∧ x ∈ xs :=
  ⟨le_fst_of_mem_enumFrom h, fst_lt_add_of_mem_enumFrom h, snd_mem_of_mem_enumFrom h⟩
#align list.mem_enum_from List.mem_enumFrom

@[simp]
theorem enum_nil : enum ([] : List α) = [] :=
  rfl
#align list.enum_nil List.enum_nil

#align list.enum_from_nil List.enumFrom_nil
#align list.enum_from_cons List.enumFrom_cons

@[simp]
theorem enum_cons (x : α) (xs : List α) : enum (x :: xs) = (0, x) :: enumFrom 1 xs :=
  rfl
#align list.enum_cons List.enum_cons

@[simp]
theorem enumFrom_singleton (x : α) (n : ℕ) : enumFrom n [x] = [(n, x)] :=
  rfl
#align list.enum_from_singleton List.enumFrom_singleton

@[simp]
theorem enum_singleton (x : α) : enum [x] = [(0, x)] :=
  rfl
#align list.enum_singleton List.enum_singleton

theorem enumFrom_append (xs ys : List α) (n : ℕ) :
    enumFrom n (xs ++ ys) = enumFrom n xs ++ enumFrom (n + xs.length) ys := by
  induction' xs with x xs IH generalizing ys n
  · simp
  · rw [cons_append, enumFrom_cons, IH, ← cons_append, ← enumFrom_cons, length, Nat.add_right_comm,
      Nat.add_assoc]
#align list.enum_from_append List.enumFrom_append

theorem enum_append (xs ys : List α) : enum (xs ++ ys) = enum xs ++ enumFrom xs.length ys := by
  simp [enum, enumFrom_append]
#align list.enum_append List.enum_append

theorem map_fst_add_enumFrom_eq_enumFrom (l : List α) (n k : ℕ) :
    map (Prod.map (· + n) id) (enumFrom k l) = enumFrom (n + k) l :=
  ext_get? fun i ↦ by simp [(· ∘ ·), Nat.add_comm, Nat.add_left_comm]
#align list.map_fst_add_enum_from_eq_enum_from List.map_fst_add_enumFrom_eq_enumFrom

theorem map_fst_add_enum_eq_enumFrom (l : List α) (n : ℕ) :
    map (Prod.map (· + n) id) (enum l) = enumFrom n l :=
  map_fst_add_enumFrom_eq_enumFrom l _ _
#align list.map_fst_add_enum_eq_enum_from List.map_fst_add_enum_eq_enumFrom

theorem enumFrom_cons' (n : ℕ) (x : α) (xs : List α) :
    enumFrom n (x :: xs) = (n, x) :: (enumFrom n xs).map (Prod.map Nat.succ id) := by
  rw [enumFrom_cons, Nat.add_comm, ← map_fst_add_enumFrom_eq_enumFrom]
#align list.enum_from_cons' List.enumFrom_cons'

theorem enum_cons' (x : α) (xs : List α) :
    enum (x :: xs) = (0, x) :: (enum xs).map (Prod.map Nat.succ id) :=
  enumFrom_cons' _ _ _
#align list.enum_cons' List.enum_cons'

theorem enumFrom_map (n : ℕ) (l : List α) (f : α → β) :
    enumFrom n (l.map f) = (enumFrom n l).map (Prod.map id f) := by
  induction' l with hd tl IH
  · rfl
  · rw [map_cons, enumFrom_cons', enumFrom_cons', map_cons, map_map, IH, map_map]
    rfl
#align list.enum_from_map List.enumFrom_map

theorem enum_map (l : List α) (f : α → β) : (l.map f).enum = l.enum.map (Prod.map id f) :=
  enumFrom_map _ _ _
#align list.enum_map List.enum_map

@[simp]
theorem enumFrom_eq_nil {n : ℕ} {l : List α} : List.enumFrom n l = [] ↔ l = [] := by
  cases l <;> simp

@[simp]
theorem enum_eq_nil {l : List α} : List.enum l = [] ↔ l = [] := enumFrom_eq_nil
