/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yakov Pechersky, Eric Wieser
-/
import Mathlib.Init.Data.Nat.Notation
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Convert

/-!
# Properties of `List.enum`
-/

namespace List

variable {α β : Type*}

#align list.length_enum_from List.enumFrom_length
#align list.length_enum List.enum_length

@[simp]
theorem enumFrom_get? :
    ∀ (n) (l : List α) (m), get? (enumFrom n l) m = (fun a => (n + m, a)) <$> get? l m
  | n, [], m => rfl
  | n, a :: l, 0 => rfl
  | n, a :: l, m + 1 => (enumFrom_get? (n + 1) l m).trans <| by rw [Nat.add_right_comm]; rfl
#align list.enum_from_nth List.enumFrom_get?

@[simp]
theorem enum_get? : ∀ (l : List α) (n), get? (enum l) n = (fun a => (n, a)) <$> get? l n := by
  simp only [enum, enumFrom_get?, Nat.zero_add]; intros; trivial
#align list.enum_nth List.enum_get?

@[simp]
theorem enumFrom_map_snd : ∀ (n) (l : List α), map Prod.snd (enumFrom n l) = l
  | _, [] => rfl
  | _, _ :: _ => congr_arg (cons _) (enumFrom_map_snd _ _)
#align list.enum_from_map_snd List.enumFrom_map_snd

@[simp]
theorem enum_map_snd : ∀ l : List α, map Prod.snd (enum l) = l :=
  enumFrom_map_snd _
#align list.enum_map_snd List.enum_map_snd

theorem mem_enumFrom {x : α} {i : ℕ} :
    ∀ {j : ℕ} (xs : List α), (i, x) ∈ xs.enumFrom j → j ≤ i ∧ i < j + xs.length ∧ x ∈ xs
  | j, [] => by simp [enumFrom]
  | j, y :: ys => by
    suffices
      i = j ∧ x = y ∨ (i, x) ∈ enumFrom (j + 1) ys →
        j ≤ i ∧ i < j + (length ys + 1) ∧ (x = y ∨ x ∈ ys)
      by simpa [enumFrom, mem_enumFrom ys]
    rintro (h | h)
    · refine' ⟨Nat.le_of_eq h.1.symm, h.1 ▸ _, Or.inl h.2⟩
      apply Nat.lt_add_of_pos_right; simp
    · have ⟨hji, hijlen, hmem⟩ := mem_enumFrom _ h
      refine' ⟨_, _, _⟩
      · exact Nat.le_trans (Nat.le_succ _) hji
      · convert hijlen using 1
        omega
      · simp [hmem]
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
    map (Prod.map (· + n) id) (enumFrom k l) = enumFrom (n + k) l := by
  induction l generalizing n k <;> [rfl; simp_all [Nat.add_assoc, Nat.add_comm k, Prod.map]]
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

theorem get_enumFrom (l : List α) (n) (i : Fin (l.enumFrom n).length)
    (hi : i.1 < l.length := (by simpa using i.2)) :
    (l.enumFrom n).get i = (n + i, l.get ⟨i, hi⟩) := by
  rw [← Option.some_inj, ← get?_eq_get]
  simp [enumFrom_get?, get?_eq_get hi]
#align list.nth_le_enum_from List.get_enumFrom

theorem get_enum (l : List α) (i : Fin l.enum.length)
    (hi : i < l.length := (by simpa using i.2)) :
    l.enum.get i = (i.1, l.get ⟨i, hi⟩) := by
  convert get_enumFrom _ _ i
  exact (Nat.zero_add _).symm
#align list.nth_le_enum List.get_enum

@[simp]
theorem enumFrom_eq_nil {n : ℕ} {l : List α} : List.enumFrom n l = [] ↔ l = [] := by
  cases l <;> simp

@[simp]
theorem enum_eq_nil {l : List α} : List.enum l = [] ↔ l = [] := enumFrom_eq_nil
