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

universe u

variable {α : Type u}

section InsertIdx

variable {a : α}

theorem get_insertIdx_of_lt (l : List α) (x : α) (n k : ℕ) (hn : k < n) (hk : k < l.length)
    (hk' : k < (insertIdx n x l).length := hk.trans_le (length_le_length_insertIdx _ _ _)) :
    (insertIdx n x l).get ⟨k, hk'⟩ = l.get ⟨k, hk⟩ := by
  simp_all [getElem_insertIdx_of_lt]

theorem get_insertIdx_self (l : List α) (x : α) (n : ℕ) (hn : n ≤ l.length)
    (hn' : n < (insertIdx n x l).length :=
      (by rwa [length_insertIdx_of_le_length hn, Nat.lt_succ_iff])) :
    (insertIdx n x l).get ⟨n, hn'⟩ = x := by
  simp [hn, hn']

theorem getElem_insertIdx_add_succ (l : List α) (x : α) (n k : ℕ) (hk' : n + k < l.length)
    (hk : n + k + 1 < (insertIdx n x l).length := (by
      rwa [length_insertIdx_of_le_length (by omega), Nat.succ_lt_succ_iff])) :
    (insertIdx n x l)[n + k + 1] = l[n + k] := by
  rw [getElem_insertIdx_of_ge (by omega)]
  simp only [Nat.add_one_sub_one]

theorem get_insertIdx_add_succ (l : List α) (x : α) (n k : ℕ) (hk' : n + k < l.length)
    (hk : n + k + 1 < (insertIdx n x l).length := (by
      rwa [length_insertIdx_of_le_length (by omega), Nat.succ_lt_succ_iff])) :
    (insertIdx n x l).get ⟨n + k + 1, hk⟩ = get l ⟨n + k, hk'⟩ := by
  simp [getElem_insertIdx_add_succ, hk, hk']

set_option linter.unnecessarySimpa false in
theorem insertIdx_injective (n : ℕ) (x : α) : Function.Injective (insertIdx n x) := by
  induction' n with n IH
  · have : insertIdx 0 x = cons x := funext fun _ => rfl
    simp [this]
  · rintro (_ | ⟨a, as⟩) (_ | ⟨b, bs⟩) h <;> simpa [IH.eq_iff] using h

@[deprecated (since := "2024-10-21")] alias insertNth_zero := insertIdx_zero
@[deprecated (since := "2024-10-21")] alias insertNth_succ_nil := insertIdx_succ_nil
@[deprecated (since := "2024-10-21")] alias insertNth_succ_cons := insertIdx_succ_cons
@[deprecated (since := "2024-10-21")] alias length_insertNth := length_insertIdx
@[deprecated (since := "2024-10-21")] alias removeNth_insertIdx := eraseIdx_insertIdx
@[deprecated (since := "2024-05-04")] alias removeNth_insertNth := eraseIdx_insertIdx
@[deprecated (since := "2024-10-21")] alias insertNth_eraseIdx_of_ge := insertIdx_eraseIdx_of_ge
@[deprecated (since := "2024-05-04")] alias insertNth_removeNth_of_ge := insertIdx_eraseIdx_of_ge
@[deprecated (since := "2024-10-21")] alias insertNth_eraseIdx_of_le := insertIdx_eraseIdx_of_le
@[deprecated (since := "2024-05-04")] alias insertIdx_removeNth_of_le := insertIdx_eraseIdx_of_le
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
