/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yakov Pechersky, Eric Wieser
-/
import Batteries.Tactic.Alias
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation

/-!
# Properties of `List.enum`

## Deprecation note
Everything in this file has been replaced by theorems in Lean4,
in terms of `xs[i]?` and `xs[i]` rather than `get` and `get?`.

The results here are unused in Mathlib, and deprecated.
Any downstream users who can not easily adapt may remove the deprecations as needed.
-/

namespace List

variable {α β : Type*}

@[deprecated getElem?_enumFrom (since := "2024-08-15")]
theorem get?_enumFrom (n) (l : List α) (m) :
    get? (enumFrom n l) m = (get? l m).map fun a => (n + m, a) := by
  simp

@[deprecated (since := "2024-04-06")] alias enumFrom_get? := get?_enumFrom

@[deprecated getElem?_enum (since := "2024-08-15")]
theorem get?_enum (l : List α) (n) : get? (enum l) n = (get? l n).map fun a => (n, a) := by
  simp

@[deprecated (since := "2024-04-06")] alias enum_get? := get?_enum

@[deprecated getElem_enumFrom (since := "2024-08-15")]
theorem get_enumFrom (l : List α) (n) (i : Fin (l.enumFrom n).length) :
    (l.enumFrom n).get i = (n + i, l.get (i.cast enumFrom_length)) := by
  simp

@[deprecated getElem_enum (since := "2024-08-15")]
theorem get_enum (l : List α) (i : Fin l.enum.length) :
    l.enum.get i = (i.1, l.get (i.cast enum_length)) := by
  simp

@[deprecated mk_add_mem_enumFrom_iff_getElem? (since := "2024-08-12")]
theorem mk_add_mem_enumFrom_iff_get? {n i : ℕ} {x : α} {l : List α} :
    (n + i, x) ∈ enumFrom n l ↔ l.get? i = x := by
  simp [mem_iff_get?]

@[deprecated mk_mem_enumFrom_iff_le_and_getElem?_sub (since := "2024-08-12")]
theorem mk_mem_enumFrom_iff_le_and_get?_sub {n i : ℕ} {x : α} {l : List α} :
    (i, x) ∈ enumFrom n l ↔ n ≤ i ∧ l.get? (i - n) = x := by
  simp [mk_mem_enumFrom_iff_le_and_getElem?_sub]

@[deprecated mk_mem_enum_iff_getElem? (since := "2024-08-15")]
theorem mk_mem_enum_iff_get? {i : ℕ} {x : α} {l : List α} : (i, x) ∈ enum l ↔ l.get? i = x := by
  simp [enum, mk_mem_enumFrom_iff_le_and_getElem?_sub]

set_option linter.deprecated false in
@[deprecated mem_enum_iff_getElem? (since := "2024-08-15")]
theorem mem_enum_iff_get? {x : ℕ × α} {l : List α} : x ∈ enum l ↔ l.get? x.1 = x.2 :=
  mk_mem_enum_iff_get?

end List
