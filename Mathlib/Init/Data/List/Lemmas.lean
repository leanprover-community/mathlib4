/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn
-/
import Batteries.Data.List.Lemmas
import Mathlib.Mathport.Rename
import Mathlib.Tactic.Cases

/-!
# Note about `Mathlib/Init/`
The files in `Mathlib/Init` are leftovers from the port from Mathlib3.
(They contain content moved from lean3 itself that Mathlib needed but was not moved to lean4.)

We intend to move all the content of these files out into the main `Mathlib` directory structure.
Contributions assisting with this are appreciated.

`#align` statements without corresponding declarations
(i.e. because the declaration is in Batteries or Lean) can be left here.
These will be deleted soon so will not significantly delay deleting otherwise empty `Init` files.

# Lemmas for `List` not (yet) in `Batteries`
-/

universe u v w w₁ w₂

variable {α : Type u} {β : Type v} {γ : Type w}

namespace List

open Nat

/-! append -/

/-! length -/

/-! map -/

/-! bind -/

/-! mem -/

theorem mem_cons_eq (a y : α) (l : List α) : (a ∈ y :: l) = (a = y ∨ a ∈ l) :=
  propext List.mem_cons

alias ⟨eq_or_mem_of_mem_cons, _⟩ := mem_cons

theorem not_exists_mem_nil (p : α → Prop) : ¬∃ x ∈ @nil α, p x :=
  fun ⟨_, hx, _⟩ => List.not_mem_nil _ hx

@[deprecated (since := "2024-03-23")] alias not_bex_nil := not_exists_mem_nil
@[deprecated (since := "2024-03-23")] alias bex_cons := exists_mem_cons

/-! list subset -/
-- This is relying on an automatically generated instance name from Batteries.

/-! sublists -/

alias length_le_of_sublist := Sublist.length_le

/-! filter -/

/-! map_accumr -/


section MapAccumr

variable {φ : Type w₁} {σ : Type w₂}

/-- Runs a function over a list returning the intermediate results and a final result. -/
def mapAccumr (f : α → σ → σ × β) : List α → σ → σ × List β
  | [], c => (c, [])
  | y :: yr, c =>
    let r := mapAccumr f yr c
    let z := f y r.1
    (z.1, z.2 :: r.2)

/-- Length of the list obtained by `mapAccumr`. -/
@[simp]
theorem length_mapAccumr :
    ∀ (f : α → σ → σ × β) (x : List α) (s : σ), length (mapAccumr f x s).2 = length x
  | f, _ :: x, s => congr_arg succ (length_mapAccumr f x s)
  | _, [], _ => rfl

end MapAccumr

section MapAccumr₂

variable {φ : Type w₁} {σ : Type w₂}

/-- Runs a function over two lists returning the intermediate results and a final result. -/
def mapAccumr₂ (f : α → β → σ → σ × φ) : List α → List β → σ → σ × List φ
  | [], _, c => (c, [])
  | _, [], c => (c, [])
  | x :: xr, y :: yr, c =>
    let r := mapAccumr₂ f xr yr c
    let q := f x y r.1
    (q.1, q.2 :: r.2)

/-- Length of a list obtained using `mapAccumr₂`. -/
@[simp]
theorem length_mapAccumr₂ :
    ∀ (f : α → β → σ → σ × φ) (x y c), length (mapAccumr₂ f x y c).2 = min (length x) (length y)
  | f, _ :: x, _ :: y, c =>
    calc
      succ (length (mapAccumr₂ f x y c).2) = succ (min (length x) (length y)) :=
        congr_arg succ (length_mapAccumr₂ f x y c)
      _ = min (succ (length x)) (succ (length y)) := Eq.symm (succ_min_succ (length x) (length y))
  | _, _ :: _, [], _ => rfl
  | _, [], _ :: _, _ => rfl
  | _, [], [], _ => rfl

end MapAccumr₂

end List
