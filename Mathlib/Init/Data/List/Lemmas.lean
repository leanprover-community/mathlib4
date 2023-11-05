/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn
-/
import Mathlib.Init.Data.List.Basic
import Mathlib.Init.Function
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Tactic.Cases

/-!
Lemmas for `List` not (yet) in `Std`
-/

#align_import init.data.list.lemmas from "leanprover-community/lean"@"4a03bdeb31b3688c31d02d7ff8e0ff2e5d6174db"

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


theorem not_bex_nil (p : α → Prop) : ¬∃ x ∈ @nil α, p x := fun ⟨_, hx, _⟩ => List.not_mem_nil _ hx


theorem bex_cons (p : α → Prop) (a : α) (l : List α) : (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x :=
  ⟨fun ⟨x, h, px⟩ => by
    simp only [find?, mem_cons] at h
    cases' h with h h
    · cases h; exact Or.inl px;
    · exact Or.inr ⟨x, h, px⟩,
  fun o =>
    o.elim (fun pa => ⟨a, mem_cons_self _ _, pa⟩) fun ⟨x, h, px⟩ => ⟨x, mem_cons_of_mem _ h, px⟩⟩


/-! list subset -/

-- This is relying on an automatically generated instance name from Std.
-- See https://github.com/leanprover/lean4/issues/2343

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
