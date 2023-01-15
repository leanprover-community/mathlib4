/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Mathport.Rename
import Std.Data.List.Basic
import Std.Data.List.Lemmas
import Mathlib.Init.Data.Nat.Notation
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Data.List.Basic
/-!
Lemmas for `List` not (yet) in `Std`
-/


open List Nat

namespace List

#align list.length_map₂ List.length_zipWith

#align list.ball_nil List.forall_mem_nil
#align list.ball_cons List.forall_mem_consₓ -- explicit → implicit arguments
#align list.mem_cons_iff List.mem_cons
#align list.sublist.cons2 List.Sublist.cons₂

section MapAccumr

variable {φ : Type w₁} {σ : Type w₂}

/-- Runs a function over a list returning the intermediate results and a
a final result.
-/
def mapAccumr (f : α → σ → σ × β) : List α → σ → σ × List β
  | [], c => (c, [])
  | y :: yr, c =>
    let r := mapAccumr f yr c
    let z := f y r.1
    (z.1, z.2 :: r.2)
#align list.map_accumr List.mapAccumr

/-- Length of the list obtained by `mapAccumr`. -/
@[simp]
theorem length_mapAccumr : ∀ (f : α → σ → σ × β) (x : List α) (s : σ),
    length (mapAccumr f x s).2 = length x
  | f, _ :: x, s => congrArg succ (length_mapAccumr f x s)
  | _, [], _ => rfl
#align list.length_map_accumr List.length_mapAccumr

end MapAccumr
section MapAccumr₂

variable {φ : Type w₁} {σ : Type w₂}

/-- Runs a function over two lists returning the intermediate results and a
 a final result.
-/
def mapAccumr₂ (f : α → β → σ → σ × φ) : List α → List β → σ → σ × List φ
  | [], _, c => (c, [])
  | _, [], c => (c, [])
  | x :: xr, y :: yr, c =>
    let r := mapAccumr₂ f xr yr c
    let q := f x y r.1
    (q.1, q.2 :: r.2)
#align list.map_accumr₂ List.mapAccumr₂

/-- Length of a list obtained using `mapAccumr₂`. -/
@[simp]
theorem length_mapAccumr₂ :
    ∀ (f : α → β → σ → σ × φ) (x y c), length (mapAccumr₂ f x y c).2 = min (length x) (length y)
  | f, _ :: x, _ :: y, c =>
    calc
      succ (length (mapAccumr₂ f x y c).2) = succ (min (length x) (length y)) :=
        congrArg succ (length_mapAccumr₂ f x y c)
      _ = min (succ (length x)) (succ (length y)) := Eq.symm (min_succ_succ (length x) (length y))

  | _, _ :: _, [], _ => rfl
  | _, [], _ :: _, _ => rfl
  | _, [], [], _ => rfl
#align list.length_map_accumr₂ List.length_mapAccumr₂

end MapAccumr₂

end List
