/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Init.SetNotation
import Mathlib.Init.Logic
import Mathlib.Tactic.Lint

open Decidable List

universe u v w

instance (α : Type u) : Inhabited (List α) :=
  ⟨List.nil⟩

variable {α : Type u} {β : Type v} {γ : Type w}

namespace List

attribute [simp] get! get? head? headD head tail! tail? tailD getLast! getLast?
  getLastD reverseAux eraseIdx isEmpty map map₂ join filterMap dropWhile find? findSome?
  replace elem lookup drop take takeWhile foldr zipWith unzip rangeAux enumFrom init
  intersperse isPrefixOf isEqv dropLast

@[simp] lemma get_cons_zero {as : List α} : (a :: as).get ⟨0, id <| Nat.zero_lt_succ _⟩ = a := rfl
@[simp] lemma get_cons_succ {as : List α} {h : i + 1 < (a :: as).length} :
  (a :: as).get ⟨i+1, h⟩ = as.get ⟨i, Nat.lt_of_succ_lt_succ h⟩ := rfl

@[simp] lemma getLast_singleton {x : α} : [x].getLast (id (by simp)) = x := rfl
@[simp] lemma getLast_cons_cons {x : α} : (x::y::ys).getLast (id (by simp)) = (y::ys).getLast (by simp) := rfl

-- The `id <|` above is a workaround to allow Lean to unify get_cons_zero's lhs
-- in reducible transparency:
example {as : List α} {h} : (a :: as).get ⟨0, h⟩ = a := by simp

attribute [simp] iota

@[simp] theorem not_mem_nil (a : α) : ¬ a ∈ [] := fun.

@[simp] theorem mem_cons {a b : α} {l : List α} :
  a ∈ (b :: l) ↔ a = b ∨ a ∈ l :=
  ⟨fun h => by cases h <;> simp [Membership.mem, *],
   fun | Or.inl rfl => by constructor | Or.inr h => by constructor; assumption⟩

protected def bagInter {α} [BEq α] : List α → List α → List α
| [], _ => []
| _, [] => []
| a :: l₁, l₂ => if l₂.elem a then a :: List.bagInter l₁ (l₂.erase a) else List.bagInter l₁ l₂

protected def diff {α} [BEq α] : List α → List α → List α
| l, [] => l
| l₁, a :: l₂ => if l₁.elem a then List.diff (l₁.erase a) l₂ else List.diff l₁ l₂

open Option Nat

/-- Get the tail of a nonempty list, or return `[]` for `[]`. -/
def tail : List α → List α
| []    => []
| _::as => as


def mapIdxAux (f : Nat → α → β) : Nat → List α → List β
| _, [] => []
| k, a :: as => f k a :: mapIdxAux f (k+1) as

/-- Given a function `f : Nat → α → β` and `as : list α`, `as = [a₀, a₁, ...]`, returns the list
`[f 0 a₀, f 1 a₁, ...]`. -/
def mapIdx (f : Nat → α → β) (as : List α) : List β :=
  mapIdxAux f 0 as

/-- Applicative variant of `mapIdx`. -/
def mapIdxM {m : Type v → Type w} [Applicative m] (as : List α) (f : Nat → α → m β) :
  m (List β) :=
  let rec loop : Nat → List α → m (List β)
  | _,  [] => pure []
  | n, a :: as => List.cons <$> f n a <*> loop (n + 1) as
  loop 0 as

/-- `after p xs` is the suffix of `xs` after the first element that satisfies
  `p`, not including that element.
  ```lean
  after      (eq 1)       [0, 1, 2, 3] = [2, 3]
  drop_while (not ∘ eq 1) [0, 1, 2, 3] = [1, 2, 3]
  ```
-/
def after (p : α → Prop) [DecidablePred p] : List α → List α
| [] => []
| x :: xs => if p x then xs else after p xs

def findIdx (p : α → Prop) [DecidablePred p] : List α → Nat
| [] => 0
| a :: l => if p a then 0 else succ (findIdx p l)

def indexOf [BEq α] (a : α) : List α → Nat := findIdx (a == ·)

@[simp] def removeNth : List α → Nat → List α
| [], _ => []
| _ :: xs, 0 => xs
| x :: xs, i+1 => x :: removeNth xs i

def bor (l : List Bool) : Bool := any l id

def band (l : List Bool) : Bool := all l id

-- TODO(Mario): restore `protected` when general `insert` is added
def insert [DecidableEq α] (a : α) (l : List α) : List α :=
  if a ∈ l then l else a :: l

protected def union [DecidableEq α] (l₁ l₂ : List α) : List α :=
  foldr insert l₂ l₁

instance [DecidableEq α] : Union (List α) :=
  ⟨List.union⟩

protected def inter [DecidableEq α] (l₁ l₂ : List α) : List α :=
  filter (· ∈ l₂) l₁

instance [DecidableEq α] : Inter (List α) := ⟨List.inter⟩

@[simp] def repeat' (a : α) : Nat → List α
| 0 => []
| succ n => a :: repeat' a n

def last! [Inhabited α] : List α → α
| [] => panic! "empty list"
| [a] => a
| [_, b] => b
| _ :: _ :: l => last! l
