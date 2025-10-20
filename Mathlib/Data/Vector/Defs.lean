/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Data.List.Defs
import Mathlib.Tactic.Common

/-!
The type `List.Vector` represents lists with fixed length.

TODO: The API of `List.Vector` is quite incomplete relative to `Vector`,
and in particular does not use `x[i]` (that is `GetElem` notation) as the preferred accessor.
Any combination of reducing the use of `List.Vector` in Mathlib, or modernising its API,
would be welcome.
-/

assert_not_exists Monoid

universe u v w
/--
`List.Vector α n` is the type of lists of length `n` with elements of type `α`.

Note that there is also `Vector α n` in the root namespace,
which is the type of *arrays* of length `n` with elements of type `α`.

Typically, if you are doing programming or verification, you will primarily use `Vector α n`,
and if you are doing mathematics, you may want to use `List.Vector α n` instead.
-/
def List.Vector (α : Type u) (n : ℕ) :=
  { l : List α // l.length = n }

namespace List.Vector

variable {α β σ φ : Type*} {n : ℕ} {p : α → Prop}

instance [DecidableEq α] : DecidableEq (Vector α n) :=
  inferInstanceAs (DecidableEq {l : List α // l.length = n})

/-- The empty vector with elements of type `α` -/
@[match_pattern]
def nil : Vector α 0 :=
  ⟨[], rfl⟩

/-- If `a : α` and `l : Vector α n`, then `cons a l`, is the vector of length `n + 1`
whose first element is a and with l as the rest of the list. -/
@[match_pattern]
def cons : α → Vector α n → Vector α (Nat.succ n)
  | a, ⟨v, h⟩ => ⟨a :: v, congrArg Nat.succ h⟩


/-- The length of a vector. -/
@[reducible, nolint unusedArguments]
def length (_ : Vector α n) : ℕ :=
  n

open Nat

/-- The first element of a vector with length at least `1`. -/
def head : Vector α (Nat.succ n) → α
  | ⟨a :: _, _⟩ => a

/-- The head of a vector obtained by prepending is the element prepended. -/
theorem head_cons (a : α) : ∀ v : Vector α n, head (cons a v) = a
  | ⟨_, _⟩ => rfl

/-- The tail of a vector, with an empty vector having empty tail. -/
def tail : Vector α n → Vector α (n - 1)
  | ⟨[], h⟩ => ⟨[], congrArg pred h⟩
  | ⟨_ :: v, h⟩ => ⟨v, congrArg pred h⟩

/-- The tail of a vector obtained by prepending is the vector prepended. to -/
theorem tail_cons (a : α) : ∀ v : Vector α n, tail (cons a v) = v
  | ⟨_, _⟩ => rfl

/-- Prepending the head of a vector to its tail gives the vector. -/
@[simp]
theorem cons_head_tail : ∀ v : Vector α (succ n), cons (head v) (tail v) = v
  | ⟨[], h⟩ => by contradiction
  | ⟨_ :: _, _⟩ => rfl

/-- The list obtained from a vector. -/
def toList (v : Vector α n) : List α :=
  v.1

/-- nth element of a vector, indexed by a `Fin` type. -/
def get (l : Vector α n) (i : Fin n) : α :=
  l.1.get <| i.cast l.2.symm

instance {n m : Nat} : HAppend (Vector α n) (Vector α m) (Vector α (n + m)) where
  hAppend | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩ => ⟨l₁ ++ l₂, by simp [*]⟩

lemma append_def {n m : Nat} :
    (HAppend.hAppend : Vector α n → Vector α m → Vector α (n + m)) =
      fun | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩ => ⟨l₁ ++ l₂, by simp [*]⟩ :=
  rfl

/-- Appending a vector to another. -/
@[deprecated "use `++` instead" (since := "2025-06-05")]
def append {n m : Nat} : Vector α n → Vector α m → Vector α (n + m)
  | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩ => ⟨l₁ ++ l₂, by simp [*]⟩

/-- Elimination rule for `Vector`. -/
@[elab_as_elim]
def elim {α} {C : ∀ {n}, Vector α n → Sort u}
    (H : ∀ l : List α, C ⟨l, rfl⟩) {n : ℕ} : ∀ v : Vector α n, C v
  | ⟨l, h⟩ =>
    match n, h with
    | _, rfl => H l

/-- Map a vector under a function. -/
def map (f : α → β) : Vector α n → Vector β n
  | ⟨l, h⟩ => ⟨List.map f l, by simp [*]⟩

/-- A `nil` vector maps to a `nil` vector. -/
@[simp]
theorem map_nil (f : α → β) : map f nil = nil :=
  rfl

/-- `map` is natural with respect to `cons`. -/
@[simp]
theorem map_cons (f : α → β) (a : α) : ∀ v : Vector α n, map f (cons a v) = cons (f a) (map f v)
  | ⟨_, _⟩ => rfl

/-- Map a vector under a partial function. -/
def pmap (f : (a : α) → p a → β) :
    (v : Vector α n) → (∀ x ∈ v.toList, p x) → Vector β n
  | ⟨l, h⟩, hp => ⟨List.pmap f l hp, by simp [h]⟩

@[simp]
theorem pmap_nil (f : (a : α) → p a → β) (hp : ∀ x ∈ nil.toList, p x) :
    nil.pmap f hp = nil := rfl

/-- Mapping two vectors under a curried function of two variables. -/
def map₂ (f : α → β → φ) : Vector α n → Vector β n → Vector φ n
  | ⟨x, _⟩, ⟨y, _⟩ => ⟨List.zipWith f x y, by simp [*]⟩

/-- Vector obtained by repeating an element. -/
def replicate (n : ℕ) (a : α) : Vector α n :=
  ⟨List.replicate n a, List.length_replicate⟩

/-- Drop `i` elements from a vector of length `n`; we can have `i > n`. -/
def drop (i : ℕ) : Vector α n → Vector α (n - i)
  | ⟨l, p⟩ => ⟨List.drop i l, by simp [*]⟩

/-- Take `i` elements from a vector of length `n`; we can have `i > n`. -/
def take (i : ℕ) : Vector α n → Vector α (min i n)
  | ⟨l, p⟩ => ⟨List.take i l, by simp [*]⟩

/-- Remove the element at position `i` from a vector of length `n`. -/
def eraseIdx (i : Fin n) : Vector α n → Vector α (n - 1)
  | ⟨l, p⟩ => ⟨List.eraseIdx l i.1, by rw [l.length_eraseIdx_of_lt] <;> rw [p]; exact i.2⟩

/-- Vector of length `n` from a function on `Fin n`. -/
def ofFn : ∀ {n}, (Fin n → α) → Vector α n
  | 0, _ => nil
  | _ + 1, f => cons (f 0) (ofFn fun i ↦ f i.succ)

/-- Create a vector from another with a provably equal length. -/
protected def congr {n m : ℕ} (h : n = m) : Vector α n → Vector α m
  | ⟨x, p⟩ => ⟨x, h ▸ p⟩

section Accum

open Prod

/-- Runs a function over a vector returning the intermediate results and a
final result.
-/
def mapAccumr (f : α → σ → σ × β) : Vector α n → σ → σ × Vector β n
  | ⟨x, px⟩, c =>
    let res := List.mapAccumr f x c
    ⟨res.1, res.2, by simp [*, res]⟩

/-- Runs a function over a pair of vectors returning the intermediate results and a
final result.
-/
def mapAccumr₂ (f : α → β → σ → σ × φ) : Vector α n → Vector β n → σ → σ × Vector φ n
  | ⟨x, px⟩, ⟨y, py⟩, c =>
    let res := List.mapAccumr₂ f x y c
    ⟨res.1, res.2, by simp [*, res]⟩

end Accum

/-! ### Shift Primitives -/
section Shift

/-- `shiftLeftFill v i` is the vector obtained by left-shifting `v` `i` times and padding with the
    `fill` argument. If `v.length < i` then this will return `replicate n fill`. -/
def shiftLeftFill (v : Vector α n) (i : ℕ) (fill : α) : Vector α n :=
  Vector.congr (by simp) (drop i v ++ replicate (min n i) fill)

/-- `shiftRightFill v i` is the vector obtained by right-shifting `v` `i` times and padding with the
    `fill` argument. If `v.length < i` then this will return `replicate n fill`. -/
def shiftRightFill (v : Vector α n) (i : ℕ) (fill : α) : Vector α n :=
  Vector.congr (by omega) (replicate (min n i) fill ++ take (n - i) v)

end Shift


/-! ### Basic Theorems -/
/-- Vector is determined by the underlying list. -/
protected theorem eq {n : ℕ} : ∀ a1 a2 : Vector α n, toList a1 = toList a2 → a1 = a2
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- A vector of length `0` is a `nil` vector. -/
protected theorem eq_nil (v : Vector α 0) : v = nil :=
  v.eq nil (List.eq_nil_of_length_eq_zero v.2)

/-- Vector of length from a list `v`
with witness that `v` has length `n` maps to `v` under `toList`. -/
@[simp]
theorem toList_mk (v : List α) (P : List.length v = n) : toList (Subtype.mk v P) = v :=
  rfl

/-- A nil vector maps to a nil list. -/
@[simp]
theorem toList_nil : toList nil = @List.nil α :=
  rfl

/-- The length of the list to which a vector of length `n` maps is `n`. -/
@[simp]
theorem toList_length (v : Vector α n) : (toList v).length = n :=
  v.2

/-- `toList` of `cons` of a vector and an element is
the `cons` of the list obtained by `toList` and the element -/
@[simp]
theorem toList_cons (a : α) (v : Vector α n) : toList (cons a v) = a :: toList v := by
  cases v; rfl

/-- Appending of vectors corresponds under `toList` to appending of lists. -/
@[simp]
theorem toList_append {n m : ℕ} (v : Vector α n) (w : Vector α m) :
    toList (v ++ w) = toList v ++ toList w := rfl

/-- `drop` of vectors corresponds under `toList` to `drop` of lists. -/
@[simp]
theorem toList_drop {n m : ℕ} (v : Vector α m) : toList (drop n v) = List.drop n (toList v) := by
  cases v
  rfl

/-- `take` of vectors corresponds under `toList` to `take` of lists. -/
@[simp]
theorem toList_take {n m : ℕ} (v : Vector α m) : toList (take n v) = List.take n (toList v) := by
  cases v
  rfl

instance : GetElem (Vector α n) Nat α fun _ i => i < n where
  getElem := fun x i h => get x ⟨i, h⟩

lemma getElem_def (v : Vector α n) (i : ℕ) {hi : i < n} :
    v[i] = v.toList[i]'(by simpa) := rfl

lemma toList_getElem (v : Vector α n) (i : ℕ) {hi : i < v.toList.length} :
    v.toList[i] = v[i]'(by simp_all) := rfl

end List.Vector
