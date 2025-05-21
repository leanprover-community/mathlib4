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

/-- Convert a `List.Vector` to a `Vector`. -/
@[simps!]
def toVector (v : List.Vector α n) : _root_.Vector α n := ⟨v.1.toArray, v.2⟩

/-- Convert a `Vector` to a `List.Vector`. -/
@[simps!]
def ofVector {α : Type*} {n : ℕ} (v : _root_.Vector α n) : List.Vector α n := ⟨v.toList, v.2⟩

alias _root_.Vector.toListVector := ofVector

@[simp] theorem ofVector_toVector (v : List.Vector α n) : ofVector (v.toVector) = v := rfl
@[simp] theorem toVector_ofVector (v : _root_.Vector α n) : toVector (ofVector v) = v := rfl

theorem ofVector_leftInverse : Function.LeftInverse ofVector (toVector (α := α) (n := n)) :=
  ofVector_toVector

theorem toVector_leftInverse : Function.LeftInverse toVector (ofVector (α := α) (n := n)) :=
  toVector_ofVector

theorem ofVector_rightInverse : Function.RightInverse ofVector (toVector (α := α) (n := n)) :=
  toVector_ofVector

theorem toVector_rightInverse : Function.RightInverse toVector (ofVector (α := α) (n := n)) :=
  ofVector_toVector

instance [DecidableEq α] : DecidableEq (Vector α n) :=
  inferInstanceAs (DecidableEq {l : List α // l.length = n})

/-- The empty vector with elements of type `α` -/
@[match_pattern]
def nil : Vector α 0 :=
  ⟨[], rfl⟩

@[simp] theorem toVector_nil : toVector nil (α := α) = #v[] := rfl
@[simp] theorem ofVector_empty : ofVector #v[] (α := α) = nil := rfl

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

@[simp] theorem head_toVector : ∀ v : Vector α (n + 1), v.toVector.head = v.head :=
  fun ⟨_ :: _, _⟩ => rfl

@[simp] theorem head_ofVector : ∀ v : _root_.Vector α (n + 1), (ofVector v).head = v.head :=
  fun ⟨⟨_ :: _⟩, _⟩ => rfl

/-- The head of a vector obtained by prepending is the element prepended. -/
theorem head_cons (a : α) : ∀ v : Vector α n, head (cons a v) = a
  | ⟨_, _⟩ => rfl

/-- The tail of a vector, with an empty vector having empty tail. -/
def tail : Vector α n → Vector α (n - 1)
  | ⟨[], h⟩ => ⟨[], congrArg pred h⟩
  | ⟨_ :: v, h⟩ => ⟨v, congrArg pred h⟩

@[simp] theorem toVector_tail :
    ∀ {n} (v : Vector α n), (v.tail).toVector = v.toVector.tail
  | 0, ⟨[], h⟩ => _root_.Vector.toList_inj.mp rfl
  | _ + 1, ⟨_ :: v, h⟩ => _root_.Vector.toList_inj.mp <| by
    unfold tail _root_.Vector.tail
    simp_rw [dif_pos (Nat.zero_lt_succ _), Vector.toArray_eraseIdx,
      Array.toList_eraseIdx, toVector_toList, eraseIdx_zero, tail_cons]

@[simp] theorem ofVector_tail :
    ∀ {n} (v : _root_.Vector α n), ofVector v.tail = (ofVector v).tail
  | 0, ⟨⟨[]⟩, _⟩ => Subtype.ext rfl
  | _ + 1, ⟨⟨_ :: v⟩, h⟩ => Subtype.ext <| by
    unfold tail _root_.Vector.tail ofVector
    simp_rw [dif_pos (Nat.zero_lt_succ _)]
    simp_rw [Vector.eraseIdx_mk, eraseIdx_toArray, eraseIdx_zero, tail_cons]

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

@[simp] theorem mem_toVector (a : α) : ∀ (v : Vector α n), a ∈ v.toVector ↔ a ∈ v.toList :=
  fun ⟨_, _⟩ => Vector.mem_mk.trans Array.mem_toArray

@[simp] theorem mem_toList_ofVector (a : α) : ∀ (v : _root_.Vector α n),
    a ∈ (ofVector v).toList ↔ a ∈ v :=
  fun ⟨_, _⟩ => Array.mem_toList.trans Vector.mem_mk.symm

/-- nth element of a vector, indexed by a `Fin` type. -/
def get (l : Vector α n) (i : Fin n) : α :=
  l.1.get <| i.cast l.2.symm

@[simp] theorem get_toVector (v : Vector α n) : v.toVector.get = v.get := rfl
@[simp] theorem get_ofVector (v : _root_.Vector α n) : (ofVector v).get = v.get := rfl

/-- Appending a vector to another. -/
def append {n m : Nat} : Vector α n → Vector α m → Vector α (n + m)
  | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩ => ⟨l₁ ++ l₂, by simp [*]⟩

@[simp] theorem toVector_append :
    ∀ v u : Vector α n, (v.append u).toVector = v.toVector ++ u.toVector :=
  fun ⟨_, _⟩ ⟨_, _⟩ => _root_.Vector.toList_inj.mp Array.toList_append.symm

@[simp] theorem ofVector_append :
    ∀ v u : _root_.Vector α n, ofVector (v ++ u) = (ofVector v).append (ofVector u) :=
  fun ⟨_, _⟩ ⟨_, _⟩ => Subtype.ext Array.toList_append

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

@[simp] theorem toVector_map (f : α → β) : ∀ (v : Vector α n),
    (v.map f).toVector = v.toVector.map f :=
  fun ⟨_, _⟩ => _root_.Vector.toList_inj.mp Array.toList_map.symm

@[simp] theorem ofVector_map (f : α → β) : ∀ (v : _root_.Vector α n),
    ofVector (v.map f) = (ofVector v).map f :=
  fun ⟨⟨_⟩, _⟩ => Subtype.ext Array.toList_map

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

@[simp] theorem toVector_pmap (f : (a : α) → p a → β) : ∀ (v : Vector α n)
    (h : ∀ (x : α), x ∈ v.toList → p x),
    (v.pmap f h).toVector = v.toVector.pmap f (fun _ h' => h _ ((mem_toVector _ _).mp h')) :=
  fun ⟨_, _⟩ _ => rfl

@[simp] theorem ofVector_pmap (f : (a : α) → p a → β) : ∀ (v : _root_.Vector α n) (h),
    ofVector (v.pmap f h) =
    (ofVector v).pmap f (fun _ h' => h _ ((mem_toList_ofVector _ _).mp h')) :=
  fun ⟨⟨_⟩, _⟩ _ => rfl

@[simp]
theorem pmap_nil (f : (a : α) → p a → β) (hp : ∀ x ∈ nil.toList, p x) :
    nil.pmap f hp = nil := rfl

/-- Mapping two vectors under a curried function of two variables. -/
def map₂ (f : α → β → φ) : Vector α n → Vector β n → Vector φ n
  | ⟨x, _⟩, ⟨y, _⟩ => ⟨List.zipWith f x y, by simp [*]⟩

/-- Vector obtained by repeating an element. -/
def replicate (n : ℕ) (a : α) : Vector α n :=
  ⟨List.replicate n a, List.length_replicate⟩

@[simp] theorem toVector_replicate (n : ℕ) (a : α) :
    (replicate n a).toVector = _root_.Vector.replicate n a := rfl

@[simp] theorem ofVector_replicate (n : ℕ) (a : α) :
    ofVector (_root_.Vector.replicate n a) = replicate n a := rfl

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

@[simp] theorem toVector_congr {n m : ℕ} (h : n = m) (v : Vector α n) :
    (v.congr h).toVector = v.toVector.cast h := rfl

@[simp] theorem ofVector_cast {n m : ℕ} (h : n = m) (v : _root_.Vector α n) :
    ofVector (v.cast h) = (ofVector v).congr h := rfl

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
  Vector.congr (by simp) <|
    append (drop i v) (replicate (min n i) fill)

/-- `shiftRightFill v i` is the vector obtained by right-shifting `v` `i` times and padding with the
    `fill` argument. If `v.length < i` then this will return `replicate n fill`. -/
def shiftRightFill (v : Vector α n) (i : ℕ) (fill : α) : Vector α n :=
  Vector.congr (by omega) <| append (replicate (min n i) fill) (take (n - i) v)

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
    toList (append v w) = toList v ++ toList w := by
  cases v
  cases w
  rfl

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

@[simp] theorem getElem_toVector (v : Vector α n) (i : ℕ) {hi : i < n} :
  (v.toVector)[i] = v[i] := rfl

@[simp] theorem getElem_ofVector (v : _root_.Vector α n) (i : ℕ) {hi : i < n} :
  (ofVector v)[i] = v[i] := rfl

end List.Vector
