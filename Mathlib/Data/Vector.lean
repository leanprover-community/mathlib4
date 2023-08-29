/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Mathport.Rename
import Std.Data.List.Basic
import Std.Data.List.Lemmas
import Mathlib.Init.Data.List.Basic
import Mathlib.Init.Data.List.Lemmas
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Algebra.Order.Monoid.OrderDual

#align_import data.vector from "leanprover-community/lean"@"855e5b74e3a52a40552e8f067169d747d48743fd"

/-!
The type `Vector` represents lists with fixed length.
-/

universe u v w
/-- `Vector α n` is the type of lists of length `n` with elements of type `α`. -/
def Vector (α : Type u) (n : ℕ) :=
  { l : List α // l.length = n }
#align vector Vector

namespace Vector

variable {α : Type u} {β : Type v} {φ : Type w}

variable {n : ℕ}

instance [DecidableEq α] : DecidableEq (Vector α n) :=
  inferInstanceAs (DecidableEq {l : List α // l.length = n})

/-- The empty vector with elements of type `α` -/
@[match_pattern]
def nil : Vector α 0 :=
  ⟨[], rfl⟩
#align vector.nil Vector.nil

/-- If `a : α` and `l : Vector α n`, then `cons a l`, is the vector of length `n + 1`
whose first element is a and with l as the rest of the list. -/
@[match_pattern]
def cons : α → Vector α n → Vector α (Nat.succ n)
  | a, ⟨v, h⟩ => ⟨a :: v, congrArg Nat.succ h⟩
#align vector.cons Vector.cons


/-- The length of a vector. -/
@[reducible, nolint unusedArguments]
def length (_ : Vector α n) : ℕ :=
  n
#align vector.length Vector.length

open Nat

/-- The first element of a vector with length at least `1`. -/
def head : Vector α (Nat.succ n) → α
  | ⟨[], h⟩ => by contradiction
                  -- 🎉 no goals
  | ⟨a :: _, _⟩ => a
#align vector.head Vector.head

/-- The head of a vector obtained by prepending is the element prepended. -/
theorem head_cons (a : α) : ∀ v : Vector α n, head (cons a v) = a
  | ⟨_, _⟩ => rfl
#align vector.head_cons Vector.head_cons

/-- The tail of a vector, with an empty vector having empty tail.  -/
def tail : Vector α n → Vector α (n - 1)
  | ⟨[], h⟩ => ⟨[], congrArg pred h⟩
  | ⟨_ :: v, h⟩ => ⟨v, congrArg pred h⟩
#align vector.tail Vector.tail

/-- The tail of a vector obtained by prepending is the vector prepended. to -/
theorem tail_cons (a : α) : ∀ v : Vector α n, tail (cons a v) = v
  | ⟨_, _⟩ => rfl
#align vector.tail_cons Vector.tail_cons

/-- Prepending the head of a vector to its tail gives the vector. -/
@[simp]
theorem cons_head_tail : ∀ v : Vector α (succ n), cons (head v) (tail v) = v
  | ⟨[], h⟩ => by contradiction
                  -- 🎉 no goals
  | ⟨a :: v, h⟩ => rfl
#align vector.cons_head_tail Vector.cons_head_tail

/-- The list obtained from a vector. -/
def toList (v : Vector α n) : List α :=
  v.1
#align vector.to_list Vector.toList

-- porting notes: align to `List` API
/-- nth element of a vector, indexed by a `Fin` type. -/
def get : ∀ _ : Vector α n, Fin n → α
  | ⟨l, h⟩, i => l.nthLe i.1 (by rw [h]; exact i.2)
                                 -- ⊢ ↑i < n
                                         -- 🎉 no goals
#align vector.nth Vector.get

/-- Appending a vector to another. -/
def append {n m : Nat} : Vector α n → Vector α m → Vector α (n + m)
  | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩ => ⟨l₁ ++ l₂, by simp [*]⟩
                                        -- 🎉 no goals
#align vector.append Vector.append

/- warning: vector.elim -> Vector.elim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {C : forall {n : ℕ},
  (Vector.{u_1} α n) -> Sort.{u}}, (forall (l : List.{u_1} α),
  C (List.length.{u_1} α l) (Subtype.mk.{succ u_1} (List.{u_1} α)
  (fun (l_1 : List.{u_1} α) => Eq.{1} ℕ (List.length.{u_1} α l_1)
  (List.length.{u_1} α l)) l (Vector.Elim._proof_1.{u_1} α l))) ->
  (forall {n : ℕ} (v : Vector.{u_1} α n), C n v)
but is expected to have type
  forall {α : Type.{_aux_param_0}} {C : forall {n : ℕ}, (Vector.{_aux_param_0} α n) -> Sort.{u}},
  (forall (l : List.{_aux_param_0} α),
  C (List.length.{_aux_param_0} α l) (Subtype.mk.{succ _aux_param_0} (List.{_aux_param_0} α)
  (fun (l_1 : List.{_aux_param_0} α) => Eq.{1} ℕ (List.length.{_aux_param_0} α l_1)
  (List.length.{_aux_param_0} α l)) l (rfl.{1} ℕ (List.length.{_aux_param_0} α l)))) ->
  (forall {n : ℕ} (v : Vector.{_aux_param_0} α n), C n v)
Case conversion may be inaccurate. Consider using '#align vector.elim Vector.elimₓ'. -/
/-- Elimination rule for `Vector`. -/
@[elab_as_elim]
def elim {α} {C : ∀ {n}, Vector α n → Sort u}
    (H : ∀ l : List α, C ⟨l, rfl⟩) {n : ℕ} : ∀ v : Vector α n, C v
  | ⟨l, h⟩ =>
    match n, h with
    | _, rfl => H l
#align vector.elim Vector.elim

/-- Map a vector under a function. -/
def map (f : α → β) : Vector α n → Vector β n
  | ⟨l, h⟩ => ⟨List.map f l, by simp [*]⟩
                                -- 🎉 no goals
#align vector.map Vector.map

/-- A `nil` vector maps to a `nil` vector. -/
@[simp]
theorem map_nil (f : α → β) : map f nil = nil :=
  rfl
#align vector.map_nil Vector.map_nil

/-- `map` is natural with respect to `cons`. -/
@[simp]
theorem map_cons (f : α → β) (a : α) : ∀ v : Vector α n, map f (cons a v) = cons (f a) (map f v)
  | ⟨_, _⟩ => rfl
#align vector.map_cons Vector.map_cons

/-- Mapping two vectors under a curried function of two variables. -/
def map₂ (f : α → β → φ) : Vector α n → Vector β n → Vector φ n
  | ⟨x, _⟩, ⟨y, _⟩ => ⟨List.zipWith f x y, by simp [*]⟩
                                              -- 🎉 no goals
#align vector.map₂ Vector.map₂

/-- Vector obtained by repeating an element. -/
def replicate (n : ℕ) (a : α) : Vector α n :=
  ⟨List.replicate n a, List.length_replicate n a⟩
#align vector.replicate Vector.replicate

/-- Drop `i` elements from a vector of length `n`; we can have `i > n`. -/
def drop (i : ℕ) : Vector α n → Vector α (n - i)
  | ⟨l, p⟩ => ⟨List.drop i l, by simp [*]⟩
                                 -- 🎉 no goals
#align vector.drop Vector.drop

/-- Take `i` elements from a vector of length `n`; we can have `i > n`. -/
def take (i : ℕ) : Vector α n → Vector α (min i n)
  | ⟨l, p⟩ => ⟨List.take i l, by simp [*]⟩
                                 -- 🎉 no goals
#align vector.take Vector.take

/-- Remove the element at position `i` from a vector of length `n`. -/
def removeNth (i : Fin n) : Vector α n → Vector α (n - 1)
  | ⟨l, p⟩ => ⟨List.removeNth l i.1, by rw [l.length_removeNth] <;> rw [p]; exact i.2⟩
                                        -- ⊢ List.length l - 1 = n - 1
                                                                    -- 🎉 no goals
                                                                    -- ⊢ ↑i < n
                                                                            -- 🎉 no goals
#align vector.remove_nth Vector.removeNth

/-- Vector of length `n` from a function on `Fin n`. -/
def ofFn : ∀ {n}, (Fin n → α) → Vector α n
  | 0, _ => nil
  | _ + 1, f => cons (f 0) (ofFn fun i ↦ f i.succ)

/-- Create a vector from another with a provably equal length. -/
protected def congr {n m : ℕ} (h : n = m) : Vector α n → Vector α m
  | ⟨x, p⟩ => ⟨x, h ▸ p⟩

#align vector.of_fn Vector.ofFn

section Accum

open Prod

variable {σ : Type}

/-- Runs a function over a vector returning the intermediate results and a
final result.
-/
def mapAccumr (f : α → σ → σ × β) : Vector α n → σ → σ × Vector β n
  | ⟨x, px⟩, c =>
    let res := List.mapAccumr f x c
    ⟨res.1, res.2, by simp [*]⟩
                      -- 🎉 no goals
#align vector.map_accumr Vector.mapAccumr

/-- Runs a function over a pair of vectors returning the intermediate results and a
final result.
-/
def mapAccumr₂ {α β σ φ : Type} (f : α → β → σ → σ × φ) :
    Vector α n → Vector β n → σ → σ × Vector φ n
  | ⟨x, px⟩, ⟨y, py⟩, c =>
    let res := List.mapAccumr₂ f x y c
    ⟨res.1, res.2, by simp [*]⟩
                      -- 🎉 no goals
#align vector.map_accumr₂ Vector.mapAccumr₂

end Accum

/-! ### Shift Primitives-/
section Shift

/-- `shiftLeftFill v i` is the vector obtained by left-shifting `v` `i` times and padding with the
    `fill` argument. If `v.length < i` then this will return `replicate n fill`. -/
def shiftLeftFill (v : Vector α n) (i : ℕ) (fill : α) : Vector α n :=
  Vector.congr (by simp) <|
                   -- 🎉 no goals
    append (drop i v) (replicate (min n i) fill)

/-- `shiftRightFill v i` is the vector obtained by right-shifting `v` `i` times and padding with the
    `fill` argument. If `v.length < i` then this will return `replicate n fill`. -/
def shiftRightFill (v : Vector α n) (i : ℕ) (fill : α) : Vector α n :=
  Vector.congr (by
        by_cases h : i ≤ n
        -- ⊢ min n i + min (n - i) n = n
        · have h₁ := Nat.sub_le n i
          -- ⊢ min n i + min (n - i) n = n
          rw [min_eq_right h]
          -- ⊢ i + min (n - i) n = n
          rw [min_eq_left h₁, ← add_tsub_assoc_of_le h, Nat.add_comm, add_tsub_cancel_right]
          -- 🎉 no goals
        · have h₁ := le_of_not_ge h
          -- ⊢ min n i + min (n - i) n = n
          rw [min_eq_left h₁, tsub_eq_zero_iff_le.mpr h₁, zero_min, Nat.add_zero]) <|
          -- 🎉 no goals
    append (replicate (min n i) fill) (take (n - i) v)

end Shift


/-! ### Basic Theorems -/
/-- Vector is determined by the underlying list. -/
protected theorem eq {n : ℕ} : ∀ a1 a2 : Vector α n, toList a1 = toList a2 → a1 = a2
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
#align vector.eq Vector.eq

/-- A vector of length `0` is a `nil` vector. -/
protected theorem eq_nil (v : Vector α 0) : v = nil :=
  v.eq nil (List.eq_nil_of_length_eq_zero v.2)
#align vector.eq_nil Vector.eq_nil

/-- Vector of length from a list `v`
with witness that `v` has length `n` maps to `v` under `toList`.  -/
@[simp]
theorem toList_mk (v : List α) (P : List.length v = n) : toList (Subtype.mk v P) = v :=
  rfl
#align vector.to_list_mk Vector.toList_mk

/-- A nil vector maps to a nil list. -/
@[simp, nolint simpNF] -- Porting note: simp can prove this in the future
theorem toList_nil : toList nil = @List.nil α :=
  rfl
#align vector.to_list_nil Vector.toList_nil

/-- The length of the list to which a vector of length `n` maps is `n`. -/
@[simp]
theorem toList_length (v : Vector α n) : (toList v).length = n :=
  v.2
#align vector.to_list_length Vector.toList_length

/-- `toList` of `cons` of a vector and an element is
the `cons` of the list obtained by `toList` and the element -/
@[simp]
theorem toList_cons (a : α) (v : Vector α n) : toList (cons a v) = a :: toList v := by
  cases v; rfl
  -- ⊢ toList (cons a { val := val✝, property := property✝ }) = a :: toList { val : …
           -- 🎉 no goals
#align vector.to_list_cons Vector.toList_cons

/-- Appending of vectors corresponds under `toList` to appending of lists. -/
@[simp]
theorem toList_append {n m : ℕ} (v : Vector α n) (w : Vector α m) :
   toList (append v w) = toList v ++ toList w := by
  cases v
  -- ⊢ toList (append { val := val✝, property := property✝ } w) = toList { val := v …
  cases w
  -- ⊢ toList (append { val := val✝¹, property := property✝¹ } { val := val✝, prope …
  rfl
  -- 🎉 no goals
#align vector.to_list_append Vector.toList_append

/-- `drop` of vectors corresponds under `toList` to `drop` of lists. -/
@[simp]
theorem toList_drop {n m : ℕ} (v : Vector α m) : toList (drop n v) = List.drop n (toList v) := by
  cases v
  -- ⊢ toList (drop n { val := val✝, property := property✝ }) = List.drop n (toList …
  rfl
  -- 🎉 no goals
#align vector.to_list_drop Vector.toList_drop

/-- `take` of vectors corresponds under `toList` to `take` of lists. -/
@[simp]
theorem toList_take {n m : ℕ} (v : Vector α m) : toList (take n v) = List.take n (toList v) := by
  cases v
  -- ⊢ toList (take n { val := val✝, property := property✝ }) = List.take n (toList …
  rfl
  -- 🎉 no goals
#align vector.to_list_take Vector.toList_take

instance : GetElem (Vector α n) Nat α fun _ i => i < n where
  getElem := fun x i h => get x ⟨i, h⟩

end Vector
