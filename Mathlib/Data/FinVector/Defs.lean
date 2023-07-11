/-
Copyright (c) 2023 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Matrix.Notation

/-!
  This file establishes `FinVector α n` as an alias for `Fin n → α`, the preferred
  encoding of vectors of statically known-size for proofs.
-/

def FinVector (α : Type u) (n : Nat) : Type u
  := Fin n → α


namespace FinVector
variable {α : Type u} {n : Nat}



/- ## Constructors -/

/-- The empty vector -/
def nil : FinVector α 0 :=
  fun i => nomatch i

/-- Prepend a new element `hd` in front of a vector `tl` -/
def cons (hd : α) (tl : FinVector α n) : FinVector α (n+1) :=
  Fin.cases hd tl

@[inherit_doc]
scoped infixr:67 " ::ᵥ " => FinVector.cons


/- ## Destructors -/

/-- The head of a known non-empty vector -/
def head (v : FinVector α (n+1)) : α :=
  v 0

/-- The tail of a known non-empty vector -/
def tail (v : FinVector α (n+1)) : FinVector α n :=
  fun i => v i.succ



/- ## Congruence -/

/-- Create a vector from another with a provably equal length. -/
def congr (h : n = m) : FinVector α n → FinVector α m :=
  fun v i => v <| Fin.cast h.symm i



/- ## Recursion principle -/

/-- Every empty vector is equal to `nil` -/
theorem elim_nil (v : FinVector α 0) : v = nil := by
  funext i; exact i.elim0

@[simp]
theorem cons_head_tail (v : FinVector α (n+1)) :
    cons v.head v.tail = v := by
  funext i
  cases i using Fin.cases
  <;> rfl

/--
  Recursion principle in terms of `nil` and `cons` constructors
-/
@[elab_as_elim]
def rec {motive : ∀{n}, FinVector α n → Sort v} (nil : motive nil)
    (cons : ∀{n}, (hd : α) → (tl : FinVector α n) → motive tl → motive (cons hd tl)) :
    {m : Nat} → (v : FinVector α m) → motive v
  | 0, v =>
      cast (by rw[elim_nil v]) nil
  | m+1, v =>
      cast (by rw[cons_head_tail v]) <| cons v.head v.tail (rec nil cons v.tail)



/- ## Append, concat & other operations -/

/-- Append two vectors -/
def append {n m : Nat} (xs : FinVector α n) (ys : FinVector α m) : FinVector α (n+m) :=
  fun i => match i.splitAt n with
    | .inl i => xs i
    | .inr i => ys i

instance : HAppend (FinVector α n) (FinVector α m) (FinVector α (n+m)) :=
  ⟨append⟩


/-- Append a single element to the end of a vector -/
def concat (tl : FinVector α n) (hd : α) : FinVector α (n+1) :=
  tl.append ![hd]

/-- Reverse a vector -/
def reverse (xs : FinVector α n) : FinVector α n :=
  fun i => xs (Fin.rev i)

/-- Drop the first `m` elements from a vector of length `n`; we can have `m > n`. -/
def drop : {n : ℕ} → (m : ℕ) → FinVector α n → FinVector α (n - m)
  | _, 0,     v => v
  | 0, _,     _ => congr (by simp) nil
  | n+1, m+1, v => congr (by simp) <| drop m v.tail

private theorem min_succ_succ (n m : ℕ) : min (n + 1) (m + 1) = (min n m) + 1 := by
  simp[instMinNat, minOfLe]
  split <;> rfl

/-- Take the first `m` elements from a vector of length `n`; we can have `m > n`. -/
def take : {n : ℕ} → (m : ℕ) → FinVector α n → FinVector α (min m n)
  | _, 0,     _ => congr (by simp) nil
  | 0, _,     _ => congr (by simp) nil
  | n+1, m+1, v => congr (by simp[min_succ_succ]) <| cons v.head (take m v.tail)

/-- Remove the element at position `i` from a vector of length `n`. -/
def removeNth : {n : ℕ} → (i : Fin n) → FinVector α n → FinVector α (n - 1)
  | 0, _, _         => nil
  | _+1, 0, v       => v.tail
  | _+2, ⟨i+1,h⟩, v => cons v.head <| removeNth ⟨i, Nat.lt_of_succ_lt_succ h⟩ v.tail

/-- Replicate a single value into a constant vector of length `n` -/
def replicate (n : Nat) (a : α) : FinVector α n :=
  fun _ => a




/- ## fold, map, mapAccumr -/

/-- Apply a function to each element of a vector -/
def map (f : α → β) : FinVector α n → FinVector β n :=
  fun v i => f <| v i

/-- Zip two vectors into a single vector of products -/
def zip : FinVector α n → FinVector β n → FinVector (α × β) n :=
  fun as bs i => (as i, bs i)

/-- Apply a binary function to each corresponding elements of a pair of vectors -/
def map₂ (f : α → β → γ) : FinVector α n → FinVector β n → FinVector γ n :=
  fun as bs => (as.zip bs).map f.uncurry



/-- Fold a dependently typed function over a vector, left-to-right -/
def dfoldl {β : ℕ → Sort v} (f : ∀{m}, (β m) → α → (β <| m+1)) (init : β 0) :
    {n : ℕ} → FinVector α n → β n
  | 0, _    => init
  | _+1, v  => dfoldl f (f init v.head) v.tail

/-- Fold a function over a vector, left-to-right -/
def foldl (f : β → α → β) (init : β) : FinVector α n → β :=
  dfoldl f init

/-- Fold a dependently typed function over a vector, right-to-left -/
def dfoldr {β : ℕ → Sort v} (f : ∀{m}, α → (β m) → (β <| m+1)) (init : β 0) :
    {n : ℕ} → FinVector α n → β n
  | 0, _    => init
  | _+1, v  =>
    let r := @dfoldr β f init _ v.tail
    f v.head r

/-- Fold a function over a vector, right-to-left -/
def foldr (f : α → β → β) (init : β) : FinVector α n → β :=
  dfoldr f init


/-- Runs a function over a vector returning the intermediate results and a
    a final result. -/
def mapAccumr (f : α → σ → σ × β) : FinVector α n → σ → σ × FinVector β n :=
  fun v s =>
    dfoldr (β := (σ × FinVector β ·)) (fun a s =>
      let r := f a s.1
      (r.1, r.2 ::ᵥ s.2)
    ) (s, nil) v

/-- Runs a function over a vector returning the intermediate results and a
    a final result. -/
def mapAccumr₂ (f : α → β → σ → σ × γ) : FinVector α n → FinVector β n → σ → σ × FinVector γ n :=
  fun as bs s => (as.zip bs).mapAccumr f.uncurry s



/- ## toList -/

def toList : FinVector α n → List α :=
  List.ofFn

/- ## Reverse induction principle -/


end FinVector
