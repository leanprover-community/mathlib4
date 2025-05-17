/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.DList.Basic
import Mathlib.Data.WSeq.Basic

/-!
# Miscellaneous definitions concerning weak sequences

These definitions, as well as those in `Mathlib/Data/WSeq/Productive.lean`, are not needed for the
development of `Mathlib/Data/Seq/Parallel.lean`.
-/

universe u v w

namespace Stream'.WSeq

variable {α : Type u} {β : Type v} {γ : Type w}

open Function

/-- Get the length of `s` (if it is finite and completes in finite time). -/
def length (s : WSeq α) : Computation ℕ :=
  @Computation.corec ℕ (ℕ × WSeq α)
    (fun ⟨n, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl n
      | some (none, s') => Sum.inr (n, s')
      | some (some _, s') => Sum.inr (n + 1, s'))
    (0, s)

/-- A weak sequence is finite if `toList s` terminates. Equivalently,
  it is a finite number of `think` and `cons` applied to `nil`. -/
class IsFinite (s : WSeq α) : Prop where
  out : (toList s).Terminates

instance toList_terminates (s : WSeq α) [h : IsFinite s] : (toList s).Terminates :=
  h.out

/-- Get the list corresponding to a finite weak sequence. -/
def get (s : WSeq α) [IsFinite s] : List α :=
  (toList s).get

/-- Replace the `n`th element of `s` with `a`. -/
def updateNth (s : WSeq α) (n : ℕ) (a : α) : WSeq α :=
  @Seq.corec (Option α) (ℕ × WSeq α)
    (fun ⟨n, s⟩ =>
      match Seq.destruct s, n with
      | none, _ => none
      | some (none, s'), n => some (none, n, s')
      | some (some a', s'), 0 => some (some a', 0, s')
      | some (some _, s'), 1 => some (some a, 0, s')
      | some (some a', s'), n + 2 => some (some a', n + 1, s'))
    (n + 1, s)

/-- Remove the `n`th element of `s`. -/
def removeNth (s : WSeq α) (n : ℕ) : WSeq α :=
  @Seq.corec (Option α) (ℕ × WSeq α)
    (fun ⟨n, s⟩ =>
      match Seq.destruct s, n with
      | none, _ => none
      | some (none, s'), n => some (none, n, s')
      | some (some a', s'), 0 => some (some a', 0, s')
      | some (some _, s'), 1 => some (none, 0, s')
      | some (some a', s'), n + 2 => some (some a', n + 1, s'))
    (n + 1, s)

/-- Map the elements of `s` over `f`, removing any values that yield `none`. -/
def filterMap (f : α → Option β) : WSeq α → WSeq β :=
  Seq.corec fun s =>
    match Seq.destruct s with
    | none => none
    | some (none, s') => some (none, s')
    | some (some a, s') => some (f a, s')

/-- Select the elements of `s` that satisfy `p`. -/
def filter (p : α → Prop) [DecidablePred p] : WSeq α → WSeq α :=
  filterMap fun a => if p a then some a else none

-- example of infinite list manipulations
/-- Get the first element of `s` satisfying `p`. -/
def find (p : α → Prop) [DecidablePred p] (s : WSeq α) : Computation (Option α) :=
  head <| filter p s

/-- Zip a function over two weak sequences -/
def zipWith (f : α → β → γ) (s1 : WSeq α) (s2 : WSeq β) : WSeq γ :=
  @Seq.corec (Option γ) (WSeq α × WSeq β)
    (fun ⟨s1, s2⟩ =>
      match Seq.destruct s1, Seq.destruct s2 with
      | some (none, s1'), some (none, s2') => some (none, s1', s2')
      | some (some _, _), some (none, s2') => some (none, s1, s2')
      | some (none, s1'), some (some _, _) => some (none, s1', s2)
      | some (some a1, s1'), some (some a2, s2') => some (some (f a1 a2), s1', s2')
      | _, _ => none)
    (s1, s2)

/-- Zip two weak sequences into a single sequence of pairs -/
def zip : WSeq α → WSeq β → WSeq (α × β) :=
  zipWith Prod.mk

/-- Get the list of indexes of elements of `s` satisfying `p` -/
def findIndexes (p : α → Prop) [DecidablePred p] (s : WSeq α) : WSeq ℕ :=
  (zip s (Stream'.nats : WSeq ℕ)).filterMap fun ⟨a, n⟩ => if p a then some n else none

/-- Get the index of the first element of `s` satisfying `p` -/
def findIndex (p : α → Prop) [DecidablePred p] (s : WSeq α) : Computation ℕ :=
  (fun o => Option.getD o 0) <$> head (findIndexes p s)

/-- Get the index of the first occurrence of `a` in `s` -/
def indexOf [DecidableEq α] (a : α) : WSeq α → Computation ℕ :=
  findIndex (Eq a)

/-- Get the indexes of occurrences of `a` in `s` -/
def indexesOf [DecidableEq α] (a : α) : WSeq α → WSeq ℕ :=
  findIndexes (Eq a)

/-- `union s1 s2` is a weak sequence which interleaves `s1` and `s2` in
  some order (nondeterministically). -/
def union (s1 s2 : WSeq α) : WSeq α :=
  @Seq.corec (Option α) (WSeq α × WSeq α)
    (fun ⟨s1, s2⟩ =>
      match Seq.destruct s1, Seq.destruct s2 with
      | none, none => none
      | some (a1, s1'), none => some (a1, s1', nil)
      | none, some (a2, s2') => some (a2, nil, s2')
      | some (none, s1'), some (none, s2') => some (none, s1', s2')
      | some (some a1, s1'), some (none, s2') => some (some a1, s1', s2')
      | some (none, s1'), some (some a2, s2') => some (some a2, s1', s2')
      | some (some a1, s1'), some (some a2, s2') => some (some a1, cons a2 s1', s2'))
    (s1, s2)

/-- Returns `true` if `s` is `nil` and `false` if `s` has an element -/
def isEmpty (s : WSeq α) : Computation Bool :=
  Computation.map Option.isNone <| head s

/-- Calculate one step of computation -/
def compute (s : WSeq α) : WSeq α :=
  match Seq.destruct s with
  | some (none, s') => s'
  | _ => s

/-- Get the first `n` elements of a weak sequence -/
def take (s : WSeq α) (n : ℕ) : WSeq α :=
  @Seq.corec (Option α) (ℕ × WSeq α)
    (fun ⟨n, s⟩ =>
      match n, Seq.destruct s with
      | 0, _ => none
      | _ + 1, none => none
      | m + 1, some (none, s') => some (none, m + 1, s')
      | m + 1, some (some a, s') => some (some a, m, s'))
    (n, s)

/-- Split the sequence at position `n` into a finite initial segment
  and the weak sequence tail -/
def splitAt (s : WSeq α) (n : ℕ) : Computation (List α × WSeq α) :=
  @Computation.corec (List α × WSeq α) (ℕ × List α × WSeq α)
    (fun ⟨n, l, s⟩ =>
      match n, Seq.destruct s with
      | 0, _ => Sum.inl (l.reverse, s)
      | _ + 1, none => Sum.inl (l.reverse, s)
      | _ + 1, some (none, s') => Sum.inr (n, l, s')
      | m + 1, some (some a, s') => Sum.inr (m, a::l, s'))
    (n, [], s)

/-- Returns `true` if any element of `s` satisfies `p` -/
def any (s : WSeq α) (p : α → Bool) : Computation Bool :=
  Computation.corec
    (fun s : WSeq α =>
      match Seq.destruct s with
      | none => Sum.inl false
      | some (none, s') => Sum.inr s'
      | some (some a, s') => if p a then Sum.inl true else Sum.inr s')
    s

/-- Returns `true` if every element of `s` satisfies `p` -/
def all (s : WSeq α) (p : α → Bool) : Computation Bool :=
  Computation.corec
    (fun s : WSeq α =>
      match Seq.destruct s with
      | none => Sum.inl true
      | some (none, s') => Sum.inr s'
      | some (some a, s') => if p a then Sum.inr s' else Sum.inl false)
    s

/-- Apply a function to the elements of the sequence to produce a sequence
  of partial results. (There is no `scanr` because this would require
  working from the end of the sequence, which may not exist.) -/
def scanl (f : α → β → α) (a : α) (s : WSeq β) : WSeq α :=
  cons a <|
    @Seq.corec (Option α) (α × WSeq β)
      (fun ⟨a, s⟩ =>
        match Seq.destruct s with
        | none => none
        | some (none, s') => some (none, a, s')
        | some (some b, s') =>
          let a' := f a b
          some (some a', a', s'))
      (a, s)

/-- Get the weak sequence of initial segments of the input sequence -/
def inits (s : WSeq α) : WSeq (List α) :=
  cons [] <|
    @Seq.corec (Option (List α)) (Batteries.DList α × WSeq α)
      (fun ⟨l, s⟩ =>
        match Seq.destruct s with
        | none => none
        | some (none, s') => some (none, l, s')
        | some (some a, s') =>
          let l' := l.push a
          some (some l'.toList, l', s'))
      (Batteries.DList.empty, s)

/-- Like take, but does not wait for a result. Calculates `n` steps of
  computation and returns the sequence computed so far -/
def collect (s : WSeq α) (n : ℕ) : List α :=
  (Seq.take n s).filterMap id

theorem length_eq_map (s : WSeq α) : length s = Computation.map List.length (toList s) := by
  refine
    Computation.eq_of_bisim
      (fun c1 c2 =>
        ∃ (l : List α) (s : WSeq α),
          c1 = Computation.corec (fun ⟨n, s⟩ =>
            match Seq.destruct s with
            | none => Sum.inl n
            | some (none, s') => Sum.inr (n, s')
            | some (some _, s') => Sum.inr (n + 1, s')) (l.length, s) ∧
            c2 = Computation.map List.length (Computation.corec (fun ⟨l, s⟩ =>
              match Seq.destruct s with
              | none => Sum.inl l.reverse
              | some (none, s') => Sum.inr (l, s')
              | some (some a, s') => Sum.inr (a::l, s')) (l, s)))
      ?_ ⟨[], s, rfl, rfl⟩
  intro s1 s2 h; rcases h with ⟨l, s, h⟩; rw [h.left, h.right]
  induction' s using WSeq.recOn with a s s <;> simp [toList, nil, cons, think, length]
  · refine ⟨a::l, s, ?_, ?_⟩ <;> simp
  · refine ⟨l, s, ?_, ?_⟩ <;> simp

end Stream'.WSeq
