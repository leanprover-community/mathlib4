/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.seq.wseq
! leanprover-community/mathlib commit a7e36e48519ab281320c4d192da6a7b348ce40ad
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Basic
import Mathbin.Data.Seq.Seq

namespace Stream'

open Function

universe u v w

/-
coinductive wseq (α : Type u) : Type u
| nil : wseq α
| cons : α → wseq α → wseq α
| think : wseq α → wseq α
-/
/-- Weak sequences.

  While the `seq` structure allows for lists which may not be finite,
  a weak sequence also allows the computation of each element to
  involve an indeterminate amount of computation, including possibly
  an infinite loop. This is represented as a regular `seq` interspersed
  with `none` elements to indicate that computation is ongoing.

  This model is appropriate for Haskell style lazy lists, and is closed
  under most interesting computation patterns on infinite lists,
  but conversely it is difficult to extract elements from it. -/
def Wseq (α) :=
  Seq (Option α)
#align stream.wseq Stream'.Wseq

namespace Wseq

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Turn a sequence into a weak sequence -/
def ofSeq : Seq α → Wseq α :=
  (· <$> ·) some
#align stream.wseq.of_seq Stream'.Wseq.ofSeq

/-- Turn a list into a weak sequence -/
def ofList (l : List α) : Wseq α :=
  ofSeq l
#align stream.wseq.of_list Stream'.Wseq.ofList

/-- Turn a stream into a weak sequence -/
def ofStream (l : Stream' α) : Wseq α :=
  ofSeq l
#align stream.wseq.of_stream Stream'.Wseq.ofStream

instance coeSeq : Coe (Seq α) (Wseq α) :=
  ⟨ofSeq⟩
#align stream.wseq.coe_seq Stream'.Wseq.coeSeq

instance coeList : Coe (List α) (Wseq α) :=
  ⟨ofList⟩
#align stream.wseq.coe_list Stream'.Wseq.coeList

instance coeStream : Coe (Stream' α) (Wseq α) :=
  ⟨ofStream⟩
#align stream.wseq.coe_stream Stream'.Wseq.coeStream

/-- The empty weak sequence -/
def nil : Wseq α :=
  Seq.nil
#align stream.wseq.nil Stream'.Wseq.nil

instance : Inhabited (Wseq α) :=
  ⟨nil⟩

/-- Prepend an element to a weak sequence -/
def cons (a : α) : Wseq α → Wseq α :=
  Seq.cons (some a)
#align stream.wseq.cons Stream'.Wseq.cons

/-- Compute for one tick, without producing any elements -/
def think : Wseq α → Wseq α :=
  Seq.cons none
#align stream.wseq.think Stream'.Wseq.think

/-- Destruct a weak sequence, to (eventually possibly) produce either
  `none` for `nil` or `some (a, s)` if an element is produced. -/
def destruct : Wseq α → Computation (Option (α × Wseq α)) :=
  Computation.corec fun s =>
    match Seq.destruct s with
    | none => Sum.inl none
    | some (none, s') => Sum.inr s'
    | some (some a, s') => Sum.inl (some (a, s'))
#align stream.wseq.destruct Stream'.Wseq.destruct

/-- Recursion principle for weak sequences, compare with `list.rec_on`. -/
def recOn {C : Wseq α → Sort v} (s : Wseq α) (h1 : C nil) (h2 : ∀ x s, C (cons x s))
    (h3 : ∀ s, C (think s)) : C s :=
  Seq.recOn s h1 fun o => Option.recOn o h3 h2
#align stream.wseq.rec_on Stream'.Wseq.recOn

/-- membership for weak sequences-/
protected def Mem (a : α) (s : Wseq α) :=
  Seq.Mem (some a) s
#align stream.wseq.mem Stream'.Wseq.Mem

instance : Membership α (Wseq α) :=
  ⟨Wseq.Mem⟩

theorem not_mem_nil (a : α) : a ∉ @nil α :=
  Seq.not_mem_nil a
#align stream.wseq.not_mem_nil Stream'.Wseq.not_mem_nil

/-- Get the head of a weak sequence. This involves a possibly
  infinite computation. -/
def head (s : Wseq α) : Computation (Option α) :=
  Computation.map ((· <$> ·) Prod.fst) (destruct s)
#align stream.wseq.head Stream'.Wseq.head

/-- Encode a computation yielding a weak sequence into additional
  `think` constructors in a weak sequence -/
def flatten : Computation (Wseq α) → Wseq α :=
  Seq.corec fun c =>
    match Computation.destruct c with
    | Sum.inl s => Seq.omap return (Seq.destruct s)
    | Sum.inr c' => some (none, c')
#align stream.wseq.flatten Stream'.Wseq.flatten

/-- Get the tail of a weak sequence. This doesn't need a `computation`
  wrapper, unlike `head`, because `flatten` allows us to hide this
  in the construction of the weak sequence itself. -/
def tail (s : Wseq α) : Wseq α :=
  flatten <| (fun o => Option.recOn o nil Prod.snd) <$> destruct s
#align stream.wseq.tail Stream'.Wseq.tail

/-- drop the first `n` elements from `s`. -/
def drop (s : Wseq α) : ℕ → Wseq α
  | 0 => s
  | n + 1 => tail (drop n)
#align stream.wseq.drop Stream'.Wseq.drop

attribute [simp] drop

/-- Get the nth element of `s`. -/
def nth (s : Wseq α) (n : ℕ) : Computation (Option α) :=
  head (drop s n)
#align stream.wseq.nth Stream'.Wseq.nth

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Convert `s` to a list (if it is finite and completes in finite time). -/
def toList (s : Wseq α) : Computation (List α) :=
  @Computation.corec (List α) (List α × Wseq α)
    (fun ⟨l, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a::l, s'))
    ([], s)
#align stream.wseq.to_list Stream'.Wseq.toList

/-- Get the length of `s` (if it is finite and completes in finite time). -/
def length (s : Wseq α) : Computation ℕ :=
  @Computation.corec ℕ (ℕ × Wseq α)
    (fun ⟨n, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl n
      | some (none, s') => Sum.inr (n, s')
      | some (some a, s') => Sum.inr (n + 1, s'))
    (0, s)
#align stream.wseq.length Stream'.Wseq.length

/-- A weak sequence is finite if `to_list s` terminates. Equivalently,
  it is a finite number of `think` and `cons` applied to `nil`. -/
class IsFinite (s : Wseq α) : Prop where
  out : (toList s).Terminates
#align stream.wseq.is_finite Stream'.Wseq.IsFinite

instance toList_terminates (s : Wseq α) [h : IsFinite s] : (toList s).Terminates :=
  h.out
#align stream.wseq.to_list_terminates Stream'.Wseq.toList_terminates

/-- Get the list corresponding to a finite weak sequence. -/
def get (s : Wseq α) [IsFinite s] : List α :=
  (toList s).get
#align stream.wseq.get Stream'.Wseq.get

/-- A weak sequence is *productive* if it never stalls forever - there are
 always a finite number of `think`s between `cons` constructors.
 The sequence itself is allowed to be infinite though. -/
class Productive (s : Wseq α) : Prop where
  nth_terminates : ∀ n, (nth s n).Terminates
#align stream.wseq.productive Stream'.Wseq.Productive

theorem productive_iff (s : Wseq α) : Productive s ↔ ∀ n, (nth s n).Terminates :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align stream.wseq.productive_iff Stream'.Wseq.productive_iff

instance nth_terminates (s : Wseq α) [h : Productive s] : ∀ n, (nth s n).Terminates :=
  h.nth_terminates
#align stream.wseq.nth_terminates Stream'.Wseq.nth_terminates

instance head_terminates (s : Wseq α) [Productive s] : (head s).Terminates :=
  s.nth_terminates 0
#align stream.wseq.head_terminates Stream'.Wseq.head_terminates

/-- Replace the `n`th element of `s` with `a`. -/
def updateNth (s : Wseq α) (n : ℕ) (a : α) : Wseq α :=
  @Seq.corec (Option α) (ℕ × Wseq α)
    (fun ⟨n, s⟩ =>
      match Seq.destruct s, n with
      | none, n => none
      | some (none, s'), n => some (none, n, s')
      | some (some a', s'), 0 => some (some a', 0, s')
      | some (some a', s'), 1 => some (some a, 0, s')
      | some (some a', s'), n + 2 => some (some a', n + 1, s'))
    (n + 1, s)
#align stream.wseq.update_nth Stream'.Wseq.updateNth

/-- Remove the `n`th element of `s`. -/
def removeNth (s : Wseq α) (n : ℕ) : Wseq α :=
  @Seq.corec (Option α) (ℕ × Wseq α)
    (fun ⟨n, s⟩ =>
      match Seq.destruct s, n with
      | none, n => none
      | some (none, s'), n => some (none, n, s')
      | some (some a', s'), 0 => some (some a', 0, s')
      | some (some a', s'), 1 => some (none, 0, s')
      | some (some a', s'), n + 2 => some (some a', n + 1, s'))
    (n + 1, s)
#align stream.wseq.remove_nth Stream'.Wseq.removeNth

/-- Map the elements of `s` over `f`, removing any values that yield `none`. -/
def filterMap (f : α → Option β) : Wseq α → Wseq β :=
  Seq.corec fun s =>
    match Seq.destruct s with
    | none => none
    | some (none, s') => some (none, s')
    | some (some a, s') => some (f a, s')
#align stream.wseq.filter_map Stream'.Wseq.filterMap

/-- Select the elements of `s` that satisfy `p`. -/
def filter (p : α → Prop) [DecidablePred p] : Wseq α → Wseq α :=
  filterMap fun a => if p a then some a else none
#align stream.wseq.filter Stream'.Wseq.filter

-- example of infinite list manipulations
/-- Get the first element of `s` satisfying `p`. -/
def find (p : α → Prop) [DecidablePred p] (s : Wseq α) : Computation (Option α) :=
  head <| filter p s
#align stream.wseq.find Stream'.Wseq.find

/-- Zip a function over two weak sequences -/
def zipWith (f : α → β → γ) (s1 : Wseq α) (s2 : Wseq β) : Wseq γ :=
  @Seq.corec (Option γ) (Wseq α × Wseq β)
    (fun ⟨s1, s2⟩ =>
      match Seq.destruct s1, Seq.destruct s2 with
      | some (none, s1'), some (none, s2') => some (none, s1', s2')
      | some (some a1, s1'), some (none, s2') => some (none, s1, s2')
      | some (none, s1'), some (some a2, s2') => some (none, s1', s2)
      | some (some a1, s1'), some (some a2, s2') => some (some (f a1 a2), s1', s2')
      | _, _ => none)
    (s1, s2)
#align stream.wseq.zip_with Stream'.Wseq.zipWith

/-- Zip two weak sequences into a single sequence of pairs -/
def zip : Wseq α → Wseq β → Wseq (α × β) :=
  zipWith Prod.mk
#align stream.wseq.zip Stream'.Wseq.zip

/-- Get the list of indexes of elements of `s` satisfying `p` -/
def findIndexes (p : α → Prop) [DecidablePred p] (s : Wseq α) : Wseq ℕ :=
  (zip s (Stream'.nats : Wseq ℕ)).filterMap fun ⟨a, n⟩ => if p a then some n else none
#align stream.wseq.find_indexes Stream'.Wseq.findIndexes

/-- Get the index of the first element of `s` satisfying `p` -/
def findIndex (p : α → Prop) [DecidablePred p] (s : Wseq α) : Computation ℕ :=
  (fun o => Option.getD o 0) <$> head (findIndexes p s)
#align stream.wseq.find_index Stream'.Wseq.findIndex

/-- Get the index of the first occurrence of `a` in `s` -/
def indexOf [DecidableEq α] (a : α) : Wseq α → Computation ℕ :=
  findIndex (Eq a)
#align stream.wseq.index_of Stream'.Wseq.indexOf

/-- Get the indexes of occurrences of `a` in `s` -/
def indexesOf [DecidableEq α] (a : α) : Wseq α → Wseq ℕ :=
  findIndexes (Eq a)
#align stream.wseq.indexes_of Stream'.Wseq.indexesOf

/-- `union s1 s2` is a weak sequence which interleaves `s1` and `s2` in
  some order (nondeterministically). -/
def union (s1 s2 : Wseq α) : Wseq α :=
  @Seq.corec (Option α) (Wseq α × Wseq α)
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
#align stream.wseq.union Stream'.Wseq.union

/-- Returns `tt` if `s` is `nil` and `ff` if `s` has an element -/
def isEmpty (s : Wseq α) : Computation Bool :=
  Computation.map Option.isNone <| head s
#align stream.wseq.is_empty Stream'.Wseq.isEmpty

/-- Calculate one step of computation -/
def compute (s : Wseq α) : Wseq α :=
  match Seq.destruct s with
  | some (none, s') => s'
  | _ => s
#align stream.wseq.compute Stream'.Wseq.compute

/-- Get the first `n` elements of a weak sequence -/
def take (s : Wseq α) (n : ℕ) : Wseq α :=
  @Seq.corec (Option α) (ℕ × Wseq α)
    (fun ⟨n, s⟩ =>
      match n, Seq.destruct s with
      | 0, _ => none
      | m + 1, none => none
      | m + 1, some (none, s') => some (none, m + 1, s')
      | m + 1, some (some a, s') => some (some a, m, s'))
    (n, s)
#align stream.wseq.take Stream'.Wseq.take

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Split the sequence at position `n` into a finite initial segment
  and the weak sequence tail -/
def splitAt (s : Wseq α) (n : ℕ) : Computation (List α × Wseq α) :=
  @Computation.corec (List α × Wseq α) (ℕ × List α × Wseq α)
    (fun ⟨n, l, s⟩ =>
      match n, Seq.destruct s with
      | 0, _ => Sum.inl (l.reverse, s)
      | m + 1, none => Sum.inl (l.reverse, s)
      | m + 1, some (none, s') => Sum.inr (n, l, s')
      | m + 1, some (some a, s') => Sum.inr (m, a::l, s'))
    (n, [], s)
#align stream.wseq.split_at Stream'.Wseq.splitAt

/-- Returns `tt` if any element of `s` satisfies `p` -/
def any (s : Wseq α) (p : α → Bool) : Computation Bool :=
  Computation.corec
    (fun s : Wseq α =>
      match Seq.destruct s with
      | none => Sum.inl false
      | some (none, s') => Sum.inr s'
      | some (some a, s') => if p a then Sum.inl true else Sum.inr s')
    s
#align stream.wseq.any Stream'.Wseq.any

/-- Returns `tt` if every element of `s` satisfies `p` -/
def all (s : Wseq α) (p : α → Bool) : Computation Bool :=
  Computation.corec
    (fun s : Wseq α =>
      match Seq.destruct s with
      | none => Sum.inl true
      | some (none, s') => Sum.inr s'
      | some (some a, s') => if p a then Sum.inr s' else Sum.inl false)
    s
#align stream.wseq.all Stream'.Wseq.all

/-- Apply a function to the elements of the sequence to produce a sequence
  of partial results. (There is no `scanr` because this would require
  working from the end of the sequence, which may not exist.) -/
def scanl (f : α → β → α) (a : α) (s : Wseq β) : Wseq α :=
  cons a <|
    @Seq.corec (Option α) (α × Wseq β)
      (fun ⟨a, s⟩ =>
        match Seq.destruct s with
        | none => none
        | some (none, s') => some (none, a, s')
        | some (some b, s') =>
          let a' := f a b
          some (some a', a', s'))
      (a, s)
#align stream.wseq.scanl Stream'.Wseq.scanl

/-- Get the weak sequence of initial segments of the input sequence -/
def inits (s : Wseq α) : Wseq (List α) :=
  cons [] <|
    @Seq.corec (Option (List α)) (Dlist α × Wseq α)
      (fun ⟨l, s⟩ =>
        match Seq.destruct s with
        | none => none
        | some (none, s') => some (none, l, s')
        | some (some a, s') =>
          let l' := l.concat a
          some (some l'.toList, l', s'))
      (Dlist.empty, s)
#align stream.wseq.inits Stream'.Wseq.inits

/-- Like take, but does not wait for a result. Calculates `n` steps of
  computation and returns the sequence computed so far -/
def collect (s : Wseq α) (n : ℕ) : List α :=
  (Seq.take n s).filterMap id
#align stream.wseq.collect Stream'.Wseq.collect

/-- Append two weak sequences. As with `seq.append`, this may not use
  the second sequence if the first one takes forever to compute -/
def append : Wseq α → Wseq α → Wseq α :=
  Seq.append
#align stream.wseq.append Stream'.Wseq.append

/-- Map a function over a weak sequence -/
def map (f : α → β) : Wseq α → Wseq β :=
  Seq.map (Option.map f)
#align stream.wseq.map Stream'.Wseq.map

/-- Flatten a sequence of weak sequences. (Note that this allows
  empty sequences, unlike `seq.join`.) -/
def join (S : Wseq (Wseq α)) : Wseq α :=
  Seq.join
    ((fun o : Option (Wseq α) =>
        match o with
        | none => Seq1.ret none
        | some s => (none, s)) <$>
      S)
#align stream.wseq.join Stream'.Wseq.join

/-- Monadic bind operator for weak sequences -/
def bind (s : Wseq α) (f : α → Wseq β) : Wseq β :=
  join (map f s)
#align stream.wseq.bind Stream'.Wseq.bind

/-- lift a relation to a relation over weak sequences -/
@[simp]
def LiftRelO (R : α → β → Prop) (C : Wseq α → Wseq β → Prop) :
    Option (α × Wseq α) → Option (β × Wseq β) → Prop
  | none, none => True
  | some (a, s), some (b, t) => R a b ∧ C s t
  | _, _ => False
#align stream.wseq.lift_rel_o Stream'.Wseq.LiftRelO

theorem LiftRelO.imp {R S : α → β → Prop} {C D : Wseq α → Wseq β → Prop} (H1 : ∀ a b, R a b → S a b)
    (H2 : ∀ s t, C s t → D s t) : ∀ {o p}, LiftRelO R C o p → LiftRelO S D o p
  | none, none, h => trivial
  | some (a, s), some (b, t), h => And.imp (H1 _ _) (H2 _ _) h
  | none, some _, h => False.elim h
  | some (_, _), none, h => False.elim h
#align stream.wseq.lift_rel_o.imp Stream'.Wseq.LiftRelO.imp

theorem LiftRelO.imp_right (R : α → β → Prop) {C D : Wseq α → Wseq β → Prop}
    (H : ∀ s t, C s t → D s t) {o p} : LiftRelO R C o p → LiftRelO R D o p :=
  LiftRelO.imp (fun _ _ => id) H
#align stream.wseq.lift_rel_o.imp_right Stream'.Wseq.LiftRelO.imp_right

/-- Definitino of bisimilarity for weak sequences-/
@[simp]
def BisimO (R : Wseq α → Wseq α → Prop) : Option (α × Wseq α) → Option (α × Wseq α) → Prop :=
  LiftRelO (· = ·) R
#align stream.wseq.bisim_o Stream'.Wseq.BisimO

theorem BisimO.imp {R S : Wseq α → Wseq α → Prop} (H : ∀ s t, R s t → S s t) {o p} :
    BisimO R o p → BisimO S o p :=
  LiftRelO.imp_right _ H
#align stream.wseq.bisim_o.imp Stream'.Wseq.BisimO.imp

/-- Two weak sequences are `lift_rel R` related if they are either both empty,
  or they are both nonempty and the heads are `R` related and the tails are
  `lift_rel R` related. (This is a coinductive definition.) -/
def LiftRel (R : α → β → Prop) (s : Wseq α) (t : Wseq β) : Prop :=
  ∃ C : Wseq α → Wseq β → Prop,
    C s t ∧ ∀ {s t}, C s t → Computation.LiftRel (LiftRelO R C) (destruct s) (destruct t)
#align stream.wseq.lift_rel Stream'.Wseq.LiftRel

/-- If two sequences are equivalent, then they have the same values and
  the same computational behavior (i.e. if one loops forever then so does
  the other), although they may differ in the number of `think`s needed to
  arrive at the answer. -/
def Equiv : Wseq α → Wseq α → Prop :=
  LiftRel (· = ·)
#align stream.wseq.equiv Stream'.Wseq.Equiv

theorem liftRel_destruct {R : α → β → Prop} {s : Wseq α} {t : Wseq β} :
    LiftRel R s t → Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct s) (destruct t)
  | ⟨R, h1, h2⟩ => by
    refine' Computation.LiftRel.imp _ _ _ (h2 h1) <;> apply lift_rel_o.imp_right <;>
      exact fun s' t' h' => ⟨R, h', @h2⟩
#align stream.wseq.lift_rel_destruct Stream'.Wseq.liftRel_destruct

theorem liftRel_destruct_iff {R : α → β → Prop} {s : Wseq α} {t : Wseq β} :
    LiftRel R s t ↔ Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct s) (destruct t) :=
  ⟨liftRel_destruct, fun h =>
    ⟨fun s t =>
      LiftRel R s t ∨ Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct s) (destruct t),
      Or.inr h, fun s t h =>
      by
      have h : Computation.LiftRel (lift_rel_o R (lift_rel R)) (destruct s) (destruct t) :=
        by
        cases' h with h h
        exact lift_rel_destruct h
        assumption
      apply Computation.LiftRel.imp _ _ _ h
      intro a b
      apply lift_rel_o.imp_right
      intro s t
      apply Or.inl⟩⟩
#align stream.wseq.lift_rel_destruct_iff Stream'.Wseq.liftRel_destruct_iff

-- mathport name: equiv
infixl:50 " ~ " => Equiv

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:228:8: unsupported: ambiguous notation -/
theorem destruct_congr {s t : Wseq α} :
    s ~ t → Computation.LiftRel (BisimO (· ~ ·)) (destruct s) (destruct t) :=
  liftRel_destruct
#align stream.wseq.destruct_congr Stream'.Wseq.destruct_congr

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:228:8: unsupported: ambiguous notation -/
theorem destruct_congr_iff {s t : Wseq α} :
    s ~ t ↔ Computation.LiftRel (BisimO (· ~ ·)) (destruct s) (destruct t) :=
  liftRel_destruct_iff
#align stream.wseq.destruct_congr_iff Stream'.Wseq.destruct_congr_iff

theorem LiftRel.refl (R : α → α → Prop) (H : Reflexive R) : Reflexive (LiftRel R) := fun s =>
  by
  refine' ⟨(· = ·), rfl, fun s t (h : s = t) => _⟩
  rw [← h]; apply Computation.LiftRel.refl
  intro a; cases' a with a; simp; cases a <;> simp; apply H
#align stream.wseq.lift_rel.refl Stream'.Wseq.LiftRel.refl

theorem LiftRelO.swap (R : α → β → Prop) (C) : swap (LiftRelO R C) = LiftRelO (swap R) (swap C) :=
  by
  funext x y <;> cases' x with x <;> [skip, cases x] <;>
    · cases' y with y <;> [skip, cases y] <;> rfl
#align stream.wseq.lift_rel_o.swap Stream'.Wseq.LiftRelO.swap

theorem LiftRel.swap_lem {R : α → β → Prop} {s1 s2} (h : LiftRel R s1 s2) :
    LiftRel (swap R) s2 s1 :=
  by
  refine' ⟨swap (lift_rel R), h, fun s t (h : lift_rel R t s) => _⟩
  rw [← lift_rel_o.swap, Computation.LiftRel.swap]
  apply lift_rel_destruct h
#align stream.wseq.lift_rel.swap_lem Stream'.Wseq.LiftRel.swap_lem

theorem LiftRel.swap (R : α → β → Prop) : swap (LiftRel R) = LiftRel (swap R) :=
  funext fun x => funext fun y => propext ⟨LiftRel.swap_lem, LiftRel.swap_lem⟩
#align stream.wseq.lift_rel.swap Stream'.Wseq.LiftRel.swap

theorem LiftRel.symm (R : α → α → Prop) (H : Symmetric R) : Symmetric (LiftRel R) :=
  fun s1 s2 (h : swap (LiftRel R) s2 s1) => by
  rwa [lift_rel.swap,
    show swap R = R from funext fun a => funext fun b => propext <| by constructor <;> apply H] at h
#align stream.wseq.lift_rel.symm Stream'.Wseq.LiftRel.symm

theorem LiftRel.trans (R : α → α → Prop) (H : Transitive R) : Transitive (LiftRel R) :=
  fun s t u h1 h2 =>
  by
  refine' ⟨fun s u => ∃ t, lift_rel R s t ∧ lift_rel R t u, ⟨t, h1, h2⟩, fun s u h => _⟩
  rcases h with ⟨t, h1, h2⟩
  have h1 := lift_rel_destruct h1
  have h2 := lift_rel_destruct h2
  refine'
    Computation.liftRel_def.2
      ⟨(Computation.terminates_of_LiftRel h1).trans (Computation.terminates_of_LiftRel h2),
        fun a c ha hc => _⟩
  rcases h1.left ha with ⟨b, hb, t1⟩
  have t2 := Computation.rel_of_LiftRel h2 hb hc
  cases' a with a <;> cases' c with c
  · trivial
  · cases b
    · cases t2
    · cases t1
  · cases a
    cases' b with b
    · cases t1
    · cases b
      cases t2
  · cases' a with a s
    cases' b with b
    · cases t1
    cases' b with b t
    cases' c with c u
    cases' t1 with ab st
    cases' t2 with bc tu
    exact ⟨H ab bc, t, st, tu⟩
#align stream.wseq.lift_rel.trans Stream'.Wseq.LiftRel.trans

theorem LiftRel.equiv (R : α → α → Prop) : Equivalence R → Equivalence (LiftRel R)
  | ⟨refl, symm, trans⟩ => ⟨LiftRel.refl R refl, LiftRel.symm R symm, LiftRel.trans R trans⟩
#align stream.wseq.lift_rel.equiv Stream'.Wseq.LiftRel.equiv

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[refl]
theorem Equiv.refl : ∀ s : Wseq α, s ~ s :=
  LiftRel.refl (· = ·) Eq.refl
#align stream.wseq.equiv.refl Stream'.Wseq.Equiv.refl

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[symm]
theorem Equiv.symm : ∀ {s t : Wseq α}, s ~ t → t ~ s :=
  LiftRel.symm (· = ·) (@Eq.symm _)
#align stream.wseq.equiv.symm Stream'.Wseq.Equiv.symm

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[trans]
theorem Equiv.trans : ∀ {s t u : Wseq α}, s ~ t → t ~ u → s ~ u :=
  LiftRel.trans (· = ·) (@Eq.trans _)
#align stream.wseq.equiv.trans Stream'.Wseq.Equiv.trans

theorem Equiv.equivalence : Equivalence (@Equiv α) :=
  ⟨@Equiv.refl _, @Equiv.symm _, @Equiv.trans _⟩
#align stream.wseq.equiv.equivalence Stream'.Wseq.Equiv.equivalence

open Computation

-- mathport name: exprreturn
local notation "return" => Computation.pure

@[simp]
theorem destruct_nil : destruct (nil : Wseq α) = return none :=
  Computation.destruct_eq_pure rfl
#align stream.wseq.destruct_nil Stream'.Wseq.destruct_nil

@[simp]
theorem destruct_cons (a : α) (s) : destruct (cons a s) = return (some (a, s)) :=
  Computation.destruct_eq_pure <| by simp [destruct, cons, Computation.rmap]
#align stream.wseq.destruct_cons Stream'.Wseq.destruct_cons

@[simp]
theorem destruct_think (s : Wseq α) : destruct (think s) = (destruct s).think :=
  Computation.destruct_eq_think <| by simp [destruct, think, Computation.rmap]
#align stream.wseq.destruct_think Stream'.Wseq.destruct_think

@[simp]
theorem seq_destruct_nil : Seq.destruct (nil : Wseq α) = none :=
  Seq.destruct_nil
#align stream.wseq.seq_destruct_nil Stream'.Wseq.seq_destruct_nil

@[simp]
theorem seq_destruct_cons (a : α) (s) : Seq.destruct (cons a s) = some (some a, s) :=
  Seq.destruct_cons _ _
#align stream.wseq.seq_destruct_cons Stream'.Wseq.seq_destruct_cons

@[simp]
theorem seq_destruct_think (s : Wseq α) : Seq.destruct (think s) = some (none, s) :=
  Seq.destruct_cons _ _
#align stream.wseq.seq_destruct_think Stream'.Wseq.seq_destruct_think

@[simp]
theorem head_nil : head (nil : Wseq α) = return none := by simp [head] <;> rfl
#align stream.wseq.head_nil Stream'.Wseq.head_nil

@[simp]
theorem head_cons (a : α) (s) : head (cons a s) = return (some a) := by simp [head] <;> rfl
#align stream.wseq.head_cons Stream'.Wseq.head_cons

@[simp]
theorem head_think (s : Wseq α) : head (think s) = (head s).think := by simp [head] <;> rfl
#align stream.wseq.head_think Stream'.Wseq.head_think

@[simp]
theorem flatten_ret (s : Wseq α) : flatten (return s) = s :=
  by
  refine' seq.eq_of_bisim (fun s1 s2 => flatten (return s2) = s1) _ rfl
  intro s' s h; rw [← h]; simp [flatten]
  cases seq.destruct s; · simp
  · cases' val with o s'
    simp
#align stream.wseq.flatten_ret Stream'.Wseq.flatten_ret

@[simp]
theorem flatten_think (c : Computation (Wseq α)) : flatten c.think = think (flatten c) :=
  Seq.destruct_eq_cons <| by simp [flatten, think]
#align stream.wseq.flatten_think Stream'.Wseq.flatten_think

@[simp]
theorem destruct_flatten (c : Computation (Wseq α)) : destruct (flatten c) = c >>= destruct :=
  by
  refine'
    Computation.eq_of_bisim
      (fun c1 c2 => c1 = c2 ∨ ∃ c, c1 = destruct (flatten c) ∧ c2 = Computation.bind c destruct) _
      (Or.inr ⟨c, rfl, rfl⟩)
  intro c1 c2 h;
  exact
    match c1, c2, h with
    | _, _, Or.inl <| Eq.refl c => by cases c.destruct <;> simp
    | _, _, Or.inr ⟨c, rfl, rfl⟩ =>
      by
      apply c.rec_on (fun a => _) fun c' => _ <;> repeat' simp
      · cases (destruct a).destruct <;> simp
      · exact Or.inr ⟨c', rfl, rfl⟩
#align stream.wseq.destruct_flatten Stream'.Wseq.destruct_flatten

theorem head_terminates_iff (s : Wseq α) : Terminates (head s) ↔ Terminates (destruct s) :=
  terminates_map_iff _ (destruct s)
#align stream.wseq.head_terminates_iff Stream'.Wseq.head_terminates_iff

@[simp]
theorem tail_nil : tail (nil : Wseq α) = nil := by simp [tail]
#align stream.wseq.tail_nil Stream'.Wseq.tail_nil

@[simp]
theorem tail_cons (a : α) (s) : tail (cons a s) = s := by simp [tail]
#align stream.wseq.tail_cons Stream'.Wseq.tail_cons

@[simp]
theorem tail_think (s : Wseq α) : tail (think s) = (tail s).think := by simp [tail]
#align stream.wseq.tail_think Stream'.Wseq.tail_think

@[simp]
theorem dropn_nil (n) : drop (nil : Wseq α) n = nil := by induction n <;> simp [*, drop]
#align stream.wseq.dropn_nil Stream'.Wseq.dropn_nil

@[simp]
theorem dropn_cons (a : α) (s) (n) : drop (cons a s) (n + 1) = drop s n := by
  induction n <;> simp [*, drop]
#align stream.wseq.dropn_cons Stream'.Wseq.dropn_cons

@[simp]
theorem dropn_think (s : Wseq α) (n) : drop (think s) n = (drop s n).think := by
  induction n <;> simp [*, drop]
#align stream.wseq.dropn_think Stream'.Wseq.dropn_think

theorem dropn_add (s : Wseq α) (m) : ∀ n, drop s (m + n) = drop (drop s m) n
  | 0 => rfl
  | n + 1 => congr_arg tail (dropn_add n)
#align stream.wseq.dropn_add Stream'.Wseq.dropn_add

theorem dropn_tail (s : Wseq α) (n) : drop (tail s) n = drop s (n + 1) := by
  rw [add_comm] <;> symm <;> apply dropn_add
#align stream.wseq.dropn_tail Stream'.Wseq.dropn_tail

theorem nth_add (s : Wseq α) (m n) : nth s (m + n) = nth (drop s m) n :=
  congr_arg head (dropn_add _ _ _)
#align stream.wseq.nth_add Stream'.Wseq.nth_add

theorem nth_tail (s : Wseq α) (n) : nth (tail s) n = nth s (n + 1) :=
  congr_arg head (dropn_tail _ _)
#align stream.wseq.nth_tail Stream'.Wseq.nth_tail

@[simp]
theorem join_nil : join nil = (nil : Wseq α) :=
  Seq.join_nil
#align stream.wseq.join_nil Stream'.Wseq.join_nil

@[simp]
theorem join_think (S : Wseq (Wseq α)) : join (think S) = think (join S) :=
  by
  simp [think, join]
  unfold Functor.map
  simp [join, seq1.ret]
#align stream.wseq.join_think Stream'.Wseq.join_think

@[simp]
theorem join_cons (s : Wseq α) (S) : join (cons s S) = think (append s (join S)) :=
  by
  simp [think, join]
  unfold Functor.map
  simp [join, cons, append]
#align stream.wseq.join_cons Stream'.Wseq.join_cons

@[simp]
theorem nil_append (s : Wseq α) : append nil s = s :=
  Seq.nil_append _
#align stream.wseq.nil_append Stream'.Wseq.nil_append

@[simp]
theorem cons_append (a : α) (s t) : append (cons a s) t = cons a (append s t) :=
  Seq.cons_append _ _ _
#align stream.wseq.cons_append Stream'.Wseq.cons_append

@[simp]
theorem think_append (s t : Wseq α) : append (think s) t = think (append s t) :=
  Seq.cons_append _ _ _
#align stream.wseq.think_append Stream'.Wseq.think_append

@[simp]
theorem append_nil (s : Wseq α) : append s nil = s :=
  Seq.append_nil _
#align stream.wseq.append_nil Stream'.Wseq.append_nil

@[simp]
theorem append_assoc (s t u : Wseq α) : append (append s t) u = append s (append t u) :=
  Seq.append_assoc _ _ _
#align stream.wseq.append_assoc Stream'.Wseq.append_assoc

/-- auxilary defintion of tail over weak sequences-/
@[simp]
def tail.aux : Option (α × Wseq α) → Computation (Option (α × Wseq α))
  | none => return none
  | some (a, s) => destruct s
#align stream.wseq.tail.aux Stream'.Wseq.tail.aux

theorem destruct_tail (s : Wseq α) : destruct (tail s) = destruct s >>= tail.aux :=
  by
  simp [tail]; rw [← bind_pure_comp_eq_map, LawfulMonad.bind_assoc]
  apply congr_arg; ext1 (_ | ⟨a, s⟩) <;> apply (@pure_bind Computation _ _ _ _ _ _).trans _ <;> simp
#align stream.wseq.destruct_tail Stream'.Wseq.destruct_tail

/-- auxilary defintion of drop over weak sequences-/
@[simp]
def drop.aux : ℕ → Option (α × Wseq α) → Computation (Option (α × Wseq α))
  | 0 => return
  | n + 1 => fun a => tail.aux a >>= drop.aux n
#align stream.wseq.drop.aux Stream'.Wseq.drop.aux

theorem drop.aux_none : ∀ n, @drop.aux α n none = return none
  | 0 => rfl
  | n + 1 =>
    show Computation.bind (return none) (drop.aux n) = return none by rw [ret_bind, drop.aux_none]
#align stream.wseq.drop.aux_none Stream'.Wseq.drop.aux_none

theorem destruct_dropn : ∀ (s : Wseq α) (n), destruct (drop s n) = destruct s >>= drop.aux n
  | s, 0 => (bind_pure' _).symm
  | s, n + 1 => by
    rw [← dropn_tail, destruct_dropn _ n, destruct_tail, LawfulMonad.bind_assoc] <;> rfl
#align stream.wseq.destruct_dropn Stream'.Wseq.destruct_dropn

theorem head_terminates_of_head_tail_terminates (s : Wseq α) [T : Terminates (head (tail s))] :
    Terminates (head s) :=
  (head_terminates_iff _).2 <|
    by
    rcases(head_terminates_iff _).1 T with ⟨⟨a, h⟩⟩
    simp [tail] at h
    rcases exists_of_mem_bind h with ⟨s', h1, h2⟩
    unfold Functor.map at h1
    exact
      let ⟨t, h3, h4⟩ := Computation.exists_of_mem_map h1
      Computation.terminates_of_mem h3
#align stream.wseq.head_terminates_of_head_tail_terminates Stream'.Wseq.head_terminates_of_head_tail_terminates

theorem destruct_some_of_destruct_tail_some {s : Wseq α} {a} (h : some a ∈ destruct (tail s)) :
    ∃ a', some a' ∈ destruct s := by
  unfold tail Functor.map at h; simp at h
  rcases exists_of_mem_bind h with ⟨t, tm, td⟩; clear h
  rcases Computation.exists_of_mem_map tm with ⟨t', ht', ht2⟩; clear tm
  cases' t' with t' <;> rw [← ht2] at td <;> simp at td
  · have := mem_unique td (ret_mem _)
    contradiction
  · exact ⟨_, ht'⟩
#align stream.wseq.destruct_some_of_destruct_tail_some Stream'.Wseq.destruct_some_of_destruct_tail_some

theorem head_some_of_head_tail_some {s : Wseq α} {a} (h : some a ∈ head (tail s)) :
    ∃ a', some a' ∈ head s := by
  unfold head at h
  rcases Computation.exists_of_mem_map h with ⟨o, md, e⟩; clear h
  cases' o with o <;> injection e with h'; clear e h'
  cases' destruct_some_of_destruct_tail_some md with a am
  exact ⟨_, Computation.mem_map ((· <$> ·) (@Prod.fst α (wseq α))) am⟩
#align stream.wseq.head_some_of_head_tail_some Stream'.Wseq.head_some_of_head_tail_some

theorem head_some_of_nth_some {s : Wseq α} {a n} (h : some a ∈ nth s n) : ∃ a', some a' ∈ head s :=
  by
  revert a; induction' n with n IH <;> intros
  exacts[⟨_, h⟩,
    let ⟨a', h'⟩ := head_some_of_head_tail_some h
    IH h']
#align stream.wseq.head_some_of_nth_some Stream'.Wseq.head_some_of_nth_some

instance productive_tail (s : Wseq α) [Productive s] : Productive (tail s) :=
  ⟨fun n => by rw [nth_tail] <;> infer_instance⟩
#align stream.wseq.productive_tail Stream'.Wseq.productive_tail

instance productive_dropn (s : Wseq α) [Productive s] (n) : Productive (drop s n) :=
  ⟨fun m => by rw [← nth_add] <;> infer_instance⟩
#align stream.wseq.productive_dropn Stream'.Wseq.productive_dropn

/-- Given a productive weak sequence, we can collapse all the `think`s to
  produce a sequence. -/
def toSeq (s : Wseq α) [Productive s] : Seq α :=
  ⟨fun n => (nth s n).get, fun n h =>
    by
    cases e : Computation.get (nth s (n + 1)); · assumption
    have := mem_of_get_eq _ e
    simp [nth] at this h; cases' head_some_of_head_tail_some this with a' h'
    have := mem_unique h' (@mem_of_get_eq _ _ _ _ h)
    contradiction⟩
#align stream.wseq.to_seq Stream'.Wseq.toSeq

theorem nth_terminates_le {s : Wseq α} {m n} (h : m ≤ n) :
    Terminates (nth s n) → Terminates (nth s m) := by
  induction' h with m' h IH <;> [exact id,
    exact fun T => IH (@head_terminates_of_head_tail_terminates _ _ T)]
#align stream.wseq.nth_terminates_le Stream'.Wseq.nth_terminates_le

theorem head_terminates_of_nth_terminates {s : Wseq α} {n} :
    Terminates (nth s n) → Terminates (head s) :=
  nth_terminates_le (Nat.zero_le n)
#align stream.wseq.head_terminates_of_nth_terminates Stream'.Wseq.head_terminates_of_nth_terminates

theorem destruct_terminates_of_nth_terminates {s : Wseq α} {n} (T : Terminates (nth s n)) :
    Terminates (destruct s) :=
  (head_terminates_iff _).1 <| head_terminates_of_nth_terminates T
#align stream.wseq.destruct_terminates_of_nth_terminates Stream'.Wseq.destruct_terminates_of_nth_terminates

theorem mem_rec_on {C : Wseq α → Prop} {a s} (M : a ∈ s) (h1 : ∀ b s', a = b ∨ C s' → C (cons b s'))
    (h2 : ∀ s, C s → C (think s)) : C s :=
  by
  apply seq.mem_rec_on M
  intro o s' h; cases' o with b
  · apply h2
    cases h
    · contradiction
    · assumption
  · apply h1
    apply Or.imp_left _ h
    intro h
    injection h
#align stream.wseq.mem_rec_on Stream'.Wseq.mem_rec_on

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem mem_think (s : Wseq α) (a) : a ∈ think s ↔ a ∈ s :=
  by
  cases' s with f al
  change (some (some a) ∈ some none::f) ↔ some (some a) ∈ f
  constructor <;> intro h
  · apply (Stream'.eq_or_mem_of_mem_cons h).resolve_left
    intro
    injections
  · apply Stream'.mem_cons_of_mem _ h
#align stream.wseq.mem_think Stream'.Wseq.mem_think

theorem eq_or_mem_iff_mem {s : Wseq α} {a a' s'} :
    some (a', s') ∈ destruct s → (a ∈ s ↔ a = a' ∨ a ∈ s') :=
  by
  generalize e : destruct s = c; intro h
  revert s;
  apply Computation.memRecOn h _ fun c IH => _ <;> intro s <;>
            apply s.rec_on _ (fun x s => _) fun s => _ <;>
          intro m <;>
        have := congr_arg Computation.destruct m <;>
      simp at this <;>
    cases' this with i1 i2
  · rw [i1, i2]
    cases' s' with f al
    unfold cons Membership.Mem wseq.mem seq.mem seq.cons
    simp
    have h_a_eq_a' : a = a' ↔ some (some a) = some (some a') := by simp
    rw [h_a_eq_a']
    refine' ⟨Stream'.eq_or_mem_of_mem_cons, fun o => _⟩
    · cases' o with e m
      · rw [e]
        apply Stream'.mem_cons
      · exact Stream'.mem_cons_of_mem _ m
  · simp
    exact IH this
#align stream.wseq.eq_or_mem_iff_mem Stream'.Wseq.eq_or_mem_iff_mem

@[simp]
theorem mem_cons_iff (s : Wseq α) (b) {a} : a ∈ cons b s ↔ a = b ∨ a ∈ s :=
  eq_or_mem_iff_mem <| by simp [ret_mem]
#align stream.wseq.mem_cons_iff Stream'.Wseq.mem_cons_iff

theorem mem_cons_of_mem {s : Wseq α} (b) {a} (h : a ∈ s) : a ∈ cons b s :=
  (mem_cons_iff _ _).2 (Or.inr h)
#align stream.wseq.mem_cons_of_mem Stream'.Wseq.mem_cons_of_mem

theorem mem_cons (s : Wseq α) (a) : a ∈ cons a s :=
  (mem_cons_iff _ _).2 (Or.inl rfl)
#align stream.wseq.mem_cons Stream'.Wseq.mem_cons

theorem mem_of_mem_tail {s : Wseq α} {a} : a ∈ tail s → a ∈ s :=
  by
  intro h; have := h; cases' h with n e; revert s; simp [Stream'.nth]
  induction' n with n IH <;> intro s <;> apply s.rec_on _ (fun x s => _) fun s => _ <;>
        repeat' simp <;>
      intro m e <;>
    injections
  · exact Or.inr m
  · exact Or.inr m
  · apply IH m
    rw [e]
    cases tail s
    rfl
#align stream.wseq.mem_of_mem_tail Stream'.Wseq.mem_of_mem_tail

theorem mem_of_mem_dropn {s : Wseq α} {a} : ∀ {n}, a ∈ drop s n → a ∈ s
  | 0, h => h
  | n + 1, h => @mem_of_mem_dropn n (mem_of_mem_tail h)
#align stream.wseq.mem_of_mem_dropn Stream'.Wseq.mem_of_mem_dropn

theorem nth_mem {s : Wseq α} {a n} : some a ∈ nth s n → a ∈ s :=
  by
  revert s; induction' n with n IH <;> intro s h
  · rcases Computation.exists_of_mem_map h with ⟨o, h1, h2⟩
    cases' o with o <;> injection h2 with h'
    cases' o with a' s'
    exact (eq_or_mem_iff_mem h1).2 (Or.inl h'.symm)
  · have := @IH (tail s)
    rw [nth_tail] at this
    exact mem_of_mem_tail (this h)
#align stream.wseq.nth_mem Stream'.Wseq.nth_mem

theorem exists_nth_of_mem {s : Wseq α} {a} (h : a ∈ s) : ∃ n, some a ∈ nth s n :=
  by
  apply mem_rec_on h
  · intro a' s' h
    cases' h with h h
    · exists 0
      simp [nth]
      rw [h]
      apply ret_mem
    · cases' h with n h
      exists n + 1
      simp [nth]
      exact h
  · intro s' h
    cases' h with n h
    exists n
    simp [nth]
    apply think_mem h
#align stream.wseq.exists_nth_of_mem Stream'.Wseq.exists_nth_of_mem

theorem exists_dropn_of_mem {s : Wseq α} {a} (h : a ∈ s) :
    ∃ n s', some (a, s') ∈ destruct (drop s n) :=
  let ⟨n, h⟩ := exists_nth_of_mem h
  ⟨n, by
    rcases(head_terminates_iff _).1 ⟨⟨_, h⟩⟩ with ⟨⟨o, om⟩⟩
    have := Computation.mem_unique (Computation.mem_map _ om) h
    cases' o with o <;> injection this with i
    cases' o with a' s'; dsimp at i
    rw [i] at om; exact ⟨_, om⟩⟩
#align stream.wseq.exists_dropn_of_mem Stream'.Wseq.exists_dropn_of_mem

theorem liftRel_dropn_destruct {R : α → β → Prop} {s t} (H : LiftRel R s t) :
    ∀ n, Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct (drop s n)) (destruct (drop t n))
  | 0 => liftRel_destruct H
  | n + 1 => by
    simp [destruct_tail]
    apply lift_rel_bind
    apply lift_rel_dropn_destruct n
    exact fun a b o =>
      match a, b, o with
      | none, none, _ => by simp
      | some (a, s), some (b, t), ⟨h1, h2⟩ => by simp [tail.aux] <;> apply lift_rel_destruct h2
#align stream.wseq.lift_rel_dropn_destruct Stream'.Wseq.liftRel_dropn_destruct

theorem exists_of_liftRel_left {R : α → β → Prop} {s t} (H : LiftRel R s t) {a} (h : a ∈ s) :
    ∃ b, b ∈ t ∧ R a b :=
  let ⟨n, h⟩ := exists_nth_of_mem h
  let ⟨some (_, s'), sd, rfl⟩ := Computation.exists_of_mem_map h
  let ⟨some (b, t'), td, ⟨ab, _⟩⟩ := (liftRel_dropn_destruct H n).left sd
  ⟨b, nth_mem (Computation.mem_map ((· <$> ·) Prod.fst.{v, v}) td), ab⟩
#align stream.wseq.exists_of_lift_rel_left Stream'.Wseq.exists_of_liftRel_left

theorem exists_of_liftRel_right {R : α → β → Prop} {s t} (H : LiftRel R s t) {b} (h : b ∈ t) :
    ∃ a, a ∈ s ∧ R a b := by rw [← lift_rel.swap] at H <;> exact exists_of_lift_rel_left H h
#align stream.wseq.exists_of_lift_rel_right Stream'.Wseq.exists_of_liftRel_right

theorem head_terminates_of_mem {s : Wseq α} {a} (h : a ∈ s) : Terminates (head s) :=
  let ⟨n, h⟩ := exists_nth_of_mem h
  head_terminates_of_nth_terminates ⟨⟨_, h⟩⟩
#align stream.wseq.head_terminates_of_mem Stream'.Wseq.head_terminates_of_mem

theorem of_mem_append {s₁ s₂ : Wseq α} {a : α} : a ∈ append s₁ s₂ → a ∈ s₁ ∨ a ∈ s₂ :=
  Seq.of_mem_append
#align stream.wseq.of_mem_append Stream'.Wseq.of_mem_append

theorem mem_append_left {s₁ s₂ : Wseq α} {a : α} : a ∈ s₁ → a ∈ append s₁ s₂ :=
  Seq.mem_append_left
#align stream.wseq.mem_append_left Stream'.Wseq.mem_append_left

theorem exists_of_mem_map {f} {b : β} : ∀ {s : Wseq α}, b ∈ map f s → ∃ a, a ∈ s ∧ f a = b
  | ⟨g, al⟩, h => by
    let ⟨o, om, oe⟩ := Seq.exists_of_mem_map h
    cases' o with a <;> injection oe with h' <;> exact ⟨a, om, h'⟩
#align stream.wseq.exists_of_mem_map Stream'.Wseq.exists_of_mem_map

@[simp]
theorem liftRel_nil (R : α → β → Prop) : LiftRel R nil nil := by rw [lift_rel_destruct_iff] <;> simp
#align stream.wseq.lift_rel_nil Stream'.Wseq.liftRel_nil

@[simp]
theorem liftRel_cons (R : α → β → Prop) (a b s t) :
    LiftRel R (cons a s) (cons b t) ↔ R a b ∧ LiftRel R s t := by
  rw [lift_rel_destruct_iff] <;> simp
#align stream.wseq.lift_rel_cons Stream'.Wseq.liftRel_cons

@[simp]
theorem liftRel_think_left (R : α → β → Prop) (s t) : LiftRel R (think s) t ↔ LiftRel R s t := by
  rw [lift_rel_destruct_iff, lift_rel_destruct_iff] <;> simp
#align stream.wseq.lift_rel_think_left Stream'.Wseq.liftRel_think_left

@[simp]
theorem liftRel_think_right (R : α → β → Prop) (s t) : LiftRel R s (think t) ↔ LiftRel R s t := by
  rw [lift_rel_destruct_iff, lift_rel_destruct_iff] <;> simp
#align stream.wseq.lift_rel_think_right Stream'.Wseq.liftRel_think_right

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem cons_congr {s t : Wseq α} (a : α) (h : s ~ t) : cons a s ~ cons a t := by
  unfold Equiv <;> simp <;> exact h
#align stream.wseq.cons_congr Stream'.Wseq.cons_congr

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem think_equiv (s : Wseq α) : think s ~ s := by unfold Equiv <;> simp <;> apply Equiv.refl
#align stream.wseq.think_equiv Stream'.Wseq.think_equiv

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem think_congr {s t : Wseq α} (h : s ~ t) : think s ~ think t := by
  unfold Equiv <;> simp <;> exact h
#align stream.wseq.think_congr Stream'.Wseq.think_congr

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem head_congr : ∀ {s t : Wseq α}, s ~ t → head s ~ head t :=
  by
  suffices ∀ {s t : Wseq α}, s ~ t → ∀ {o}, o ∈ head s → o ∈ head t from fun s t h o =>
    ⟨this h, this h.symm⟩
  intro s t h o ho
  rcases@Computation.exists_of_mem_map _ _ _ _ (destruct s) ho with ⟨ds, dsm, dse⟩
  rw [← dse]
  cases' destruct_congr h with l r
  rcases l dsm with ⟨dt, dtm, dst⟩
  cases' ds with a <;> cases' dt with b
  · apply Computation.mem_map _ dtm
  · cases b
    cases dst
  · cases a
    cases dst
  · cases' a with a s'
    cases' b with b t'
    rw [dst.left]
    exact @Computation.mem_map _ _ (@Functor.map _ _ (α × wseq α) _ Prod.fst) _ (destruct t) dtm
#align stream.wseq.head_congr Stream'.Wseq.head_congr

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem flatten_equiv {c : Computation (Wseq α)} {s} (h : s ∈ c) : flatten c ~ s :=
  by
  apply Computation.memRecOn h; · simp
  · intro s'
    apply Equiv.trans
    simp [think_equiv]
#align stream.wseq.flatten_equiv Stream'.Wseq.flatten_equiv

theorem liftRel_flatten {R : α → β → Prop} {c1 : Computation (Wseq α)} {c2 : Computation (Wseq β)}
    (h : c1.LiftRel (LiftRel R) c2) : LiftRel R (flatten c1) (flatten c2) :=
  let S s t := ∃ c1 c2, s = flatten c1 ∧ t = flatten c2 ∧ Computation.LiftRel (LiftRel R) c1 c2
  ⟨S, ⟨c1, c2, rfl, rfl, h⟩, fun s t h =>
    match s, t, h with
    | _, _, ⟨c1, c2, rfl, rfl, h⟩ => by
      simp; apply lift_rel_bind _ _ h
      intro a b ab; apply Computation.LiftRel.imp _ _ _ (lift_rel_destruct ab)
      intro a b; apply lift_rel_o.imp_right
      intro s t h; refine' ⟨return s, return t, _, _, _⟩ <;> simp [h]⟩
#align stream.wseq.lift_rel_flatten Stream'.Wseq.liftRel_flatten

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem flatten_congr {c1 c2 : Computation (Wseq α)} :
    Computation.LiftRel Equiv c1 c2 → flatten c1 ~ flatten c2 :=
  liftRel_flatten
#align stream.wseq.flatten_congr Stream'.Wseq.flatten_congr

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem tail_congr {s t : Wseq α} (h : s ~ t) : tail s ~ tail t :=
  by
  apply flatten_congr
  unfold Functor.map; rw [← bind_ret, ← bind_ret]
  apply lift_rel_bind _ _ (destruct_congr h)
  intro a b h; simp
  cases' a with a <;> cases' b with b
  · trivial
  · cases h
  · cases a
    cases h
  · cases' a with a s'
    cases' b with b t'
    exact h.right
#align stream.wseq.tail_congr Stream'.Wseq.tail_congr

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem dropn_congr {s t : Wseq α} (h : s ~ t) (n) : drop s n ~ drop t n := by
  induction n <;> simp [*, tail_congr]
#align stream.wseq.dropn_congr Stream'.Wseq.dropn_congr

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem nth_congr {s t : Wseq α} (h : s ~ t) (n) : nth s n ~ nth t n :=
  head_congr (dropn_congr h _)
#align stream.wseq.nth_congr Stream'.Wseq.nth_congr

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mem_congr {s t : Wseq α} (h : s ~ t) (a) : a ∈ s ↔ a ∈ t :=
  suffices ∀ {s t : Wseq α}, s ~ t → a ∈ s → a ∈ t from ⟨this h, this h.symm⟩
  fun s t h as =>
  let ⟨n, hn⟩ := exists_nth_of_mem as
  nth_mem ((nth_congr h _ _).1 hn)
#align stream.wseq.mem_congr Stream'.Wseq.mem_congr

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem productive_congr {s t : Wseq α} (h : s ~ t) : Productive s ↔ Productive t := by
  simp only [productive_iff] <;> exact forall_congr' fun n => terminates_congr <| nth_congr h _
#align stream.wseq.productive_congr Stream'.Wseq.productive_congr

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Equiv.ext {s t : Wseq α} (h : ∀ n, nth s n ~ nth t n) : s ~ t :=
  ⟨fun s t => ∀ n, nth s n ~ nth t n, h, fun s t h =>
    by
    refine' lift_rel_def.2 ⟨_, _⟩
    · rw [← head_terminates_iff, ← head_terminates_iff]
      exact terminates_congr (h 0)
    · intro a b ma mb
      cases' a with a <;> cases' b with b
      · trivial
      · injection mem_unique (Computation.mem_map _ ma) ((h 0 _).2 (Computation.mem_map _ mb))
      · injection mem_unique (Computation.mem_map _ ma) ((h 0 _).2 (Computation.mem_map _ mb))
      · cases' a with a s'
        cases' b with b t'
        injection mem_unique (Computation.mem_map _ ma) ((h 0 _).2 (Computation.mem_map _ mb)) with
          ab
        refine' ⟨ab, fun n => _⟩
        refine'
          (nth_congr (flatten_equiv (Computation.mem_map _ ma)) n).symm.trans
            ((_ : nth (tail s) n ~ nth (tail t) n).trans
              (nth_congr (flatten_equiv (Computation.mem_map _ mb)) n))
        rw [nth_tail, nth_tail]
        apply h⟩
#align stream.wseq.equiv.ext Stream'.Wseq.Equiv.ext

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem length_eq_map (s : Wseq α) : length s = Computation.map List.length (toList s) :=
  by
  refine'
    Computation.eq_of_bisim
      (fun c1 c2 =>
        ∃ (l : List α)(s : wseq α),
          c1 = Computation.corec length._match_2 (l.length, s) ∧
            c2 = Computation.map List.length (Computation.corec to_list._match_2 (l, s)))
      _ ⟨[], s, rfl, rfl⟩
  intro s1 s2 h; rcases h with ⟨l, s, h⟩; rw [h.left, h.right]
  apply s.rec_on _ (fun a s => _) fun s => _ <;> repeat' simp [to_list, nil, cons, think, length]
  · refine' ⟨a::l, s, _, _⟩ <;> simp
  · refine' ⟨l, s, _, _⟩ <;> simp
#align stream.wseq.length_eq_map Stream'.Wseq.length_eq_map

@[simp]
theorem ofList_nil : ofList [] = (nil : Wseq α) :=
  rfl
#align stream.wseq.of_list_nil Stream'.Wseq.ofList_nil

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem ofList_cons (a : α) (l) : ofList (a::l) = cons a (ofList l) :=
  show Seq.map some (Seq.ofList (a::l)) = Seq.cons (some a) (Seq.map some (Seq.ofList l)) by simp
#align stream.wseq.of_list_cons Stream'.Wseq.ofList_cons

@[simp]
theorem to_list'_nil (l : List α) : Computation.corec ToList._match2 (l, nil) = return l.reverse :=
  destruct_eq_pure rfl
#align stream.wseq.to_list'_nil Stream'.Wseq.to_list'_nil

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem to_list'_cons (l : List α) (s : Wseq α) (a : α) :
    Computation.corec ToList._match2 (l, cons a s) =
      (Computation.corec ToList._match2 (a::l, s)).think :=
  destruct_eq_think <| by simp [to_list, cons]
#align stream.wseq.to_list'_cons Stream'.Wseq.to_list'_cons

@[simp]
theorem to_list'_think (l : List α) (s : Wseq α) :
    Computation.corec ToList._match2 (l, think s) =
      (Computation.corec ToList._match2 (l, s)).think :=
  destruct_eq_think <| by simp [to_list, think]
#align stream.wseq.to_list'_think Stream'.Wseq.to_list'_think

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem to_list'_map (l : List α) (s : Wseq α) :
    Computation.corec ToList._match2 (l, s) = (· ++ ·) l.reverse <$> toList s :=
  by
  refine'
    Computation.eq_of_bisim
      (fun c1 c2 =>
        ∃ (l' : List α)(s : wseq α),
          c1 = Computation.corec to_list._match_2 (l' ++ l, s) ∧
            c2 = Computation.map ((· ++ ·) l.reverse) (Computation.corec to_list._match_2 (l', s)))
      _ ⟨[], s, rfl, rfl⟩
  intro s1 s2 h; rcases h with ⟨l', s, h⟩; rw [h.left, h.right]
  apply s.rec_on _ (fun a s => _) fun s => _ <;> repeat' simp [to_list, nil, cons, think, length]
  · refine' ⟨a::l', s, _, _⟩ <;> simp
  · refine' ⟨l', s, _, _⟩ <;> simp
#align stream.wseq.to_list'_map Stream'.Wseq.to_list'_map

@[simp]
theorem toList_cons (a : α) (s) : toList (cons a s) = (List.cons a <$> toList s).think :=
  destruct_eq_think <| by unfold to_list <;> simp <;> rw [to_list'_map] <;> simp <;> rfl
#align stream.wseq.to_list_cons Stream'.Wseq.toList_cons

@[simp]
theorem toList_nil : toList (nil : Wseq α) = return [] :=
  destruct_eq_pure rfl
#align stream.wseq.to_list_nil Stream'.Wseq.toList_nil

theorem toList_ofList (l : List α) : l ∈ toList (ofList l) := by
  induction' l with a l IH <;> simp [ret_mem] <;> exact think_mem (Computation.mem_map _ IH)
#align stream.wseq.to_list_of_list Stream'.Wseq.toList_ofList

@[simp]
theorem destruct_ofSeq (s : Seq α) :
    destruct (ofSeq s) = return (s.headI.map fun a => (a, ofSeq s.tail)) :=
  destruct_eq_pure <| by
    simp [of_seq, head, destruct, seq.destruct, seq.head]
    rw [show seq.nth (some <$> s) 0 = some <$> seq.nth s 0 by apply seq.map_nth]
    cases' seq.nth s 0 with a; · rfl
    unfold Functor.map
    simp [destruct]
#align stream.wseq.destruct_of_seq Stream'.Wseq.destruct_ofSeq

@[simp]
theorem head_ofSeq (s : Seq α) : head (ofSeq s) = return s.headI := by
  simp [head] <;> cases seq.head s <;> rfl
#align stream.wseq.head_of_seq Stream'.Wseq.head_ofSeq

@[simp]
theorem tail_ofSeq (s : Seq α) : tail (ofSeq s) = ofSeq s.tail :=
  by
  simp [tail]; apply s.rec_on _ fun x s => _ <;> simp [of_seq]; · rfl
  rw [seq.head_cons, seq.tail_cons]; rfl
#align stream.wseq.tail_of_seq Stream'.Wseq.tail_ofSeq

@[simp]
theorem dropn_ofSeq (s : Seq α) : ∀ n, drop (ofSeq s) n = ofSeq (s.drop n)
  | 0 => rfl
  | n + 1 => by dsimp [drop] <;> rw [dropn_of_seq, tail_of_seq]
#align stream.wseq.dropn_of_seq Stream'.Wseq.dropn_ofSeq

theorem nth_ofSeq (s : Seq α) (n) : nth (ofSeq s) n = return (Seq.get? s n) := by
  dsimp [nth] <;> rw [dropn_of_seq, head_of_seq, seq.head_dropn]
#align stream.wseq.nth_of_seq Stream'.Wseq.nth_ofSeq

instance productive_ofSeq (s : Seq α) : Productive (ofSeq s) :=
  ⟨fun n => by rw [nth_of_seq] <;> infer_instance⟩
#align stream.wseq.productive_of_seq Stream'.Wseq.productive_ofSeq

theorem toSeq_ofSeq (s : Seq α) : toSeq (ofSeq s) = s :=
  by
  apply Subtype.eq; funext n
  dsimp [to_seq]; apply get_eq_of_mem
  rw [nth_of_seq]; apply ret_mem
#align stream.wseq.to_seq_of_seq Stream'.Wseq.toSeq_ofSeq

/-- The monadic `return a` is a singleton list containing `a`. -/
def ret (a : α) : Wseq α :=
  ofList [a]
#align stream.wseq.ret Stream'.Wseq.ret

@[simp]
theorem map_nil (f : α → β) : map f nil = nil :=
  rfl
#align stream.wseq.map_nil Stream'.Wseq.map_nil

@[simp]
theorem map_cons (f : α → β) (a s) : map f (cons a s) = cons (f a) (map f s) :=
  Seq.map_cons _ _ _
#align stream.wseq.map_cons Stream'.Wseq.map_cons

@[simp]
theorem map_think (f : α → β) (s) : map f (think s) = think (map f s) :=
  Seq.map_cons _ _ _
#align stream.wseq.map_think Stream'.Wseq.map_think

@[simp]
theorem map_id (s : Wseq α) : map id s = s := by simp [map]
#align stream.wseq.map_id Stream'.Wseq.map_id

@[simp]
theorem map_ret (f : α → β) (a) : map f (ret a) = ret (f a) := by simp [ret]
#align stream.wseq.map_ret Stream'.Wseq.map_ret

@[simp]
theorem map_append (f : α → β) (s t) : map f (append s t) = append (map f s) (map f t) :=
  Seq.map_append _ _ _
#align stream.wseq.map_append Stream'.Wseq.map_append

theorem map_comp (f : α → β) (g : β → γ) (s : Wseq α) : map (g ∘ f) s = map g (map f s) :=
  by
  dsimp [map]; rw [← seq.map_comp]
  apply congr_fun; apply congr_arg
  ext ⟨⟩ <;> rfl
#align stream.wseq.map_comp Stream'.Wseq.map_comp

theorem mem_map (f : α → β) {a : α} {s : Wseq α} : a ∈ s → f a ∈ map f s :=
  Seq.mem_map (Option.map f)
#align stream.wseq.mem_map Stream'.Wseq.mem_map

-- The converse is not true without additional assumptions
theorem exists_of_mem_join {a : α} : ∀ {S : Wseq (Wseq α)}, a ∈ join S → ∃ s, s ∈ S ∧ a ∈ s :=
  by
  suffices
    ∀ ss : Wseq α,
      a ∈ ss → ∀ s S, append s (join S) = ss → a ∈ append s (join S) → a ∈ s ∨ ∃ s, s ∈ S ∧ a ∈ s
    from fun S h => (this _ h nil S (by simp) (by simp [h])).resolve_left (not_mem_nil _)
  intro ss h; apply mem_rec_on h (fun b ss o => _) fun ss IH => _ <;> intro s S
  · refine' s.rec_on (S.rec_on _ (fun s S => _) fun S => _) (fun b' s => _) fun s => _ <;>
                intro ej m <;> simp at ej <;> have := congr_arg seq.destruct ej <;> simp at this <;>
        try cases this <;> try contradiction
    substs b' ss
    simp at m⊢
    cases' o with e IH
    · simp [e]
    cases' m with e m
    · simp [e]
    exact Or.imp_left Or.inr (IH _ _ rfl m)
  · refine' s.rec_on (S.rec_on _ (fun s S => _) fun S => _) (fun b' s => _) fun s => _ <;>
                intro ej m <;> simp at ej <;> have := congr_arg seq.destruct ej <;> simp at this <;>
        try try have := this.1; contradiction <;> subst ss
    · apply Or.inr
      simp at m⊢
      cases' IH s S rfl m with as ex
      · exact ⟨s, Or.inl rfl, as⟩
      · rcases ex with ⟨s', sS, as⟩
        exact ⟨s', Or.inr sS, as⟩
    · apply Or.inr
      simp at m
      rcases(IH nil S (by simp) (by simp [m])).resolve_left (not_mem_nil _) with ⟨s, sS, as⟩
      exact ⟨s, by simp [sS], as⟩
    · simp at m IH⊢
      apply IH _ _ rfl m
#align stream.wseq.exists_of_mem_join Stream'.Wseq.exists_of_mem_join

theorem exists_of_mem_bind {s : Wseq α} {f : α → Wseq β} {b} (h : b ∈ bind s f) :
    ∃ a ∈ s, b ∈ f a :=
  let ⟨t, tm, bt⟩ := exists_of_mem_join h
  let ⟨a, as, e⟩ := exists_of_mem_map tm
  ⟨a, as, by rwa [e]⟩
#align stream.wseq.exists_of_mem_bind Stream'.Wseq.exists_of_mem_bind

theorem destruct_map (f : α → β) (s : Wseq α) :
    destruct (map f s) = Computation.map (Option.map (Prod.map f (map f))) (destruct s) :=
  by
  apply
    Computation.eq_of_bisim fun c1 c2 =>
      ∃ s,
        c1 = destruct (map f s) ∧
          c2 = Computation.map (Option.map (Prod.map f (map f))) (destruct s)
  · intro c1 c2 h
    cases' h with s h
    rw [h.left, h.right]
    apply s.rec_on _ (fun a s => _) fun s => _ <;> simp
    exact ⟨s, rfl, rfl⟩
  · exact ⟨s, rfl, rfl⟩
#align stream.wseq.destruct_map Stream'.Wseq.destruct_map

theorem liftRel_map {δ} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : Wseq α} {s2 : Wseq β}
    {f1 : α → γ} {f2 : β → δ} (h1 : LiftRel R s1 s2) (h2 : ∀ {a b}, R a b → S (f1 a) (f2 b)) :
    LiftRel S (map f1 s1) (map f2 s2) :=
  ⟨fun s1 s2 => ∃ s t, s1 = map f1 s ∧ s2 = map f2 t ∧ LiftRel R s t, ⟨s1, s2, rfl, rfl, h1⟩,
    fun s1 s2 h =>
    match s1, s2, h with
    | _, _, ⟨s, t, rfl, rfl, h⟩ => by
      simp [destruct_map]; apply Computation.liftRel_map _ _ (lift_rel_destruct h)
      intro o p h
      cases' o with a <;> cases' p with b <;> simp
      · cases b <;> cases h
      · cases a <;> cases h
      · cases' a with a s <;> cases' b with b t
        cases' h with r h
        exact ⟨h2 r, s, rfl, t, rfl, h⟩⟩
#align stream.wseq.lift_rel_map Stream'.Wseq.liftRel_map

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem map_congr (f : α → β) {s t : Wseq α} (h : s ~ t) : map f s ~ map f t :=
  liftRel_map _ _ h fun _ _ => congr_arg _
#align stream.wseq.map_congr Stream'.Wseq.map_congr

/-- auxilary defintion of `destruct_append` over weak sequences-/
@[simp]
def DestructAppend.aux (t : Wseq α) : Option (α × Wseq α) → Computation (Option (α × Wseq α))
  | none => destruct t
  | some (a, s) => return (some (a, append s t))
#align stream.wseq.destruct_append.aux Stream'.Wseq.DestructAppend.aux

theorem destruct_append (s t : Wseq α) :
    destruct (append s t) = (destruct s).bind (DestructAppend.aux t) :=
  by
  apply
    Computation.eq_of_bisim
      (fun c1 c2 =>
        ∃ s t, c1 = destruct (append s t) ∧ c2 = (destruct s).bind (destruct_append.aux t))
      _ ⟨s, t, rfl, rfl⟩
  intro c1 c2 h; rcases h with ⟨s, t, h⟩; rw [h.left, h.right]
  apply s.rec_on _ (fun a s => _) fun s => _ <;> simp
  · apply t.rec_on _ (fun b t => _) fun t => _ <;> simp
    · refine' ⟨nil, t, _, _⟩ <;> simp
  · exact ⟨s, t, rfl, rfl⟩
#align stream.wseq.destruct_append Stream'.Wseq.destruct_append

/-- auxilary defintion of `destruct_join` over weak sequences-/
@[simp]
def DestructJoin.aux : Option (Wseq α × Wseq (Wseq α)) → Computation (Option (α × Wseq α))
  | none => return none
  | some (s, S) => (destruct (append s (join S))).think
#align stream.wseq.destruct_join.aux Stream'.Wseq.DestructJoin.aux

theorem destruct_join (S : Wseq (Wseq α)) :
    destruct (join S) = (destruct S).bind DestructJoin.aux :=
  by
  apply
    Computation.eq_of_bisim
      (fun c1 c2 =>
        c1 = c2 ∨ ∃ S, c1 = destruct (join S) ∧ c2 = (destruct S).bind destruct_join.aux)
      _ (Or.inr ⟨S, rfl, rfl⟩)
  intro c1 c2 h;
  exact
    match c1, c2, h with
    | _, _, Or.inl <| Eq.refl c => by cases c.destruct <;> simp
    | _, _, Or.inr ⟨S, rfl, rfl⟩ =>
      by
      apply S.rec_on _ (fun s S => _) fun S => _ <;> simp
      · refine' Or.inr ⟨S, rfl, rfl⟩
#align stream.wseq.destruct_join Stream'.Wseq.destruct_join

theorem liftRel_append (R : α → β → Prop) {s1 s2 : Wseq α} {t1 t2 : Wseq β} (h1 : LiftRel R s1 t1)
    (h2 : LiftRel R s2 t2) : LiftRel R (append s1 s2) (append t1 t2) :=
  ⟨fun s t => LiftRel R s t ∨ ∃ s1 t1, s = append s1 s2 ∧ t = append t1 t2 ∧ LiftRel R s1 t1,
    Or.inr ⟨s1, t1, rfl, rfl, h1⟩, fun s t h =>
    match s, t, h with
    | s, t, Or.inl h =>
      by
      apply Computation.LiftRel.imp _ _ _ (lift_rel_destruct h)
      intro a b; apply lift_rel_o.imp_right
      intro s t; apply Or.inl
    | _, _, Or.inr ⟨s1, t1, rfl, rfl, h⟩ =>
      by
      simp [destruct_append]
      apply Computation.liftRel_bind _ _ (lift_rel_destruct h)
      intro o p h
      cases' o with a <;> cases' p with b
      · simp
        apply Computation.LiftRel.imp _ _ _ (lift_rel_destruct h2)
        intro a b
        apply lift_rel_o.imp_right
        intro s t
        apply Or.inl
      · cases b <;> cases h
      · cases a <;> cases h
      · cases' a with a s <;> cases' b with b t
        cases' h with r h
        simp
        exact ⟨r, Or.inr ⟨s, rfl, t, rfl, h⟩⟩⟩
#align stream.wseq.lift_rel_append Stream'.Wseq.liftRel_append

theorem LiftRelJoin.lem (R : α → β → Prop) {S T} {U : Wseq α → Wseq β → Prop}
    (ST : LiftRel (LiftRel R) S T)
    (HU :
      ∀ s1 s2,
        (∃ s t S T,
            s1 = append s (join S) ∧
              s2 = append t (join T) ∧ LiftRel R s t ∧ LiftRel (LiftRel R) S T) →
          U s1 s2)
    {a} (ma : a ∈ destruct (join S)) : ∃ b, b ∈ destruct (join T) ∧ LiftRelO R U a b :=
  by
  cases' exists_results_of_mem ma with n h; clear ma; revert a S T
  apply Nat.strong_induction_on n _
  intro n IH a S T ST ra; simp [destruct_join] at ra;
  exact
    let ⟨o, m, k, rs1, rs2, en⟩ := of_results_bind ra
    let ⟨p, mT, rop⟩ := Computation.exists_of_LiftRel_left (lift_rel_destruct ST) rs1.Mem
    match o, p, rop, rs1, rs2, mT with
    | none, none, _, rs1, rs2, mT => by
      simp only [destruct_join] <;>
        exact ⟨none, mem_bind mT (ret_mem _), by rw [eq_of_ret_mem rs2.mem] <;> trivial⟩
    | some (s, S'), some (t, T'), ⟨st, ST'⟩, rs1, rs2, mT => by
      simp [destruct_append] at rs2 <;>
        exact
          let ⟨k1, rs3, ek⟩ := of_results_think rs2
          let ⟨o', m1, n1, rs4, rs5, ek1⟩ := of_results_bind rs3
          let ⟨p', mt, rop'⟩ := Computation.exists_of_LiftRel_left (lift_rel_destruct st) rs4.Mem
          match o', p', rop', rs4, rs5, mt with
          | none, none, _, rs4, rs5', mt =>
            by
            have : n1 < n := by
              rw [en, ek, ek1]
              apply lt_of_lt_of_le _ (Nat.le_add_right _ _)
              apply Nat.lt_succ_of_le (Nat.le_add_right _ _)
            let ⟨ob, mb, rob⟩ := IH _ this ST' rs5'
            refine' ⟨ob, _, rob⟩ <;>
              · simp [destruct_join]
                apply mem_bind mT
                simp [destruct_append]
                apply think_mem
                apply mem_bind mt
                exact mb
          | some (a, s'), some (b, t'), ⟨ab, st'⟩, rs4, rs5, mt =>
            by
            simp at rs5
            refine' ⟨some (b, append t' (join T')), _, _⟩
            · simp [destruct_join]
              apply mem_bind mT
              simp [destruct_append]
              apply think_mem
              apply mem_bind mt
              apply ret_mem
            rw [eq_of_ret_mem rs5.mem]
            exact ⟨ab, HU _ _ ⟨s', t', S', T', rfl, rfl, st', ST'⟩⟩
#align stream.wseq.lift_rel_join.lem Stream'.Wseq.LiftRelJoin.lem

theorem liftRel_join (R : α → β → Prop) {S : Wseq (Wseq α)} {T : Wseq (Wseq β)}
    (h : LiftRel (LiftRel R) S T) : LiftRel R (join S) (join T) :=
  ⟨fun s1 s2 =>
    ∃ s t S T,
      s1 = append s (join S) ∧ s2 = append t (join T) ∧ LiftRel R s t ∧ LiftRel (LiftRel R) S T,
    ⟨nil, nil, S, T, by simp, by simp, by simp, h⟩, fun s1 s2 ⟨s, t, S, T, h1, h2, st, ST⟩ =>
    by
    clear _fun_match _x
    rw [h1, h2]; rw [destruct_append, destruct_append]
    apply Computation.liftRel_bind _ _ (lift_rel_destruct st)
    exact fun o p h =>
      match o, p, h with
      | some (a, s), some (b, t), ⟨h1, h2⟩ => by simp <;> exact ⟨h1, s, t, S, rfl, T, rfl, h2, ST⟩
      | none, none, _ => by
        dsimp [destruct_append.aux, Computation.LiftRel]; constructor
        · intro
          apply lift_rel_join.lem _ ST fun _ _ => id
        · intro b mb
          rw [← lift_rel_o.swap]
          apply lift_rel_join.lem (swap R)
          · rw [← lift_rel.swap R, ← lift_rel.swap]
            apply ST
          · rw [← lift_rel.swap R, ← lift_rel.swap (lift_rel R)]
            exact fun s1 s2 ⟨s, t, S, T, h1, h2, st, ST⟩ => ⟨t, s, T, S, h2, h1, st, ST⟩
          · exact mb⟩
#align stream.wseq.lift_rel_join Stream'.Wseq.liftRel_join

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem join_congr {S T : Wseq (Wseq α)} (h : LiftRel Equiv S T) : join S ~ join T :=
  liftRel_join _ h
#align stream.wseq.join_congr Stream'.Wseq.join_congr

theorem liftRel_bind {δ} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : Wseq α} {s2 : Wseq β}
    {f1 : α → Wseq γ} {f2 : β → Wseq δ} (h1 : LiftRel R s1 s2)
    (h2 : ∀ {a b}, R a b → LiftRel S (f1 a) (f2 b)) : LiftRel S (bind s1 f1) (bind s2 f2) :=
  liftRel_join _ (liftRel_map _ _ h1 @h2)
#align stream.wseq.lift_rel_bind Stream'.Wseq.liftRel_bind

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem bind_congr {s1 s2 : Wseq α} {f1 f2 : α → Wseq β} (h1 : s1 ~ s2) (h2 : ∀ a, f1 a ~ f2 a) :
    bind s1 f1 ~ bind s2 f2 :=
  liftRel_bind _ _ h1 fun a b h => by rw [h] <;> apply h2
#align stream.wseq.bind_congr Stream'.Wseq.bind_congr

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem join_ret (s : Wseq α) : join (ret s) ~ s := by simp [ret] <;> apply think_equiv
#align stream.wseq.join_ret Stream'.Wseq.join_ret

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem join_map_ret (s : Wseq α) : join (map ret s) ~ s :=
  by
  refine' ⟨fun s1 s2 => join (map ret s2) = s1, rfl, _⟩
  intro s' s h; rw [← h]
  apply lift_rel_rec fun c1 c2 => ∃ s, c1 = destruct (join (map ret s)) ∧ c2 = destruct s
  ·
    exact fun c1 c2 h =>
      match c1, c2, h with
      | _, _, ⟨s, rfl, rfl⟩ => by
        clear h _match
        have :
          ∀ s,
            ∃ s' : wseq α,
              (map ret s).join.destruct = (map ret s').join.destruct ∧ destruct s = s'.destruct :=
          fun s => ⟨s, rfl, rfl⟩
        apply s.rec_on _ (fun a s => _) fun s => _ <;> simp [ret, ret_mem, this, Option.exists]
  · exact ⟨s, rfl, rfl⟩
#align stream.wseq.join_map_ret Stream'.Wseq.join_map_ret

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem join_append (S T : Wseq (Wseq α)) : join (append S T) ~ append (join S) (join T) :=
  by
  refine'
    ⟨fun s1 s2 =>
      ∃ s S T, s1 = append s (join (append S T)) ∧ s2 = append s (append (join S) (join T)),
      ⟨nil, S, T, by simp, by simp⟩, _⟩
  intro s1 s2 h
  apply
    lift_rel_rec
      (fun c1 c2 =>
        ∃ (s : wseq α)(S T : _),
          c1 = destruct (append s (join (append S T))) ∧
            c2 = destruct (append s (append (join S) (join T))))
      _ _ _
      (let ⟨s, S, T, h1, h2⟩ := h
      ⟨s, S, T, congr_arg destruct h1, congr_arg destruct h2⟩)
  intro c1 c2 h
  exact
    match c1, c2, h with
    | _, _, ⟨s, S, T, rfl, rfl⟩ => by
      clear _match h h
      apply wseq.rec_on s _ (fun a s => _) fun s => _ <;> simp
      · apply wseq.rec_on S _ (fun s S => _) fun S => _ <;> simp
        · apply wseq.rec_on T _ (fun s T => _) fun T => _ <;> simp
          · refine' ⟨s, nil, T, _, _⟩ <;> simp
          · refine' ⟨nil, nil, T, _, _⟩ <;> simp
        · exact ⟨s, S, T, rfl, rfl⟩
        · refine' ⟨nil, S, T, _, _⟩ <;> simp
      · exact ⟨s, S, T, rfl, rfl⟩
      · exact ⟨s, S, T, rfl, rfl⟩
#align stream.wseq.join_append Stream'.Wseq.join_append

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem bind_ret (f : α → β) (s) : bind s (ret ∘ f) ~ map f s :=
  by
  dsimp [bind]; change fun x => ret (f x) with ret ∘ f
  rw [map_comp]; apply join_map_ret
#align stream.wseq.bind_ret Stream'.Wseq.bind_ret

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem ret_bind (a : α) (f : α → Wseq β) : bind (ret a) f ~ f a := by simp [bind]
#align stream.wseq.ret_bind Stream'.Wseq.ret_bind

@[simp]
theorem map_join (f : α → β) (S) : map f (join S) = join (map (map f) S) :=
  by
  apply
    seq.eq_of_bisim fun s1 s2 =>
      ∃ s S, s1 = append s (map f (join S)) ∧ s2 = append s (join (map (map f) S))
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, S, rfl, rfl⟩ =>
        by
        apply wseq.rec_on s _ (fun a s => _) fun s => _ <;> simp
        · apply wseq.rec_on S _ (fun s S => _) fun S => _ <;> simp
          · exact ⟨map f s, S, rfl, rfl⟩
          · refine' ⟨nil, S, _, _⟩ <;> simp
        · exact ⟨_, _, rfl, rfl⟩
        · exact ⟨_, _, rfl, rfl⟩
  · refine' ⟨nil, S, _, _⟩ <;> simp
#align stream.wseq.map_join Stream'.Wseq.map_join

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem join_join (SS : Wseq (Wseq (Wseq α))) : join (join SS) ~ join (map join SS) :=
  by
  refine'
    ⟨fun s1 s2 =>
      ∃ s S SS,
        s1 = append s (join (append S (join SS))) ∧
          s2 = append s (append (join S) (join (map join SS))),
      ⟨nil, nil, SS, by simp, by simp⟩, _⟩
  intro s1 s2 h
  apply
    lift_rel_rec
      (fun c1 c2 =>
        ∃ s S SS,
          c1 = destruct (append s (join (append S (join SS)))) ∧
            c2 = destruct (append s (append (join S) (join (map join SS)))))
      _ (destruct s1) (destruct s2)
      (let ⟨s, S, SS, h1, h2⟩ := h
      ⟨s, S, SS, by simp [h1], by simp [h2]⟩)
  intro c1 c2 h
  exact
    match c1, c2, h with
    | _, _, ⟨s, S, SS, rfl, rfl⟩ => by
      clear _match h h
      apply wseq.rec_on s _ (fun a s => _) fun s => _ <;> simp
      · apply wseq.rec_on S _ (fun s S => _) fun S => _ <;> simp
        · apply wseq.rec_on SS _ (fun S SS => _) fun SS => _ <;> simp
          · refine' ⟨nil, S, SS, _, _⟩ <;> simp
          · refine' ⟨nil, nil, SS, _, _⟩ <;> simp
        · exact ⟨s, S, SS, rfl, rfl⟩
        · refine' ⟨nil, S, SS, _, _⟩ <;> simp
      · exact ⟨s, S, SS, rfl, rfl⟩
      · exact ⟨s, S, SS, rfl, rfl⟩
#align stream.wseq.join_join Stream'.Wseq.join_join

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem bind_assoc (s : Wseq α) (f : α → Wseq β) (g : β → Wseq γ) :
    bind (bind s f) g ~ bind s fun x : α => bind (f x) g :=
  by
  simp [bind]; rw [← map_comp f (map g), map_comp (map g ∘ f) join]
  apply join_join
#align stream.wseq.bind_assoc Stream'.Wseq.bind_assoc

instance : Monad Wseq where
  map := @map
  pure := @ret
  bind := @bind

/-
  Unfortunately, wseq is not a lawful monad, because it does not satisfy
  the monad laws exactly, only up to sequence equivalence.
  Furthermore, even quotienting by the equivalence is not sufficient,
  because the join operation involves lists of quotient elements,
  with a lifted equivalence relation, and pure quotients cannot handle
  this type of construction.

instance : is_lawful_monad wseq :=
{ id_map := @map_id,
  bind_pure_comp_eq_map := @bind_ret,
  pure_bind := @ret_bind,
  bind_assoc := @bind_assoc }
-/
end Wseq

end Stream'

