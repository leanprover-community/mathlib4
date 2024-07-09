/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Logic.Relation
import Mathlib.Data.Option.Basic
import Mathlib.Data.Seq.Seq

#align_import data.seq.wseq from "leanprover-community/mathlib"@"a7e36e48519ab281320c4d192da6a7b348ce40ad"

/-!
# Partially defined possibly infinite lists

This file provides a `WSeq α` type representing partially defined possibly infinite lists
(referred here as weak sequences).
-/

namespace Stream'

open Function

universe u v w

/-
coinductive WSeq (α : Type u) : Type u
| nil : WSeq α
| cons : α → WSeq α → WSeq α
| think : WSeq α → WSeq α
-/
/-- Weak sequences.

  While the `Seq` structure allows for lists which may not be finite,
  a weak sequence also allows the computation of each element to
  involve an indeterminate amount of computation, including possibly
  an infinite loop. This is represented as a regular `Seq` interspersed
  with `none` elements to indicate that computation is ongoing.

  This model is appropriate for Haskell style lazy lists, and is closed
  under most interesting computation patterns on infinite lists,
  but conversely it is difficult to extract elements from it. -/
def WSeq (α) :=
  Seq (Option α)
#align stream.wseq Stream'.WSeq

/-
coinductive WSeq (α : Type u) : Type u
| nil : WSeq α
| cons : α → WSeq α → WSeq α
| think : WSeq α → WSeq α
-/

namespace WSeq

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Turn a sequence into a weak sequence -/
@[coe]
def ofSeq : Seq α → WSeq α :=
  (· <$> ·) some
#align stream.wseq.of_seq Stream'.WSeq.ofSeq

/-- Turn a list into a weak sequence -/
@[coe]
def ofList (l : List α) : WSeq α :=
  ofSeq l
#align stream.wseq.of_list Stream'.WSeq.ofList

/-- Turn a stream into a weak sequence -/
@[coe]
def ofStream (l : Stream' α) : WSeq α :=
  ofSeq l
#align stream.wseq.of_stream Stream'.WSeq.ofStream

instance coeSeq : Coe (Seq α) (WSeq α) :=
  ⟨ofSeq⟩
#align stream.wseq.coe_seq Stream'.WSeq.coeSeq

instance coeList : Coe (List α) (WSeq α) :=
  ⟨ofList⟩
#align stream.wseq.coe_list Stream'.WSeq.coeList

instance coeStream : Coe (Stream' α) (WSeq α) :=
  ⟨ofStream⟩
#align stream.wseq.coe_stream Stream'.WSeq.coeStream

/-- The empty weak sequence -/
def nil : WSeq α :=
  Seq.nil
#align stream.wseq.nil Stream'.WSeq.nil

instance inhabited : Inhabited (WSeq α) :=
  ⟨nil⟩
#align stream.wseq.inhabited Stream'.WSeq.inhabited

/-- Prepend an element to a weak sequence -/
def cons (a : α) : WSeq α → WSeq α :=
  Seq.cons (some a)
#align stream.wseq.cons Stream'.WSeq.cons

/-- Compute for one tick, without producing any elements -/
def think : WSeq α → WSeq α :=
  Seq.cons none
#align stream.wseq.think Stream'.WSeq.think

/-- Destruct a weak sequence, to (eventually possibly) produce either
  `none` for `nil` or `some (a, s)` if an element is produced. -/
def destruct : WSeq α → Computation (Option (α × WSeq α)) :=
  Computation.corec fun s =>
    match Seq.destruct s with
    | none => Sum.inl none
    | some (none, s') => Sum.inr s'
    | some (some a, s') => Sum.inl (some (a, s'))
#align stream.wseq.destruct Stream'.WSeq.destruct

/-- Recursion principle for weak sequences, compare with `List.recOn`. -/
def recOn {C : WSeq α → Sort v} (s : WSeq α) (h1 : C nil) (h2 : ∀ x s, C (cons x s))
    (h3 : ∀ s, C (think s)) : C s :=
  Seq.recOn s h1 fun o => Option.recOn o h3 h2
#align stream.wseq.rec_on Stream'.WSeq.recOn

/-- membership for weak sequences-/
protected def Mem (a : α) (s : WSeq α) :=
  Seq.Mem (some a) s
#align stream.wseq.mem Stream'.WSeq.Mem

instance membership : Membership α (WSeq α) :=
  ⟨WSeq.Mem⟩
#align stream.wseq.has_mem Stream'.WSeq.membership

theorem not_mem_nil (a : α) : a ∉ @nil α :=
  Seq.not_mem_nil (some a)
#align stream.wseq.not_mem_nil Stream'.WSeq.not_mem_nil

/-- Get the head of a weak sequence. This involves a possibly
  infinite computation. -/
def head (s : WSeq α) : Computation (Option α) :=
  Computation.map (Prod.fst <$> ·) (destruct s)
#align stream.wseq.head Stream'.WSeq.head

/-- Encode a computation yielding a weak sequence into additional
  `think` constructors in a weak sequence -/
def flatten : Computation (WSeq α) → WSeq α :=
  Seq.corec fun c =>
    match Computation.destruct c with
    | Sum.inl s => Seq.omap (return ·) (Seq.destruct s)
    | Sum.inr c' => some (none, c')
#align stream.wseq.flatten Stream'.WSeq.flatten

/-- Get the tail of a weak sequence. This doesn't need a `Computation`
  wrapper, unlike `head`, because `flatten` allows us to hide this
  in the construction of the weak sequence itself. -/
def tail (s : WSeq α) : WSeq α :=
  flatten <| (fun o => Option.recOn o nil Prod.snd) <$> destruct s
#align stream.wseq.tail Stream'.WSeq.tail

/-- drop the first `n` elements from `s`. -/
def drop (s : WSeq α) : ℕ → WSeq α
  | 0 => s
  | n + 1 => tail (drop s n)
#align stream.wseq.drop Stream'.WSeq.drop

/-- Get the nth element of `s`. -/
def get? (s : WSeq α) (n : ℕ) : Computation (Option α) :=
  head (drop s n)
#align stream.wseq.nth Stream'.WSeq.get?

/-- Convert `s` to a list (if it is finite and completes in finite time). -/
def toList (s : WSeq α) : Computation (List α) :=
  @Computation.corec (List α) (List α × WSeq α)
    (fun ⟨l, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a::l, s'))
    ([], s)
#align stream.wseq.to_list Stream'.WSeq.toList

/-- Get the length of `s` (if it is finite and completes in finite time). -/
def length (s : WSeq α) : Computation ℕ :=
  @Computation.corec ℕ (ℕ × WSeq α)
    (fun ⟨n, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl n
      | some (none, s') => Sum.inr (n, s')
      | some (some _, s') => Sum.inr (n + 1, s'))
    (0, s)
#align stream.wseq.length Stream'.WSeq.length

/-- A weak sequence is finite if `toList s` terminates. Equivalently,
  it is a finite number of `think` and `cons` applied to `nil`. -/
class IsFinite (s : WSeq α) : Prop where
  out : (toList s).Terminates
#align stream.wseq.is_finite Stream'.WSeq.IsFinite

instance toList_terminates (s : WSeq α) [h : IsFinite s] : (toList s).Terminates :=
  h.out
#align stream.wseq.to_list_terminates Stream'.WSeq.toList_terminates

/-- Get the list corresponding to a finite weak sequence. -/
def get (s : WSeq α) [IsFinite s] : List α :=
  (toList s).get
#align stream.wseq.get Stream'.WSeq.get

/-- A weak sequence is *productive* if it never stalls forever - there are
 always a finite number of `think`s between `cons` constructors.
 The sequence itself is allowed to be infinite though. -/
class Productive (s : WSeq α) : Prop where
  get?_terminates : ∀ n, (get? s n).Terminates
#align stream.wseq.productive Stream'.WSeq.Productive
#align stream.wseq.productive.nth_terminates Stream'.WSeq.Productive.get?_terminates

theorem productive_iff (s : WSeq α) : Productive s ↔ ∀ n, (get? s n).Terminates :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align stream.wseq.productive_iff Stream'.WSeq.productive_iff

instance get?_terminates (s : WSeq α) [h : Productive s] : ∀ n, (get? s n).Terminates :=
  h.get?_terminates
#align stream.wseq.nth_terminates Stream'.WSeq.get?_terminates

instance head_terminates (s : WSeq α) [Productive s] : (head s).Terminates :=
  s.get?_terminates 0
#align stream.wseq.head_terminates Stream'.WSeq.head_terminates

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
#align stream.wseq.update_nth Stream'.WSeq.updateNth

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
#align stream.wseq.remove_nth Stream'.WSeq.removeNth

/-- Map the elements of `s` over `f`, removing any values that yield `none`. -/
def filterMap (f : α → Option β) : WSeq α → WSeq β :=
  Seq.corec fun s =>
    match Seq.destruct s with
    | none => none
    | some (none, s') => some (none, s')
    | some (some a, s') => some (f a, s')
#align stream.wseq.filter_map Stream'.WSeq.filterMap

/-- Select the elements of `s` that satisfy `p`. -/
def filter (p : α → Prop) [DecidablePred p] : WSeq α → WSeq α :=
  filterMap fun a => if p a then some a else none
#align stream.wseq.filter Stream'.WSeq.filter

-- example of infinite list manipulations
/-- Get the first element of `s` satisfying `p`. -/
def find (p : α → Prop) [DecidablePred p] (s : WSeq α) : Computation (Option α) :=
  head <| filter p s
#align stream.wseq.find Stream'.WSeq.find

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
#align stream.wseq.zip_with Stream'.WSeq.zipWith

/-- Zip two weak sequences into a single sequence of pairs -/
def zip : WSeq α → WSeq β → WSeq (α × β) :=
  zipWith Prod.mk
#align stream.wseq.zip Stream'.WSeq.zip

/-- Get the list of indexes of elements of `s` satisfying `p` -/
def findIndexes (p : α → Prop) [DecidablePred p] (s : WSeq α) : WSeq ℕ :=
  (zip s (Stream'.nats : WSeq ℕ)).filterMap fun ⟨a, n⟩ => if p a then some n else none
#align stream.wseq.find_indexes Stream'.WSeq.findIndexes

/-- Get the index of the first element of `s` satisfying `p` -/
def findIndex (p : α → Prop) [DecidablePred p] (s : WSeq α) : Computation ℕ :=
  (fun o => Option.getD o 0) <$> head (findIndexes p s)
#align stream.wseq.find_index Stream'.WSeq.findIndex

/-- Get the index of the first occurrence of `a` in `s` -/
def indexOf [DecidableEq α] (a : α) : WSeq α → Computation ℕ :=
  findIndex (Eq a)
#align stream.wseq.index_of Stream'.WSeq.indexOf

/-- Get the indexes of occurrences of `a` in `s` -/
def indexesOf [DecidableEq α] (a : α) : WSeq α → WSeq ℕ :=
  findIndexes (Eq a)
#align stream.wseq.indexes_of Stream'.WSeq.indexesOf

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
#align stream.wseq.union Stream'.WSeq.union

/-- Returns `true` if `s` is `nil` and `false` if `s` has an element -/
def isEmpty (s : WSeq α) : Computation Bool :=
  Computation.map Option.isNone <| head s
#align stream.wseq.is_empty Stream'.WSeq.isEmpty

/-- Calculate one step of computation -/
def compute (s : WSeq α) : WSeq α :=
  match Seq.destruct s with
  | some (none, s') => s'
  | _ => s
#align stream.wseq.compute Stream'.WSeq.compute

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
#align stream.wseq.take Stream'.WSeq.take

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
#align stream.wseq.split_at Stream'.WSeq.splitAt

/-- Returns `true` if any element of `s` satisfies `p` -/
def any (s : WSeq α) (p : α → Bool) : Computation Bool :=
  Computation.corec
    (fun s : WSeq α =>
      match Seq.destruct s with
      | none => Sum.inl false
      | some (none, s') => Sum.inr s'
      | some (some a, s') => if p a then Sum.inl true else Sum.inr s')
    s
#align stream.wseq.any Stream'.WSeq.any

/-- Returns `true` if every element of `s` satisfies `p` -/
def all (s : WSeq α) (p : α → Bool) : Computation Bool :=
  Computation.corec
    (fun s : WSeq α =>
      match Seq.destruct s with
      | none => Sum.inl true
      | some (none, s') => Sum.inr s'
      | some (some a, s') => if p a then Sum.inr s' else Sum.inl false)
    s
#align stream.wseq.all Stream'.WSeq.all

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
#align stream.wseq.scanl Stream'.WSeq.scanl

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
#align stream.wseq.inits Stream'.WSeq.inits

/-- Like take, but does not wait for a result. Calculates `n` steps of
  computation and returns the sequence computed so far -/
def collect (s : WSeq α) (n : ℕ) : List α :=
  (Seq.take n s).filterMap id
#align stream.wseq.collect Stream'.WSeq.collect

/-- Append two weak sequences. As with `Seq.append`, this may not use
  the second sequence if the first one takes forever to compute -/
def append : WSeq α → WSeq α → WSeq α :=
  Seq.append
#align stream.wseq.append Stream'.WSeq.append

/-- Map a function over a weak sequence -/
def map (f : α → β) : WSeq α → WSeq β :=
  Seq.map (Option.map f)
#align stream.wseq.map Stream'.WSeq.map

/-- Flatten a sequence of weak sequences. (Note that this allows
  empty sequences, unlike `Seq.join`.) -/
def join (S : WSeq (WSeq α)) : WSeq α :=
  Seq.join
    ((fun o : Option (WSeq α) =>
        match o with
        | none => Seq1.ret none
        | some s => (none, s)) <$>
      S)
#align stream.wseq.join Stream'.WSeq.join

/-- Monadic bind operator for weak sequences -/
def bind (s : WSeq α) (f : α → WSeq β) : WSeq β :=
  join (map f s)
#align stream.wseq.bind Stream'.WSeq.bind

/-- lift a relation to a relation over weak sequences -/
@[simp]
def LiftRelO (R : α → β → Prop) (C : WSeq α → WSeq β → Prop) :
    Option (α × WSeq α) → Option (β × WSeq β) → Prop
  | none, none => True
  | some (a, s), some (b, t) => R a b ∧ C s t
  | _, _ => False
#align stream.wseq.lift_rel_o Stream'.WSeq.LiftRelO

theorem LiftRelO.imp {R S : α → β → Prop} {C D : WSeq α → WSeq β → Prop} (H1 : ∀ a b, R a b → S a b)
    (H2 : ∀ s t, C s t → D s t) : ∀ {o p}, LiftRelO R C o p → LiftRelO S D o p
  | none, none, _ => trivial
  | some (_, _), some (_, _), h => And.imp (H1 _ _) (H2 _ _) h
  | none, some _, h => False.elim h
  | some (_, _), none, h => False.elim h
#align stream.wseq.lift_rel_o.imp Stream'.WSeq.LiftRelO.imp

theorem LiftRelO.imp_right (R : α → β → Prop) {C D : WSeq α → WSeq β → Prop}
    (H : ∀ s t, C s t → D s t) {o p} : LiftRelO R C o p → LiftRelO R D o p :=
  LiftRelO.imp (fun _ _ => id) H
#align stream.wseq.lift_rel_o.imp_right Stream'.WSeq.LiftRelO.imp_right

/-- Definition of bisimilarity for weak sequences-/
@[simp]
def BisimO (R : WSeq α → WSeq α → Prop) : Option (α × WSeq α) → Option (α × WSeq α) → Prop :=
  LiftRelO (· = ·) R
#align stream.wseq.bisim_o Stream'.WSeq.BisimO

theorem BisimO.imp {R S : WSeq α → WSeq α → Prop} (H : ∀ s t, R s t → S s t) {o p} :
    BisimO R o p → BisimO S o p :=
  LiftRelO.imp_right _ H
#align stream.wseq.bisim_o.imp Stream'.WSeq.BisimO.imp

/-- Two weak sequences are `LiftRel R` related if they are either both empty,
  or they are both nonempty and the heads are `R` related and the tails are
  `LiftRel R` related. (This is a coinductive definition.) -/
def LiftRel (R : α → β → Prop) (s : WSeq α) (t : WSeq β) : Prop :=
  ∃ C : WSeq α → WSeq β → Prop,
    C s t ∧ ∀ {s t}, C s t → Computation.LiftRel (LiftRelO R C) (destruct s) (destruct t)
#align stream.wseq.lift_rel Stream'.WSeq.LiftRel

/-- If two sequences are equivalent, then they have the same values and
  the same computational behavior (i.e. if one loops forever then so does
  the other), although they may differ in the number of `think`s needed to
  arrive at the answer. -/
def Equiv : WSeq α → WSeq α → Prop :=
  LiftRel (· = ·)
#align stream.wseq.equiv Stream'.WSeq.Equiv

theorem liftRel_destruct {R : α → β → Prop} {s : WSeq α} {t : WSeq β} :
    LiftRel R s t → Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct s) (destruct t)
  | ⟨R, h1, h2⟩ => by
    refine Computation.LiftRel.imp ?_ _ _ (h2 h1)
    apply LiftRelO.imp_right
    exact fun s' t' h' => ⟨R, h', @h2⟩
#align stream.wseq.lift_rel_destruct Stream'.WSeq.liftRel_destruct

theorem liftRel_destruct_iff {R : α → β → Prop} {s : WSeq α} {t : WSeq β} :
    LiftRel R s t ↔ Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct s) (destruct t) :=
  ⟨liftRel_destruct, fun h =>
    ⟨fun s t =>
      LiftRel R s t ∨ Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct s) (destruct t),
      Or.inr h, fun {s t} h => by
      have h : Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct s) (destruct t) := by
        cases' h with h h
        · exact liftRel_destruct h
        · assumption
      apply Computation.LiftRel.imp _ _ _ h
      intro a b
      apply LiftRelO.imp_right
      intro s t
      apply Or.inl⟩⟩
#align stream.wseq.lift_rel_destruct_iff Stream'.WSeq.liftRel_destruct_iff

-- Porting note: To avoid ambiguous notation, `~` became `~ʷ`.
infixl:50 " ~ʷ " => Equiv

theorem destruct_congr {s t : WSeq α} :
    s ~ʷ t → Computation.LiftRel (BisimO (· ~ʷ ·)) (destruct s) (destruct t) :=
  liftRel_destruct
#align stream.wseq.destruct_congr Stream'.WSeq.destruct_congr

theorem destruct_congr_iff {s t : WSeq α} :
    s ~ʷ t ↔ Computation.LiftRel (BisimO (· ~ʷ ·)) (destruct s) (destruct t) :=
  liftRel_destruct_iff
#align stream.wseq.destruct_congr_iff Stream'.WSeq.destruct_congr_iff

theorem LiftRel.refl (R : α → α → Prop) (H : Reflexive R) : Reflexive (LiftRel R) := fun s => by
  refine ⟨(· = ·), rfl, fun {s t} (h : s = t) => ?_⟩
  rw [← h]
  apply Computation.LiftRel.refl
  intro a
  cases' a with a
  · simp
  · cases a
    simp only [LiftRelO, and_true]
    apply H
#align stream.wseq.lift_rel.refl Stream'.WSeq.LiftRel.refl

theorem LiftRelO.swap (R : α → β → Prop) (C) :
    swap (LiftRelO R C) = LiftRelO (swap R) (swap C) := by
  funext x y
  rcases x with ⟨⟩ | ⟨hx, jx⟩ <;> rcases y with ⟨⟩ | ⟨hy, jy⟩ <;> rfl
#align stream.wseq.lift_rel_o.swap Stream'.WSeq.LiftRelO.swap

theorem LiftRel.swap_lem {R : α → β → Prop} {s1 s2} (h : LiftRel R s1 s2) :
    LiftRel (swap R) s2 s1 := by
  refine ⟨swap (LiftRel R), h, fun {s t} (h : LiftRel R t s) => ?_⟩
  rw [← LiftRelO.swap, Computation.LiftRel.swap]
  apply liftRel_destruct h
#align stream.wseq.lift_rel.swap_lem Stream'.WSeq.LiftRel.swap_lem

theorem LiftRel.swap (R : α → β → Prop) : swap (LiftRel R) = LiftRel (swap R) :=
  funext fun _ => funext fun _ => propext ⟨LiftRel.swap_lem, LiftRel.swap_lem⟩
#align stream.wseq.lift_rel.swap Stream'.WSeq.LiftRel.swap

theorem LiftRel.symm (R : α → α → Prop) (H : Symmetric R) : Symmetric (LiftRel R) :=
  fun s1 s2 (h : Function.swap (LiftRel R) s2 s1) => by rwa [LiftRel.swap, H.swap_eq] at h
#align stream.wseq.lift_rel.symm Stream'.WSeq.LiftRel.symm

theorem LiftRel.trans (R : α → α → Prop) (H : Transitive R) : Transitive (LiftRel R) :=
  fun s t u h1 h2 => by
  refine ⟨fun s u => ∃ t, LiftRel R s t ∧ LiftRel R t u, ⟨t, h1, h2⟩, fun {s u} h => ?_⟩
  rcases h with ⟨t, h1, h2⟩
  have h1 := liftRel_destruct h1
  have h2 := liftRel_destruct h2
  refine
    Computation.liftRel_def.2
      ⟨(Computation.terminates_of_liftRel h1).trans (Computation.terminates_of_liftRel h2),
        fun {a c} ha hc => ?_⟩
  rcases h1.left ha with ⟨b, hb, t1⟩
  have t2 := Computation.rel_of_liftRel h2 hb hc
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
#align stream.wseq.lift_rel.trans Stream'.WSeq.LiftRel.trans

theorem LiftRel.equiv (R : α → α → Prop) : Equivalence R → Equivalence (LiftRel R)
  | ⟨refl, symm, trans⟩ => ⟨LiftRel.refl R refl, @(LiftRel.symm R @symm), @(LiftRel.trans R @trans)⟩
#align stream.wseq.lift_rel.equiv Stream'.WSeq.LiftRel.equiv

@[refl]
theorem Equiv.refl : ∀ s : WSeq α, s ~ʷ s :=
  LiftRel.refl (· = ·) Eq.refl
#align stream.wseq.equiv.refl Stream'.WSeq.Equiv.refl

@[symm]
theorem Equiv.symm : ∀ {s t : WSeq α}, s ~ʷ t → t ~ʷ s :=
  @(LiftRel.symm (· = ·) (@Eq.symm _))
#align stream.wseq.equiv.symm Stream'.WSeq.Equiv.symm

@[trans]
theorem Equiv.trans : ∀ {s t u : WSeq α}, s ~ʷ t → t ~ʷ u → s ~ʷ u :=
  @(LiftRel.trans (· = ·) (@Eq.trans _))
#align stream.wseq.equiv.trans Stream'.WSeq.Equiv.trans

theorem Equiv.equivalence : Equivalence (@Equiv α) :=
  ⟨@Equiv.refl _, @Equiv.symm _, @Equiv.trans _⟩
#align stream.wseq.equiv.equivalence Stream'.WSeq.Equiv.equivalence

open Computation

@[simp]
theorem destruct_nil : destruct (nil : WSeq α) = Computation.pure none :=
  Computation.destruct_eq_pure rfl
#align stream.wseq.destruct_nil Stream'.WSeq.destruct_nil

@[simp]
theorem destruct_cons (a : α) (s) : destruct (cons a s) = Computation.pure (some (a, s)) :=
  Computation.destruct_eq_pure <| by simp [destruct, cons, Computation.rmap]
#align stream.wseq.destruct_cons Stream'.WSeq.destruct_cons

@[simp]
theorem destruct_think (s : WSeq α) : destruct (think s) = (destruct s).think :=
  Computation.destruct_eq_think <| by simp [destruct, think, Computation.rmap]
#align stream.wseq.destruct_think Stream'.WSeq.destruct_think

@[simp]
theorem seq_destruct_nil : Seq.destruct (nil : WSeq α) = none :=
  Seq.destruct_nil
#align stream.wseq.seq_destruct_nil Stream'.WSeq.seq_destruct_nil

@[simp]
theorem seq_destruct_cons (a : α) (s) : Seq.destruct (cons a s) = some (some a, s) :=
  Seq.destruct_cons _ _
#align stream.wseq.seq_destruct_cons Stream'.WSeq.seq_destruct_cons

@[simp]
theorem seq_destruct_think (s : WSeq α) : Seq.destruct (think s) = some (none, s) :=
  Seq.destruct_cons _ _
#align stream.wseq.seq_destruct_think Stream'.WSeq.seq_destruct_think

@[simp]
theorem head_nil : head (nil : WSeq α) = Computation.pure none := by simp [head]
#align stream.wseq.head_nil Stream'.WSeq.head_nil

@[simp]
theorem head_cons (a : α) (s) : head (cons a s) = Computation.pure (some a) := by simp [head]
#align stream.wseq.head_cons Stream'.WSeq.head_cons

@[simp]
theorem head_think (s : WSeq α) : head (think s) = (head s).think := by simp [head]
#align stream.wseq.head_think Stream'.WSeq.head_think

@[simp]
theorem flatten_pure (s : WSeq α) : flatten (Computation.pure s) = s := by
  refine Seq.eq_of_bisim (fun s1 s2 => flatten (Computation.pure s2) = s1) ?_ rfl
  intro s' s h
  rw [← h]
  simp only [Seq.BisimO, flatten, Seq.omap, pure_def, Seq.corec_eq, destruct_pure]
  cases Seq.destruct s with
  | none => simp
  | some val =>
    cases' val with o s'
    simp
#align stream.wseq.flatten_ret Stream'.WSeq.flatten_pure

@[simp]
theorem flatten_think (c : Computation (WSeq α)) : flatten c.think = think (flatten c) :=
  Seq.destruct_eq_cons <| by simp [flatten, think]
#align stream.wseq.flatten_think Stream'.WSeq.flatten_think

@[simp]
theorem destruct_flatten (c : Computation (WSeq α)) : destruct (flatten c) = c >>= destruct := by
  refine
    Computation.eq_of_bisim
      (fun c1 c2 => c1 = c2 ∨ ∃ c, c1 = destruct (flatten c) ∧ c2 = Computation.bind c destruct) ?_
      (Or.inr ⟨c, rfl, rfl⟩)
  intro c1 c2 h
  exact
    match c1, c2, h with
    | c, _, Or.inl rfl => by cases c.destruct <;> simp
    | _, _, Or.inr ⟨c, rfl, rfl⟩ => by
      induction' c using Computation.recOn with a c' <;> simp
      · cases (destruct a).destruct <;> simp
      · exact Or.inr ⟨c', rfl, rfl⟩
#align stream.wseq.destruct_flatten Stream'.WSeq.destruct_flatten

theorem head_terminates_iff (s : WSeq α) : Terminates (head s) ↔ Terminates (destruct s) :=
  terminates_map_iff _ (destruct s)
#align stream.wseq.head_terminates_iff Stream'.WSeq.head_terminates_iff

@[simp]
theorem tail_nil : tail (nil : WSeq α) = nil := by simp [tail]
#align stream.wseq.tail_nil Stream'.WSeq.tail_nil

@[simp]
theorem tail_cons (a : α) (s) : tail (cons a s) = s := by simp [tail]
#align stream.wseq.tail_cons Stream'.WSeq.tail_cons

@[simp]
theorem tail_think (s : WSeq α) : tail (think s) = (tail s).think := by simp [tail]
#align stream.wseq.tail_think Stream'.WSeq.tail_think

@[simp]
theorem dropn_nil (n) : drop (nil : WSeq α) n = nil := by induction n <;> simp [*, drop]
#align stream.wseq.dropn_nil Stream'.WSeq.dropn_nil

@[simp]
theorem dropn_cons (a : α) (s) (n) : drop (cons a s) (n + 1) = drop s n := by
  induction n with
  | zero => simp [drop]
  | succ n n_ih =>
    -- porting note (#10745): was `simp [*, drop]`.
    simp [drop, ← n_ih]
#align stream.wseq.dropn_cons Stream'.WSeq.dropn_cons

@[simp]
theorem dropn_think (s : WSeq α) (n) : drop (think s) n = (drop s n).think := by
  induction n <;> simp [*, drop]
#align stream.wseq.dropn_think Stream'.WSeq.dropn_think

theorem dropn_add (s : WSeq α) (m) : ∀ n, drop s (m + n) = drop (drop s m) n
  | 0 => rfl
  | n + 1 => congr_arg tail (dropn_add s m n)
#align stream.wseq.dropn_add Stream'.WSeq.dropn_add

theorem dropn_tail (s : WSeq α) (n) : drop (tail s) n = drop s (n + 1) := by
  rw [Nat.add_comm]
  symm
  apply dropn_add
#align stream.wseq.dropn_tail Stream'.WSeq.dropn_tail

theorem get?_add (s : WSeq α) (m n) : get? s (m + n) = get? (drop s m) n :=
  congr_arg head (dropn_add _ _ _)
#align stream.wseq.nth_add Stream'.WSeq.get?_add

theorem get?_tail (s : WSeq α) (n) : get? (tail s) n = get? s (n + 1) :=
  congr_arg head (dropn_tail _ _)
#align stream.wseq.nth_tail Stream'.WSeq.get?_tail

@[simp]
theorem join_nil : join nil = (nil : WSeq α) :=
  Seq.join_nil
#align stream.wseq.join_nil Stream'.WSeq.join_nil

@[simp]
theorem join_think (S : WSeq (WSeq α)) : join (think S) = think (join S) := by
  simp only [join, think]
  dsimp only [(· <$> ·)]
  simp [join, Seq1.ret]
#align stream.wseq.join_think Stream'.WSeq.join_think

@[simp]
theorem join_cons (s : WSeq α) (S) : join (cons s S) = think (append s (join S)) := by
  simp only [join, think]
  dsimp only [(· <$> ·)]
  simp [join, cons, append]
#align stream.wseq.join_cons Stream'.WSeq.join_cons

@[simp]
theorem nil_append (s : WSeq α) : append nil s = s :=
  Seq.nil_append _
#align stream.wseq.nil_append Stream'.WSeq.nil_append

@[simp]
theorem cons_append (a : α) (s t) : append (cons a s) t = cons a (append s t) :=
  Seq.cons_append _ _ _
#align stream.wseq.cons_append Stream'.WSeq.cons_append

@[simp]
theorem think_append (s t : WSeq α) : append (think s) t = think (append s t) :=
  Seq.cons_append _ _ _
#align stream.wseq.think_append Stream'.WSeq.think_append

@[simp]
theorem append_nil (s : WSeq α) : append s nil = s :=
  Seq.append_nil _
#align stream.wseq.append_nil Stream'.WSeq.append_nil

@[simp]
theorem append_assoc (s t u : WSeq α) : append (append s t) u = append s (append t u) :=
  Seq.append_assoc _ _ _
#align stream.wseq.append_assoc Stream'.WSeq.append_assoc

/-- auxiliary definition of tail over weak sequences-/
@[simp]
def tail.aux : Option (α × WSeq α) → Computation (Option (α × WSeq α))
  | none => Computation.pure none
  | some (_, s) => destruct s
#align stream.wseq.tail.aux Stream'.WSeq.tail.aux

theorem destruct_tail (s : WSeq α) : destruct (tail s) = destruct s >>= tail.aux := by
  simp only [tail, destruct_flatten, tail.aux]; rw [← bind_pure_comp, LawfulMonad.bind_assoc]
  apply congr_arg; ext1 (_ | ⟨a, s⟩) <;> apply (@pure_bind Computation _ _ _ _ _ _).trans _ <;> simp
#align stream.wseq.destruct_tail Stream'.WSeq.destruct_tail

/-- auxiliary definition of drop over weak sequences-/
@[simp]
def drop.aux : ℕ → Option (α × WSeq α) → Computation (Option (α × WSeq α))
  | 0 => Computation.pure
  | n + 1 => fun a => tail.aux a >>= drop.aux n
#align stream.wseq.drop.aux Stream'.WSeq.drop.aux

theorem drop.aux_none : ∀ n, @drop.aux α n none = Computation.pure none
  | 0 => rfl
  | n + 1 =>
    show Computation.bind (Computation.pure none) (drop.aux n) = Computation.pure none by
      rw [ret_bind, drop.aux_none n]
#align stream.wseq.drop.aux_none Stream'.WSeq.drop.aux_none

theorem destruct_dropn : ∀ (s : WSeq α) (n), destruct (drop s n) = destruct s >>= drop.aux n
  | s, 0 => (bind_pure' _).symm
  | s, n + 1 => by
    rw [← dropn_tail, destruct_dropn _ n, destruct_tail, LawfulMonad.bind_assoc]
    rfl
#align stream.wseq.destruct_dropn Stream'.WSeq.destruct_dropn

theorem head_terminates_of_head_tail_terminates (s : WSeq α) [T : Terminates (head (tail s))] :
    Terminates (head s) :=
  (head_terminates_iff _).2 <| by
    rcases (head_terminates_iff _).1 T with ⟨⟨a, h⟩⟩
    simp? [tail] at h says simp only [tail, destruct_flatten] at h
    rcases exists_of_mem_bind h with ⟨s', h1, _⟩
    unfold Functor.map at h1
    exact
      let ⟨t, h3, _⟩ := Computation.exists_of_mem_map h1
      Computation.terminates_of_mem h3
#align stream.wseq.head_terminates_of_head_tail_terminates Stream'.WSeq.head_terminates_of_head_tail_terminates

theorem destruct_some_of_destruct_tail_some {s : WSeq α} {a} (h : some a ∈ destruct (tail s)) :
    ∃ a', some a' ∈ destruct s := by
  unfold tail Functor.map at h; simp only [destruct_flatten] at h
  rcases exists_of_mem_bind h with ⟨t, tm, td⟩; clear h
  rcases Computation.exists_of_mem_map tm with ⟨t', ht', ht2⟩; clear tm
  cases' t' with t' <;> rw [← ht2] at td <;> simp only [destruct_nil] at td
  · have := mem_unique td (ret_mem _)
    contradiction
  · exact ⟨_, ht'⟩
#align stream.wseq.destruct_some_of_destruct_tail_some Stream'.WSeq.destruct_some_of_destruct_tail_some

theorem head_some_of_head_tail_some {s : WSeq α} {a} (h : some a ∈ head (tail s)) :
    ∃ a', some a' ∈ head s := by
  unfold head at h
  rcases Computation.exists_of_mem_map h with ⟨o, md, e⟩; clear h
  cases' o with o <;> [injection e; injection e with h']; clear h'
  cases' destruct_some_of_destruct_tail_some md with a am
  exact ⟨_, Computation.mem_map (@Prod.fst α (WSeq α) <$> ·) am⟩
#align stream.wseq.head_some_of_head_tail_some Stream'.WSeq.head_some_of_head_tail_some

theorem head_some_of_get?_some {s : WSeq α} {a n} (h : some a ∈ get? s n) :
    ∃ a', some a' ∈ head s := by
  induction n generalizing a with
  | zero => exact ⟨_, h⟩
  | succ n IH =>
      let ⟨a', h'⟩ := head_some_of_head_tail_some h
      exact IH h'
#align stream.wseq.head_some_of_nth_some Stream'.WSeq.head_some_of_get?_some

instance productive_tail (s : WSeq α) [Productive s] : Productive (tail s) :=
  ⟨fun n => by rw [get?_tail]; infer_instance⟩
#align stream.wseq.productive_tail Stream'.WSeq.productive_tail

instance productive_dropn (s : WSeq α) [Productive s] (n) : Productive (drop s n) :=
  ⟨fun m => by rw [← get?_add]; infer_instance⟩
#align stream.wseq.productive_dropn Stream'.WSeq.productive_dropn

/-- Given a productive weak sequence, we can collapse all the `think`s to
  produce a sequence. -/
def toSeq (s : WSeq α) [Productive s] : Seq α :=
  ⟨fun n => (get? s n).get,
   fun {n} h => by
    cases e : Computation.get (get? s (n + 1))
    · assumption
    have := Computation.mem_of_get_eq _ e
    simp? [get?] at this h says simp only [get?] at this h
    cases' head_some_of_head_tail_some this with a' h'
    have := mem_unique h' (@Computation.mem_of_get_eq _ _ _ _ h)
    contradiction⟩
#align stream.wseq.to_seq Stream'.WSeq.toSeq

theorem get?_terminates_le {s : WSeq α} {m n} (h : m ≤ n) :
    Terminates (get? s n) → Terminates (get? s m) := by
  induction' h with m' _ IH
  exacts [id, fun T => IH (@head_terminates_of_head_tail_terminates _ _ T)]
#align stream.wseq.nth_terminates_le Stream'.WSeq.get?_terminates_le

theorem head_terminates_of_get?_terminates {s : WSeq α} {n} :
    Terminates (get? s n) → Terminates (head s) :=
  get?_terminates_le (Nat.zero_le n)
#align stream.wseq.head_terminates_of_nth_terminates Stream'.WSeq.head_terminates_of_get?_terminates

theorem destruct_terminates_of_get?_terminates {s : WSeq α} {n} (T : Terminates (get? s n)) :
    Terminates (destruct s) :=
  (head_terminates_iff _).1 <| head_terminates_of_get?_terminates T
#align stream.wseq.destruct_terminates_of_nth_terminates Stream'.WSeq.destruct_terminates_of_get?_terminates

theorem mem_rec_on {C : WSeq α → Prop} {a s} (M : a ∈ s) (h1 : ∀ b s', a = b ∨ C s' → C (cons b s'))
    (h2 : ∀ s, C s → C (think s)) : C s := by
  apply Seq.mem_rec_on M
  intro o s' h; cases' o with b
  · apply h2
    cases h
    · contradiction
    · assumption
  · apply h1
    apply Or.imp_left _ h
    intro h
    injection h
#align stream.wseq.mem_rec_on Stream'.WSeq.mem_rec_on

@[simp]
theorem mem_think (s : WSeq α) (a) : a ∈ think s ↔ a ∈ s := by
  cases' s with f al
  change (some (some a) ∈ some none::f) ↔ some (some a) ∈ f
  constructor <;> intro h
  · apply (Stream'.eq_or_mem_of_mem_cons h).resolve_left
    intro
    injections
  · apply Stream'.mem_cons_of_mem _ h
#align stream.wseq.mem_think Stream'.WSeq.mem_think

theorem eq_or_mem_iff_mem {s : WSeq α} {a a' s'} :
    some (a', s') ∈ destruct s → (a ∈ s ↔ a = a' ∨ a ∈ s') := by
  generalize e : destruct s = c; intro h
  revert s
  apply Computation.memRecOn h <;> [skip; intro c IH] <;> intro s <;>
    induction' s using WSeq.recOn with x s s <;>
    intro m <;>
    have := congr_arg Computation.destruct m <;>
    simp at this
  · cases' this with i1 i2
    rw [i1, i2]
    cases' s' with f al
    dsimp only [cons, (· ∈ ·), WSeq.Mem, Seq.Mem, Seq.cons]
    have h_a_eq_a' : a = a' ↔ some (some a) = some (some a') := by simp
    rw [h_a_eq_a']
    refine ⟨Stream'.eq_or_mem_of_mem_cons, fun o => ?_⟩
    · cases' o with e m
      · rw [e]
        apply Stream'.mem_cons
      · exact Stream'.mem_cons_of_mem _ m
  · simp [IH this]
#align stream.wseq.eq_or_mem_iff_mem Stream'.WSeq.eq_or_mem_iff_mem

@[simp]
theorem mem_cons_iff (s : WSeq α) (b) {a} : a ∈ cons b s ↔ a = b ∨ a ∈ s :=
  eq_or_mem_iff_mem <| by simp [ret_mem]
#align stream.wseq.mem_cons_iff Stream'.WSeq.mem_cons_iff

theorem mem_cons_of_mem {s : WSeq α} (b) {a} (h : a ∈ s) : a ∈ cons b s :=
  (mem_cons_iff _ _).2 (Or.inr h)
#align stream.wseq.mem_cons_of_mem Stream'.WSeq.mem_cons_of_mem

theorem mem_cons (s : WSeq α) (a) : a ∈ cons a s :=
  (mem_cons_iff _ _).2 (Or.inl rfl)
#align stream.wseq.mem_cons Stream'.WSeq.mem_cons

theorem mem_of_mem_tail {s : WSeq α} {a} : a ∈ tail s → a ∈ s := by
  intro h; have := h; cases' h with n e; revert s; simp only [Stream'.get]
  induction' n with n IH <;> intro s <;> induction' s using WSeq.recOn with x s s <;>
    simp <;> intro m e <;>
    injections
  · exact Or.inr m
  · exact Or.inr m
  · apply IH m
    rw [e]
    cases tail s
    rfl
#align stream.wseq.mem_of_mem_tail Stream'.WSeq.mem_of_mem_tail

theorem mem_of_mem_dropn {s : WSeq α} {a} : ∀ {n}, a ∈ drop s n → a ∈ s
  | 0, h => h
  | n + 1, h => @mem_of_mem_dropn s a n (mem_of_mem_tail h)
#align stream.wseq.mem_of_mem_dropn Stream'.WSeq.mem_of_mem_dropn

theorem get?_mem {s : WSeq α} {a n} : some a ∈ get? s n → a ∈ s := by
  revert s; induction' n with n IH <;> intro s h
  · -- Porting note: This line is required to infer metavariables in
    --               `Computation.exists_of_mem_map`.
    dsimp only [get?, head] at h
    rcases Computation.exists_of_mem_map h with ⟨o, h1, h2⟩
    cases' o with o
    · injection h2
    injection h2 with h'
    cases' o with a' s'
    exact (eq_or_mem_iff_mem h1).2 (Or.inl h'.symm)
  · have := @IH (tail s)
    rw [get?_tail] at this
    exact mem_of_mem_tail (this h)
#align stream.wseq.nth_mem Stream'.WSeq.get?_mem

theorem exists_get?_of_mem {s : WSeq α} {a} (h : a ∈ s) : ∃ n, some a ∈ get? s n := by
  apply mem_rec_on h
  · intro a' s' h
    cases' h with h h
    · exists 0
      simp only [get?, drop, head_cons]
      rw [h]
      apply ret_mem
    · cases' h with n h
      exists n + 1
      -- porting note (#10745): was `simp [get?]`.
      simpa [get?]
  · intro s' h
    cases' h with n h
    exists n
    simp only [get?, dropn_think, head_think]
    apply think_mem h
#align stream.wseq.exists_nth_of_mem Stream'.WSeq.exists_get?_of_mem

theorem exists_dropn_of_mem {s : WSeq α} {a} (h : a ∈ s) :
    ∃ n s', some (a, s') ∈ destruct (drop s n) :=
  let ⟨n, h⟩ := exists_get?_of_mem h
  ⟨n, by
    rcases (head_terminates_iff _).1 ⟨⟨_, h⟩⟩ with ⟨⟨o, om⟩⟩
    have := Computation.mem_unique (Computation.mem_map _ om) h
    cases' o with o
    · injection this
    injection this with i
    cases' o with a' s'
    dsimp at i
    rw [i] at om
    exact ⟨_, om⟩⟩
#align stream.wseq.exists_dropn_of_mem Stream'.WSeq.exists_dropn_of_mem

theorem liftRel_dropn_destruct {R : α → β → Prop} {s t} (H : LiftRel R s t) :
    ∀ n, Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct (drop s n)) (destruct (drop t n))
  | 0 => liftRel_destruct H
  | n + 1 => by
    simp only [LiftRelO, drop, Nat.add_eq, Nat.add_zero, destruct_tail, tail.aux]
    apply liftRel_bind
    · apply liftRel_dropn_destruct H n
    exact fun {a b} o =>
      match a, b, o with
      | none, none, _ => by
        -- Porting note: These 2 theorems should be excluded.
        simp [-liftRel_pure_left, -liftRel_pure_right]
      | some (a, s), some (b, t), ⟨_, h2⟩ => by simpa [tail.aux] using liftRel_destruct h2
#align stream.wseq.lift_rel_dropn_destruct Stream'.WSeq.liftRel_dropn_destruct

theorem exists_of_liftRel_left {R : α → β → Prop} {s t} (H : LiftRel R s t) {a} (h : a ∈ s) :
    ∃ b, b ∈ t ∧ R a b := by
  let ⟨n, h⟩ := exists_get?_of_mem h
  -- Porting note: This line is required to infer metavariables in
  --               `Computation.exists_of_mem_map`.
  dsimp only [get?, head] at h
  let ⟨some (_, s'), sd, rfl⟩ := Computation.exists_of_mem_map h
  let ⟨some (b, t'), td, ⟨ab, _⟩⟩ := (liftRel_dropn_destruct H n).left sd
  exact ⟨b, get?_mem (Computation.mem_map (Prod.fst.{v, v} <$> ·) td), ab⟩
#align stream.wseq.exists_of_lift_rel_left Stream'.WSeq.exists_of_liftRel_left

theorem exists_of_liftRel_right {R : α → β → Prop} {s t} (H : LiftRel R s t) {b} (h : b ∈ t) :
    ∃ a, a ∈ s ∧ R a b := by rw [← LiftRel.swap] at H; exact exists_of_liftRel_left H h
#align stream.wseq.exists_of_lift_rel_right Stream'.WSeq.exists_of_liftRel_right

theorem head_terminates_of_mem {s : WSeq α} {a} (h : a ∈ s) : Terminates (head s) :=
  let ⟨_, h⟩ := exists_get?_of_mem h
  head_terminates_of_get?_terminates ⟨⟨_, h⟩⟩
#align stream.wseq.head_terminates_of_mem Stream'.WSeq.head_terminates_of_mem

theorem of_mem_append {s₁ s₂ : WSeq α} {a : α} : a ∈ append s₁ s₂ → a ∈ s₁ ∨ a ∈ s₂ :=
  Seq.of_mem_append
#align stream.wseq.of_mem_append Stream'.WSeq.of_mem_append

theorem mem_append_left {s₁ s₂ : WSeq α} {a : α} : a ∈ s₁ → a ∈ append s₁ s₂ :=
  Seq.mem_append_left
#align stream.wseq.mem_append_left Stream'.WSeq.mem_append_left

theorem exists_of_mem_map {f} {b : β} : ∀ {s : WSeq α}, b ∈ map f s → ∃ a, a ∈ s ∧ f a = b
  | ⟨g, al⟩, h => by
    let ⟨o, om, oe⟩ := Seq.exists_of_mem_map h
    cases' o with a
    · injection oe
    injection oe with h'
    exact ⟨a, om, h'⟩
#align stream.wseq.exists_of_mem_map Stream'.WSeq.exists_of_mem_map

@[simp]
theorem liftRel_nil (R : α → β → Prop) : LiftRel R nil nil := by
  rw [liftRel_destruct_iff]
  -- Porting note: These 2 theorems should be excluded.
  simp [-liftRel_pure_left, -liftRel_pure_right]
#align stream.wseq.lift_rel_nil Stream'.WSeq.liftRel_nil

@[simp]
theorem liftRel_cons (R : α → β → Prop) (a b s t) :
    LiftRel R (cons a s) (cons b t) ↔ R a b ∧ LiftRel R s t := by
  rw [liftRel_destruct_iff]
  -- Porting note: These 2 theorems should be excluded.
  simp [-liftRel_pure_left, -liftRel_pure_right]
#align stream.wseq.lift_rel_cons Stream'.WSeq.liftRel_cons

@[simp]
theorem liftRel_think_left (R : α → β → Prop) (s t) : LiftRel R (think s) t ↔ LiftRel R s t := by
  rw [liftRel_destruct_iff, liftRel_destruct_iff]; simp
#align stream.wseq.lift_rel_think_left Stream'.WSeq.liftRel_think_left

@[simp]
theorem liftRel_think_right (R : α → β → Prop) (s t) : LiftRel R s (think t) ↔ LiftRel R s t := by
  rw [liftRel_destruct_iff, liftRel_destruct_iff]; simp
#align stream.wseq.lift_rel_think_right Stream'.WSeq.liftRel_think_right

theorem cons_congr {s t : WSeq α} (a : α) (h : s ~ʷ t) : cons a s ~ʷ cons a t := by
  unfold Equiv; simpa using h
#align stream.wseq.cons_congr Stream'.WSeq.cons_congr

theorem think_equiv (s : WSeq α) : think s ~ʷ s := by unfold Equiv; simpa using Equiv.refl _
#align stream.wseq.think_equiv Stream'.WSeq.think_equiv

theorem think_congr {s t : WSeq α} (h : s ~ʷ t) : think s ~ʷ think t := by
  unfold Equiv; simpa using h
#align stream.wseq.think_congr Stream'.WSeq.think_congr

theorem head_congr : ∀ {s t : WSeq α}, s ~ʷ t → head s ~ head t := by
  suffices ∀ {s t : WSeq α}, s ~ʷ t → ∀ {o}, o ∈ head s → o ∈ head t from fun s t h o =>
    ⟨this h, this h.symm⟩
  intro s t h o ho
  rcases @Computation.exists_of_mem_map _ _ _ _ (destruct s) ho with ⟨ds, dsm, dse⟩
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
    exact @Computation.mem_map _ _ (@Functor.map _ _ (α × WSeq α) _ Prod.fst)
      (some (b, t')) (destruct t) dtm
#align stream.wseq.head_congr Stream'.WSeq.head_congr

theorem flatten_equiv {c : Computation (WSeq α)} {s} (h : s ∈ c) : flatten c ~ʷ s := by
  apply Computation.memRecOn h
  · simp [Equiv.refl]
  · intro s'
    apply Equiv.trans
    simp [think_equiv]
#align stream.wseq.flatten_equiv Stream'.WSeq.flatten_equiv

theorem liftRel_flatten {R : α → β → Prop} {c1 : Computation (WSeq α)} {c2 : Computation (WSeq β)}
    (h : c1.LiftRel (LiftRel R) c2) : LiftRel R (flatten c1) (flatten c2) :=
  let S s t := ∃ c1 c2, s = flatten c1 ∧ t = flatten c2 ∧ Computation.LiftRel (LiftRel R) c1 c2
  ⟨S, ⟨c1, c2, rfl, rfl, h⟩, fun {s t} h =>
    match s, t, h with
    | _, _, ⟨c1, c2, rfl, rfl, h⟩ => by
      simp only [destruct_flatten]; apply liftRel_bind _ _ h
      intro a b ab; apply Computation.LiftRel.imp _ _ _ (liftRel_destruct ab)
      intro a b; apply LiftRelO.imp_right
      intro s t h; refine ⟨Computation.pure s, Computation.pure t, ?_, ?_, ?_⟩ <;>
        -- Porting note: These 2 theorems should be excluded.
        simp [h, -liftRel_pure_left, -liftRel_pure_right]⟩
#align stream.wseq.lift_rel_flatten Stream'.WSeq.liftRel_flatten

theorem flatten_congr {c1 c2 : Computation (WSeq α)} :
    Computation.LiftRel Equiv c1 c2 → flatten c1 ~ʷ flatten c2 :=
  liftRel_flatten
#align stream.wseq.flatten_congr Stream'.WSeq.flatten_congr

theorem tail_congr {s t : WSeq α} (h : s ~ʷ t) : tail s ~ʷ tail t := by
  apply flatten_congr
  dsimp only [(· <$> ·)]; rw [← Computation.bind_pure, ← Computation.bind_pure]
  apply liftRel_bind _ _ (destruct_congr h)
  intro a b h; simp only [comp_apply, liftRel_pure]
  cases' a with a <;> cases' b with b
  · trivial
  · cases h
  · cases a
    cases h
  · cases' a with a s'
    cases' b with b t'
    exact h.right
#align stream.wseq.tail_congr Stream'.WSeq.tail_congr

theorem dropn_congr {s t : WSeq α} (h : s ~ʷ t) (n) : drop s n ~ʷ drop t n := by
  induction n <;> simp [*, tail_congr, drop]
#align stream.wseq.dropn_congr Stream'.WSeq.dropn_congr

theorem get?_congr {s t : WSeq α} (h : s ~ʷ t) (n) : get? s n ~ get? t n :=
  head_congr (dropn_congr h _)
#align stream.wseq.nth_congr Stream'.WSeq.get?_congr

theorem mem_congr {s t : WSeq α} (h : s ~ʷ t) (a) : a ∈ s ↔ a ∈ t :=
  suffices ∀ {s t : WSeq α}, s ~ʷ t → a ∈ s → a ∈ t from ⟨this h, this h.symm⟩
  fun {_ _} h as =>
  let ⟨_, hn⟩ := exists_get?_of_mem as
  get?_mem ((get?_congr h _ _).1 hn)
#align stream.wseq.mem_congr Stream'.WSeq.mem_congr

theorem productive_congr {s t : WSeq α} (h : s ~ʷ t) : Productive s ↔ Productive t := by
  simp only [productive_iff]; exact forall_congr' fun n => terminates_congr <| get?_congr h _
#align stream.wseq.productive_congr Stream'.WSeq.productive_congr

theorem Equiv.ext {s t : WSeq α} (h : ∀ n, get? s n ~ get? t n) : s ~ʷ t :=
  ⟨fun s t => ∀ n, get? s n ~ get? t n, h, fun {s t} h => by
    refine liftRel_def.2 ⟨?_, ?_⟩
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
        refine ⟨ab, fun n => ?_⟩
        refine
          (get?_congr (flatten_equiv (Computation.mem_map _ ma)) n).symm.trans
            ((?_ : get? (tail s) n ~ get? (tail t) n).trans
              (get?_congr (flatten_equiv (Computation.mem_map _ mb)) n))
        rw [get?_tail, get?_tail]
        apply h⟩
#align stream.wseq.equiv.ext Stream'.WSeq.Equiv.ext

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
#align stream.wseq.length_eq_map Stream'.WSeq.length_eq_map

@[simp]
theorem ofList_nil : ofList [] = (nil : WSeq α) :=
  rfl
#align stream.wseq.of_list_nil Stream'.WSeq.ofList_nil

@[simp]
theorem ofList_cons (a : α) (l) : ofList (a::l) = cons a (ofList l) :=
  show Seq.map some (Seq.ofList (a::l)) = Seq.cons (some a) (Seq.map some (Seq.ofList l)) by simp
#align stream.wseq.of_list_cons Stream'.WSeq.ofList_cons

@[simp]
theorem toList'_nil (l : List α) :
    Computation.corec (fun ⟨l, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a::l, s')) (l, nil) = Computation.pure l.reverse :=
  destruct_eq_pure rfl
#align stream.wseq.to_list'_nil Stream'.WSeq.toList'_nil

@[simp]
theorem toList'_cons (l : List α) (s : WSeq α) (a : α) :
    Computation.corec (fun ⟨l, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a::l, s')) (l, cons a s) =
      (Computation.corec (fun ⟨l, s⟩ =>
        match Seq.destruct s with
        | none => Sum.inl l.reverse
        | some (none, s') => Sum.inr (l, s')
        | some (some a, s') => Sum.inr (a::l, s')) (a::l, s)).think :=
  destruct_eq_think <| by simp [toList, cons]
#align stream.wseq.to_list'_cons Stream'.WSeq.toList'_cons

@[simp]
theorem toList'_think (l : List α) (s : WSeq α) :
    Computation.corec (fun ⟨l, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a::l, s')) (l, think s) =
      (Computation.corec (fun ⟨l, s⟩ =>
        match Seq.destruct s with
        | none => Sum.inl l.reverse
        | some (none, s') => Sum.inr (l, s')
        | some (some a, s') => Sum.inr (a::l, s')) (l, s)).think :=
  destruct_eq_think <| by simp [toList, think]
#align stream.wseq.to_list'_think Stream'.WSeq.toList'_think

theorem toList'_map (l : List α) (s : WSeq α) :
    Computation.corec (fun ⟨l, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a :: l, s')) (l, s) = (l.reverse ++ ·) <$> toList s := by
  refine
    Computation.eq_of_bisim
      (fun c1 c2 =>
        ∃ (l' : List α) (s : WSeq α),
          c1 = Computation.corec (fun ⟨l, s⟩ =>
            match Seq.destruct s with
            | none => Sum.inl l.reverse
            | some (none, s') => Sum.inr (l, s')
            | some (some a, s') => Sum.inr (a::l, s')) (l' ++ l, s) ∧
            c2 = Computation.map (l.reverse ++ ·) (Computation.corec (fun ⟨l, s⟩ =>
              match Seq.destruct s with
              | none => Sum.inl l.reverse
              | some (none, s') => Sum.inr (l, s')
              | some (some a, s') => Sum.inr (a::l, s')) (l', s)))
      ?_ ⟨[], s, rfl, rfl⟩
  intro s1 s2 h; rcases h with ⟨l', s, h⟩; rw [h.left, h.right]
  induction' s using WSeq.recOn with a s s <;> simp [toList, nil, cons, think, length]
  · refine ⟨a::l', s, ?_, ?_⟩ <;> simp
  · refine ⟨l', s, ?_, ?_⟩ <;> simp
#align stream.wseq.to_list'_map Stream'.WSeq.toList'_map

@[simp]
theorem toList_cons (a : α) (s) : toList (cons a s) = (List.cons a <$> toList s).think :=
  destruct_eq_think <| by
    unfold toList
    simp only [toList'_cons, Computation.destruct_think, Sum.inr.injEq]
    rw [toList'_map]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
    rfl
#align stream.wseq.to_list_cons Stream'.WSeq.toList_cons

@[simp]
theorem toList_nil : toList (nil : WSeq α) = Computation.pure [] :=
  destruct_eq_pure rfl
#align stream.wseq.to_list_nil Stream'.WSeq.toList_nil

theorem toList_ofList (l : List α) : l ∈ toList (ofList l) := by
  induction' l with a l IH <;> simp [ret_mem]; exact think_mem (Computation.mem_map _ IH)
#align stream.wseq.to_list_of_list Stream'.WSeq.toList_ofList

@[simp]
theorem destruct_ofSeq (s : Seq α) :
    destruct (ofSeq s) = Computation.pure (s.head.map fun a => (a, ofSeq s.tail)) :=
  destruct_eq_pure <| by
    simp only [destruct, Seq.destruct, Option.map_eq_map, ofSeq, Computation.corec_eq, rmap,
      Seq.head]
    rw [show Seq.get? (some <$> s) 0 = some <$> Seq.get? s 0 by apply Seq.map_get?]
    cases' Seq.get? s 0 with a
    · rfl
    dsimp only [(· <$> ·)]
    simp [destruct]
#align stream.wseq.destruct_of_seq Stream'.WSeq.destruct_ofSeq

@[simp]
theorem head_ofSeq (s : Seq α) : head (ofSeq s) = Computation.pure s.head := by
  simp only [head, Option.map_eq_map, destruct_ofSeq, Computation.map_pure, Option.map_map]
  cases Seq.head s <;> rfl
#align stream.wseq.head_of_seq Stream'.WSeq.head_ofSeq

@[simp]
theorem tail_ofSeq (s : Seq α) : tail (ofSeq s) = ofSeq s.tail := by
  simp only [tail, destruct_ofSeq, map_pure', flatten_pure]
  induction' s using Seq.recOn with x s <;> simp only [ofSeq, Seq.tail_nil, Seq.head_nil,
    Option.map_none', Seq.tail_cons, Seq.head_cons, Option.map_some']
  · rfl
#align stream.wseq.tail_of_seq Stream'.WSeq.tail_ofSeq

@[simp]
theorem dropn_ofSeq (s : Seq α) : ∀ n, drop (ofSeq s) n = ofSeq (s.drop n)
  | 0 => rfl
  | n + 1 => by
    simp only [drop, Nat.add_eq, Nat.add_zero, Seq.drop]
    rw [dropn_ofSeq s n, tail_ofSeq]
#align stream.wseq.dropn_of_seq Stream'.WSeq.dropn_ofSeq

theorem get?_ofSeq (s : Seq α) (n) : get? (ofSeq s) n = Computation.pure (Seq.get? s n) := by
  dsimp [get?]; rw [dropn_ofSeq, head_ofSeq, Seq.head_dropn]
#align stream.wseq.nth_of_seq Stream'.WSeq.get?_ofSeq

instance productive_ofSeq (s : Seq α) : Productive (ofSeq s) :=
  ⟨fun n => by rw [get?_ofSeq]; infer_instance⟩
#align stream.wseq.productive_of_seq Stream'.WSeq.productive_ofSeq

theorem toSeq_ofSeq (s : Seq α) : toSeq (ofSeq s) = s := by
  apply Subtype.eq; funext n
  dsimp [toSeq]; apply get_eq_of_mem
  rw [get?_ofSeq]; apply ret_mem
#align stream.wseq.to_seq_of_seq Stream'.WSeq.toSeq_ofSeq

/-- The monadic `return a` is a singleton list containing `a`. -/
def ret (a : α) : WSeq α :=
  ofList [a]
#align stream.wseq.ret Stream'.WSeq.ret

@[simp]
theorem map_nil (f : α → β) : map f nil = nil :=
  rfl
#align stream.wseq.map_nil Stream'.WSeq.map_nil

@[simp]
theorem map_cons (f : α → β) (a s) : map f (cons a s) = cons (f a) (map f s) :=
  Seq.map_cons _ _ _
#align stream.wseq.map_cons Stream'.WSeq.map_cons

@[simp]
theorem map_think (f : α → β) (s) : map f (think s) = think (map f s) :=
  Seq.map_cons _ _ _
#align stream.wseq.map_think Stream'.WSeq.map_think

@[simp]
theorem map_id (s : WSeq α) : map id s = s := by simp [map]
#align stream.wseq.map_id Stream'.WSeq.map_id

@[simp]
theorem map_ret (f : α → β) (a) : map f (ret a) = ret (f a) := by simp [ret]
#align stream.wseq.map_ret Stream'.WSeq.map_ret

@[simp]
theorem map_append (f : α → β) (s t) : map f (append s t) = append (map f s) (map f t) :=
  Seq.map_append _ _ _
#align stream.wseq.map_append Stream'.WSeq.map_append

theorem map_comp (f : α → β) (g : β → γ) (s : WSeq α) : map (g ∘ f) s = map g (map f s) := by
  dsimp [map]; rw [← Seq.map_comp]
  apply congr_fun; apply congr_arg
  ext ⟨⟩ <;> rfl
#align stream.wseq.map_comp Stream'.WSeq.map_comp

theorem mem_map (f : α → β) {a : α} {s : WSeq α} : a ∈ s → f a ∈ map f s :=
  Seq.mem_map (Option.map f)
#align stream.wseq.mem_map Stream'.WSeq.mem_map

-- The converse is not true without additional assumptions
theorem exists_of_mem_join {a : α} : ∀ {S : WSeq (WSeq α)}, a ∈ join S → ∃ s, s ∈ S ∧ a ∈ s := by
  suffices
    ∀ ss : WSeq α,
      a ∈ ss → ∀ s S, append s (join S) = ss → a ∈ append s (join S) → a ∈ s ∨ ∃ s, s ∈ S ∧ a ∈ s
    from fun S h => (this _ h nil S (by simp) (by simp [h])).resolve_left (not_mem_nil _)
  intro ss h; apply mem_rec_on h <;> [intro b ss o; intro ss IH] <;> intro s S
  · induction' s using WSeq.recOn with b' s s <;>
      [induction' S using WSeq.recOn with s S S; skip; skip] <;>
      intro ej m <;> simp at ej <;> have := congr_arg Seq.destruct ej <;>
      simp at this; cases this
    substs b' ss
    simp? at m ⊢ says simp only [cons_append, mem_cons_iff] at m ⊢
    cases' o with e IH
    · simp [e]
    cases' m with e m
    · simp [e]
    exact Or.imp_left Or.inr (IH _ _ rfl m)
  · induction' s using WSeq.recOn with b' s s <;>
      [induction' S using WSeq.recOn with s S S; skip; skip] <;>
      intro ej m <;> simp at ej <;> have := congr_arg Seq.destruct ej <;> simp at this <;>
      subst ss
    · apply Or.inr
      -- Porting note: `exists_eq_or_imp` should be excluded.
      simp [-exists_eq_or_imp] at m ⊢
      cases' IH s S rfl m with as ex
      · exact ⟨s, Or.inl rfl, as⟩
      · rcases ex with ⟨s', sS, as⟩
        exact ⟨s', Or.inr sS, as⟩
    · apply Or.inr
      simp? at m says simp only [join_think, nil_append, mem_think] at m
      rcases (IH nil S (by simp) (by simp [m])).resolve_left (not_mem_nil _) with ⟨s, sS, as⟩
      exact ⟨s, by simp [sS], as⟩
    · simp only [think_append, mem_think] at m IH ⊢
      apply IH _ _ rfl m
#align stream.wseq.exists_of_mem_join Stream'.WSeq.exists_of_mem_join

theorem exists_of_mem_bind {s : WSeq α} {f : α → WSeq β} {b} (h : b ∈ bind s f) :
    ∃ a ∈ s, b ∈ f a :=
  let ⟨t, tm, bt⟩ := exists_of_mem_join h
  let ⟨a, as, e⟩ := exists_of_mem_map tm
  ⟨a, as, by rwa [e]⟩
#align stream.wseq.exists_of_mem_bind Stream'.WSeq.exists_of_mem_bind

theorem destruct_map (f : α → β) (s : WSeq α) :
    destruct (map f s) = Computation.map (Option.map (Prod.map f (map f))) (destruct s) := by
  apply
    Computation.eq_of_bisim fun c1 c2 =>
      ∃ s,
        c1 = destruct (map f s) ∧
          c2 = Computation.map (Option.map (Prod.map f (map f))) (destruct s)
  · intro c1 c2 h
    cases' h with s h
    rw [h.left, h.right]
    induction' s using WSeq.recOn with a s s <;> simp
    exact ⟨s, rfl, rfl⟩
  · exact ⟨s, rfl, rfl⟩
#align stream.wseq.destruct_map Stream'.WSeq.destruct_map

theorem liftRel_map {δ} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : WSeq α} {s2 : WSeq β}
    {f1 : α → γ} {f2 : β → δ} (h1 : LiftRel R s1 s2) (h2 : ∀ {a b}, R a b → S (f1 a) (f2 b)) :
    LiftRel S (map f1 s1) (map f2 s2) :=
  ⟨fun s1 s2 => ∃ s t, s1 = map f1 s ∧ s2 = map f2 t ∧ LiftRel R s t, ⟨s1, s2, rfl, rfl, h1⟩,
    fun {s1 s2} h =>
    match s1, s2, h with
    | _, _, ⟨s, t, rfl, rfl, h⟩ => by
      simp only [exists_and_left, destruct_map]
      apply Computation.liftRel_map _ _ (liftRel_destruct h)
      intro o p h
      cases' o with a <;> cases' p with b <;> simp
      · cases b; cases h
      · cases a; cases h
      · cases' a with a s; cases' b with b t
        cases' h with r h
        exact ⟨h2 r, s, rfl, t, rfl, h⟩⟩
#align stream.wseq.lift_rel_map Stream'.WSeq.liftRel_map

theorem map_congr (f : α → β) {s t : WSeq α} (h : s ~ʷ t) : map f s ~ʷ map f t :=
  liftRel_map _ _ h fun {_ _} => congr_arg _
#align stream.wseq.map_congr Stream'.WSeq.map_congr

/-- auxiliary definition of `destruct_append` over weak sequences-/
@[simp]
def destruct_append.aux (t : WSeq α) : Option (α × WSeq α) → Computation (Option (α × WSeq α))
  | none => destruct t
  | some (a, s) => Computation.pure (some (a, append s t))
#align stream.wseq.destruct_append.aux Stream'.WSeq.destruct_append.aux

theorem destruct_append (s t : WSeq α) :
    destruct (append s t) = (destruct s).bind (destruct_append.aux t) := by
  apply
    Computation.eq_of_bisim
      (fun c1 c2 =>
        ∃ s t, c1 = destruct (append s t) ∧ c2 = (destruct s).bind (destruct_append.aux t))
      _ ⟨s, t, rfl, rfl⟩
  intro c1 c2 h; rcases h with ⟨s, t, h⟩; rw [h.left, h.right]
  induction' s using WSeq.recOn with a s s <;> simp
  · induction' t using WSeq.recOn with b t t <;> simp
    · refine ⟨nil, t, ?_, ?_⟩ <;> simp
  · exact ⟨s, t, rfl, rfl⟩
#align stream.wseq.destruct_append Stream'.WSeq.destruct_append

/-- auxiliary definition of `destruct_join` over weak sequences-/
@[simp]
def destruct_join.aux : Option (WSeq α × WSeq (WSeq α)) → Computation (Option (α × WSeq α))
  | none => Computation.pure none
  | some (s, S) => (destruct (append s (join S))).think
#align stream.wseq.destruct_join.aux Stream'.WSeq.destruct_join.aux

theorem destruct_join (S : WSeq (WSeq α)) :
    destruct (join S) = (destruct S).bind destruct_join.aux := by
  apply
    Computation.eq_of_bisim
      (fun c1 c2 =>
        c1 = c2 ∨ ∃ S, c1 = destruct (join S) ∧ c2 = (destruct S).bind destruct_join.aux)
      _ (Or.inr ⟨S, rfl, rfl⟩)
  intro c1 c2 h
  exact
    match c1, c2, h with
    | c, _, Or.inl <| rfl => by cases c.destruct <;> simp
    | _, _, Or.inr ⟨S, rfl, rfl⟩ => by
      induction' S using WSeq.recOn with s S S <;> simp
      · refine Or.inr ⟨S, rfl, rfl⟩
#align stream.wseq.destruct_join Stream'.WSeq.destruct_join

theorem liftRel_append (R : α → β → Prop) {s1 s2 : WSeq α} {t1 t2 : WSeq β} (h1 : LiftRel R s1 t1)
    (h2 : LiftRel R s2 t2) : LiftRel R (append s1 s2) (append t1 t2) :=
  ⟨fun s t => LiftRel R s t ∨ ∃ s1 t1, s = append s1 s2 ∧ t = append t1 t2 ∧ LiftRel R s1 t1,
    Or.inr ⟨s1, t1, rfl, rfl, h1⟩, fun {s t} h =>
    match s, t, h with
    | s, t, Or.inl h => by
      apply Computation.LiftRel.imp _ _ _ (liftRel_destruct h)
      intro a b; apply LiftRelO.imp_right
      intro s t; apply Or.inl
    | _, _, Or.inr ⟨s1, t1, rfl, rfl, h⟩ => by
      simp only [LiftRelO, exists_and_left, destruct_append, destruct_append.aux]
      apply Computation.liftRel_bind _ _ (liftRel_destruct h)
      intro o p h
      cases' o with a <;> cases' p with b
      · simp only [destruct_append.aux]
        apply Computation.LiftRel.imp _ _ _ (liftRel_destruct h2)
        intro a b
        apply LiftRelO.imp_right
        intro s t
        apply Or.inl
      · cases b; cases h
      · cases a; cases h
      · cases' a with a s; cases' b with b t
        cases' h with r h
        -- Porting note: These 2 theorems should be excluded.
        simpa [-liftRel_pure_left, -liftRel_pure_right] using ⟨r, Or.inr ⟨s, rfl, t, rfl, h⟩⟩⟩
#align stream.wseq.lift_rel_append Stream'.WSeq.liftRel_append

theorem liftRel_join.lem (R : α → β → Prop) {S T} {U : WSeq α → WSeq β → Prop}
    (ST : LiftRel (LiftRel R) S T)
    (HU :
      ∀ s1 s2,
        (∃ s t S T,
            s1 = append s (join S) ∧
              s2 = append t (join T) ∧ LiftRel R s t ∧ LiftRel (LiftRel R) S T) →
          U s1 s2)
    {a} (ma : a ∈ destruct (join S)) : ∃ b, b ∈ destruct (join T) ∧ LiftRelO R U a b := by
  cases' exists_results_of_mem ma with n h; clear ma; revert S T ST a
  induction' n using Nat.strongInductionOn with n IH
  intro S T ST a ra; simp only [destruct_join] at ra
  exact
    let ⟨o, m, k, rs1, rs2, en⟩ := of_results_bind ra
    let ⟨p, mT, rop⟩ := Computation.exists_of_liftRel_left (liftRel_destruct ST) rs1.mem
    match o, p, rop, rs1, rs2, mT with
    | none, none, _, _, rs2, mT => by
      simp only [destruct_join]
      exact ⟨none, mem_bind mT (ret_mem _), by rw [eq_of_pure_mem rs2.mem]; trivial⟩
    | some (s, S'), some (t, T'), ⟨st, ST'⟩, _, rs2, mT => by
      simp? [destruct_append]  at rs2  says simp only [destruct_join.aux, destruct_append] at rs2
      exact
        let ⟨k1, rs3, ek⟩ := of_results_think rs2
        let ⟨o', m1, n1, rs4, rs5, ek1⟩ := of_results_bind rs3
        let ⟨p', mt, rop'⟩ := Computation.exists_of_liftRel_left (liftRel_destruct st) rs4.mem
        match o', p', rop', rs4, rs5, mt with
        | none, none, _, _, rs5', mt => by
          have : n1 < n := by
            rw [en, ek, ek1]
            apply lt_of_lt_of_le _ (Nat.le_add_right _ _)
            apply Nat.lt_succ_of_le (Nat.le_add_right _ _)
          let ⟨ob, mb, rob⟩ := IH _ this ST' rs5'
          refine ⟨ob, ?_, rob⟩
          · simp (config := { unfoldPartialApp := true }) only [destruct_join, destruct_join.aux]
            apply mem_bind mT
            simp only [destruct_append, destruct_append.aux]
            apply think_mem
            apply mem_bind mt
            exact mb
        | some (a, s'), some (b, t'), ⟨ab, st'⟩, _, rs5, mt => by
          simp?  at rs5  says simp only [destruct_append.aux] at rs5
          refine ⟨some (b, append t' (join T')), ?_, ?_⟩
          · simp (config := { unfoldPartialApp := true }) only [destruct_join, destruct_join.aux]
            apply mem_bind mT
            simp only [destruct_append, destruct_append.aux]
            apply think_mem
            apply mem_bind mt
            apply ret_mem
          rw [eq_of_pure_mem rs5.mem]
          exact ⟨ab, HU _ _ ⟨s', t', S', T', rfl, rfl, st', ST'⟩⟩
#align stream.wseq.lift_rel_join.lem Stream'.WSeq.liftRel_join.lem

theorem liftRel_join (R : α → β → Prop) {S : WSeq (WSeq α)} {T : WSeq (WSeq β)}
    (h : LiftRel (LiftRel R) S T) : LiftRel R (join S) (join T) :=
  ⟨fun s1 s2 =>
    ∃ s t S T,
      s1 = append s (join S) ∧ s2 = append t (join T) ∧ LiftRel R s t ∧ LiftRel (LiftRel R) S T,
    ⟨nil, nil, S, T, by simp, by simp, by simp, h⟩, fun {s1 s2} ⟨s, t, S, T, h1, h2, st, ST⟩ => by
    rw [h1, h2]; rw [destruct_append, destruct_append]
    apply Computation.liftRel_bind _ _ (liftRel_destruct st)
    exact fun {o p} h =>
      match o, p, h with
      | some (a, s), some (b, t), ⟨h1, h2⟩ => by
        -- Porting note: These 2 theorems should be excluded.
        simpa [-liftRel_pure_left, -liftRel_pure_right] using ⟨h1, s, t, S, rfl, T, rfl, h2, ST⟩
      | none, none, _ => by
        -- Porting note: `LiftRelO` should be excluded.
        dsimp [destruct_append.aux, Computation.LiftRel, -LiftRelO]; constructor
        · intro
          apply liftRel_join.lem _ ST fun _ _ => id
        · intro b mb
          rw [← LiftRelO.swap]
          apply liftRel_join.lem (swap R)
          · rw [← LiftRel.swap R, ← LiftRel.swap]
            apply ST
          · rw [← LiftRel.swap R, ← LiftRel.swap (LiftRel R)]
            exact fun s1 s2 ⟨s, t, S, T, h1, h2, st, ST⟩ => ⟨t, s, T, S, h2, h1, st, ST⟩
          · exact mb⟩
#align stream.wseq.lift_rel_join Stream'.WSeq.liftRel_join

theorem join_congr {S T : WSeq (WSeq α)} (h : LiftRel Equiv S T) : join S ~ʷ join T :=
  liftRel_join _ h
#align stream.wseq.join_congr Stream'.WSeq.join_congr

theorem liftRel_bind {δ} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : WSeq α} {s2 : WSeq β}
    {f1 : α → WSeq γ} {f2 : β → WSeq δ} (h1 : LiftRel R s1 s2)
    (h2 : ∀ {a b}, R a b → LiftRel S (f1 a) (f2 b)) : LiftRel S (bind s1 f1) (bind s2 f2) :=
  liftRel_join _ (liftRel_map _ _ h1 @h2)
#align stream.wseq.lift_rel_bind Stream'.WSeq.liftRel_bind

theorem bind_congr {s1 s2 : WSeq α} {f1 f2 : α → WSeq β} (h1 : s1 ~ʷ s2) (h2 : ∀ a, f1 a ~ʷ f2 a) :
    bind s1 f1 ~ʷ bind s2 f2 :=
  liftRel_bind _ _ h1 fun {a b} h => by rw [h]; apply h2
#align stream.wseq.bind_congr Stream'.WSeq.bind_congr

@[simp]
theorem join_ret (s : WSeq α) : join (ret s) ~ʷ s := by simpa [ret] using think_equiv _
#align stream.wseq.join_ret Stream'.WSeq.join_ret

@[simp]
theorem join_map_ret (s : WSeq α) : join (map ret s) ~ʷ s := by
  refine ⟨fun s1 s2 => join (map ret s2) = s1, rfl, ?_⟩
  intro s' s h; rw [← h]
  apply liftRel_rec fun c1 c2 => ∃ s, c1 = destruct (join (map ret s)) ∧ c2 = destruct s
  · exact fun {c1 c2} h =>
      match c1, c2, h with
      | _, _, ⟨s, rfl, rfl⟩ => by
        clear h
        -- Porting note: `ret` is simplified in `simp` so `ret`s become `fun a => cons a nil` here.
        have : ∀ s, ∃ s' : WSeq α,
            (map (fun a => cons a nil) s).join.destruct =
              (map (fun a => cons a nil) s').join.destruct ∧ destruct s = s'.destruct :=
          fun s => ⟨s, rfl, rfl⟩
        induction' s using WSeq.recOn with a s s <;>
          simp (config := { unfoldPartialApp := true }) [ret, ret_mem, this, Option.exists]
  · exact ⟨s, rfl, rfl⟩
#align stream.wseq.join_map_ret Stream'.WSeq.join_map_ret

@[simp]
theorem join_append (S T : WSeq (WSeq α)) : join (append S T) ~ʷ append (join S) (join T) := by
  refine
    ⟨fun s1 s2 =>
      ∃ s S T, s1 = append s (join (append S T)) ∧ s2 = append s (append (join S) (join T)),
      ⟨nil, S, T, by simp, by simp⟩, ?_⟩
  intro s1 s2 h
  apply
    liftRel_rec
      (fun c1 c2 =>
        ∃ (s : WSeq α) (S T : _),
          c1 = destruct (append s (join (append S T))) ∧
            c2 = destruct (append s (append (join S) (join T))))
      _ _ _
      (let ⟨s, S, T, h1, h2⟩ := h
      ⟨s, S, T, congr_arg destruct h1, congr_arg destruct h2⟩)
  rintro c1 c2 ⟨s, S, T, rfl, rfl⟩
  induction' s using WSeq.recOn with a s s <;> simp
  · induction' S using WSeq.recOn with s S S <;> simp
    · induction' T using WSeq.recOn with s T T <;> simp
      · refine ⟨s, nil, T, ?_, ?_⟩ <;> simp
      · refine ⟨nil, nil, T, ?_, ?_⟩ <;> simp
    · exact ⟨s, S, T, rfl, rfl⟩
    · refine ⟨nil, S, T, ?_, ?_⟩ <;> simp
  · exact ⟨s, S, T, rfl, rfl⟩
  · exact ⟨s, S, T, rfl, rfl⟩
#align stream.wseq.join_append Stream'.WSeq.join_append

@[simp]
theorem bind_ret (f : α → β) (s) : bind s (ret ∘ f) ~ʷ map f s := by
  dsimp [bind]
  rw [map_comp]
  apply join_map_ret
#align stream.wseq.bind_ret Stream'.WSeq.bind_ret

@[simp]
theorem ret_bind (a : α) (f : α → WSeq β) : bind (ret a) f ~ʷ f a := by simp [bind]
#align stream.wseq.ret_bind Stream'.WSeq.ret_bind

@[simp]
theorem map_join (f : α → β) (S) : map f (join S) = join (map (map f) S) := by
  apply
    Seq.eq_of_bisim fun s1 s2 =>
      ∃ s S, s1 = append s (map f (join S)) ∧ s2 = append s (join (map (map f) S))
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, S, rfl, rfl⟩ => by
        induction' s using WSeq.recOn with a s s <;> simp
        · induction' S using WSeq.recOn with s S S <;> simp
          · exact ⟨map f s, S, rfl, rfl⟩
          · refine ⟨nil, S, ?_, ?_⟩ <;> simp
        · exact ⟨_, _, rfl, rfl⟩
        · exact ⟨_, _, rfl, rfl⟩
  · refine ⟨nil, S, ?_, ?_⟩ <;> simp
#align stream.wseq.map_join Stream'.WSeq.map_join

@[simp]
theorem join_join (SS : WSeq (WSeq (WSeq α))) : join (join SS) ~ʷ join (map join SS) := by
  refine
    ⟨fun s1 s2 =>
      ∃ s S SS,
        s1 = append s (join (append S (join SS))) ∧
          s2 = append s (append (join S) (join (map join SS))),
      ⟨nil, nil, SS, by simp, by simp⟩, ?_⟩
  intro s1 s2 h
  apply
    liftRel_rec
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
      clear h
      induction' s using WSeq.recOn with a s s <;> simp
      · induction' S using WSeq.recOn with s S S <;> simp
        · induction' SS using WSeq.recOn with S SS SS <;> simp
          · refine ⟨nil, S, SS, ?_, ?_⟩ <;> simp
          · refine ⟨nil, nil, SS, ?_, ?_⟩ <;> simp
        · exact ⟨s, S, SS, rfl, rfl⟩
        · refine ⟨nil, S, SS, ?_, ?_⟩ <;> simp
      · exact ⟨s, S, SS, rfl, rfl⟩
      · exact ⟨s, S, SS, rfl, rfl⟩
#align stream.wseq.join_join Stream'.WSeq.join_join

@[simp]
theorem bind_assoc (s : WSeq α) (f : α → WSeq β) (g : β → WSeq γ) :
    bind (bind s f) g ~ʷ bind s fun x : α => bind (f x) g := by
  simp only [bind, map_join]; erw [← map_comp f (map g), map_comp (map g ∘ f) join]
  apply join_join
#align stream.wseq.bind_assoc Stream'.WSeq.bind_assoc

instance monad : Monad WSeq where
  map := @map
  pure := @ret
  bind := @bind
#align stream.wseq.monad Stream'.WSeq.monad

/-
  Unfortunately, WSeq is not a lawful monad, because it does not satisfy
  the monad laws exactly, only up to sequence equivalence.
  Furthermore, even quotienting by the equivalence is not sufficient,
  because the join operation involves lists of quotient elements,
  with a lifted equivalence relation, and pure quotients cannot handle
  this type of construction.

instance lawfulMonad : LawfulMonad WSeq :=
  { id_map := @map_id,
    bind_pure_comp := @bind_ret,
    pure_bind := @ret_bind,
    bind_assoc := @bind_assoc }
-/
end WSeq

end Stream'
