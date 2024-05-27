/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Seq.Seq

#align_import data.seq.wseq from "leanprover-community/mathlib"@"a7e36e48519ab281320c4d192da6a7b348ce40ad"

/-!
# Partially defined possibly infinite lists

This file provides a `WSeq α` type representing partially defined possibly infinite lists
(referred here as weak sequences).
-/

open Function

universe u v w

/-- Weak sequences.

  While the `Seq'` structure allows for lists which may not be finite,
  a weak sequence also allows the computation of each element to
  involve an indeterminate amount of computation, including possibly
  an infinite loop. This is represented as a regular `Seq'` interspersed
  with `none` elements to indicate that computation is ongoing.

  This model is appropriate for Haskell style lazy lists, and is closed
  under most interesting computation patterns on infinite lists,
  but conversely it is difficult to extract elements from it. -/
@[ext]
structure WSeq (α : Type u) : Type u where
  /-- The representation of `WSeq` by `Seq'`. -/
  data : Seq' (Option α)
#align stream.wseq WSeq

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
def ofSeq (s : Seq' α) : WSeq α where
  data := Seq'.map some s
#align stream.wseq.of_seq WSeq.ofSeq

/-- Turn a list into a weak sequence -/
@[coe]
def ofList (l : List α) : WSeq α :=
  ofSeq ↑l
#align stream.wseq.of_list WSeq.ofList

/-- Turn a stream into a weak sequence -/
@[coe]
def ofStream (s : Stream' α) : WSeq α :=
  ofSeq ↑s
#align stream.wseq.of_stream WSeq.ofStream

instance coeSeq : Coe (Seq' α) (WSeq α) :=
  ⟨ofSeq⟩
#align stream.wseq.coe_seq WSeq.coeSeq

instance coeList : Coe (List α) (WSeq α) :=
  ⟨ofList⟩
#align stream.wseq.coe_list WSeq.coeList

instance coeStream : Coe (Stream' α) (WSeq α) :=
  ⟨ofStream⟩
#align stream.wseq.coe_stream WSeq.coeStream

/-- The empty weak sequence -/
def nil : WSeq α where
  data := Seq'.nil
#align stream.wseq.nil WSeq.nil

@[simp]
theorem data_nil : data (nil : WSeq α) = Seq'.nil :=
  rfl

instance inhabited : Inhabited (WSeq α) :=
  ⟨nil⟩
#align stream.wseq.inhabited WSeq.inhabited

/-- Prepend an element to a weak sequence -/
def cons (a : α) (s : WSeq α) : WSeq α where
  data := some a ::ₑ data s
#align stream.wseq.cons WSeq.cons

/-- Prepend an element to a we**a**k sequence -/
infixr:67 " ::ₐ " => cons

@[simp]
theorem data_cons (a : α) (s : WSeq α) : data (a ::ₐ s) = some a ::ₑ data s :=
  rfl

/-- Compute for one tick, without producing any elements -/
def think (s : WSeq α) : WSeq α where
  data := none ::ₑ data s
#align stream.wseq.think WSeq.think

@[simp]
theorem data_think (s : WSeq α) : data (think s) = none ::ₑ data s :=
  rfl

/-- Destruct a weak sequence, to (eventually possibly) produce either
  `none` for `nil` or `some (a, s)` if an element is produced. -/
def dest (s : WSeq α) : Computation (Option (α × WSeq α)) :=
  Computation.corec (fun s =>
    match Seq'.dest s with
    | none => Sum.inl none
    | some (none, s') => Sum.inr s'
    | some (some a, s') => Sum.inl (some (a, ⟨s'⟩))) (data s)
#align stream.wseq.destruct WSeq.dest

/-- Recursion principle for weak sequences, compare with `List.recOn`. -/
@[elab_as_elim]
def recOn' {C : WSeq α → Sort v} (s : WSeq α) (nil : C nil) (cons : ∀ x s, C (cons x s))
    (think : ∀ s, C (think s)) : C s :=
  Seq'.recOn' (C := fun s => C ⟨s⟩) (data s) nil
    (fun o s => Option.recOn (motive := fun o => (s : WSeq α) → C ⟨o ::ₑ data s⟩) o think cons ⟨s⟩)
#align stream.wseq.rec_on WSeq.recOn'

/-- membership for weak sequences-/
protected def Mem (a : α) (s : WSeq α) :=
  some a ∈ data s
#align stream.wseq.mem WSeq.Mem

instance membership : Membership α (WSeq α) :=
  ⟨WSeq.Mem⟩
#align stream.wseq.has_mem WSeq.membership

theorem mem_def (a : α) (s : WSeq α) : a ∈ s ↔ some a ∈ data s :=
  Iff.rfl

@[simp]
theorem not_mem_nil (a : α) : a ∉ (nil : WSeq α) :=
  Seq'.not_mem_nil (some a)
#align stream.wseq.not_mem_nil WSeq.not_mem_nil

/-- Get the head of a weak sequence. This involves a possibly
  infinite computation. -/
def head (s : WSeq α) : Computation (Option α) :=
  Computation.map (Option.map Prod.fst) (dest s)
#align stream.wseq.head WSeq.head

/-- Encode a computation yielding a weak sequence into additional
  `think` constructors in a weak sequence -/
def flatten (c : Computation (WSeq α)) : WSeq α where
  data :=
    Seq'.corec (fun c =>
      match Computation.dest c with
      | Sum.inl s => Option.map (Prod.map id Computation.pure) (Seq'.dest s)
      | Sum.inr c' => some (none, c')) (Computation.map data c)
#align stream.wseq.flatten WSeq.flatten

/-- Get the tail of a weak sequence. This doesn't need a `Computation`
  wrapper, unlike `head`, because `flatten` allows us to hide this
  in the construction of the weak sequence itself. -/
def tail (s : WSeq α) : WSeq α :=
  flatten (Computation.map (fun o => Option.elim o nil Prod.snd) (dest s))
#align stream.wseq.tail WSeq.tail

/-- drop the first `n` elements from `s`. -/
def drop (s : WSeq α) : ℕ → WSeq α
  | 0 => s
  | n + 1 => tail (drop s n)
#align stream.wseq.drop WSeq.drop

/-- Get the nth element of `s`. -/
def get? (s : WSeq α) (n : ℕ) : Computation (Option α) :=
  head (drop s n)
#align stream.wseq.nth WSeq.get?

/-- Convert `s` to a list (if it is finite and completes in finite time). -/
def toList (s : WSeq α) : Computation (List α) :=
  Computation.corec
    (fun (l, s) =>
      match Seq'.dest s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a :: l, s'))
    ([], data s)
#align stream.wseq.to_list WSeq.toList

/-- Get the length of `s` (if it is finite and completes in finite time). -/
def length (s : WSeq α) : Computation ℕ :=
  Computation.corec
    (fun (n, s) =>
      match Seq'.dest s with
      | none => Sum.inl n
      | some (none, s') => Sum.inr (n, s')
      | some (some _, s') => Sum.inr (n + 1, s'))
    (0, data s)
#align stream.wseq.length WSeq.length

/-- A weak sequence is finite if `toList s` terminates. Equivalently,
  it is a finite number of `think` and `cons` applied to `nil`. -/
class IsFinite (s : WSeq α) : Prop where
  out : (toList s).Terminates
#align stream.wseq.is_finite WSeq.IsFinite

instance toList_terminates (s : WSeq α) [h : IsFinite s] : (toList s).Terminates :=
  h.out
#align stream.wseq.to_list_terminates WSeq.toList_terminates

/-- Get the list corresponding to a finite weak sequence. -/
def get (s : WSeq α) [IsFinite s] : List α :=
  (toList s).get
#align stream.wseq.get WSeq.get

/-- A weak sequence is *productive* if it never stalls forever - there are
 always a finite number of `think`s between `cons` constructors.
 The sequence itself is allowed to be infinite though. -/
class Productive (s : WSeq α) : Prop where
  get?_terminates : ∀ n, (get? s n).Terminates
#align stream.wseq.productive WSeq.Productive
#align stream.wseq.productive.nth_terminates WSeq.Productive.get?_terminates

theorem productive_iff (s : WSeq α) : Productive s ↔ ∀ n, (get? s n).Terminates :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align stream.wseq.productive_iff WSeq.productive_iff

instance get?_terminates (s : WSeq α) [h : Productive s] : ∀ n, (get? s n).Terminates :=
  h.get?_terminates
#align stream.wseq.nth_terminates WSeq.get?_terminates

instance head_terminates (s : WSeq α) [Productive s] : (head s).Terminates :=
  s.get?_terminates 0
#align stream.wseq.head_terminates WSeq.head_terminates

/-- Replace the `n`th element of `s` with `a`. -/
def updateNth (s : WSeq α) (n : ℕ) (a : α) : WSeq α where
  data :=
    Seq'.corec
      (fun (n, s) =>
        match Seq'.dest s, n with
        | none, _ => none
        | some (none, s'), n => some (none, n, s')
        | some (some a', s'), 0 => some (some a', 0, s')
        | some (some _, s'), 1 => some (some a, 0, s')
        | some (some a', s'), n + 2 => some (some a', n + 1, s'))
      (n + 1, data s)
#align stream.wseq.update_nth WSeq.updateNth

/-- Remove the `n`th element of `s`. -/
def removeNth (s : WSeq α) (n : ℕ) : WSeq α where
  data :=
    Seq'.corec
      (fun (n, s) =>
        match Seq'.dest s, n with
        | none, _ => none
        | some (none, s'), n => some (none, n, s')
        | some (some a', s'), 0 => some (some a', 0, s')
        | some (some _, s'), 1 => some (none, 0, s')
        | some (some a', s'), n + 2 => some (some a', n + 1, s'))
      (n + 1, data s)
#align stream.wseq.remove_nth WSeq.removeNth

/-- Map the elements of `s` over `f`, removing any values that yield `none`. -/
def filterMap (f : α → Option β) (s : WSeq α) : WSeq β where
  data :=
    Seq'.corec (fun s =>
      match Seq'.dest s with
      | none => none
      | some (none, s') => some (none, s')
      | some (some a, s') => some (f a, s')) (data s)
#align stream.wseq.filter_map WSeq.filterMap

/-- Select the elements of `s` that satisfy `p`. -/
def filter (p : α → Prop) [DecidablePred p] : WSeq α → WSeq α :=
  filterMap fun a => if p a then some a else none
#align stream.wseq.filter WSeq.filter

-- example of infinite list manipulations
/-- Get the first element of `s` satisfying `p`. -/
def find (p : α → Prop) [DecidablePred p] (s : WSeq α) : Computation (Option α) :=
  head <| filter p s
#align stream.wseq.find WSeq.find

/-- Zip a function over two weak sequences -/
def zipWith (f : α → β → γ) (s1 : WSeq α) (s2 : WSeq β) : WSeq γ where
  data :=
    Seq'.corec
      (fun ⟨s1, s2⟩ =>
        match Seq'.dest s1, Seq'.dest s2 with
        | some (none, s1'), some (none, s2') => some (none, s1', s2')
        | some (some _, _), some (none, s2') => some (none, s1, s2')
        | some (none, s1'), some (some _, _) => some (none, s1', s2)
        | some (some a1, s1'), some (some a2, s2') => some (some (f a1 a2), s1', s2')
        | _, _ => none)
      (data s1, data s2)
#align stream.wseq.zip_with WSeq.zipWith

/-- Zip two weak sequences into a single sequence of pairs -/
def zip : WSeq α → WSeq β → WSeq (α × β) :=
  zipWith Prod.mk
#align stream.wseq.zip WSeq.zip

/-- Get the list of indexes of elements of `s` satisfying `p` -/
def findIndexes (p : α → Prop) [DecidablePred p] (s : WSeq α) : WSeq ℕ :=
  (zip s (Stream'.nats : WSeq ℕ)).filterMap fun (a, n) => if p a then some n else none
#align stream.wseq.find_indexes WSeq.findIndexes

/-- Get the index of the first element of `s` satisfying `p` -/
def findIndex (p : α → Prop) [DecidablePred p] (s : WSeq α) : Computation ℕ :=
  Computation.map (fun o => Option.getD o 0) (head (findIndexes p s))
#align stream.wseq.find_index WSeq.findIndex

/-- Get the index of the first occurrence of `a` in `s` -/
def indexOf [DecidableEq α] (a : α) : WSeq α → Computation ℕ :=
  findIndex (Eq a)
#align stream.wseq.index_of WSeq.indexOf

/-- Get the indexes of occurrences of `a` in `s` -/
def indexesOf [DecidableEq α] (a : α) : WSeq α → WSeq ℕ :=
  findIndexes (Eq a)
#align stream.wseq.indexes_of WSeq.indexesOf

/-- `union s1 s2` is a weak sequence which interleaves `s1` and `s2` in
  some order (nondeterministically). -/
def union (s1 s2 : WSeq α) : WSeq α where
  data :=
    Seq'.corec
      (fun (s1, s2) =>
        match Seq'.dest s1, Seq'.dest s2 with
        | none, none => none
        | some (a1, s1'), none => some (a1, s1', Seq'.nil)
        | none, some (a2, s2') => some (a2, Seq'.nil, s2')
        | some (none, s1'), some (none, s2') => some (none, s1', s2')
        | some (some a1, s1'), some (none, s2') => some (some a1, s1', s2')
        | some (none, s1'), some (some a2, s2') => some (some a2, s1', s2')
        | some (some a1, s1'), some (some a2, s2') => some (some a1, a2 ::ₑ s1', s2'))
      (data s1, data s2)
#align stream.wseq.union WSeq.union

/-- Returns `true` if `s` is `nil` and `false` if `s` has an element -/
def isEmpty (s : WSeq α) : Computation Bool :=
  Computation.map Option.isNone <| head s
#align stream.wseq.is_empty WSeq.isEmpty

/-- Calculate one step of computation -/
def compute (s : WSeq α) : WSeq α :=
  match Seq'.dest (data s) with
  | some (none, s') => ⟨s'⟩
  | _ => s
#align stream.wseq.compute WSeq.compute

/-- Get the first `n` elements of a weak sequence -/
def take (s : WSeq α) (n : ℕ) : WSeq α where
  data :=
    Seq'.corec
      (fun (n, s) =>
        match n, Seq'.dest s with
        | 0, _ => none
        | _ + 1, none => none
        | m + 1, some (none, s') => some (none, m + 1, s')
        | m + 1, some (some a, s') => some (some a, m, s'))
      (n, data s)
#align stream.wseq.take WSeq.take

/-- Split the sequence at position `n` into a finite initial segment
  and the weak sequence tail -/
def splitAt (s : WSeq α) (n : ℕ) : Computation (List α × WSeq α) :=
  Computation.corec
    (fun (n, l, s) =>
      match n, Seq'.dest s with
      | 0, _ => Sum.inl (l.reverse, ⟨s⟩)
      | _ + 1, none => Sum.inl (l.reverse, ⟨s⟩)
      | _ + 1, some (none, s') => Sum.inr (n, l, s')
      | m + 1, some (some a, s') => Sum.inr (m, a :: l, s'))
    (n, [], data s)
#align stream.wseq.split_at WSeq.splitAt

/-- Returns `true` if any element of `s` satisfies `p` -/
def any (s : WSeq α) (p : α → Bool) : Computation Bool :=
  Computation.corec
    (fun s =>
      match Seq'.dest s with
      | none => Sum.inl false
      | some (none, s') => Sum.inr s'
      | some (some a, s') => if p a then Sum.inl true else Sum.inr s')
    (data s)
#align stream.wseq.any WSeq.any

/-- Returns `true` if every element of `s` satisfies `p` -/
def all (s : WSeq α) (p : α → Bool) : Computation Bool :=
  Computation.corec
    (fun s =>
      match Seq'.dest s with
      | none => Sum.inl true
      | some (none, s') => Sum.inr s'
      | some (some a, s') => if p a then Sum.inr s' else Sum.inl false)
    (data s)
#align stream.wseq.all WSeq.all

/-- Apply a function to the elements of the sequence to produce a sequence
  of partial results. (There is no `scanr` because this would require
  working from the end of the sequence, which may not exist.) -/
def scanl (f : α → β → α) (a : α) (s : WSeq β) : WSeq α :=
  a ::ₐ
    ⟨Seq'.corec
      (fun (a, s) =>
        match Seq'.dest s with
        | none => none
        | some (none, s') => some (none, a, s')
        | some (some b, s') =>
          let a' := f a b
          some (some a', a', s'))
      (a, data s)⟩
#align stream.wseq.scanl WSeq.scanl

/-- Get the weak sequence of initial segments of the input sequence -/
def inits (s : WSeq α) : WSeq (List α) :=
  [] ::ₐ
    ⟨Seq'.corec
      (fun (l, s) =>
        match Seq'.dest s with
        | none => none
        | some (none, s') => some (none, l, s')
        | some (some a, s') =>
          let l' := l.push a
          some (some l'.toList, l', s'))
      (Batteries.DList.empty, data s)⟩
#align stream.wseq.inits WSeq.inits

/-- Like take, but does not wait for a result. Calculates `n` steps of
  computation and returns the sequence computed so far -/
def collect (s : WSeq α) (n : ℕ) : List α :=
  (Seq'.take n (data s)).filterMap id
#align stream.wseq.collect WSeq.collect

/-- Append two weak sequences. As with `Seq'.append`, this may not use
  the second sequence if the first one takes forever to compute -/
def append (s₁ s₂ : WSeq α) : WSeq α where
  data := data s₁ ++ data s₂
#align stream.wseq.append WSeq.append

instance : Append (WSeq α) where
  append := append

theorem append_def (s₁ s₂ : WSeq α) : s₁ ++ s₂ = ⟨data s₁ ++ data s₂⟩ :=
  rfl

/-- Map a function over a weak sequence -/
def map (f : α → β) (s : WSeq α) : WSeq β where
  data := Seq'.map (Option.map f) (data s)
#align stream.wseq.map WSeq.map

/-- Flatten a sequence of weak sequences. (Note that this allows
  empty sequences, unlike `Seq'.join`.) -/
def join (S : WSeq (WSeq α)) : WSeq α where
  data :=
    Seq'.join
      (Seq'.map (fun o =>
          match o with
          | none => Seq1.pure none
          | some s => ⟨none, s⟩)
      (Seq'.map (Option.map data) (data S)))
#align stream.wseq.join WSeq.join

/-- Monadic bind operator for weak sequences -/
def bind (s : WSeq α) (f : α → WSeq β) : WSeq β :=
  join (map f s)
#align stream.wseq.bind WSeq.bind

/-- lift a relation to a relation over weak sequences -/
@[simp]
def LiftRelO (R : α → β → Prop) (C : WSeq α → WSeq β → Prop) :
    Option (α × WSeq α) → Option (β × WSeq β) → Prop
  | none, none => True
  | some (a, s), some (b, t) => R a b ∧ C s t
  | _, _ => False
#align stream.wseq.lift_rel_o WSeq.LiftRelO

theorem LiftRelO.imp {R S : α → β → Prop} {C D : WSeq α → WSeq β → Prop} (H1 : ∀ a b, R a b → S a b)
    (H2 : ∀ s t, C s t → D s t) : ∀ {o p}, LiftRelO R C o p → LiftRelO S D o p
  | none, none, _ => trivial
  | some (_, _), some (_, _), h => And.imp (H1 _ _) (H2 _ _) h
  | none, some _, h => False.elim h
  | some (_, _), none, h => False.elim h
#align stream.wseq.lift_rel_o.imp WSeq.LiftRelO.imp

theorem LiftRelO.imp_right (R : α → β → Prop) {C D : WSeq α → WSeq β → Prop}
    (H : ∀ s t, C s t → D s t) {o p} : LiftRelO R C o p → LiftRelO R D o p :=
  LiftRelO.imp (fun _ _ => id) H
#align stream.wseq.lift_rel_o.imp_right WSeq.LiftRelO.imp_right

/-- Definition of bisimilarity for weak sequences-/
@[simp]
def BisimO (R : WSeq α → WSeq α → Prop) : Option (α × WSeq α) → Option (α × WSeq α) → Prop :=
  LiftRelO Eq R
#align stream.wseq.bisim_o WSeq.BisimO

theorem BisimO.imp {R S : WSeq α → WSeq α → Prop} (H : ∀ s t, R s t → S s t) {o p} :
    BisimO R o p → BisimO S o p :=
  LiftRelO.imp_right _ H
#align stream.wseq.bisim_o.imp WSeq.BisimO.imp

/-- Two weak sequences are `LiftRel R` related if they are either both empty,
  or they are both nonempty and the heads are `R` related and the tails are
  `LiftRel R` related. (This is a coinductive definition.) -/
def LiftRel (R : α → β → Prop) (s : WSeq α) (t : WSeq β) : Prop :=
  ∃ C : WSeq α → WSeq β → Prop,
    C s t ∧ ∀ {s t}, C s t → Computation.LiftRel (LiftRelO R C) (dest s) (dest t)
#align stream.wseq.lift_rel WSeq.LiftRel

/-- If two sequences are equivalent, then they have the same values and
  the same computational behavior (i.e. if one loops forever then so does
  the other), although they may differ in the number of `think`s needed to
  arrive at the answer. -/
def Equiv : WSeq α → WSeq α → Prop :=
  LiftRel Eq
#align stream.wseq.equiv WSeq.Equiv

theorem liftRel_dest {R : α → β → Prop} {s : WSeq α} {t : WSeq β} :
    LiftRel R s t → Computation.LiftRel (LiftRelO R (LiftRel R)) (dest s) (dest t)
  | ⟨R, h1, h2⟩ => by
    refine Computation.LiftRel.imp ?_ _ _ (h2 h1)
    apply LiftRelO.imp_right
    exact fun s' t' h' => ⟨R, h', @h2⟩
#align stream.wseq.lift_rel_destruct WSeq.liftRel_dest

theorem liftRel_dest_iff {R : α → β → Prop} {s : WSeq α} {t : WSeq β} :
    LiftRel R s t ↔ Computation.LiftRel (LiftRelO R (LiftRel R)) (dest s) (dest t) :=
  ⟨liftRel_dest, fun h =>
    ⟨fun s t =>
      LiftRel R s t ∨ Computation.LiftRel (LiftRelO R (LiftRel R)) (dest s) (dest t),
      Or.inr h, fun {s t} h => by
      have h : Computation.LiftRel (LiftRelO R (LiftRel R)) (dest s) (dest t) := by
        cases' h with h h
        · exact liftRel_dest h
        · assumption
      apply Computation.LiftRel.imp _ _ _ h
      intro a b
      apply LiftRelO.imp_right
      intro s t
      apply Or.inl⟩⟩
#align stream.wseq.lift_rel_destruct_iff WSeq.liftRel_dest_iff

theorem LiftRel.refl (R : α → α → Prop) (H : Reflexive R) : Reflexive (LiftRel R) := fun s => by
  refine ⟨Eq, rfl, fun {s t} (h : s = t) => ?_⟩
  rw [← h]
  apply Computation.LiftRel.refl
  intro a
  cases' a with a
  · simp
  · cases a
    simp only [LiftRelO, and_true]
    apply H
#align stream.wseq.lift_rel.refl WSeq.LiftRel.refl

theorem LiftRelO.swap (R : α → β → Prop) (C) :
    swap (LiftRelO R C) = LiftRelO (swap R) (swap C) := by
  funext x y
  rcases x with ⟨⟩ | ⟨hx, jx⟩ <;> rcases y with ⟨⟩ | ⟨hy, jy⟩ <;> rfl
#align stream.wseq.lift_rel_o.swap WSeq.LiftRelO.swap

theorem LiftRel.swap_lem {R : α → β → Prop} {s1 s2} (h : LiftRel R s1 s2) :
    LiftRel (swap R) s2 s1 := by
  refine ⟨swap (LiftRel R), h, fun {s t} (h : LiftRel R t s) => ?_⟩
  rw [← LiftRelO.swap, Computation.LiftRel.swap]
  apply liftRel_dest h
#align stream.wseq.lift_rel.swap_lem WSeq.LiftRel.swap_lem

theorem LiftRel.swap (R : α → β → Prop) : swap (LiftRel R) = LiftRel (swap R) :=
  funext fun _ => funext fun _ => propext ⟨LiftRel.swap_lem, LiftRel.swap_lem⟩
#align stream.wseq.lift_rel.swap WSeq.LiftRel.swap

theorem LiftRel.symm (R : α → α → Prop) (H : Symmetric R) : Symmetric (LiftRel R) :=
  fun s1 s2 (h : Function.swap (LiftRel R) s2 s1) => by rwa [LiftRel.swap, H.swap_eq] at h
#align stream.wseq.lift_rel.symm WSeq.LiftRel.symm

theorem LiftRel.trans (R : α → α → Prop) (H : Transitive R) : Transitive (LiftRel R) :=
  fun s t u h1 h2 => by
  refine ⟨fun s u => ∃ t, LiftRel R s t ∧ LiftRel R t u, ⟨t, h1, h2⟩, fun {s u} h => ?_⟩
  rcases h with ⟨t, h1, h2⟩
  have h1 := liftRel_dest h1
  have h2 := liftRel_dest h2
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
#align stream.wseq.lift_rel.trans WSeq.LiftRel.trans

theorem LiftRel.equiv (R : α → α → Prop) : Equivalence R → Equivalence (LiftRel R)
  | ⟨refl, symm, trans⟩ => ⟨LiftRel.refl R refl, @(LiftRel.symm R @symm), @(LiftRel.trans R @trans)⟩
#align stream.wseq.lift_rel.equiv WSeq.LiftRel.equiv

theorem Equiv.refl : ∀ s : WSeq α, Equiv s s :=
  LiftRel.refl Eq Eq.refl
#align stream.wseq.equiv.refl WSeq.Equiv.refl

theorem Equiv.symm : ∀ {s t : WSeq α}, Equiv s t → Equiv t s :=
  @(LiftRel.symm Eq (@Eq.symm _))
#align stream.wseq.equiv.symm WSeq.Equiv.symm

theorem Equiv.trans : ∀ {s t u : WSeq α}, Equiv s t → Equiv t u → Equiv s u :=
  @(LiftRel.trans Eq (@Eq.trans _))
#align stream.wseq.equiv.trans WSeq.Equiv.trans

theorem Equiv.equivalence : Equivalence (@Equiv α) :=
  LiftRel.equiv Eq eq_equivalence
#align stream.wseq.equiv.equivalence WSeq.Equiv.equivalence

instance : Setoid (WSeq α) where
  r     := Equiv
  iseqv := Equiv.equivalence

theorem equiv_def {s t : WSeq α} : s ≈ t ↔ LiftRel Eq s t :=
  Iff.rfl

theorem dest_congr {s t : WSeq α} :
    s ≈ t → Computation.LiftRel (BisimO (· ≈ ·)) (dest s) (dest t) :=
  liftRel_dest
#align stream.wseq.destruct_congr WSeq.dest_congr

theorem dest_congr_iff {s t : WSeq α} :
    s ≈ t ↔ Computation.LiftRel (BisimO (· ≈ ·)) (dest s) (dest t) :=
  liftRel_dest_iff
#align stream.wseq.destruct_congr_iff WSeq.dest_congr_iff

open Computation

@[simp]
theorem dest_nil : dest (nil : WSeq α) = Computation.pure none :=
  Computation.dest_eq_pure rfl
#align stream.wseq.destruct_nil WSeq.dest_nil

@[simp]
theorem dest_cons (a : α) (s) : dest (a ::ₐ s) = Computation.pure (some (a, s)) :=
  Computation.dest_eq_pure <| by simp [dest, cons]
#align stream.wseq.destruct_cons WSeq.dest_cons

@[simp]
theorem dest_think (s : WSeq α) : dest (think s) = (dest s).think :=
  Computation.dest_eq_think <| by simp [dest, think]
#align stream.wseq.destruct_think WSeq.dest_think

#noalign stream.wseq.seq_destruct_nil

#noalign stream.wseq.seq_destruct_cons

#noalign stream.wseq.seq_destruct_think

@[simp]
theorem head_nil : head (nil : WSeq α) = Computation.pure none := by simp [head]
#align stream.wseq.head_nil WSeq.head_nil

@[simp]
theorem head_cons (a : α) (s) : head (a ::ₐ s) = Computation.pure (some a) := by simp [head]
#align stream.wseq.head_cons WSeq.head_cons

@[simp]
theorem head_think (s : WSeq α) : head (think s) = (head s).think := by simp [head]
#align stream.wseq.head_think WSeq.head_think

@[simp]
theorem flatten_pure (s : WSeq α) : flatten (Computation.pure s) = s := by
  ext1
  refine Seq'.eq_of_bisim (fun s1 s2 => data (flatten (Computation.pure ⟨s2⟩)) = s1) ?_ rfl
  intro s' s h; rw [← h]
  simp only [Seq'.BisimO, flatten, Computation.map_pure, Seq'.dest_corec,
    dest_pure, Option.map_map]
  cases Seq'.dest s with
  | none => simp
  | some val =>
    cases' val with o s'
    simp
#align stream.wseq.flatten_ret WSeq.flatten_pure

@[simp]
theorem flatten_think (c : Computation (WSeq α)) : flatten c.think = think (flatten c) :=
  WSeq.ext _ _ <| Seq'.dest_eq_cons <| by simp [flatten, think]
#align stream.wseq.flatten_think WSeq.flatten_think

@[simp]
theorem dest_flatten (c : Computation (WSeq α)) :
    dest (flatten c) = Computation.bind c dest := by
  refine
    Computation.eq_of_bisim
      (fun c1 c2 => c1 = c2 ∨ ∃ c, c1 = dest (flatten c) ∧ c2 = Computation.bind c dest) ?_
      (Or.inr ⟨c, rfl, rfl⟩)
  intro c1 c2 h
  exact
    match c1, c2, h with
    | c, _, Or.inl rfl => by cases c.dest <;> simp
    | _, _, Or.inr ⟨c, rfl, rfl⟩ => by
      induction' c using Computation.recOn' with a c' <;> simp
      · cases (dest a).dest <;> simp
      · exact Or.inr ⟨c', rfl, rfl⟩
#align stream.wseq.destruct_flatten WSeq.dest_flatten

theorem head_terminates_iff {s : WSeq α} : Terminates (head s) ↔ Terminates (dest s) :=
  terminates_map_iff _ (dest s)
#align stream.wseq.head_terminates_iff WSeq.head_terminates_iff

@[simp]
theorem tail_nil : tail (nil : WSeq α) = nil := by simp [tail]
#align stream.wseq.tail_nil WSeq.tail_nil

@[simp]
theorem tail_cons (a : α) (s) : tail (a ::ₐ s) = s := by simp [tail]
#align stream.wseq.tail_cons WSeq.tail_cons

@[simp]
theorem tail_think (s : WSeq α) : tail (think s) = (tail s).think := by simp [tail]
#align stream.wseq.tail_think WSeq.tail_think

@[simp]
theorem drop_nil (n) : drop (nil : WSeq α) n = nil := by induction n <;> simp [*, drop]
#align stream.wseq.dropn_nil WSeq.drop_nil

@[simp]
theorem drop_cons (a : α) (s) (n) : drop (a ::ₐ s) (n + 1) = drop s n := by
  induction n with
  | zero => simp [drop]
  | succ n n_ih =>
    -- Porting note (#10745): was `simp [*, drop]`.
    simp [drop, ←  n_ih]
#align stream.wseq.dropn_cons WSeq.drop_cons

@[simp]
theorem drop_think (s : WSeq α) (n) : drop (think s) n = (drop s n).think := by
  induction n <;> simp [*, drop]
#align stream.wseq.dropn_think WSeq.drop_think

theorem drop_add (s : WSeq α) (m) : ∀ n, drop s (m + n) = drop (drop s m) n
  | 0 => rfl
  | n + 1 => congr_arg tail (drop_add s m n)
#align stream.wseq.dropn_add WSeq.drop_add

theorem drop_tail (s : WSeq α) (n) : drop (tail s) n = drop s (n + 1) := by
  rw [Nat.add_comm]
  symm
  apply drop_add
#align stream.wseq.dropn_tail WSeq.drop_tail

theorem get?_add (s : WSeq α) (m n) : get? s (m + n) = get? (drop s m) n :=
  congr_arg head (drop_add _ _ _)
#align stream.wseq.nth_add WSeq.get?_add

theorem get?_tail (s : WSeq α) (n) : get? (tail s) n = get? s (n + 1) :=
  congr_arg head (drop_tail _ _)
#align stream.wseq.nth_tail WSeq.get?_tail

@[simp]
theorem join_nil : join nil = (nil : WSeq α) :=
  WSeq.ext _ _ <| Seq'.join_nil
#align stream.wseq.join_nil WSeq.join_nil

@[simp]
theorem join_think (S : WSeq (WSeq α)) : join (think S) = think (join S) := by
  simp [think, join]
  simp [join, Seq1.pure]
#align stream.wseq.join_think WSeq.join_think

@[simp]
theorem join_cons (s : WSeq α) (S) : join (s ::ₐ S) = think (s ++ join S) := by
  simp [think, join]
  simp [join, cons, append_def]
#align stream.wseq.join_cons WSeq.join_cons

@[simp]
theorem nil_append (s : WSeq α) : nil ++ s = s :=
  WSeq.ext _ _ <| Seq'.nil_append _
#align stream.wseq.nil_append WSeq.nil_append

@[simp]
theorem cons_append (a : α) (s t) : a ::ₐ s ++ t = a ::ₐ (s ++ t) :=
  WSeq.ext _ _ <| Seq'.cons_append _ _ _
#align stream.wseq.cons_append WSeq.cons_append

@[simp]
theorem think_append (s t : WSeq α) : think s ++ t = think (s ++ t) :=
  WSeq.ext _ _ <| Seq'.cons_append _ _ _
#align stream.wseq.think_append WSeq.think_append

@[simp]
theorem append_nil (s : WSeq α) : s ++ nil = s :=
  WSeq.ext _ _ <| Seq'.append_nil _
#align stream.wseq.append_nil WSeq.append_nil

@[simp]
theorem append_assoc (s t u : WSeq α) : s ++ t ++ u = s ++ (t ++ u) :=
  WSeq.ext _ _ <| Seq'.append_assoc _ _ _
#align stream.wseq.append_assoc WSeq.append_assoc

/-- auxiliary definition of tail over weak sequences-/
@[simp]
def tail.aux : Option (α × WSeq α) → Computation (Option (α × WSeq α))
  | none => Computation.pure none
  | some (_, s) => dest s
#align stream.wseq.tail.aux WSeq.tail.aux

theorem dest_tail (s : WSeq α) :
    dest (tail s) = Computation.bind (dest s) tail.aux := by
  simp [tail]; rw [← Computation.bind_pure, Computation.bind_assoc]
  apply congr_arg; ext1 (_ | ⟨a, s⟩) <;> apply (Computation.pure_bind _ _).trans _ <;> simp
#align stream.wseq.destruct_tail WSeq.dest_tail

/-- auxiliary definition of drop over weak sequences-/
@[simp]
def drop.aux : ℕ → Option (α × WSeq α) → Computation (Option (α × WSeq α))
  | 0 => Computation.pure
  | n + 1 => fun a => Computation.bind (tail.aux a) (drop.aux n)
#align stream.wseq.drop.aux WSeq.drop.aux

theorem drop.aux_none : ∀ n, @drop.aux α n none = Computation.pure none
  | 0 => rfl
  | n + 1 => by simp [drop.aux, drop.aux_none n]
#align stream.wseq.drop.aux_none WSeq.drop.aux_none

theorem dest_drop :
    ∀ (s : WSeq α) (n), dest (drop s n) = Computation.bind (dest s) (drop.aux n)
  | s, 0 => (bind_pure' _).symm
  | s, n + 1 => by
    rw [← drop_tail, dest_drop _ n, dest_tail, Computation.bind_assoc, drop.aux]
#align stream.wseq.destruct_dropn WSeq.dest_drop

theorem head_terminates_of_head_tail_terminates (s : WSeq α) [T : Terminates (head (tail s))] :
    Terminates (head s) :=
  head_terminates_iff.2 <| by
    rcases head_terminates_iff.1 T with ⟨⟨a, h⟩⟩
    simp? [tail] at h says simp only [tail, dest_flatten] at h
    rcases exists_of_mem_bind h with ⟨s', h1, _⟩
    exact
      let ⟨t, h3, _⟩ := Computation.exists_of_mem_map h1
      Computation.terminates_of_mem h3
#align stream.wseq.head_terminates_of_head_tail_terminates WSeq.head_terminates_of_head_tail_terminates

theorem dest_some_of_dest_tail_some {s : WSeq α} {a} (h : some a ∈ dest (tail s)) :
    ∃ a', some a' ∈ dest s := by
  unfold tail at h; simp only [dest_flatten] at h
  rcases exists_of_mem_bind h with ⟨t, tm, td⟩; clear h
  rcases Computation.exists_of_mem_map tm with ⟨t', ht', ht2⟩; clear tm
  cases' t' with t' <;> rw [← ht2] at td <;> simp only [Option.elim, dest_nil, mem_pure_iff] at td
  exact ⟨_, ht'⟩
#align stream.wseq.destruct_some_of_destruct_tail_some WSeq.dest_some_of_dest_tail_some

theorem head_some_of_head_tail_some {s : WSeq α} {a} (h : some a ∈ head (tail s)) :
    ∃ a', some a' ∈ head s := by
  unfold head at h
  rcases Computation.exists_of_mem_map h with ⟨o, md, e⟩; clear h
  cases' o with o <;> [injection e; injection e with h']; clear h'
  cases' dest_some_of_dest_tail_some md with a am
  exact ⟨_, Computation.mem_map (Option.map Prod.fst) am⟩
#align stream.wseq.head_some_of_head_tail_some WSeq.head_some_of_head_tail_some

theorem head_some_of_get?_some {s : WSeq α} {a n} (h : some a ∈ get? s n) :
    ∃ a', some a' ∈ head s := by
  induction n generalizing a with
  | zero => exact ⟨_, h⟩
  | succ n IH =>
      let ⟨a', h'⟩ := head_some_of_head_tail_some h
      exact IH h'
#align stream.wseq.head_some_of_nth_some WSeq.head_some_of_get?_some

instance dest_terminates (s : WSeq α) [Productive s] : (dest s).Terminates :=
  head_terminates_iff.mp (head_terminates s)

instance productive_tail (s : WSeq α) [Productive s] : Productive (tail s) :=
  ⟨fun n => by rw [get?_tail]; infer_instance⟩
#align stream.wseq.productive_tail WSeq.productive_tail

instance productive_drop (s : WSeq α) [Productive s] (n) : Productive (drop s n) :=
  ⟨fun m => by rw [← get?_add]; infer_instance⟩
#align stream.wseq.productive_dropn WSeq.productive_drop

/-- Given a productive weak sequence, we can collapse all the `think`s to
  produce a sequence. -/
def toSeq (s : WSeq α) [Productive s] : Seq' α where
  get? n := Computation.get (get? s n)
  succ_stable n h := by
    cases e : Computation.get (get? s (n + 1))
    · assumption
    have := Computation.mem_of_get_eq _ e
    simp? [get?] at this h says simp only [get?] at this h
    cases' head_some_of_head_tail_some this with a' h'
    have := mem_unique h' (@Computation.mem_of_get_eq _ _ _ _ h)
    contradiction
#align stream.wseq.to_seq WSeq.toSeq

@[simp]
theorem get?_toSeq (s : WSeq α) [Productive s] (n : ℕ) :
    Seq'.get? (toSeq s) n = Computation.get (get? s n) :=
  rfl

theorem get?_terminates_le {s : WSeq α} {m n} (h : m ≤ n) :
    Terminates (get? s n) → Terminates (get? s m) := by
  induction' h with m' _ IH
  exacts [id, fun T => IH (@head_terminates_of_head_tail_terminates _ _ T)]
#align stream.wseq.nth_terminates_le WSeq.get?_terminates_le

theorem head_terminates_of_get?_terminates {s : WSeq α} {n} :
    Terminates (get? s n) → Terminates (head s) :=
  get?_terminates_le (Nat.zero_le n)
#align stream.wseq.head_terminates_of_nth_terminates WSeq.head_terminates_of_get?_terminates

theorem dest_terminates_of_get?_terminates {s : WSeq α} {n} (T : Terminates (get? s n)) :
    Terminates (dest s) :=
  head_terminates_iff.1 <| head_terminates_of_get?_terminates T
#align stream.wseq.destruct_terminates_of_nth_terminates WSeq.dest_terminates_of_get?_terminates

@[simp]
theorem mem_think (s : WSeq α) (a) : a ∈ think s ↔ a ∈ s := by simp [mem_def, think]
#align stream.wseq.mem_think WSeq.mem_think

theorem mem_think_of_mem {s : WSeq α} {a} : a ∈ s → a ∈ think s :=
  mem_think s a |>.mpr

theorem eq_or_mem_iff_mem {s : WSeq α} {a a' s'} :
    some (a', s') ∈ dest s → (a ∈ s ↔ a = a' ∨ a ∈ s') := by
  generalize e : dest s = c; intro h
  induction' h using Computation.memRecOn with _ _ IH generalizing s <;>
    induction' s using WSeq.recOn' with x s s <;>
    have := congr_arg Computation.dest e <;>
    simp at this
  · cases' this with i1 i2
    rw [i1, i2]
    simp [mem_def, cons]
  · simp [IH this]
#align stream.wseq.eq_or_mem_iff_mem WSeq.eq_or_mem_iff_mem

@[simp]
theorem mem_cons_iff (s : WSeq α) (b) {a} : a ∈ b ::ₐ s ↔ a = b ∨ a ∈ s :=
  eq_or_mem_iff_mem <| by simp [mem_pure]
#align stream.wseq.mem_cons_iff WSeq.mem_cons_iff

theorem mem_cons_of_mem {s : WSeq α} (b) {a} (h : a ∈ s) : a ∈ b ::ₐ s :=
  (mem_cons_iff _ _).2 (Or.inr h)
#align stream.wseq.mem_cons_of_mem WSeq.mem_cons_of_mem

theorem mem_cons (s : WSeq α) (a) : a ∈ a ::ₐ s :=
  (mem_cons_iff _ _).2 (Or.inl rfl)
#align stream.wseq.mem_cons WSeq.mem_cons

@[elab_as_elim]
theorem mem_rec_on {a} {C : (s : WSeq α) → a ∈ s → Prop} {s} (M : a ∈ s)
    (mem_cons : ∀ s', C (a ::ₐ s') (mem_cons s' a))
    (mem_cons_of_mem : ∀ (b) {s'} (h : a ∈ s'), C s' h → C (b ::ₐ s') (mem_cons_of_mem b h))
    (mem_think_of_mem : ∀ {s} (h : a ∈ s), C s h → C (think s) (mem_think_of_mem h)) : C s M := by
  cases s with
  | mk s =>
    change some a ∈ s at M
    induction M using Seq'.mem_rec_on with
    | mem_cons s' =>
      exact mem_cons ⟨s'⟩
    | mem_cons_of_mem o h ih =>
      cases o with
      | some b => exact mem_cons_of_mem b h ih
      | none   => exact mem_think_of_mem h ih
#align stream.wseq.mem_rec_on WSeq.mem_rec_onₓ

theorem mem_of_mem_tail {s : WSeq α} {a} : a ∈ tail s → a ∈ s := by
  intro h; have := h; cases' h with n e; revert s
  induction' n with n IH <;> intro s <;> induction' s using WSeq.recOn' with x s s <;>
    simp <;> intro m e <;>
    injections
  · exact Or.inr m
  · exact Or.inr m
  · apply IH m
    rw [e]
#align stream.wseq.mem_of_mem_tail WSeq.mem_of_mem_tail

theorem mem_of_mem_drop {s : WSeq α} {a} : ∀ {n}, a ∈ drop s n → a ∈ s
  | 0, h => h
  | n + 1, h => @mem_of_mem_drop s a n (mem_of_mem_tail h)
#align stream.wseq.mem_of_mem_dropn WSeq.mem_of_mem_drop

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
#align stream.wseq.nth_mem WSeq.get?_mem

theorem exists_get?_of_mem {s : WSeq α} {a} (h : a ∈ s) : ∃ n, some a ∈ get? s n := by
  induction h using mem_rec_on with
  -- · intro a' s' h
  --   cases' h with h h
  | mem_cons s' =>
    exists 0
    simp only [get?, drop, head_cons]
    apply mem_pure
  | mem_cons_of_mem a' _ h =>
    cases' h with n h
    exists n + 1
    -- porting note (#10745): was `simp [get?]`.
    simpa [get?]
  | mem_think_of_mem _ h =>
    cases' h with n h
    exists n
    simpa [get?]
#align stream.wseq.exists_nth_of_mem WSeq.exists_get?_of_mem

theorem exists_drop_of_mem {s : WSeq α} {a} (h : a ∈ s) :
    ∃ n s', some (a, s') ∈ dest (drop s n) :=
  let ⟨n, h⟩ := exists_get?_of_mem h
  ⟨n, by
    rcases head_terminates_iff.1 ⟨⟨_, h⟩⟩ with ⟨⟨o, om⟩⟩
    have := Computation.mem_unique (Computation.mem_map _ om) h
    cases' o with o
    · injection this
    injection this with i
    cases' o with a' s'
    dsimp at i
    rw [i] at om
    exact ⟨_, om⟩⟩
#align stream.wseq.exists_dropn_of_mem WSeq.exists_drop_of_mem

theorem liftRel_drop_dest {R : α → β → Prop} {s t} (H : LiftRel R s t) :
    ∀ n, Computation.LiftRel (LiftRelO R (LiftRel R)) (dest (drop s n)) (dest (drop t n))
  | 0 => liftRel_dest H
  | n + 1 => by
    simp only [LiftRelO, drop, Nat.add_eq, Nat.add_zero, dest_tail, tail.aux]
    apply liftRel_bind
    · apply liftRel_drop_dest H n
    exact fun {a b} o =>
      match a, b, o with
      | none, none, _ => by simp
      | some (a, s), some (b, t), ⟨_, h2⟩ => by simpa [tail.aux] using liftRel_dest h2
#align stream.wseq.lift_rel_dropn_destruct WSeq.liftRel_drop_dest

theorem exists_of_liftRel_left {R : α → β → Prop} {s t} (H : LiftRel R s t) {a} (h : a ∈ s) :
    ∃ b, b ∈ t ∧ R a b := by
  let ⟨n, h⟩ := exists_get?_of_mem h
  -- Porting note: This line is required to infer metavariables in
  --               `Computation.exists_of_mem_map`.
  dsimp only [get?, head] at h
  let ⟨some (_, s'), sd, rfl⟩ := Computation.exists_of_mem_map h
  let ⟨some (b, t'), td, ⟨ab, _⟩⟩ := (liftRel_drop_dest H n).left sd
  exact ⟨b, get?_mem (Computation.mem_map (Option.map Prod.fst) td), ab⟩
#align stream.wseq.exists_of_lift_rel_left WSeq.exists_of_liftRel_left

theorem exists_of_liftRel_right {R : α → β → Prop} {s t} (H : LiftRel R s t) {b} (h : b ∈ t) :
    ∃ a, a ∈ s ∧ R a b := by rw [← LiftRel.swap] at H; exact exists_of_liftRel_left H h
#align stream.wseq.exists_of_lift_rel_right WSeq.exists_of_liftRel_right

theorem head_terminates_of_mem {s : WSeq α} {a} (h : a ∈ s) : Terminates (head s) :=
  let ⟨_, h⟩ := exists_get?_of_mem h
  head_terminates_of_get?_terminates ⟨⟨_, h⟩⟩
#align stream.wseq.head_terminates_of_mem WSeq.head_terminates_of_mem

theorem of_mem_append {s₁ s₂ : WSeq α} {a : α} : a ∈ s₁ ++ s₂ → a ∈ s₁ ∨ a ∈ s₂ :=
  Seq'.of_mem_append
#align stream.wseq.of_mem_append WSeq.of_mem_append

theorem mem_append_left {s₁ s₂ : WSeq α} {a : α} : a ∈ s₁ → a ∈ s₁ ++ s₂ :=
  Seq'.mem_append_left
#align stream.wseq.mem_append_left WSeq.mem_append_left

theorem exists_of_mem_map {f} {b : β} {s : WSeq α} (h : b ∈ map f s) : ∃ a, a ∈ s ∧ f a = b := by
  let ⟨o, om, oe⟩ := Seq'.exists_of_mem_map h
  cases' o with a
  · injection oe
  injection oe with h'
  exact ⟨a, om, h'⟩
#align stream.wseq.exists_of_mem_map WSeq.exists_of_mem_map

@[simp]
theorem liftRel_nil (R : α → β → Prop) : LiftRel R nil nil := by
  rw [liftRel_dest_iff]
  -- Porting note: These 2 theorems should be excluded.
  simp [-liftRel_pure_left, -liftRel_pure_right]
#align stream.wseq.lift_rel_nil WSeq.liftRel_nil

@[simp]
theorem liftRel_cons (R : α → β → Prop) (a b s t) :
    LiftRel R (a ::ₐ s) (b ::ₐ t) ↔ R a b ∧ LiftRel R s t := by
  rw [liftRel_dest_iff]
  -- Porting note: These 2 theorems should be excluded.
  simp [-liftRel_pure_left, -liftRel_pure_right]
#align stream.wseq.lift_rel_cons WSeq.liftRel_cons

@[simp]
theorem liftRel_think_left (R : α → β → Prop) (s t) : LiftRel R (think s) t ↔ LiftRel R s t := by
  rw [liftRel_dest_iff, liftRel_dest_iff]; simp
#align stream.wseq.lift_rel_think_left WSeq.liftRel_think_left

@[simp]
theorem liftRel_think_right (R : α → β → Prop) (s t) : LiftRel R s (think t) ↔ LiftRel R s t := by
  rw [liftRel_dest_iff, liftRel_dest_iff]; simp
#align stream.wseq.lift_rel_think_right WSeq.liftRel_think_right

theorem cons_congr {s t : WSeq α} (a : α) (h : s ≈ t) : a ::ₐ s ≈ a ::ₐ t := by
  simpa [equiv_def] using h
#align stream.wseq.cons_congr WSeq.cons_congr

theorem think_equiv (s : WSeq α) : think s ≈ s := by simpa [equiv_def] using Equiv.refl _
#align stream.wseq.think_equiv WSeq.think_equiv

theorem think_congr {s t : WSeq α} (h : s ≈ t) : think s ≈ think t := by
  simpa [equiv_def] using h
#align stream.wseq.think_congr WSeq.think_congr

theorem head_congr : ∀ {s t : WSeq α}, s ≈ t → head s ≈ head t := by
  suffices ∀ {s t : WSeq α}, s ≈ t → ∀ {o}, o ∈ head s → o ∈ head t from fun s t h o =>
    ⟨this h, this h.symm⟩
  intro s t h o ho
  rcases @Computation.exists_of_mem_map _ _ _ _ (dest s) ho with ⟨ds, dsm, dse⟩
  rw [← dse]
  cases' dest_congr h with l r
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
    exact @Computation.mem_map _ _ (Option.map Prod.fst) (some (b, t')) (dest t) dtm
#align stream.wseq.head_congr WSeq.head_congr

theorem flatten_equiv {c : Computation (WSeq α)} {s} (h : s ∈ c) : flatten c ≈ s := by
  induction h using Computation.memRecOn with
  | mem_pure => simp [Setoid.refl]
  | @mem_think s' _ h =>
    trans flatten s'
    · simp [think_equiv]
    · exact h
#align stream.wseq.flatten_equiv WSeq.flatten_equiv

theorem congr_tail_of_some_mem_dest {a : α} {s' s : WSeq α} (hds : some (a, s') ∈ dest s) :
    s' ≈ tail s := by
  apply Setoid.symm
  apply flatten_equiv
  exact Computation.mem_map _ hds

theorem liftRel_flatten {R : α → β → Prop} {c1 : Computation (WSeq α)} {c2 : Computation (WSeq β)}
    (h : c1.LiftRel (LiftRel R) c2) : LiftRel R (flatten c1) (flatten c2) :=
  let S s t := ∃ c1 c2, s = flatten c1 ∧ t = flatten c2 ∧ Computation.LiftRel (LiftRel R) c1 c2
  ⟨S, ⟨c1, c2, rfl, rfl, h⟩, fun {s t} h =>
    match s, t, h with
    | _, _, ⟨c1, c2, rfl, rfl, h⟩ => by
      simp only [dest_flatten]; apply liftRel_bind _ _ h
      intro a b ab; apply Computation.LiftRel.imp _ _ _ (liftRel_dest ab)
      intro a b; apply LiftRelO.imp_right
      intro s t h; refine ⟨Computation.pure s, Computation.pure t, ?_, ?_, ?_⟩ <;>
        -- Porting note: These 2 theorems should be excluded.
        simp [h, - liftRel_pure_left, - liftRel_pure_right]⟩
#align stream.wseq.lift_rel_flatten WSeq.liftRel_flatten

theorem flatten_congr {c1 c2 : Computation (WSeq α)} :
    Computation.LiftRel (· ≈ ·) c1 c2 → flatten c1 ≈ flatten c2 :=
  liftRel_flatten
#align stream.wseq.flatten_congr WSeq.flatten_congr

theorem tail_congr {s t : WSeq α} (h : s ≈ t) : tail s ≈ tail t := by
  apply flatten_congr
  rw [← Computation.bind_pure, ← Computation.bind_pure]
  apply liftRel_bind _ _ (dest_congr h)
  intro a b h; simp only [comp_apply, liftRel_pure]
  cases' a with a <;> cases' b with b
  · apply Setoid.refl
  · cases h
  · cases a
    cases h
  · cases' a with a s'
    cases' b with b t'
    exact h.right
#align stream.wseq.tail_congr WSeq.tail_congr

theorem drop_congr {s t : WSeq α} (h : s ≈ t) (n) : drop s n ≈ drop t n := by
  induction n <;> simp [*, tail_congr, drop]
#align stream.wseq.dropn_congr WSeq.drop_congr

theorem get?_congr {s t : WSeq α} (h : s ≈ t) (n) : get? s n ≈ get? t n :=
  head_congr (drop_congr h _)
#align stream.wseq.nth_congr WSeq.get?_congr

theorem mem_congr {s t : WSeq α} (h : s ≈ t) (a) : a ∈ s ↔ a ∈ t :=
  suffices ∀ {s t : WSeq α}, s ≈ t → a ∈ s → a ∈ t from ⟨this h, this h.symm⟩
  fun {_ _} h as =>
  let ⟨_, hn⟩ := exists_get?_of_mem as
  get?_mem ((get?_congr h _ _).1 hn)
#align stream.wseq.mem_congr WSeq.mem_congr

theorem productive_congr {s t : WSeq α} (h : s ≈ t) : Productive s ↔ Productive t := by
  simp only [productive_iff]; exact forall_congr' fun n => terminates_congr <| get?_congr h _
#align stream.wseq.productive_congr WSeq.productive_congr

theorem Equiv.ext {s t : WSeq α} (h : ∀ n, get? s n ≈ get? t n) : s ≈ t :=
  ⟨fun s t => ∀ n, get? s n ≈ get? t n, h, fun {s t} h => by
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
            ((?_ : get? (tail s) n ≈ get? (tail t) n).trans
              (get?_congr (flatten_equiv (Computation.mem_map _ mb)) n))
        rw [get?_tail, get?_tail]
        apply h⟩
#align stream.wseq.equiv.ext WSeq.Equiv.ext

theorem length_eq_map (s : WSeq α) : length s = Computation.map List.length (toList s) := by
  refine
    Computation.eq_of_bisim
      (fun c1 c2 =>
        ∃ (l : List α) (s : WSeq α),
          c1 = Computation.corec (fun (n, s) =>
            match Seq'.dest s with
            | none => Sum.inl n
            | some (none, s') => Sum.inr (n, s')
            | some (some _, s') => Sum.inr (n + 1, s')) (l.length, data s) ∧
            c2 = Computation.map List.length (Computation.corec (fun (l, s) =>
              match Seq'.dest s with
              | none => Sum.inl l.reverse
              | some (none, s') => Sum.inr (l, s')
              | some (some a, s') => Sum.inr (a :: l, s')) (l, data s)))
      ?_ ⟨[], s, rfl, rfl⟩
  intro s1 s2 h; rcases h with ⟨l, s, h⟩; rw [h.left, h.right]
  induction' s using WSeq.recOn' with a s s <;> simp [toList, nil, cons, think, length]
  · refine ⟨a :: l, s, ?_, ?_⟩ <;> simp
  · refine ⟨l, s, ?_, ?_⟩ <;> simp
#align stream.wseq.length_eq_map WSeq.length_eq_map

@[simp, norm_cast]
theorem ofList_nil : (↑([] : List α) : WSeq α) = nil :=
  rfl
#align stream.wseq.of_list_nil WSeq.ofList_nil

@[simp, norm_cast]
theorem ofList_cons (a : α) (l) : (↑(a :: l) : WSeq α) = a ::ₐ ↑l := by simp [cons, ofList, ofSeq]
#align stream.wseq.of_list_cons WSeq.ofList_cons

@[simp]
theorem toList'_nil (l : List α) :
    Computation.corec (fun (l, s) =>
      match Seq'.dest s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a :: l, s')) (l, data nil) = Computation.pure l.reverse :=
  dest_eq_pure rfl
#align stream.wseq.to_list'_nil WSeq.toList'_nil

@[simp]
theorem toList'_cons (l : List α) (s : WSeq α) (a : α) :
    Computation.corec (fun (l, s) =>
      match Seq'.dest s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a :: l, s')) (l, data (a ::ₐ s)) =
      (Computation.corec (fun (l, s) =>
        match Seq'.dest s with
        | none => Sum.inl l.reverse
        | some (none, s') => Sum.inr (l, s')
        | some (some a, s') => Sum.inr (a :: l, s')) (a :: l, data s)).think :=
  dest_eq_think <| by simp [toList, cons]
#align stream.wseq.to_list'_cons WSeq.toList'_cons

@[simp]
theorem toList'_think (l : List α) (s : WSeq α) :
    Computation.corec (fun (l, s) =>
      match Seq'.dest s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a :: l, s')) (l, data (think s)) =
      (Computation.corec (fun (l, s) =>
        match Seq'.dest s with
        | none => Sum.inl l.reverse
        | some (none, s') => Sum.inr (l, s')
        | some (some a, s') => Sum.inr (a :: l, s')) (l, data s)).think :=
  dest_eq_think <| by simp [toList, think]
#align stream.wseq.to_list'_think WSeq.toList'_think

theorem toList'_map (l : List α) (s : WSeq α) :
    Computation.corec (fun (l, s) =>
      match Seq'.dest s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a :: l, s')) (l, data s) =
      Computation.map (l.reverse ++ ·) (toList s) := by
  refine
    Computation.eq_of_bisim
      (fun c1 c2 =>
        ∃ (l' : List α) (s : WSeq α),
          c1 = Computation.corec (fun (l, s) =>
            match Seq'.dest s with
            | none => Sum.inl l.reverse
            | some (none, s') => Sum.inr (l, s')
            | some (some a, s') => Sum.inr (a :: l, s')) (l' ++ l, data s) ∧
            c2 = Computation.map (l.reverse ++ ·) (Computation.corec (fun (l, s) =>
              match Seq'.dest s with
              | none => Sum.inl l.reverse
              | some (none, s') => Sum.inr (l, s')
              | some (some a, s') => Sum.inr (a :: l, s')) (l', data s)))
      ?_ ⟨[], s, rfl, rfl⟩
  intro s1 s2 h; rcases h with ⟨l', s, h⟩; rw [h.left, h.right]
  induction' s using WSeq.recOn' with a s s <;> simp [toList, nil, cons, think, length]
  · refine ⟨a :: l', s, ?_, ?_⟩ <;> simp
  · refine ⟨l', s, ?_, ?_⟩ <;> simp
#align stream.wseq.to_list'_map WSeq.toList'_map

@[simp]
theorem toList_cons (a : α) (s) :
    toList (a ::ₐ s) = (Computation.map (List.cons a) (toList s)).think :=
  dest_eq_think <| by
    unfold toList
    simp only [toList'_cons, Computation.dest_think, Sum.inr.injEq]
    rw [toList'_map]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
    rfl
#align stream.wseq.to_list_cons WSeq.toList_cons

@[simp]
theorem toList_nil : toList (nil : WSeq α) = Computation.pure [] :=
  dest_eq_pure rfl
#align stream.wseq.to_list_nil WSeq.toList_nil

theorem toList_ofList (l : List α) : l ∈ toList (l : WSeq α) := by
  induction' l with a l IH <;> simp; exact Computation.mem_map _ IH
#align stream.wseq.to_list_of_list WSeq.toList_ofList

@[simp]
theorem dest_ofSeq (s : Seq' α) :
    dest ↑s = Computation.pure (s.head.map fun a => (a, ↑s.tail)) :=
  dest_eq_pure <| by
    simp only [dest, Seq'.dest, ofSeq, Computation.dest_corec,
      Seq'.head, Seq'.map_get?]
    cases' Seq'.get? s 0 with a
    · rfl
    simp [dest]
#align stream.wseq.destruct_of_seq WSeq.dest_ofSeq

@[simp]
theorem head_ofSeq (s : Seq' α) : head ↑s = Computation.pure s.head := by
  simp only [head, Option.map_eq_map, dest_ofSeq, Computation.map_pure, Option.map_map]
  cases Seq'.head s <;> rfl
#align stream.wseq.head_of_seq WSeq.head_ofSeq

@[simp]
theorem tail_ofSeq (s : Seq' α) : tail (↑s : WSeq α) = ↑s.tail := by
  simp [tail, Option.elim, dest_ofSeq, Computation.map_pure, flatten_pure]
  induction' s using Seq'.recOn' with x s <;> simp [ofSeq]
  · rfl
#align stream.wseq.tail_of_seq WSeq.tail_ofSeq

@[simp, norm_cast]
theorem drop_ofSeq (s : Seq' α) : ∀ n, drop (↑s : WSeq α) n = ↑(s.drop n)
  | 0 => rfl
  | n + 1 => by
    simp only [drop, Nat.add_eq, Nat.add_zero]
    rw [drop_ofSeq s n, tail_ofSeq, Seq'.tail_drop]
#align stream.wseq.dropn_of_seq WSeq.drop_ofSeq

theorem get?_ofSeq (s : Seq' α) (n) : get? (↑s : WSeq α) n = Computation.pure (Seq'.get? s n) := by
  dsimp [get?]; rw [drop_ofSeq, head_ofSeq, Seq'.head_drop]
#align stream.wseq.nth_of_seq WSeq.get?_ofSeq

instance productive_ofSeq (s : Seq' α) : Productive (↑s : WSeq α) :=
  ⟨fun n => by rw [get?_ofSeq]; infer_instance⟩
#align stream.wseq.productive_of_seq WSeq.productive_ofSeq

theorem toSeq_ofSeq (s : Seq' α) : toSeq ↑s = s := by
  ext1 n
  dsimp; apply get_eq_of_mem
  rw [get?_ofSeq]; apply mem_pure
#align stream.wseq.to_seq_of_seq WSeq.toSeq_ofSeq

/-- Corecursive verseion of `toSeq`. -/
@[simp]
def toSeqCorec (s : WSeq α) [hs : Productive s] : Seq' α :=
  Seq'.corec (β := { s : WSeq α // Productive s })
    (fun ⟨s, _⟩ =>
      match Computation.get (dest s), Computation.get_mem (dest s) with
      | some (a, s'), hs' =>
        some (a, ⟨s', (productive_congr (congr_tail_of_some_mem_dest hs')).mpr (productive_tail s)⟩)
      | none       , _  => none)
    ⟨s, hs⟩

@[csimp]
theorem toSeq_eq_toSeqCorec : @toSeq.{u} = @toSeqCorec.{u} := by
  funext α s hs
  ext1 n
  simp
  apply Computation.get_eq_of_mem
  have hpf :
      (Prod.fst : α × { s : WSeq α // Productive s } → α) = Prod.fst ∘ Prod.map id Subtype.val := by
    simp [Prod.map_fst']
  rw [get?, head, hpf, ← Option.map_map]
  apply Computation.mem_map
  induction n using Nat.recAux with
  | zero =>
    simp [drop]
    split
    next _ _ a s₁ hs₁ _ _ => exact hs₁
    next _ _ hds _ _ => exact hds
  | succ n hn =>
    simp [drop, dest_tail, iterate_succ', - iterate_succ]
    rcases hms :
      Option.map (Prod.map id Subtype.val)
        ((fun o ↦
            Option.bind o
              ((fun ⟨s, _⟩ ↦
                  match Computation.get (dest s), Computation.get_mem (dest s) with
                  | some (a, s'), hs' =>
                    some (a, ⟨s', (productive_congr (congr_tail_of_some_mem_dest hs')).mpr
                      (productive_tail s)⟩)
                  | none, _ => none) ∘
                Prod.snd))^[n]
          (match Computation.get (dest s), Computation.get_mem (dest s) with
           | some (a, s'), hs' =>
             some (a, ⟨s', (productive_congr (congr_tail_of_some_mem_dest hs')).mpr
              (productive_tail s)⟩)
           | none, _ => none)) with (_ | ⟨a, s₁⟩)
    · simp at hms
      simp [hms] at hn ⊢
      exact Computation.mem_bind (f := tail.aux) hn (Computation.mem_pure none)
    · simp at hms
      rcases hms with ⟨hs₁, hms⟩
      simp [hms] at hn ⊢
      split
      next _ _ a s₃ hs₃ _ _ =>
        exact Computation.mem_bind (f := tail.aux) hn hs₃
      next _ _ hds _ _ =>
        exact Computation.mem_bind (f := tail.aux) hn hds

/-- The monadic `pure a` is a singleton list containing `a`. -/
def pure (a : α) : WSeq α :=
  a ::ₐ nil
#align stream.wseq.ret WSeq.pure

@[simp]
theorem map_nil (f : α → β) : map f nil = nil :=
  rfl
#align stream.wseq.map_nil WSeq.map_nil

@[simp]
theorem map_cons (f : α → β) (a s) : map f (a ::ₐ s) = f a ::ₐ map f s :=
  WSeq.ext _ _ <| Seq'.map_cons _ _ _
#align stream.wseq.map_cons WSeq.map_cons

@[simp]
theorem map_think (f : α → β) (s) : map f (think s) = think (map f s) :=
  WSeq.ext _ _ <| Seq'.map_cons _ _ _
#align stream.wseq.map_think WSeq.map_think

@[simp]
theorem map_id (s : WSeq α) : map id s = s := by simp [map]
#align stream.wseq.map_id WSeq.map_id

@[simp]
theorem map_pure (f : α → β) (a) : map f (pure a) = pure (f a) := by simp [pure]
#align stream.wseq.map_ret WSeq.map_pure

@[simp]
theorem map_append (f : α → β) (s t) : map f (s ++ t) = map f s ++ map f t :=
  WSeq.ext _ _ <| Seq'.map_append _ _ _
#align stream.wseq.map_append WSeq.map_append

@[simp]
theorem map_map (g : β → γ) (f : α → β) (s : WSeq α) : map g (map f s) = map (g ∘ f) s := by
  simp [map]
#align stream.wseq.map_comp WSeq.map_map

theorem mem_map (f : α → β) {a : α} {s : WSeq α} : a ∈ s → f a ∈ map f s :=
  Seq'.mem_map_of_mem (Option.map f)
#align stream.wseq.mem_map WSeq.mem_map

-- The converse is not true without additional assumptions
theorem exists_of_mem_join {a : α} : ∀ {S : WSeq (WSeq α)}, a ∈ join S → ∃ s, s ∈ S ∧ a ∈ s := by
  suffices
    ∀ ss : WSeq α,
      a ∈ ss → ∀ s S, s ++ join S = ss → a ∈ s ++ join S → a ∈ s ∨ ∃ s, s ∈ S ∧ a ∈ s
    from fun S h => (this _ h nil S (by simp) (by simp [h])).resolve_left (not_mem_nil _)
  intro ss h; induction' h using mem_rec_on with ss b ss _ IH ss _ IH <;> intro s S <;>
    cases' ss with ss
  · induction' s using WSeq.recOn' with b' s s <;>
      [induction' S using WSeq.recOn' with s S S; skip; skip] <;>
      intro ej m <;> simp at ej <;> have := congr_arg (Seq'.dest ∘ data) ej <;>
      simp at this; cases this
    substs b' ss
    simp? at m ⊢ says simp only [cons_append, mem_cons_iff, true_or] at m ⊢
  · induction' s using WSeq.recOn' with b' s s <;>
      [induction' S using WSeq.recOn' with s S S; skip; skip] <;>
      intro ej m <;> simp at ej <;> have := congr_arg (Seq'.dest ∘ data) ej <;>
      simp at this; try cases this; try contradiction
    substs b' ss
    simp at m ⊢
    cases' m with e m
    · simp [e]
    exact Or.imp_left Or.inr (IH _ _ rfl m)
  · induction' s using WSeq.recOn' with b' s s <;>
      [induction' S using WSeq.recOn' with s S S; skip; skip] <;>
      intro ej m <;> simp at ej <;> have := congr_arg (Seq'.dest ∘ data) ej <;>
      simp at this <;> subst ss
    · apply Or.inr
      -- Porting note: `exists_eq_or_imp` should be excluded.
      simp [- exists_eq_or_imp] at m ⊢
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
#align stream.wseq.exists_of_mem_join WSeq.exists_of_mem_join

theorem exists_of_mem_bind {s : WSeq α} {f : α → WSeq β} {b} (h : b ∈ bind s f) :
    ∃ a ∈ s, b ∈ f a :=
  let ⟨t, tm, bt⟩ := exists_of_mem_join h
  let ⟨a, as, e⟩ := exists_of_mem_map tm
  ⟨a, as, by rwa [e]⟩
#align stream.wseq.exists_of_mem_bind WSeq.exists_of_mem_bind

theorem dest_map (f : α → β) (s : WSeq α) :
    dest (map f s) = Computation.map (Option.map (Prod.map f (map f))) (dest s) := by
  apply
    Computation.eq_of_bisim fun c1 c2 =>
      ∃ s,
        c1 = dest (map f s) ∧
          c2 = Computation.map (Option.map (Prod.map f (map f))) (dest s)
  · intro c1 c2 h
    cases' h with s h
    rw [h.left, h.right]
    induction' s using WSeq.recOn' with a s s <;> simp
    exact ⟨s, rfl, rfl⟩
  · exact ⟨s, rfl, rfl⟩
#align stream.wseq.destruct_map WSeq.dest_map

theorem liftRel_map {δ} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : WSeq α} {s2 : WSeq β}
    {f1 : α → γ} {f2 : β → δ} (h1 : LiftRel R s1 s2) (h2 : ∀ {a b}, R a b → S (f1 a) (f2 b)) :
    LiftRel S (map f1 s1) (map f2 s2) :=
  ⟨fun s1 s2 => ∃ s t, s1 = map f1 s ∧ s2 = map f2 t ∧ LiftRel R s t, ⟨s1, s2, rfl, rfl, h1⟩,
    fun {s1 s2} h =>
    match s1, s2, h with
    | _, _, ⟨s, t, rfl, rfl, h⟩ => by
      simp only [exists_and_left, dest_map]
      apply Computation.liftRel_map _ _ (liftRel_dest h)
      intro o p h
      cases' o with a <;> cases' p with b <;> simp
      · cases b; cases h
      · cases a; cases h
      · cases' a with a s; cases' b with b t
        cases' h with r h
        exact ⟨h2 r, s, rfl, t, rfl, h⟩⟩
#align stream.wseq.lift_rel_map WSeq.liftRel_map

theorem map_congr (f : α → β) {s t : WSeq α} (h : s ≈ t) : map f s ≈ map f t :=
  liftRel_map _ _ h fun {_ _} => congr_arg _
#align stream.wseq.map_congr WSeq.map_congr

/-- auxiliary definition of `dest_append` over weak sequences-/
@[simp]
def dest_append.aux (t : WSeq α) : Option (α × WSeq α) → Computation (Option (α × WSeq α))
  | none => dest t
  | some (a, s) => Computation.pure (some (a, s ++ t))
#align stream.wseq.destruct_append.aux WSeq.dest_append.aux

theorem dest_append (s t : WSeq α) :
    dest (s ++ t) = (dest s).bind (dest_append.aux t) := by
  apply
    Computation.eq_of_bisim
      (fun c1 c2 =>
        ∃ s t, c1 = dest (s ++ t) ∧ c2 = (dest s).bind (dest_append.aux t))
      _ ⟨s, t, rfl, rfl⟩
  intro c1 c2 h; rcases h with ⟨s, t, h⟩; rw [h.left, h.right]
  induction' s using WSeq.recOn' with a s s <;> simp
  · induction' t using WSeq.recOn' with b t t <;> simp
    · refine ⟨nil, t, ?_, ?_⟩ <;> simp
  · exact ⟨s, t, rfl, rfl⟩
#align stream.wseq.destruct_append WSeq.dest_append

/-- auxiliary definition of `dest_join` over weak sequences-/
@[simp]
def dest_join.aux : Option (WSeq α × WSeq (WSeq α)) → Computation (Option (α × WSeq α))
  | none => Computation.pure none
  | some (s, S) => (dest (s ++ join S)).think
#align stream.wseq.destruct_join.aux WSeq.dest_join.aux

theorem dest_join (S : WSeq (WSeq α)) :
    dest (join S) = (dest S).bind dest_join.aux := by
  apply
    Computation.eq_of_bisim
      (fun c1 c2 =>
        c1 = c2 ∨ ∃ S, c1 = dest (join S) ∧ c2 = (dest S).bind dest_join.aux)
      _ (Or.inr ⟨S, rfl, rfl⟩)
  intro c1 c2 h
  exact
    match c1, c2, h with
    | c, _, Or.inl <| rfl => by cases c.dest <;> simp
    | _, _, Or.inr ⟨S, rfl, rfl⟩ => by
      induction' S using WSeq.recOn' with s S S <;> simp
      · refine' Or.inr ⟨S, rfl, rfl⟩
#align stream.wseq.destruct_join WSeq.dest_join

theorem liftRel_append (R : α → β → Prop) {s1 s2 : WSeq α} {t1 t2 : WSeq β} (h1 : LiftRel R s1 t1)
    (h2 : LiftRel R s2 t2) : LiftRel R (s1 ++ s2) (t1 ++ t2) :=
  ⟨fun s t => LiftRel R s t ∨ ∃ s1 t1, s = s1 ++ s2 ∧ t = t1 ++ t2 ∧ LiftRel R s1 t1,
    Or.inr ⟨s1, t1, rfl, rfl, h1⟩, fun {s t} h =>
    match s, t, h with
    | s, t, Or.inl h => by
      apply Computation.LiftRel.imp _ _ _ (liftRel_dest h)
      intro a b; apply LiftRelO.imp_right
      intro s t; apply Or.inl
    | _, _, Or.inr ⟨s1, t1, rfl, rfl, h⟩ => by
      simp only [LiftRelO, exists_and_left, dest_append, dest_append.aux]
      apply Computation.liftRel_bind _ _ (liftRel_dest h)
      intro o p h
      cases' o with a <;> cases' p with b
      · simp only [dest_append.aux]
        apply Computation.LiftRel.imp _ _ _ (liftRel_dest h2)
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
#align stream.wseq.lift_rel_append WSeq.liftRel_append

theorem liftRel_join.lem (R : α → β → Prop) {S T} {U : WSeq α → WSeq β → Prop}
    (ST : LiftRel (LiftRel R) S T)
    (HU :
      ∀ s1 s2,
        (∃ s t S T,
            s1 = s ++ join S ∧
              s2 = t ++ join T ∧ LiftRel R s t ∧ LiftRel (LiftRel R) S T) →
          U s1 s2)
    {a} (ma : a ∈ dest (join S)) : ∃ b, b ∈ dest (join T) ∧ LiftRelO R U a b := by
  cases' exists_results_of_mem ma with n h; clear ma; revert S T ST a
  induction' n using Nat.strongInductionOn with n IH
  intro S T ST a ra; simp only [dest_join] at ra
  exact
    let ⟨o, m, k, rs1, rs2, en⟩ := of_results_bind ra
    let ⟨p, mT, rop⟩ := Computation.exists_of_liftRel_left (liftRel_dest ST) rs1.mem
    match o, p, rop, rs1, rs2, mT with
    | none, none, _, _, rs2, mT => by
      simp only [dest_join]
      exact ⟨none, mem_bind mT (mem_pure _), by rw [← eq_of_mem_pure rs2.mem]; trivial⟩
    | some (s, S'), some (t, T'), ⟨st, ST'⟩, _, rs2, mT => by
      simp? [dest_append]  at rs2  says simp only [dest_join.aux, dest_append] at rs2
      exact
        let ⟨k1, rs3, ek⟩ := of_results_think rs2
        let ⟨o', m1, n1, rs4, rs5, ek1⟩ := of_results_bind rs3
        let ⟨p', mt, rop'⟩ := Computation.exists_of_liftRel_left (liftRel_dest st) rs4.mem
        match o', p', rop', rs4, rs5, mt with
        | none, none, _, _, rs5', mt => by
          have : n1 < n := by
            rw [en, ek, ek1]
            apply lt_of_lt_of_le _ (Nat.le_add_right _ _)
            apply Nat.lt_succ_of_le (Nat.le_add_right _ _)
          let ⟨ob, mb, rob⟩ := IH _ this ST' rs5'
          refine ⟨ob, ?_, rob⟩
          · simp (config := { unfoldPartialApp := true }) only [dest_join, dest_join.aux]
            apply mem_bind mT
            simp [dest_append]
            apply mem_bind mt
            exact mb
        | some (a, s'), some (b, t'), ⟨ab, st'⟩, _, rs5, mt => by
          simp?  at rs5  says simp only [dest_append.aux] at rs5
          refine ⟨some (b, t' ++ join T'), ?_, ?_⟩
          · simp (config := { unfoldPartialApp := true }) only [dest_join, dest_join.aux]
            apply mem_bind mT
            simp [dest_append]
            apply mem_bind mt
            apply mem_pure
          rw [← eq_of_mem_pure rs5.mem]
          exact ⟨ab, HU _ _ ⟨s', t', S', T', rfl, rfl, st', ST'⟩⟩
#align stream.wseq.lift_rel_join.lem WSeq.liftRel_join.lem

theorem liftRel_join (R : α → β → Prop) {S : WSeq (WSeq α)} {T : WSeq (WSeq β)}
    (h : LiftRel (LiftRel R) S T) : LiftRel R (join S) (join T) :=
  ⟨fun s1 s2 =>
    ∃ s t S T,
      s1 = s ++ join S ∧ s2 = t ++ join T ∧ LiftRel R s t ∧ LiftRel (LiftRel R) S T,
    ⟨nil, nil, S, T, by simp, by simp, by simp, h⟩, fun {s1 s2} ⟨s, t, S, T, h1, h2, st, ST⟩ => by
    rw [h1, h2]; rw [dest_append, dest_append]
    apply Computation.liftRel_bind _ _ (liftRel_dest st)
    exact fun {o p} h =>
      match o, p, h with
      | some (a, s), some (b, t), ⟨h1, h2⟩ => by
        -- Porting note: These 2 theorems should be excluded.
        simpa [-liftRel_pure_left, -liftRel_pure_right] using ⟨h1, s, t, S, rfl, T, rfl, h2, ST⟩
      | none, none, _ => by
        -- Porting note: `LiftRelO` should be excluded.
        dsimp [dest_append.aux, Computation.LiftRel, -LiftRelO]; constructor
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
#align stream.wseq.lift_rel_join WSeq.liftRel_join

theorem join_congr {S T : WSeq (WSeq α)} (h : LiftRel Equiv S T) : join S ≈ join T :=
  liftRel_join _ h
#align stream.wseq.join_congr WSeq.join_congr

theorem liftRel_bind {δ} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : WSeq α} {s2 : WSeq β}
    {f1 : α → WSeq γ} {f2 : β → WSeq δ} (h1 : LiftRel R s1 s2)
    (h2 : ∀ {a b}, R a b → LiftRel S (f1 a) (f2 b)) : LiftRel S (bind s1 f1) (bind s2 f2) :=
  liftRel_join _ (liftRel_map _ _ h1 @h2)
#align stream.wseq.lift_rel_bind WSeq.liftRel_bind

theorem bind_congr {s1 s2 : WSeq α} {f1 f2 : α → WSeq β} (h1 : s1 ≈ s2) (h2 : ∀ a, f1 a ≈ f2 a) :
    bind s1 f1 ≈ bind s2 f2 :=
  liftRel_bind _ _ h1 fun {a b} h => by rw [h]; apply h2
#align stream.wseq.bind_congr WSeq.bind_congr

@[simp]
theorem join_pure (s : WSeq α) : join (pure s) ≈ s := by simpa [pure] using think_equiv _
#align stream.wseq.join_ret WSeq.join_pure

@[simp]
theorem join_map_pure (s : WSeq α) : join (map pure s) ≈ s := by
  refine ⟨fun s1 s2 => join (map pure s2) = s1, rfl, ?_⟩
  intro s' s h; rw [← h]
  apply liftRel_rec fun c1 c2 => ∃ s, c1 = dest (join (map pure s)) ∧ c2 = dest s
  · exact fun {c1 c2} h =>
      match c1, c2, h with
      | _, _, ⟨s, rfl, rfl⟩ => by
        clear h
        -- Porting note: `pure` is simplified in `simp` so
        --               `pure`s become `fun a => a ::ₐ nil` here.
        have : ∀ s, ∃ s' : WSeq α,
            (map (· ::ₐ nil) s).join.dest =
              (map (· ::ₐ nil) s').join.dest ∧ dest s = s'.dest :=
          fun s => ⟨s, rfl, rfl⟩
        induction' s using WSeq.recOn' with a s s <;>
          simp (config := { unfoldPartialApp := true }) [pure, this, Option.exists]
  · exact ⟨s, rfl, rfl⟩
#align stream.wseq.join_map_ret WSeq.join_map_pure

@[simp]
theorem join_append (S T : WSeq (WSeq α)) : join (S ++ T) ≈ join S ++ join T := by
  refine
    ⟨fun s1 s2 =>
      ∃ s S T, s1 = s ++ join (S ++ T) ∧ s2 = s ++ (join S ++ join T),
      ⟨nil, S, T, by simp, by simp⟩, ?_⟩
  intro s1 s2 h
  apply
    liftRel_rec
      (fun c1 c2 =>
        ∃ (s : WSeq α) (S T : _),
          c1 = dest (s ++ join (S ++ T)) ∧
            c2 = dest (s ++ (join S ++ join T)))
      _ _ _
      (let ⟨s, S, T, h1, h2⟩ := h
      ⟨s, S, T, congr_arg dest h1, congr_arg dest h2⟩)
  rintro c1 c2 ⟨s, S, T, rfl, rfl⟩
  induction' s using WSeq.recOn' with a s s <;> simp
  · induction' S using WSeq.recOn' with s S S <;> simp
    · induction' T using WSeq.recOn' with s T T <;> simp
      · refine ⟨s, nil, T, ?_, ?_⟩ <;> simp
      · refine ⟨nil, nil, T, ?_, ?_⟩ <;> simp
    · exact ⟨s, S, T, rfl, rfl⟩
    · refine ⟨nil, S, T, ?_, ?_⟩ <;> simp
  · exact ⟨s, S, T, rfl, rfl⟩
  · exact ⟨s, S, T, rfl, rfl⟩
#align stream.wseq.join_append WSeq.join_append

@[simp]
theorem bind_pure (f : α → β) (s) : bind s (pure ∘ f) ≈ map f s := by
  dsimp [bind]
  rw [← map_map]
  apply join_map_pure
#align stream.wseq.bind_ret WSeq.bind_pure

@[simp]
theorem pure_bind (a : α) (f : α → WSeq β) : bind (pure a) f ≈ f a := by simp [bind]
#align stream.wseq.ret_bind WSeq.pure_bind

@[simp]
theorem map_join (f : α → β) (S) : map f (join S) = join (map (map f) S) := by
  ext1
  apply
    Seq'.eq_of_bisim fun s1 s2 =>
      ∃ s S, s1 = data (s ++ map f (join S)) ∧ s2 = data (s ++ join (map (map f) S))
  · intro s1 s2 h
    rcases h with ⟨s, S, rfl, rfl⟩
    induction' s using WSeq.recOn' with a s s <;> simp
    · induction' S using WSeq.recOn' with s S S <;> simp
      · exact ⟨map f s, S, rfl, rfl⟩
      · refine' ⟨nil, S, _, _⟩ <;> simp
    · exact ⟨_, _, rfl, rfl⟩
    · exact ⟨_, _, rfl, rfl⟩
  · refine' ⟨nil, S, _, _⟩ <;> simp
#align stream.wseq.map_join WSeq.map_join

@[simp]
theorem join_join (SS : WSeq (WSeq (WSeq α))) : join (join SS) ≈ join (map join SS) := by
  refine
    ⟨fun s1 s2 =>
      ∃ s S SS,
        s1 = s ++ join (S ++ join SS) ∧
          s2 = s ++ (join S ++ join (map join SS)),
      ⟨nil, nil, SS, by simp, by simp⟩, ?_⟩
  intro s1 s2 h
  apply
    liftRel_rec
      (fun c1 c2 =>
        ∃ s S SS,
          c1 = dest (s ++ join (S ++ join SS)) ∧
            c2 = dest (s ++ (join S ++ join (map join SS))))
      _ (dest s1) (dest s2)
      (let ⟨s, S, SS, h1, h2⟩ := h
      ⟨s, S, SS, by simp [h1], by simp [h2]⟩)
  intro c1 c2 h
  rcases h with ⟨s, S, SS, rfl, rfl⟩
  induction' s using WSeq.recOn' with a s s <;> simp
  · induction' S using WSeq.recOn' with s S S <;> simp
    · induction' SS using WSeq.recOn' with S SS SS <;> simp
      · refine ⟨nil, S, SS, ?_, ?_⟩ <;> simp
      · refine ⟨nil, nil, SS, ?_, ?_⟩ <;> simp
    · exact ⟨s, S, SS, rfl, rfl⟩
    · refine ⟨nil, S, SS, ?_, ?_⟩ <;> simp
  · exact ⟨s, S, SS, rfl, rfl⟩
  · exact ⟨s, S, SS, rfl, rfl⟩
#align stream.wseq.join_join WSeq.join_join

@[simp]
theorem bind_assoc (s : WSeq α) (f : α → WSeq β) (g : β → WSeq γ) :
    bind (bind s f) g ≈ bind s fun x : α => bind (f x) g := by
  simp [bind]; erw [← map_map join (map g ∘ f)]
  apply join_join
#align stream.wseq.bind_assoc WSeq.bind_assoc

instance monad : Monad WSeq where
  map := @map
  pure := @pure
  bind := @bind
#align stream.wseq.monad WSeq.monad

/-
  Unfortunately, `WSeq` is not a lawful monad, because it does not satisfy
  the monad laws exactly, only up to sequence equivalence.
  Furthermore, even quotienting by the equivalence is not sufficient,
  because the join operation involves lists of quotient elements,
  with a lifted equivalence relation, and pure quotients cannot handle
  this type of construction.

```lean
instance lawfulMonad : LawfulMonad WSeq :=
  { id_map := @map_id,
    bind_pure_comp := @bind_pure,
    pure_bind := @pure_bind,
    bind_assoc := @bind_assoc }
```
-/
end WSeq
