/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Control.Traversable.Equiv
import Mathlib.Control.Traversable.Instances
import Batteries.Data.LazyList
import Mathlib.Lean.Thunk

#align_import data.lazy_list.basic from "leanprover-community/mathlib"@"1f0096e6caa61e9c849ec2adbd227e960e9dff58"

/-!
## Definitions on lazy lists

This file contains various definitions and proofs on lazy lists.

TODO: move the `LazyList.lean` file from core to mathlib.
-/


universe u

namespace LazyList

open Function

/-- Isomorphism between strict and lazy lists. -/
def listEquivLazyList (α : Type*) : List α ≃ LazyList α where
  toFun := LazyList.ofList
  invFun := LazyList.toList
  right_inv := by
    intro xs
    induction xs using toList.induct
    · simp [toList, ofList]
    · simp [toList, ofList, *]; rfl
  left_inv := by
    intro xs
    induction xs
    · simp [toList, ofList]
    · simpa [ofList, toList]
#align lazy_list.list_equiv_lazy_list LazyList.listEquivLazyList

-- Porting note: Added a name to make the recursion work.
instance decidableEq {α : Type u} [DecidableEq α] : DecidableEq (LazyList α)
  | nil, nil => isTrue rfl
  | cons x xs, cons y ys =>
    if h : x = y then
      match decidableEq xs.get ys.get with
      | isFalse h2 => by
        apply isFalse; simp only [cons.injEq, not_and]; intro _ xs_ys; apply h2; rw [xs_ys]
      | isTrue h2 => by apply isTrue; congr; ext; exact h2
    else by apply isFalse; simp only [cons.injEq, not_and]; intro; contradiction
  | nil, cons _ _ => by apply isFalse; simp
  | cons _ _, nil => by apply isFalse; simp

/-- Traversal of lazy lists using an applicative effect. -/
protected def traverse {m : Type u → Type u} [Applicative m] {α β : Type u} (f : α → m β) :
    LazyList α → m (LazyList β)
  | LazyList.nil => pure LazyList.nil
  | LazyList.cons x xs => LazyList.cons <$> f x <*> Thunk.pure <$> xs.get.traverse f
#align lazy_list.traverse LazyList.traverse

instance : Traversable LazyList where
  map := @LazyList.traverse Id _
  traverse := @LazyList.traverse

instance : LawfulTraversable LazyList := by
  apply Equiv.isLawfulTraversable' listEquivLazyList <;> intros <;> ext <;> rename_i f xs
  · induction' xs using LazyList.rec with _ _ _ _ ih
    · simp only [Functor.map, LazyList.traverse, pure, Equiv.map, listEquivLazyList,
        Equiv.coe_fn_symm_mk, toList, Equiv.coe_fn_mk, ofList]
    · simpa only [Equiv.map, Functor.map, listEquivLazyList, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk,
        LazyList.traverse, Seq.seq, toList, ofList, cons.injEq, true_and]
    · ext; apply ih
  · simp only [Equiv.map, listEquivLazyList, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, comp,
      Functor.mapConst]
    induction' xs using LazyList.rec with _ _ _ _ ih
    · simp only [LazyList.traverse, pure, Functor.map, toList, ofList]
    · simpa only [toList, ofList, LazyList.traverse, Seq.seq, Functor.map, cons.injEq, true_and]
    · congr; apply ih
  · simp only [traverse, Equiv.traverse, listEquivLazyList, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
    induction' xs using LazyList.rec with _ tl ih _ ih
    · simp only [LazyList.traverse, toList, List.traverse, map_pure, ofList]
    · replace ih : tl.get.traverse f = ofList <$> tl.get.toList.traverse f := ih
      simp [traverse.eq_2, ih, Functor.map_map, seq_map_assoc, toList, List.traverse, map_seq,
        Function.comp, Thunk.pure, ofList]
    · apply ih

/-- `init xs`, if `xs` non-empty, drops the last element of the list.
Otherwise, return the empty list. -/
def init {α} : LazyList α → LazyList α
  | LazyList.nil => LazyList.nil
  | LazyList.cons x xs =>
    let xs' := xs.get
    match xs' with
    | LazyList.nil => LazyList.nil
    | LazyList.cons _ _ => LazyList.cons x (init xs')
#align lazy_list.init LazyList.init

/-- Return the first object contained in the list that satisfies
predicate `p` -/
def find {α} (p : α → Prop) [DecidablePred p] : LazyList α → Option α
  | nil => none
  | cons h t => if p h then some h else t.get.find p
#align lazy_list.find LazyList.find

/-- `interleave xs ys` creates a list where elements of `xs` and `ys` alternate. -/
def interleave {α} : LazyList α → LazyList α → LazyList α
  | LazyList.nil, xs => xs
  | a@(LazyList.cons _ _), LazyList.nil => a
  | LazyList.cons x xs, LazyList.cons y ys =>
    LazyList.cons x (LazyList.cons y (interleave xs.get ys.get))
#align lazy_list.interleave LazyList.interleave

/-- `interleaveAll (xs::ys::zs::xss)` creates a list where elements of `xs`, `ys`
and `zs` and the rest alternate. Every other element of the resulting list is taken from
`xs`, every fourth is taken from `ys`, every eighth is taken from `zs` and so on. -/
def interleaveAll {α} : List (LazyList α) → LazyList α
  | [] => LazyList.nil
  | x :: xs => interleave x (interleaveAll xs)
#align lazy_list.interleave_all LazyList.interleaveAll

/-- Monadic bind operation for `LazyList`. -/
protected def bind {α β} : LazyList α → (α → LazyList β) → LazyList β
  | LazyList.nil, _ => LazyList.nil
  | LazyList.cons x xs, f => (f x).append (xs.get.bind f)
#align lazy_list.bind LazyList.bind

/-- Reverse the order of a `LazyList`.
It is done by converting to a `List` first because reversal involves evaluating all
the list and if the list is all evaluated, `List` is a better representation for
it than a series of thunks. -/
def reverse {α} (xs : LazyList α) : LazyList α :=
  ofList xs.toList.reverse
#align lazy_list.reverse LazyList.reverse

instance : Monad LazyList where
  pure := @LazyList.singleton
  bind := @LazyList.bind

-- Porting note: Added `Thunk.pure` to definition.
theorem append_nil {α} (xs : LazyList α) : xs.append (Thunk.pure LazyList.nil) = xs := by
  induction' xs using LazyList.rec with _ _ _ _ ih
  · simp only [Thunk.pure, append, Thunk.get]
  · simpa only [append, cons.injEq, true_and]
  · ext; apply ih
#align lazy_list.append_nil LazyList.append_nil

theorem append_assoc {α} (xs ys zs : LazyList α) :
    (xs.append ys).append zs = xs.append (ys.append zs) := by
  induction' xs using LazyList.rec with _ _ _ _ ih
  · simp only [append, Thunk.get]
  · simpa only [append, cons.injEq, true_and]
  · ext; apply ih
#align lazy_list.append_assoc LazyList.append_assoc

-- Porting note: Rewrote proof of `append_bind`.
theorem append_bind {α β} (xs : LazyList α) (ys : Thunk (LazyList α)) (f : α → LazyList β) :
    (xs.append ys).bind f = (xs.bind f).append (ys.get.bind f) := by
  match xs with
  | LazyList.nil =>
    simp only [append, Thunk.get, LazyList.bind]
  | LazyList.cons x xs =>
    simp only [append, Thunk.get, LazyList.bind]
    have := append_bind xs.get ys f
    simp only [Thunk.get] at this
    rw [this, append_assoc]
#align lazy_list.append_bind LazyList.append_bind

instance : LawfulMonad LazyList := LawfulMonad.mk'
  (bind_pure_comp := by
    intro _ _ f xs
    simp only [bind, Functor.map, pure, singleton]
    induction xs using LazyList.traverse.induct (m := @Id) (f := f)
    case case1 =>
      simp only [Thunk.pure, LazyList.bind, LazyList.traverse, Id.pure_eq]
    case case2 ih =>
      simp only [LazyList.bind, LazyList.traverse, Seq.seq, Id.map_eq, append, Thunk.pure]
      rw [← ih]
      simp [Thunk.pure, Thunk.get, append])
  (pure_bind := by
    intros
    simp only [bind, pure, singleton, LazyList.bind, append, Thunk.pure, Thunk.get]
    apply append_nil)
  (bind_assoc := by
    intro _ _ _ xs _ _
    induction' xs using LazyList.rec with _ _ _ _ ih
    · simp only [bind, LazyList.bind]
    · simp only [bind, LazyList.bind, append_bind]; congr
    · congr; funext; apply ih)
  (id_map := by
    intro _ xs
    induction' xs using LazyList.rec with _ _ _ _ ih
    · simp only [Functor.map, LazyList.traverse, pure]
    · simpa only [Functor.map, traverse.eq_2, id_eq, Id.map_eq, Seq.seq, cons.injEq, true_and]
    · ext; apply ih)

-- Porting note: This is a dubious translation. In the warning, u1 and u3 are swapped.
/-- Try applying function `f` to every element of a `LazyList` and
return the result of the first attempt that succeeds. -/
def mfirst {m} [Alternative m] {α β} (f : α → m β) : LazyList α → m β
  | nil => failure
  | cons x xs => f x <|> xs.get.mfirst f
#align lazy_list.mfirst LazyList.mfirstₓ

/-- Membership in lazy lists -/
protected def Mem {α} (x : α) : LazyList α → Prop
  | nil => False
  | cons y ys => x = y ∨ ys.get.Mem x
#align lazy_list.mem LazyList.Mem

instance {α} : Membership α (LazyList α) :=
  ⟨LazyList.Mem⟩

instance Mem.decidable {α} [DecidableEq α] (x : α) : ∀ xs : LazyList α, Decidable (x ∈ xs)
  | LazyList.nil => by
    apply Decidable.isFalse
    simp [Membership.mem, LazyList.Mem]
  | LazyList.cons y ys =>
    if h : x = y then by
      apply Decidable.isTrue
      simp only [Membership.mem, LazyList.Mem]
      exact Or.inl h
    else by
      have := Mem.decidable x ys.get
      have : (x ∈ ys.get) ↔ (x ∈ cons y ys) := by simp [(· ∈ ·), LazyList.Mem, h]
      exact decidable_of_decidable_of_iff this
#align lazy_list.mem.decidable LazyList.Mem.decidable

@[simp]
theorem mem_nil {α} (x : α) : x ∈ @LazyList.nil α ↔ False := by
  simp [Membership.mem, LazyList.Mem]
#align lazy_list.mem_nil LazyList.mem_nil

@[simp]
theorem mem_cons {α} (x y : α) (ys : Thunk (LazyList α)) :
    x ∈ @LazyList.cons α y ys ↔ x = y ∨ x ∈ ys.get := by
  simp [Membership.mem, LazyList.Mem]
#align lazy_list.mem_cons LazyList.mem_cons

theorem forall_mem_cons {α} {p : α → Prop} {a : α} {l : Thunk (LazyList α)} :
    (∀ x ∈ @LazyList.cons _ a l, p x) ↔ p a ∧ ∀ x ∈ l.get, p x := by
  simp only [Membership.mem, LazyList.Mem, or_imp, forall_and, forall_eq]
#align lazy_list.forall_mem_cons LazyList.forall_mem_cons

/-! ### map for partial functions -/


/-- Partial map. If `f : ∀ a, p a → β` is a partial function defined on
  `a : α` satisfying `p`, then `pmap f l h` is essentially the same as `map f l`
  but is defined only when all members of `l` satisfy `p`, using the proof
  to apply `f`. -/
@[simp]
def pmap {α β} {p : α → Prop} (f : ∀ a, p a → β) : ∀ l : LazyList α, (∀ a ∈ l, p a) → LazyList β
  | LazyList.nil, _ => LazyList.nil
  | LazyList.cons x xs, H =>
    LazyList.cons (f x (forall_mem_cons.1 H).1) (xs.get.pmap f (forall_mem_cons.1 H).2)
#align lazy_list.pmap LazyList.pmap

/-- "Attach" the proof that the elements of `l` are in `l` to produce a new `LazyList`
  with the same elements but in the type `{x // x ∈ l}`. -/
def attach {α} (l : LazyList α) : LazyList { x // x ∈ l } :=
  pmap Subtype.mk l fun _ ↦ id
#align lazy_list.attach LazyList.attach

instance {α} [Repr α] : Repr (LazyList α) :=
  ⟨fun xs _ ↦ repr xs.toList⟩

end LazyList
