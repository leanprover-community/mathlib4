/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module data.lazy_list.basic
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Control.Traversable.Equiv
import Mathlib.Control.Traversable.Instances
import Mathlib.Data.LazyList

/-!
## Definitions on lazy lists

This file contains various definitions and proofs on lazy lists.

TODO: move the `lazy_list.lean` file from core to mathlib.
-/


universe u

namespace Thunk

#noalign thunk.mk

instance {α : Type u} [DecidableEq α] : DecidableEq (Thunk α)
  | a, b =>
    by
    have : a = b ↔ a.get = b.get := ⟨
      by intro x; rw [x],
      by intro ; ext x ; cases x ; assumption⟩
    rw [this] <;> infer_instance

end Thunk

namespace LazyList

open Function

/-- Isomorphism between strict and lazy lists. -/
def listEquivLazyList (α : Type _) : List α ≃ LazyList α
    where
  toFun := LazyList.ofList
  invFun := LazyList.toList
  right_inv := by
    intro x
    induction x using LazyList.rec with
    | nil => rfl
    | cons => simpa [LazyList.toList, LazyList.ofList]
    | mk _ ih => simp [Thunk.get, ih ()]
  left_inv := by
    intro x
    induction x
    rfl
    simpa [LazyList.ofList, LazyList.toList]
#align lazy_list.list_equiv_lazy_list LazyList.listEquivLazyList

instance {α : Type u} [DecidableEq α] : DecidableEq (LazyList α)
  | nil, nil => isTrue rfl
  | cons x xs, cons y ys =>
    if h : x = y then
      match DecidableEq xs.get ys.get with
      | isFalse h2 => isFalse (by intro <;> cc)
      | isTrue h2 =>
        have : xs = ys := by ext u <;> cases u <;> assumption
        isTrue (by cc)
    else isFalse (by intro <;> cc)
  | nil, cons _ _ => isFalse (by cc)
  | cons _ _, nil => isFalse (by cc)

/-- Traversal of lazy lists using an applicative effect. -/
protected def traverse {m : Type u → Type u} [Applicative m] {α β : Type u} (f : α → m β) :
    LazyList α → m (LazyList β)
  | LazyList.nil => pure LazyList.nil
  | LazyList.cons x xs => LazyList.cons <$> f x <*> Thunk.mk <$> traverse xs.get
#align lazy_list.traverse LazyList.traverse

instance : Traversable LazyList
    where
  map := @LazyList.traverse Id _
  traverse := @LazyList.traverse

instance : IsLawfulTraversable LazyList := by
  apply Equiv.isLawfulTraversable' listEquivLazyList <;> intros <;> skip <;> ext
  · induction x
    rfl
    simp! [Equiv.map, Functor.map] at *
    simp [*]
    rfl
  · induction x
    rfl
    simp! [Equiv.map, Functor.mapConst] at *
    simp [*]
    rfl
  · induction x
    · simp! [Traversable.traverse, Equiv.traverse, functor_norm]
      rfl
    simp! [Equiv.map, Functor.mapConst, Traversable.traverse] at *
    rw [x_ih]
    dsimp [listEquivLazyList, Equiv.traverse, to_list, Traversable.traverse, List.traverse]
    simp! [functor_norm]
    rfl

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
  | cons h t => if p h then some h else find p t.get
#align lazy_list.find LazyList.find

/-- `interleave xs ys` creates a list where elements of `xs` and `ys` alternate. -/
def interleave {α} : LazyList α → LazyList α → LazyList α
  | LazyList.nil, xs => xs
  | a@(LazyList.cons x xs), LazyList.nil => a
  | LazyList.cons x xs, LazyList.cons y ys =>
    LazyList.cons x (LazyList.cons y (interleave xs.get ys.get))
#align lazy_list.interleave LazyList.interleave

/-- `interleave_all (xs::ys::zs::xss)` creates a list where elements of `xs`, `ys`
and `zs` and the rest alternate. Every other element of the resulting list is taken from
`xs`, every fourth is taken from `ys`, every eighth is taken from `zs` and so on. -/
def interleaveAll {α} : List (LazyList α) → LazyList α
  | [] => LazyList.nil
  | x :: xs => interleave x (interleaveAll xs)
#align lazy_list.interleave_all LazyList.interleaveAll

/-- Monadic bind operation for `lazy_list`. -/
protected def bind {α β} : LazyList α → (α → LazyList β) → LazyList β
  | LazyList.nil, _ => LazyList.nil
  | LazyList.cons x xs, f => LazyList.append (f x) (LazyList.bind xs.get f)
#align lazy_list.bind LazyList.bind

/-- Reverse the order of a `lazy_list`.
It is done by converting to a `list` first because reversal involves evaluating all
the list and if the list is all evaluated, `list` is a better representation for
it than a series of thunks. -/
def reverse {α} (xs : LazyList α) : LazyList α :=
  ofList xs.toList.reverse
#align lazy_list.reverse LazyList.reverse

instance : Monad LazyList where
  pure := @LazyList.singleton
  bind := @LazyList.bind

theorem append_nil {α} (xs : LazyList α) : xs.append (Thunk.pure LazyList.nil) = xs := by
  induction xs; rfl
  simp [LazyList.append, xs_ih]
  ext; congr
#align lazy_list.append_nil LazyList.append_nil

theorem append_assoc {α} (xs ys zs : LazyList α) :
    (xs.append ys).append zs = xs.append (ys.append zs) := by induction xs <;> simp [append, *]
#align lazy_list.append_assoc LazyList.append_assoc

theorem append_bind {α β} (xs : LazyList α) (ys : Thunk (LazyList α)) (f : α → LazyList β) :
    (@LazyList.append _ xs ys).bind f = (xs.bind f).append (ys.get.bind f) := by
  induction xs <;> simp [LazyList.bind, append, *, append_assoc, append, LazyList.bind]
#align lazy_list.append_bind LazyList.append_bind

instance : LawfulMonad LazyList := LawfulMonad.mk'
  (bind_pure_comp := sorry)
  (pure_bind := by
    intros
    apply append_nil)
  (bind_assoc := by
    intros
    dsimp [(· >>= ·)]
    induction x <;> simp [LazyList.bind, append_bind, *])
  (id_map := by
    intros
    simp [(· <$> ·)]
    induction x <;> simp [LazyList.bind, *, singleton, append]
    ext ⟨⟩; rfl)

/- warning: lazy_list.mfirst -> LazyList.mfirst is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Alternative.{u1, u2} m] {α : Type.{u3}} {β : Type.{u1}}, (α -> (m β)) -> (LazyList.{u3} α) -> (m β)
but is expected to have type
  forall {m : Type.{u3} -> Type.{u2}} [_inst_1 : Alternative.{u3, u2} m] {α : Type.{u1}} {β : Type.{u3}}, (α -> (m β)) -> (LazyList.{u1} α) -> (m β)
Case conversion may be inaccurate. Consider using '#align lazy_list.mfirst LazyList.mfirstₓ'. -/
/-- Try applying function `f` to every element of a `lazy_list` and
return the result of the first attempt that succeeds. -/
def mfirst {m} [Alternative m] {α β} (f : α → m β) : LazyList α → m β
  | nil => failure
  | cons x xs => f x <|> LazyList.mfirst f xs.get
#align lazy_list.mfirst LazyList.mfirst

/-- Membership in lazy lists -/
protected def mem {α} (x : α) : LazyList α → Prop
  | LazyList.nil => False
  | LazyList.cons y ys => x = y ∨ LazyList.mem x ys.get
#align lazy_list.mem LazyList.mem

instance {α} : Membership α (LazyList α) :=
  ⟨LazyList.mem⟩

instance mem.decidable {α} [DecidableEq α] (x : α) : ∀ xs : LazyList α, Decidable (x ∈ xs)
  | LazyList.nil => by
    apply Decidable.isFalse
    simp [Membership.mem, LazyList.mem]
  | LazyList.cons y ys =>
    if h : x = y then by
      apply Decidable.isTrue
      simp [Membership.mem, LazyList.mem]
      exact Or.inl h
    else by
      have := mem.decidable x ys.get
      have : (x ∈ ys.get) ↔ (x ∈ cons y ys) := by simp [(· ∈ ·), LazyList.mem, h]
      exact decidable_of_decidable_of_iff this
#align lazy_list.mem.decidable LazyList.mem.decidable

@[simp]
theorem mem_nil {α} (x : α) : x ∈ @LazyList.nil α ↔ False :=
  Iff.rfl
#align lazy_list.mem_nil LazyList.mem_nil

@[simp]
theorem mem_cons {α} (x y : α) (ys : Thunk (LazyList α)) :
    x ∈ @LazyList.cons α y ys ↔ x = y ∨ x ∈ ys.get :=
  Iff.rfl
#align lazy_list.mem_cons LazyList.mem_cons

theorem forall_mem_cons {α} {p : α → Prop} {a : α} {l : Thunk (LazyList α)} :
    (∀ x ∈ @LazyList.cons _ a l, p x) ↔ p a ∧ ∀ x ∈ l.get, p x := by
  simp only [Membership.mem, LazyList.mem, or_imp, forall_and, forall_eq]
#align lazy_list.forall_mem_cons LazyList.forall_mem_cons

/-! ### map for partial functions -/


/-- Partial map. If `f : Π a, p a → β` is a partial function defined on
  `a : α` satisfying `p`, then `pmap f l h` is essentially the same as `map f l`
  but is defined only when all members of `l` satisfy `p`, using the proof
  to apply `f`. -/
@[simp]
def pmap {α β} {p : α → Prop} (f : ∀ a, p a → β) : ∀ l : LazyList α, (∀ a ∈ l, p a) → LazyList β
  | LazyList.nil, H => LazyList.nil
  | LazyList.cons x xs, H =>
    LazyList.cons (f x (forall_mem_cons.1 H).1) (pmap f xs.get (forall_mem_cons.1 H).2)
#align lazy_list.pmap LazyList.pmap

/-- "Attach" the proof that the elements of `l` are in `l` to produce a new `lazy_list`
  with the same elements but in the type `{x // x ∈ l}`. -/
def attach {α} (l : LazyList α) : LazyList { x // x ∈ l } :=
  pmap Subtype.mk l fun a => id
#align lazy_list.attach LazyList.attach

instance {α} [Repr α] : Repr (LazyList α) :=
  ⟨fun xs => repr xs.toList⟩

end LazyList
