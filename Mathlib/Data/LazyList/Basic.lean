/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module data.lazy_list.basic
! leanprover-community/mathlib commit 1f0096e6caa61e9c849ec2adbd227e960e9dff58
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

-- Porting note: `Thunk.pure` appears to do the same thing
#align thunk.mk Thunk.pure

-- Porting note: Added `Thunk.ext` to get `ext` tactic to work
@[ext]
theorem ext {α : Type u} {a b : Thunk α} (eq : a.get = b.get) : a = b := by
  have ⟨_⟩ := a
  have ⟨_⟩ := b
  congr
  exact funext fun _ ↦ eq

instance {α : Type u} [DecidableEq α] : DecidableEq (Thunk α) := by
  intro a b
  have : a = b ↔ a.get = b.get := ⟨by intro x; rw [x], by intro; ext; assumption⟩
  rw [this]
  infer_instance

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
    induction x using LazyList.rec
    rfl
    simpa [toList, ofList]
    rename_i ih; rw [Thunk.get, ih]
  left_inv := by
    intro x
    induction x
    rfl
    simpa [ofList, toList]
#align lazy_list.list_equiv_lazy_list LazyList.listEquivLazyList

-- Porting note: Added a name to make the recursion work
instance decidableEq {α : Type u} [DecidableEq α] : DecidableEq (LazyList α)
  | nil, nil => isTrue rfl
  | cons x xs, cons y ys =>
    if h : x = y then
      match decidableEq xs.get ys.get with
      | isFalse h2 => by apply isFalse; simp; intro _ xs_ys; apply h2; rw [xs_ys]
      | isTrue h2 => by apply isTrue; congr; ext; exact h2
    else by apply isFalse; simp; intro; contradiction
  | nil, cons _ _ => by apply isFalse; simp
  | cons _ _, nil => by apply isFalse; simp

/-- Traversal of lazy lists using an applicative effect. -/
protected def traverse {m : Type u → Type u} [Applicative m] {α β : Type u} (f : α → m β) :
    LazyList α → m (LazyList β)
  | LazyList.nil => pure LazyList.nil
  | LazyList.cons x xs => LazyList.cons <$> f x <*> Thunk.pure <$> xs.get.traverse f
#align lazy_list.traverse LazyList.traverse

instance : Traversable LazyList
    where
  map := @LazyList.traverse Id _
  traverse := @LazyList.traverse

instance : IsLawfulTraversable LazyList := by
  apply Equiv.isLawfulTraversable' listEquivLazyList <;> intros <;> ext <;> rename_i f x
  · induction x using LazyList.rec
    rfl
    simpa [Equiv.map, Functor.map, listEquivLazyList, toList, ofList, LazyList.traverse, Seq.seq]
    rename_i ih; ext; apply ih
  · induction x using LazyList.rec
    rfl
    simpa [Equiv.map, Functor.mapConst, listEquivLazyList, toList, LazyList.traverse]
    rename_i ih; simp [Seq.seq]; congr; simp [Equiv.map] at ih; apply ih
  · simp [traverse, Equiv.traverse, listEquivLazyList]
    induction x using LazyList.rec
    simp [List.traverse]; rfl
    rename_i tl ih
    have : tl.get.traverse f = ofList <$> tl.get.toList.traverse f := ih
    simp [toList, List.traverse, functor_norm, LazyList.traverse, ih]
    rfl
    rename_i ih; apply ih

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
  | LazyList.cons x xs, f => (f x).append (xs.get.bind f)
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

-- Porting note: Added `Thunk.pure` to definition
theorem append_nil {α} (xs : LazyList α) : xs.append (Thunk.pure LazyList.nil) = xs := by
  induction xs using LazyList.rec; rfl
  simp [LazyList.append, xs_ih]
  ext; congr
#align lazy_list.append_nil LazyList.append_nil

theorem append_assoc {α} (xs ys zs : LazyList α) :
    (xs.append ys).append zs = xs.append (ys.append zs) := by
  induction xs using LazyList.rec <;> simp [append, *]
#align lazy_list.append_assoc LazyList.append_assoc

theorem append_bind {α β} (xs : LazyList α) (ys : Thunk (LazyList α)) (f : α → LazyList β) :
    (xs.append ys).bind f = (xs.bind f).append (ys.get.bind f) := by
  induction xs using LazyList.rec <;> simp [LazyList.bind, append, *, append_assoc, append, LazyList.bind]
#align lazy_list.append_bind LazyList.append_bind

instance : LawfulMonad LazyList
    where
  pure_bind := by
    intros
    apply append_nil
  bind_assoc := by
    intros
    dsimp [(· >>= ·)]
    induction x <;> simp [LazyList.bind, append_bind, *]
  id_map := by
    intros
    simp [(· <$> ·)]
    induction x <;> simp [LazyList.bind, *, singleton, append]
    ext ⟨⟩; rfl

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
  | cons x xs => f x <|> xs.get.mfirst f
#align lazy_list.mfirst LazyList.mfirst

/-- Membership in lazy lists -/
protected def Mem {α} (x : α) : LazyList α → Prop
  | nil => False
  | cons y ys => x = y ∨ ys.get.Mem x
#align lazy_list.mem LazyList.Mem

instance {α} : Membership α (LazyList α) :=
  ⟨LazyList.Mem⟩

instance Mem.decidable {α} [DecidableEq α] (x : α) : ∀ xs : LazyList α, Decidable (x ∈ xs)
  | LazyList.nil => Decidable.false
  | LazyList.cons y ys =>
    if h : x = y then Decidable.isTrue (Or.inl h)
    else decidable_of_decidable_of_iff (Mem.decidable ys.get) (by simp [*, (· ∈ ·), LazyList.Mem])
#align lazy_list.mem.decidable LazyList.Mem.decidable

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
  simp only [Membership.mem, LazyList.Mem, or_imp, forall_and, forall_eq]
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
    LazyList.cons (f x (forall_mem_cons.1 H).1) (xs.get.pmap f (forall_mem_cons.1 H).2)
#align lazy_list.pmap LazyList.pmap

/-- "Attach" the proof that the elements of `l` are in `l` to produce a new `lazy_list`
  with the same elements but in the type `{x // x ∈ l}`. -/
def attach {α} (l : LazyList α) : LazyList { x // x ∈ l } :=
  pmap Subtype.mk l fun _ ↦ id
#align lazy_list.attach LazyList.attach

instance {α} [Repr α] : Repr (LazyList α) :=
  ⟨fun xs _ ↦ repr xs.toList⟩

end LazyList
