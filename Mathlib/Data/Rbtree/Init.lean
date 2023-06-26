/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module data.rbtree.init
! leanprover-community/mathlib commit fcc158e986d4896605e97fb3ad17d5cfed49a242
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

-- This file used to be a part of `prelude`
universe u v

inductive Rbnode (α : Type u)
  | leaf : Rbnode
  | red_node (lchild : Rbnode) (val : α) (rchild : Rbnode) : Rbnode
  | black_node (lchild : Rbnode) (val : α) (rchild : Rbnode) : Rbnode
#align rbnode Rbnode

namespace Rbnode

variable {α : Type u} {β : Type v}

inductive Color
  | red
  | black
#align rbnode.color Rbnode.Color

open Color Nat

instance Color.decidableEq : DecidableEq Color := fun a b =>
  Color.casesOn a (Color.casesOn b (isTrue rfl) (isFalse fun h => Color.noConfusion h))
    (Color.casesOn b (isFalse fun h => Color.noConfusion h) (isTrue rfl))
#align rbnode.color.decidable_eq Rbnode.Color.decidableEq

def depth (f : Nat → Nat → Nat) : Rbnode α → Nat
  | leaf => 0
  | red_node l _ r => succ (f (depth l) (depth r))
  | black_node l _ r => succ (f (depth l) (depth r))
#align rbnode.depth Rbnode.depth

protected def min : Rbnode α → Option α
  | leaf => none
  | red_node leaf v _ => some v
  | black_node leaf v _ => some v
  | red_node l v _ => min l
  | black_node l v _ => min l
#align rbnode.min Rbnode.min

protected def max : Rbnode α → Option α
  | leaf => none
  | red_node _ v leaf => some v
  | black_node _ v leaf => some v
  | red_node _ v r => max r
  | black_node _ v r => max r
#align rbnode.max Rbnode.max

def fold (f : α → β → β) : Rbnode α → β → β
  | leaf, b => b
  | red_node l v r, b => fold r (f v (fold l b))
  | black_node l v r, b => fold r (f v (fold l b))
#align rbnode.fold Rbnode.fold

def revFold (f : α → β → β) : Rbnode α → β → β
  | leaf, b => b
  | red_node l v r, b => rev_fold l (f v (rev_fold r b))
  | black_node l v r, b => rev_fold l (f v (rev_fold r b))
#align rbnode.rev_fold Rbnode.revFold

def balance1 : Rbnode α → α → Rbnode α → α → Rbnode α → Rbnode α
  | red_node l x r₁, y, r₂, v, t => red_node (black_node l x r₁) y (black_node r₂ v t)
  | l₁, y, red_node l₂ x r, v, t => red_node (black_node l₁ y l₂) x (black_node r v t)
  | l, y, r, v, t => black_node (red_node l y r) v t
#align rbnode.balance1 Rbnode.balance1

def balance1Node : Rbnode α → α → Rbnode α → Rbnode α
  | red_node l x r, v, t => balance1 l x r v t
  | black_node l x r, v, t => balance1 l x r v t
  | leaf, v, t => t
#align rbnode.balance1_node Rbnode.balance1Node

-- dummy value
def balance2 : Rbnode α → α → Rbnode α → α → Rbnode α → Rbnode α
  | red_node l x₁ r₁, y, r₂, v, t => red_node (black_node t v l) x₁ (black_node r₁ y r₂)
  | l₁, y, red_node l₂ x₂ r₂, v, t => red_node (black_node t v l₁) y (black_node l₂ x₂ r₂)
  | l, y, r, v, t => black_node t v (red_node l y r)
#align rbnode.balance2 Rbnode.balance2

def balance2Node : Rbnode α → α → Rbnode α → Rbnode α
  | red_node l x r, v, t => balance2 l x r v t
  | black_node l x r, v, t => balance2 l x r v t
  | leaf, v, t => t
#align rbnode.balance2_node Rbnode.balance2Node

-- dummy
def getColor : Rbnode α → Color
  | red_node _ _ _ => red
  | _ => black
#align rbnode.get_color Rbnode.getColor

section Insert

variable (lt : α → α → Prop) [DecidableRel lt]

def ins : Rbnode α → α → Rbnode α
  | leaf, x => red_node leaf x leaf
  | red_node a y b, x =>
    match cmpUsing lt x y with
    | Ordering.lt => red_node (ins a x) y b
    | Ordering.eq => red_node a x b
    | Ordering.gt => red_node a y (ins b x)
  | black_node a y b, x =>
    match cmpUsing lt x y with
    | Ordering.lt =>
      if a.getColor = red then balance1Node (ins a x) y b else black_node (ins a x) y b
    | Ordering.eq => black_node a x b
    | Ordering.gt =>
      if b.getColor = red then balance2Node (ins b x) y a else black_node a y (ins b x)
#align rbnode.ins Rbnode.ins

def mkInsertResult : Color → Rbnode α → Rbnode α
  | red, red_node l v r => black_node l v r
  | _, t => t
#align rbnode.mk_insert_result Rbnode.mkInsertResult

def insert (t : Rbnode α) (x : α) : Rbnode α :=
  mkInsertResult (getColor t) (ins lt t x)
#align rbnode.insert Rbnode.insert

end Insert

section Membership

variable (lt : α → α → Prop)

def Mem : α → Rbnode α → Prop
  | a, leaf => False
  | a, red_node l v r => mem a l ∨ ¬lt a v ∧ ¬lt v a ∨ mem a r
  | a, black_node l v r => mem a l ∨ ¬lt a v ∧ ¬lt v a ∨ mem a r
#align rbnode.mem Rbnode.Mem

def MemExact : α → Rbnode α → Prop
  | a, leaf => False
  | a, red_node l v r => mem_exact a l ∨ a = v ∨ mem_exact a r
  | a, black_node l v r => mem_exact a l ∨ a = v ∨ mem_exact a r
#align rbnode.mem_exact Rbnode.MemExact

variable [DecidableRel lt]

def find : Rbnode α → α → Option α
  | leaf, x => none
  | red_node a y b, x =>
    match cmpUsing lt x y with
    | Ordering.lt => find a x
    | Ordering.eq => some y
    | Ordering.gt => find b x
  | black_node a y b, x =>
    match cmpUsing lt x y with
    | Ordering.lt => find a x
    | Ordering.eq => some y
    | Ordering.gt => find b x
#align rbnode.find Rbnode.find

end Membership

inductive WellFormed (lt : α → α → Prop) : Rbnode α → Prop
  | leaf_wff : well_formed leaf
  |
  insert_wff {n n' : Rbnode α} {x : α} [DecidableRel lt] :
    well_formed n → n' = insert lt n x → well_formed n'
#align rbnode.well_formed Rbnode.WellFormed

end Rbnode

open Rbnode

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option auto_param.check_exists -/
set_option auto_param.check_exists false

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbtree.default_lt -/
def Rbtree (α : Type u)
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt) :
    Type u :=
  { t : Rbnode α // t.WellFormed lt }
#align rbtree Rbtree

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbtree.default_lt -/
def mkRbtree (α : Type u)
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt) :
    Rbtree α lt :=
  ⟨leaf, WellFormed.leaf_wff⟩
#align mk_rbtree mkRbtree

namespace Rbtree

variable {α : Type u} {β : Type v} {lt : α → α → Prop}

protected def Mem (a : α) (t : Rbtree α lt) : Prop :=
  Rbnode.Mem lt a t.val
#align rbtree.mem Rbtree.Mem

instance : Membership α (Rbtree α lt) :=
  ⟨Rbtree.Mem⟩

def MemExact (a : α) (t : Rbtree α lt) : Prop :=
  Rbnode.MemExact a t.val
#align rbtree.mem_exact Rbtree.MemExact

def depth (f : Nat → Nat → Nat) (t : Rbtree α lt) : Nat :=
  t.val.depth f
#align rbtree.depth Rbtree.depth

def fold (f : α → β → β) : Rbtree α lt → β → β
  | ⟨t, _⟩, b => t.fold f b
#align rbtree.fold Rbtree.fold

def revFold (f : α → β → β) : Rbtree α lt → β → β
  | ⟨t, _⟩, b => t.revFold f b
#align rbtree.rev_fold Rbtree.revFold

def empty : Rbtree α lt → Bool
  | ⟨leaf, _⟩ => true
  | _ => false
#align rbtree.empty Rbtree.empty

def toList : Rbtree α lt → List α
  | ⟨t, _⟩ => t.revFold (· :: ·) []
#align rbtree.to_list Rbtree.toList

protected def min : Rbtree α lt → Option α
  | ⟨t, _⟩ => t.min
#align rbtree.min Rbtree.min

protected def max : Rbtree α lt → Option α
  | ⟨t, _⟩ => t.max
#align rbtree.max Rbtree.max

instance [Repr α] : Repr (Rbtree α lt) :=
  ⟨fun t => "rbtree_of " ++ repr t.toList⟩

variable [DecidableRel lt]

def insert : Rbtree α lt → α → Rbtree α lt
  | ⟨t, w⟩, x => ⟨t.insert lt x, WellFormed.insert_wff w rfl⟩
#align rbtree.insert Rbtree.insert

def find : Rbtree α lt → α → Option α
  | ⟨t, _⟩, x => t.find lt x
#align rbtree.find Rbtree.find

def contains (t : Rbtree α lt) (a : α) : Bool :=
  (t.find a).isSome
#align rbtree.contains Rbtree.contains

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbtree.default_lt -/
def fromList (l : List α)
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt)
    [DecidableRel lt] : Rbtree α lt :=
  l.foldl insert (mkRbtree α lt)
#align rbtree.from_list Rbtree.fromList

end Rbtree

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbtree.default_lt -/
def rbtreeOf {α : Type u} (l : List α)
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt)
    [DecidableRel lt] : Rbtree α lt :=
  Rbtree.fromList l lt
#align rbtree_of rbtreeOf

