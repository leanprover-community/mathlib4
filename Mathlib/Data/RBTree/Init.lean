/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Mathlib.Mathport.Rename


-- This file used to be a part of `prelude`
universe u v

inductive RBNode (α : Type u) where
  | leaf : α → RBNode α
  | red_node (lchild : RBNode α) (val : α) (rchild : RBNode α ) : RBNode α
  | black_node (lchild : RBNode α) (val : α) (rchild : RBNode α) : RBNode α

#align rbnode RBNode

namespace RBNode

variable {α : Type u} {β : Type v}

inductive Color
  | red
  | black
#align rbnode.color RBNode.Color

open Color Nat

instance Color.decidableEq : DecidableEq Color := fun a b =>
  Color.casesOn a (Color.casesOn b (isTrue rfl) (isFalse fun h => Color.noConfusion h))
    (Color.casesOn b (isFalse fun h => Color.noConfusion h) (isTrue rfl))
#align rbnode.color.decidable_eq RBNode.Color.decidableEq

def depth (f : Nat → Nat → Nat) : RBNode α → Nat
  | leaf _ => 0
  | red_node l _ r => succ (f (depth f l) (depth f r))
  | black_node l _ r => succ (f (depth f l) (depth f r))
#align rbnode.depth RBNode.depth

protected def min : RBNode α → Option α
  | leaf _ => none
  | red_node (leaf _) v _ => some v
  | black_node (leaf _) v _ => some v
  | red_node l v _ => RBNode.min l
  | black_node l v _ => RBNode.min l
#align rbnode.min RBNode.min

protected def max : RBNode α → Option α
  | leaf _ => none
  | red_node _ v (leaf _) => some v
  | black_node _ v (leaf _) => some v
  | red_node _ v r => RBNode.max r
  | black_node _ v r => RBNode.max r
#align rbnode.max RBNode.max

def fold (f : α → β → β) : RBNode α → β → β
  | leaf _, b => b
  | red_node l v r, b => fold f r (f v (fold f l b))
  | black_node l v r, b => fold f r (f v (fold f l b))
#align rbnode.fold RBNode.fold

def revFold (f : α → β → β) : RBNode α → β → β
  | leaf _, b => b
  | red_node l v r, b => revFold f l (f v (revFold f r b))
  | black_node l v r, b => revFold f l (f v (revFold f r b))
#align rbnode.rev_fold RBNode.revFold

def balance1 : RBNode α → α → RBNode α → α → RBNode α → RBNode α
  | red_node l x r₁, y, r₂, v, t => red_node (black_node l x r₁) y (black_node r₂ v t)
  | l₁, y, red_node l₂ x r, v, t => red_node (black_node l₁ y l₂) x (black_node r v t)
  | l, y, r, v, t => black_node (red_node l y r) v t
#align rbnode.balance1 RBNode.balance1

def balance1Node : RBNode α → α → RBNode α → RBNode α
  | red_node l x r, v, t => balance1 l x r v t
  | black_node l x r, v, t => balance1 l x r v t
  | leaf _, v, t => t
#align rbnode.balance1_node RBNode.balance1Node

-- dummy value
def balance2 : RBNode α → α → RBNode α → α → RBNode α → RBNode α
  | red_node l x₁ r₁, y, r₂, v, t => red_node (black_node t v l) x₁ (black_node r₁ y r₂)
  | l₁, y, red_node l₂ x₂ r₂, v, t => red_node (black_node t v l₁) y (black_node l₂ x₂ r₂)
  | l, y, r, v, t => black_node t v (red_node l y r)
#align rbnode.balance2 RBNode.balance2

def balance2Node : RBNode α → α → RBNode α → RBNode α
  | red_node l x r, v, t => balance2 l x r v t
  | black_node l x r, v, t => balance2 l x r v t
  | leaf _, _, t => t
#align rbnode.balance2_node RBNode.balance2Node

-- dummy
def getColor : RBNode α → Color
  | red_node _ _ _ => red
  | _ => black
#align rbnode.get_color RBNode.getColor

section Insert

variable (lt : α → α → Prop) [DecidableRel lt]

def ins : RBNode α → α → RBNode α
  | leaf _, x => red_node (leaf _) x (leaf _)
  | red_node a y b, x =>
    match CmpUsing lt x y with
    | Ordering.lt => red_node (ins a x) y b
    | Ordering.eq => red_node a x b
    | Ordering.gt => red_node a y (ins b x)
  | black_node a y b, x =>
    match CmpUsing lt x y with
    | Ordering.lt => if a.getColor = red then balance1Node (ins a x) y b else black_node (ins a x) y b
    | Ordering.eq => black_node a x b
    | Ordering.gt => if b.getColor = red then balance2Node (ins b x) y a else black_node a y (ins b x)
#align rbnode.ins RBNode.ins

def mkInsertResult : Color → RBNode α → RBNode α
  | red, red_node l v r => black_node l v r
  | _, t => t
#align rbnode.mk_insert_result RBNode.mkInsertResult

def insert (t : RBNode α) (x : α) : RBNode α :=
  mkInsertResult (getColor t) (ins lt t x)
#align rbnode.insert RBNode.insert

end Insert

section Membership

variable (lt : α → α → Prop)

def Mem : α → RBNode α → Prop
  | _, leaf _ => False
  | a, red_node l v r => RBNode.Mem a l ∨ ¬lt a v ∧ ¬lt v a ∨ RBNode.Mem a r
  | a, black_node l v r => RBNode.Mem a l ∨ ¬lt a v ∧ ¬lt v a ∨ RBNode.Mem a r
#align rbnode.mem RBNode.Mem

def MemExact : α → RBNode α → Prop
  | _, leaf _ => False
  | a, red_node l v r => RBNode.MemExact a l ∨ a = v ∨ RBNode.MemExact a r
  | a, black_node l v r => RBNode.MemExact a l ∨ a = v ∨ RBNode.MemExact a r
#align rbnode.mem_exact RBNode.MemExact

variable [DecidableRel lt]

def find : RBNode α → α → Option α
  | leaf _, x => none
  | red_node a y b, x =>
    match CmpUsing lt x y with
    | Ordering.lt => find a x
    | Ordering.eq => some y
    | Ordering.gt => find b x
  | black_node a y b, x =>
    match CmpUsing lt x y with
    | Ordering.lt => find a x
    | Ordering.eq => some y
    | Ordering.gt => find b x
#align rbnode.find RBNode.find

end Membership

inductive WellFormed (lt : α → α → Prop) : RBNode α → Prop
  | leaf_wff : WellFormed lt (leaf _)
  | insert_wff {n n' : RBNode α} {x : α} [DecidableRel lt] : WellFormed lt n → n' = insert lt n x → WellFormed lt n'
#align rbnode.well_formed RBNode.WellFormed

end RBNode

open RBNode

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option auto_param.check_exists -/
set_option auto_param.check_exists false

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic rbtree.default_lt -/
def RBTree (α : Type u)
    (lt : α → α → Prop := by
      run_tac
        RBTree.default_lt) :
    Type u :=
  { t : RBNode α // t.WellFormed lt }
#align rbtree RBTree

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic rbtree.default_lt -/
def mkRBTree (α : Type u)
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt) :
    RBTree α lt :=
  ⟨leaf, WellFormed.leaf_wff⟩
#align mk_rbtree mkRBTree

namespace RBTree

variable {α : Type u} {β : Type v} {lt : α → α → Prop}

protected def Mem (a : α) (t : RBTree α lt) : Prop :=
  RBNode.Mem lt a t.val
#align rbtree.mem RBTree.Mem

instance : Membership α (RBTree α lt) :=
  ⟨RBTree.Mem⟩

def MemExact (a : α) (t : RBTree α lt) : Prop :=
  RBNode.MemExact a t.val
#align rbtree.mem_exact RBTree.MemExact

def depth (f : Nat → Nat → Nat) (t : RBTree α lt) : Nat :=
  t.val.depth f
#align rbtree.depth RBTree.depth

def fold (f : α → β → β) : RBTree α lt → β → β
  | ⟨t, _⟩, b => t.fold f b
#align rbtree.fold RBTree.fold

def revFold (f : α → β → β) : RBTree α lt → β → β
  | ⟨t, _⟩, b => t.revFold f b
#align rbtree.rev_fold RBTree.revFold

def empty : RBTree α lt → Bool
  | ⟨leaf _, _⟩ => true
  | _ => false
#align rbtree.empty RBTree.empty

def toList : RBTree α lt → List α
  | ⟨t, _⟩ => t.revFold (· :: ·) []
#align rbtree.to_list RBTree.toList

protected def min : RBTree α lt → Option α
  | ⟨t, _⟩ => t.min
#align rbtree.min RBTree.min

protected def max : RBTree α lt → Option α
  | ⟨t, _⟩ => t.max
#align rbtree.max RBTree.max

instance [Repr α] : Repr (RBTree α lt) :=
  ⟨fun t => "rbtree_of " ++ repr t.toList⟩

variable [DecidableRel lt]

def insert : RBTree α lt → α → RBTree α lt
  | ⟨t, w⟩, x => ⟨t.insert lt x, WellFormed.insert_wff w rfl⟩
#align rbtree.insert RBTree.insert

def find : RBTree α lt → α → Option α
  | ⟨t, _⟩, x => t.find lt x
#align rbtree.find RBTree.find

def contains (t : RBTree α lt) (a : α) : Bool :=
  (t.find a).isSome
#align rbtree.contains RBTree.contains

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic rbtree.default_lt -/
def fromList (l : List α)
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt)
    [DecidableRel lt] : RBTree α lt :=
  l.foldl insert (mkRBTree α lt)
#align rbtree.from_list RBTree.fromList

end RBTree

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic rbtree.default_lt -/
def rbtreeOf {α : Type u} (l : List α)
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt)
    [DecidableRel lt] : RBTree α lt :=
  RBTree.fromList l lt
#align rbtree_of rbtreeOf
