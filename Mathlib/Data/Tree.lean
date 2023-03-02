/-
Copyright (c) 2019 mathlib community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Wojciech Nawrocki

! This file was ported from Lean 3 source module data.tree
! leanprover-community/mathlib commit ed989ff568099019c6533a4d94b27d852a5710d8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Rbtree.Init
import Mathbin.Data.Num.Basic
import Mathbin.Order.Basic

/-!
# Binary tree

Provides binary tree storage for values of any type, with O(lg n) retrieval.
See also `data.rbtree` for red-black trees - this version allows more operations
to be defined and is better suited for in-kernel computation.

We also specialize for `tree unit`, which is a binary tree without any
additional data. We provide the notation `a △ b` for making a `tree unit` with children
`a` and `b`.

## References

<https://leanprover-community.github.io/archive/stream/113488-general/topic/tactic.20question.html>
-/


/-- A binary tree with values stored in non-leaf nodes. -/
inductive Tree.{u} (α : Type u) : Type u
  | nil : Tree
  | node : α → Tree → Tree → Tree
  deriving has_reflect, DecidableEq
#align tree Tree

namespace Tree

universe u

variable {α : Type u}

/-- Construct a string representation of a tree. Provides a `has_repr` instance. -/
def repr [Repr α] : Tree α → String
  | nil => "nil"
  | node a t1 t2 => "tree.node " ++ Repr.repr a ++ " (" ++ repr t1 ++ ") (" ++ repr t2 ++ ")"
#align tree.repr Tree.repr

instance [Repr α] : Repr (Tree α) :=
  ⟨Tree.repr⟩

instance : Inhabited (Tree α) :=
  ⟨nil⟩

/-- Makes a `tree α` out of a red-black tree. -/
def ofRbnode : Rbnode α → Tree α
  | Rbnode.leaf => nil
  | Rbnode.red_node l a r => node a (of_rbnode l) (of_rbnode r)
  | Rbnode.black_node l a r => node a (of_rbnode l) (of_rbnode r)
#align tree.of_rbnode Tree.ofRbnode

/-- Finds the index of an element in the tree assuming the tree has been
constructed according to the provided decidable order on its elements.
If it hasn't, the result will be incorrect. If it has, but the element
is not in the tree, returns none. -/
def indexOf (lt : α → α → Prop) [DecidableRel lt] (x : α) : Tree α → Option PosNum
  | nil => none
  | node a t₁ t₂ =>
    match cmpUsing lt x a with
    | Ordering.lt => PosNum.bit0 <$> index_of t₁
    | Ordering.eq => some PosNum.one
    | Ordering.gt => PosNum.bit1 <$> index_of t₂
#align tree.index_of Tree.indexOf

/-- Retrieves an element uniquely determined by a `pos_num` from the tree,
taking the following path to get to the element:
- `bit0` - go to left child
- `bit1` - go to right child
- `pos_num.one` - retrieve from here -/
def get : PosNum → Tree α → Option α
  | _, nil => none
  | PosNum.one, node a t₁ t₂ => some a
  | PosNum.bit0 n, node a t₁ t₂ => t₁.get n
  | PosNum.bit1 n, node a t₁ t₂ => t₂.get n
#align tree.get Tree.get

/-- Retrieves an element from the tree, or the provided default value
if the index is invalid. See `tree.get`. -/
def getOrElse (n : PosNum) (t : Tree α) (v : α) : α :=
  (t.get n).getD v
#align tree.get_or_else Tree.getOrElse

/- warning: tree.map -> Tree.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, (α -> β) -> (Tree.{u1} α) -> (Tree.{u2} β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, (α -> β) -> (Tree.{u2} α) -> (Tree.{u1} β)
Case conversion may be inaccurate. Consider using '#align tree.map Tree.mapₓ'. -/
/-- Apply a function to each value in the tree.  This is the `map` function for the `tree` functor.
TODO: implement `traversable tree`. -/
def map {β} (f : α → β) : Tree α → Tree β
  | nil => nil
  | node a l r => node (f a) (map l) (map r)
#align tree.map Tree.map

/-- The number of internal nodes (i.e. not including leaves) of a binary tree -/
@[simp]
def numNodes : Tree α → ℕ
  | nil => 0
  | node _ a b => a.numNodes + b.numNodes + 1
#align tree.num_nodes Tree.numNodes

/-- The number of leaves of a binary tree -/
@[simp]
def numLeaves : Tree α → ℕ
  | nil => 1
  | node _ a b => a.numLeaves + b.numLeaves
#align tree.num_leaves Tree.numLeaves

/-- The height - length of the longest path from the root - of a binary tree -/
@[simp]
def height : Tree α → ℕ
  | nil => 0
  | node _ a b => max a.height b.height + 1
#align tree.height Tree.height

theorem numLeaves_eq_numNodes_succ (x : Tree α) : x.numLeaves = x.numNodes + 1 := by
  induction x <;> simp [*, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
#align tree.num_leaves_eq_num_nodes_succ Tree.numLeaves_eq_numNodes_succ

theorem numLeaves_pos (x : Tree α) : 0 < x.numLeaves :=
  by
  rw [num_leaves_eq_num_nodes_succ]
  exact x.num_nodes.zero_lt_succ
#align tree.num_leaves_pos Tree.numLeaves_pos

theorem height_le_numNodes : ∀ x : Tree α, x.height ≤ x.numNodes
  | nil => le_rfl
  | node _ a b =>
    Nat.succ_le_succ
      (max_le (trans a.height_le_numNodes <| a.numNodes.le_add_right _)
        (trans b.height_le_numNodes <| b.numNodes.le_add_left _))
#align tree.height_le_num_nodes Tree.height_le_numNodes

/-- The left child of the tree, or `nil` if the tree is `nil` -/
@[simp]
def left : Tree α → Tree α
  | nil => nil
  | node _ l r => l
#align tree.left Tree.left

/-- The right child of the tree, or `nil` if the tree is `nil` -/
@[simp]
def right : Tree α → Tree α
  | nil => nil
  | node _ l r => r
#align tree.right Tree.right

-- mathport name: «expr △ »
-- Notation for making a node with `unit` data
scoped infixr:65 " △ " => Tree.node ()

/-- Recursion on `tree unit`; allows for a better `induction` which does not have to worry
  about the element of type `α = unit` -/
@[elab_as_elim]
def unitRecOn {motive : Tree Unit → Sort _} (t : Tree Unit) (base : motive nil)
    (ind : ∀ x y, motive x → motive y → motive (x △ y)) : motive t :=
  t.recOn base fun u => u.recOn ind
#align tree.unit_rec_on Tree.unitRecOn

theorem left_node_right_eq_self : ∀ {x : Tree Unit} (hx : x ≠ nil), x.left △ x.right = x
  | nil, h => by trivial
  | a △ b, _ => rfl
#align tree.left_node_right_eq_self Tree.left_node_right_eq_self

end Tree

