/-
Copyright (c) 2019 mathlib community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Wojciech Nawrocki

! This file was ported from Lean 3 source module data.tree
! leanprover-community/mathlib commit ed989ff568099019c6533a4d94b27d852a5710d8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Lean.Data.RBTree
import Mathlib.Data.Num.Basic
import Mathlib.Order.Basic
import Mathlib.Init.Data.Ordering.Basic

/-!
# Binary tree

Provides binary tree storage for values of any type, with O(lg n) retrieval.
See also `Lean.Data.RBTree` for red-black trees - this version allows more operations
to be defined and is better suited for in-kernel computation.

We also specialize for `Tree Unit`, which is a binary tree without any
additional data. We provide the notation `a △ b` for making a `Tree Unit` with children
`a` and `b`.

## References

<https://leanprover-community.github.io/archive/stream/113488-general/topic/tactic.20question.html>
-/


/-- A binary tree with values stored in non-leaf nodes. -/
inductive Tree.{u} (α : Type u) : Type u
  | nil : Tree α
  | node : α → Tree α → Tree α → Tree α
  deriving DecidableEq
-- Porting note: Removed `deriving has_reflect`.
#align tree Tree

namespace Tree

universe u

variable {α : Type u}

/-- Construct a string representation of a tree. Provides a `hasRepr` instance. -/
def repr [Repr α] : Tree α → String
  | nil => "nil"
  | node a t1 t2 => "Tree.node " ++ reprStr a ++ " (" ++ repr t1 ++ ") (" ++ repr t2 ++ ")"
#align tree.repr Tree.repr

instance [Repr α] : Repr (Tree α) :=
  ⟨fun s _ => Tree.repr s⟩

instance : Inhabited (Tree α) :=
  ⟨nil⟩

open Lean (RBNode)

-- Porting note: In Lean 4 RBNode's definition is changed. In Lean 3 RBNode takes a value only.
--               In Lean 4 it takes a key and a value (that map depend on a key).
--               Here we use the key only and discard the value.
/-- Makes a `tree α` out of a red-black tree. -/
def ofRBNode : RBNode α β → Tree α
  | RBNode.leaf => nil
  | RBNode.node _color l key _value r => node key (ofRBNode l) (ofRBNode r)
#align tree.of_rbnode Tree.ofRBNode

/-- Finds the index of an element in the tree assuming the tree has been
constructed according to the provided decidable order on its elements.
If it hasn't, the result will be incorrect. If it has, but the element
is not in the tree, returns none. -/
def indexOf (lt : α → α → Prop) [DecidableRel lt] (x : α) : Tree α → Option PosNum
  | nil => none
  | node a t₁ t₂ =>
    match cmpUsing lt x a with
    | Ordering.lt => PosNum.bit0 <$> indexOf lt x t₁
    | Ordering.eq => some PosNum.one
    | Ordering.gt => PosNum.bit1 <$> indexOf lt x t₂
#align tree.index_of Tree.indexOf

/-- Retrieves an element uniquely determined by a `PosNum` from the tree,
taking the following path to get to the element:
- `bit0` - go to left child
- `bit1` - go to right child
- `PosNum.one` - retrieve from here -/
def get : PosNum → Tree α → Option α
  | _, nil => none
  | PosNum.one, node a _t₁ _t₂ => some a
  | PosNum.bit0 n, node _a t₁ _t₂ => t₁.get n
  | PosNum.bit1 n, node _a _t₁ t₂ => t₂.get n
#align tree.get Tree.get

/-- Retrieves an element from the tree, or the provided default value
if the index is invalid. See `Tree.get`. -/
def getOrElse (n : PosNum) (t : Tree α) (v : α) : α :=
  (t.get n).getD v
#align tree.get_or_else Tree.getOrElse

/-- Apply a function to each value in the tree.  This is the `map` function for the `tree` functor.
TODO: implement `traversable tree`. -/
def map {β} (f : α → β) : Tree α → Tree β
  | nil => nil
  | node a l r => node (f a) (map f l) (map f r)
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

theorem numLeaves_pos (x : Tree α) : 0 < x.numLeaves := by
  rw [numLeaves_eq_numNodes_succ]
  exact x.numNodes.zero_lt_succ
#align tree.num_leaves_pos Tree.numLeaves_pos

theorem height_le_numNodes : ∀ x : Tree α, x.height ≤ x.numNodes
  | nil => le_rfl
  | node _ a b =>
    Nat.succ_le_succ
      (max_le (_root_.trans a.height_le_numNodes <| a.numNodes.le_add_right _)
        (_root_.trans b.height_le_numNodes <| b.numNodes.le_add_left _))
#align tree.height_le_num_nodes Tree.height_le_numNodes

/-- The left child of the tree, or `nil` if the tree is `nil` -/
@[simp]
def left : Tree α → Tree α
  | nil => nil
  | node _ l _r => l
#align tree.left Tree.left

/-- The right child of the tree, or `nil` if the tree is `nil` -/
@[simp]
def right : Tree α → Tree α
  | nil => nil
  | node _ _l r => r
#align tree.right Tree.right

-- mathport name: «expr △ »
-- Notation for making a node with `Unit` data
scoped infixr:65 " △ " => Tree.node ()

/-- Recursion on `Tree Unit`; allows for a better `induction` which does not have to worry
  about the element of type `α = Unit` -/
@[elab_as_elim]
def unitRecOn {motive : Tree Unit → Sort _} (t : Tree Unit) (base : motive nil)
    (ind : ∀ x y, motive x → motive y → motive (x △ y)) : motive t := by
  -- Porting note: code generator does not support recursor 'Tree.recOn'
  match t with
  | nil => exact base
  | node _a l r => exact ind l r (unitRecOn l base ind) (unitRecOn r base ind)
#align tree.unit_rec_on Tree.unitRecOn

theorem left_node_right_eq_self : ∀ {x : Tree Unit} (_hx : x ≠ nil), x.left △ x.right = x
  | nil, h => by trivial
  | node a l r, _ => rfl
#align tree.left_node_right_eq_self Tree.left_node_right_eq_self

end Tree
