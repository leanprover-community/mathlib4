/-
Copyright (c) 2019 mathlib community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Wojciech Nawrocki, Brendan Murphy
-/
import Std.Data.RBMap.Basic
import Mathlib.Data.Num.Basic
import Mathlib.Order.Basic
import Mathlib.Init.Data.Ordering.Basic
import Mathlib.Util.CompileInductive
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.DList.Defs

#align_import data.tree from "leanprover-community/mathlib"@"ed989ff568099019c6533a4d94b27d852a5710d8"

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
  deriving DecidableEq, Repr -- Porting note: Removed `has_reflect`, added `Repr`.
#align tree Tree

namespace Tree

inductive BranchPos | left | middle |right

universe u

variable {α : Type u}

-- Porting note: replaced with `deriving Repr` which builds a better instance anyway
#noalign tree.repr

open Std (RBNode)

/-- Makes a `Tree α` out of a red-black tree. -/
def ofRBNode : RBNode α → Tree α
  | RBNode.nil => nil
  | RBNode.node _color l key r => node key (ofRBNode l) (ofRBNode r)
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

/-- Apply a function to each value in the tree.  This is the `map` function for the `Tree` functor. -/
def map {β} (f : α → β) : Tree α → Tree β
  | nil => nil
  | node a l r => node (f a) (map f l) (map f r)
#align tree.map Tree.map

/-- Map each element of a Tree to an action and evaluate these actions in
preorder traversal, then collect the results.
A tree can branch in three ways . -/
def traverse {m : Type _ → Type _} [Applicative m] {α β} (f : α → m β) : Tree α → m (Tree β)
  | nil => pure nil
  | node a l r => node <$> f a <*> traverse f l <*> traverse f r

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

-- Notation for making a node with `Unit` data
scoped infixr:65 " △ " => Tree.node ()

-- porting note: workaround for leanprover/lean4#2049
compile_inductive% Tree

@[elab_as_elim]
def unitRecOn {motive : Tree Unit → Sort*} (t : Tree Unit) (base : motive nil)
    (ind : ∀ x y, motive x → motive y → motive (x △ y)) : motive t :=
    -- Porting note: Old proof was `t.recOn base fun u => u.recOn ind` but
    -- structure eta makes it unnecessary (https://github.com/leanprover/lean4/issues/777).
    t.recOn base fun _u => ind
#align tree.unit_rec_on Tree.unitRecOn

theorem left_node_right_eq_self : ∀ {x : Tree Unit} (_hx : x ≠ nil), x.left △ x.right = x
  | nil, h => by trivial
  | node a l r, _ => rfl  -- Porting note: `a △ b` no longer works in pattern matching
#align tree.left_node_right_eq_self Tree.left_node_right_eq_self

end Tree

/-- A binary tree with values of one type stored in non-leaf nodes
and values of another in the leaves. -/
inductive Tree'.{u, v} (L : Type u) (N : Type v) : Type (max u v)
  | leaf : L → Tree' L N
  | branch : N → Tree' L N → Tree' L N → Tree' L N
  deriving DecidableEq, Repr

namespace Tree'

universe u₁ v₁ u₂ v₂ w

def bimap {L : Type u₁} {L' : Type u₂} {N : Type v₁} {N' : Type v₂}
  (f : L → L') (g : N → N') : Tree' L N → Tree' L' N'
  | leaf x => leaf (f x)
  | branch y l r => branch (g y) (bimap f g l) (bimap f g r)

def mapLeaves {L : Type u₁} {L' : Type u₂} {N : Type v₁} (f : L → L') :=
  bimap f (id : N → N)

def mapNodes {L : Type u₁} {N : Type v₁} {N' : Type v₂} (g : N → N') :=
  bimap (id : L → L) g

def bitraverse' {m : Type (max v₁ u₁) → Type w} [Applicative m]
  {L : Type u₁} {L' : Type (max v₁ u₁)} {N : Type v₁} {N' : Type (max v₁ u₁)}
  (f : L → m L') (g : N → m N') : Tree' L N → m (Tree' L' N')
  | leaf x => leaf <$> f x
  | branch y l r => branch <$> g y <*> bitraverse' f g l <*> bitraverse' f g r

-- left-to-right preorder traversal
-- right-to-left postorder traversl is recovered by reversing the order on m
def bitraverse {m : Type (max v₁ u₁) → Type w} [Applicative m]
  {L : Type u₁} {L' : Type (max v₁ u₁)} {N : Type v₁} {N' : Type (max v₁ u₁)}
  (f : L → m L') (g : N → m N') : Tree' L N → m (Tree' L' N')
  | leaf x => leaf <$> f x
  | branch y l r => branch <$> g y <*> bitraverse f g l <*> bitraverse f g r

variable {L : Type u₁} {N : Type v₁}

def eraseLeafData : Tree' L N → Tree N
  | leaf _ => Tree.nil
  | branch y l r => Tree.node y (eraseLeafData l) (eraseLeafData r)

open Std

-- possibly(?) more efficient version of get_leaves using difference lists
private
def getLeaves' : Tree' L N → List L :=
  DList.toList ∘
    let rec go : Tree' L N → DList L
      | leaf x => DList.singleton x
      | branch _ l r => go l ++ go r
    go

@[implemented_by getLeaves']
def getLeaves : Tree' L N → List L
  | leaf x => [x]
  | branch _ l r => getLeaves l ++ getLeaves r

lemma getLeaves'_correct : @getLeaves' L N = @getLeaves L N := by
  dsimp [getLeaves']
  funext t
  induction t
  . exact rfl
  . dsimp [getLeaves'.go]
    rw [DList.toList_append]
    apply congr_arg₂ <;> assumption

@[simp]
def numNodes : Tree' L N → ℕ
  | leaf _ => 0
  | branch _ l r => l.numNodes + r.numNodes + 1

@[simp]
def numLeaves : Tree' L N → ℕ
  | leaf _ => 1
  | branch _ l r => l.numLeaves + r.numLeaves

@[simp]
def height : Tree' L N → ℕ
  | leaf _ => 0
  | branch _ l r => max l.height r.height + 1

theorem numLeaves_eq_numNodes_succ (x : Tree' L N) : x.numLeaves = x.numNodes + 1 := by
  induction x <;> simp [*, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]

-- theorem getLeaves_length_eq_eraseLeafData_numLeaves (x : Tree' L N)
--   : x.getLeaves.length = x.eraseLeafData.numNodes := sorry

theorem numLeaves_pos (x : Tree' L N) : 0 < x.numLeaves := by
  rw [numLeaves_eq_numNodes_succ]
  exact x.numNodes.zero_lt_succ

theorem height_le_numNodes : ∀ x : Tree' L N, x.height ≤ x.numNodes
  | leaf _ => le_rfl
  | branch _ l r =>
    Nat.succ_le_succ
      (max_le (_root_.trans l.height_le_numNodes <| l.numNodes.le_add_right _)
        (_root_.trans r.height_le_numNodes <| r.numNodes.le_add_left _))

-- def unit_leaves_equiv_Tree : Tree' Unit N ≃ Tree N where
--   toFun := eraseLeafData
--   invFun := Tree.rec ()
--   left_inv := sorry
--   right_inv := sorry

end Tree'
