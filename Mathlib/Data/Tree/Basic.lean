/-
Copyright (c) 2019 mathlib community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Wojciech Nawrocki
-/
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.TypeStar
import Mathlib.Util.CompileInductive
import Mathlib.Control.Applicative
import Mathlib.Control.Traversable.Basic

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

namespace Tree

universe u

variable {α : Type u}

-- Porting note: replaced with `deriving Repr` which builds a better instance anyway

instance : Inhabited (Tree α) :=
  ⟨nil⟩

/--
Do an action for every node of the tree.
Actions are taken in node -> left subtree -> right subtree recursive order.
This function is the `traverse` function for the `Traversable Tree` instance.
-/
def traverse {m:Type* → Type*} [Applicative m] {α β} (f:α → m β) :Tree α → m (Tree β)
  | .nil => pure nil
  | .node a l r => .node <$> f a <*> traverse f l <*> traverse f r

/-- Apply a function to each value in the tree.  This is the `map` function for the `Tree` functor.
-/
def map {β} (f : α → β) : Tree α → Tree β
  | .nil => nil
  | .node a l r => node (f a) (map f l) (map f r)

instance : Traversable Tree where
  map := map
  traverse := traverse

instance : LawfulTraversable Tree where
  map_const := rfl
  id_map t := by
    dsimp [(· <$> ·)]
    induction t
    · rw [map]
    · rename_i hl hr
      rw [map,hl,hr,id_eq]
  comp_map f g t := by
    dsimp [(· <$> ·)]
    induction t
    · rw [map,map,map]
    · rename_i hl hr
      rw [map,map,map,hl,hr,Function.comp_apply]
  id_traverse t := by
    dsimp [Traversable.traverse]
    induction t
    · rw [traverse,Id.pure_eq]
    · rename_i hl hr
      rw [traverse,hl,hr]
      rfl
  comp_traverse := by
    intro F G _ _ _ _ α β γ  f g x
    dsimp [Traversable.traverse]
    induction x
    · rw [traverse,traverse,map_pure,traverse]
      rfl
    · rename_i hl hr
      rw [traverse,hl,hr,traverse]
      simp [Functor.Comp.map_mk,Functor.map_map,Function.comp_def,Comp.seq_mk,
        seq_map_assoc,map_seq]
      rfl
  traverse_eq_map_id f t:= by
    dsimp [Traversable.traverse,(· <$> ·)]
    induction t
    · rw [Tree.traverse,Tree.map]
      rfl
    · rename_i hl hr
      rw [traverse,map,hl,hr]
      rfl
  naturality F G {_ _ _ _} η {α β} f t := by
    dsimp [Traversable.traverse]
    induction t
    · rw [traverse, traverse, η.preserves_pure']
    · rename_i hl hr
      rw [traverse, traverse, η.preserves_seq', η.preserves_seq',
        ← pure_seq, η.preserves_seq', hl, hr, η.preserves_pure', pure_seq]
      rfl

/-- The number of internal nodes (i.e. not including leaves) of a binary tree -/
@[simp]
def numNodes : Tree α → ℕ
  | nil => 0
  | node _ a b => a.numNodes + b.numNodes + 1

/-- The number of leaves of a binary tree -/
@[simp]
def numLeaves : Tree α → ℕ
  | nil => 1
  | node _ a b => a.numLeaves + b.numLeaves

/-- The height - length of the longest path from the root - of a binary tree -/
@[simp]
def height : Tree α → ℕ
  | nil => 0
  | node _ a b => max a.height b.height + 1

theorem numLeaves_eq_numNodes_succ (x : Tree α) : x.numLeaves = x.numNodes + 1 := by
  induction x <;> simp [*, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]

theorem numLeaves_pos (x : Tree α) : 0 < x.numLeaves := by
  rw [numLeaves_eq_numNodes_succ]
  exact x.numNodes.zero_lt_succ

theorem height_le_numNodes : ∀ x : Tree α, x.height ≤ x.numNodes
  | nil => Nat.le_refl _
  | node _ a b => Nat.succ_le_succ <|
    Nat.max_le.2 ⟨Nat.le_trans a.height_le_numNodes <| a.numNodes.le_add_right _,
      Nat.le_trans b.height_le_numNodes <| b.numNodes.le_add_left _⟩

/-- The left child of the tree, or `nil` if the tree is `nil` -/
@[simp]
def left : Tree α → Tree α
  | nil => nil
  | node _ l _r => l

/-- The right child of the tree, or `nil` if the tree is `nil` -/
@[simp]
def right : Tree α → Tree α
  | nil => nil
  | node _ _l r => r

/-- A node with `Unit` data -/
scoped infixr:65 " △ " => Tree.node ()

-- Porting note: workaround for leanprover/lean4#2049
compile_inductive% Tree

@[elab_as_elim]
def unitRecOn {motive : Tree Unit → Sort*} (t : Tree Unit) (base : motive nil)
    (ind : ∀ x y, motive x → motive y → motive (x △ y)) : motive t :=
  t.recOn base fun _u ↦ ind

theorem left_node_right_eq_self : ∀ {x : Tree Unit} (_hx : x ≠ nil), x.left △ x.right = x
  | nil, h => by trivial
  | node _ _ _, _ => rfl  -- Porting note: `a △ b` no longer works in pattern matching

end Tree
