/-
Copyright (c) 2019 mathlib community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Wojciech Nawrocki
-/
module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Util.CompileInductive
import Batteries.Tactic.Alias

/-!
# Binary tree

Provides binary tree storage for values of any type, with O(lg n) retrieval.
See also `Lean.Data.RBTree` for red-black trees - this version allows more operations
to be defined and is better suited for in-kernel computation.

We also specialize for `BinaryTree Unit`, which is a binary tree without any
additional data. We provide the notation `a △ b` for making a `BinaryTree Unit` with children
`a` and `b`.

## References

<https://leanprover-community.github.io/archive/stream/113488-general/topic/tactic.20question.html>
-/

@[expose] public section


/-- A binary tree with values stored in non-leaf nodes. -/
inductive BinaryTree.{u} (α : Type u) : Type u
  | nil : BinaryTree α
  | node (value : α) (left : BinaryTree α) (right : BinaryTree α) : BinaryTree α
  deriving DecidableEq, Repr
compile_inductive% BinaryTree

@[deprecated (since := "2026-06-07"), reducible]
alias Tree := BinaryTree

set_option linter.deprecated false in
/-- **Alias** of `BinaryTree.nil`. -/
@[deprecated BinaryTree.nil (since := "2026-06-07")]
abbrev Tree.nil.{u} {α : Type u} : Tree α := BinaryTree.nil

set_option linter.deprecated false in
/-- **Alias** of `BinaryTree.node`. -/
@[deprecated BinaryTree.node (since := "2026-06-07")]
abbrev Tree.node.{u} {α : Type u}
    (value : α) (left : Tree α) (right : Tree α) : Tree α :=
  BinaryTree.node value left right

namespace BinaryTree

universe u

variable {α : Type u}

instance : Inhabited (BinaryTree α) :=
  ⟨nil⟩

/--
Do an action for every node of the tree.
Actions are taken in node -> left subtree -> right subtree recursive order.
This function is the `traverse` function for the `Traversable BinaryTree` instance.
-/
def traverse
    {m : Type* → Type*} [Applicative m] {α β} (f : α → m β) :
    BinaryTree α → m (BinaryTree β)
  | .nil => pure nil
  | .node a l r => .node <$> f a <*> traverse f l <*> traverse f r

set_option linter.deprecated false in
/-- **Alias** of `BinaryTree.traverse`. -/
@[deprecated BinaryTree.traverse (since := "2026-06-07")]
abbrev _root_.Tree.traverse {m : Type* → Type*} [Applicative m] {α β} (f : α → m β)
(t : Tree α) : m (Tree β) :=
  BinaryTree.traverse f t

/-- Apply a function to each value in the BinaryTree.
This is the `map` function for the `BinaryTree` functor.
-/
def map {β} (f : α → β) : BinaryTree α → BinaryTree β
  | nil => nil
  | node a l r => node (f a) (map f l) (map f r)

set_option linter.deprecated false in
/-- **Alias** of `BinaryTree.map`. -/
@[deprecated BinaryTree.map (since := "2026-06-07")]
abbrev _root_.Tree.map {α β} (f : α → β) (t : Tree α) : Tree β := BinaryTree.map f t

theorem id_map (t : BinaryTree α) : t.map id = t := by
  induction t with
  | nil => rw [map]
  | node v l r hl hr => rw [map, hl, hr, id_eq]

theorem comp_map {β γ : Type*} (f : α → β) (g : β → γ) (t : BinaryTree α) :
    t.map (g ∘ f) = (t.map f).map g := by
  induction t with
  | nil => rw [map, map, map]
  | node v l r hl hr => rw [map, map, map, hl, hr, Function.comp_apply]

theorem traverse_pure (t : BinaryTree α) {m : Type u → Type*}
    [Applicative m] [LawfulApplicative m] :
    t.traverse (pure : α → m α) = pure t := by
  induction t with
  | nil => rw [traverse]
  | node v l r hl hr =>
    rw [traverse, hl, hr, map_pure, pure_seq, seq_pure, map_pure, map_pure]

/-- The number of internal nodes (i.e. not including leaves) of a binary tree -/
@[simp]
def numNodes : BinaryTree α → ℕ
  | nil => 0
  | node _ a b => a.numNodes + b.numNodes + 1

set_option linter.deprecated false in
/-- **Alias** of `BinaryTree.numNodes`. -/
@[deprecated BinaryTree.numNodes (since := "2026-06-07")]
abbrev _root_.Tree.numNodes {α} (t : Tree α) : ℕ := BinaryTree.numNodes t

/-- The number of leaves of a binary tree -/
@[simp]
def numLeaves : BinaryTree α → ℕ
  | nil => 1
  | node _ a b => a.numLeaves + b.numLeaves

set_option linter.deprecated false in
/-- **Alias** of `BinaryTree.numLeaves`. -/
@[deprecated BinaryTree.numLeaves (since := "2026-06-07")]
abbrev _root_.Tree.numLeaves {α} (t : Tree α) : ℕ := BinaryTree.numLeaves t

/-- The height - length of the longest path from the root - of a binary tree -/
@[simp]
def height : BinaryTree α → ℕ
  | nil => 0
  | node _ a b => max a.height b.height + 1

set_option linter.deprecated false in
/-- **Alias** of `BinaryTree.height`. -/
@[deprecated BinaryTree.height (since := "2026-06-07")]
abbrev _root_.Tree.height {α} (t : Tree α) : ℕ := BinaryTree.height t

theorem numLeaves_eq_numNodes_succ (x : BinaryTree α) : x.numLeaves = x.numNodes + 1 := by
  induction x <;> simp [*, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]

theorem numLeaves_pos (x : BinaryTree α) : 0 < x.numLeaves := by
  rw [numLeaves_eq_numNodes_succ]
  exact x.numNodes.zero_lt_succ

theorem height_le_numNodes : ∀ x : BinaryTree α, x.height ≤ x.numNodes
  | nil => Nat.le_refl _
  | node _ a b => Nat.succ_le_succ <|
    Nat.max_le.2 ⟨Nat.le_trans a.height_le_numNodes <| a.numNodes.le_add_right _,
      Nat.le_trans b.height_le_numNodes <| b.numNodes.le_add_left _⟩

/-- The left child of the tree, or `nil` if the tree is `nil` -/
@[simp]
def left : BinaryTree α → BinaryTree α
  | nil => nil
  | node _ l _r => l

set_option linter.deprecated false in
/-- **Alias** of `BinaryTree.left`. -/
@[deprecated BinaryTree.left (since := "2026-06-07")]
abbrev _root_.Tree.left {α} (t : Tree α) : Tree α := BinaryTree.left t

/-- The right child of the tree, or `nil` if the tree is `nil` -/
@[simp]
def right : BinaryTree α → BinaryTree α
  | nil => nil
  | node _ _l r => r

set_option linter.deprecated false in
/-- **Alias** of `BinaryTree.right`. -/
@[deprecated BinaryTree.right (since := "2026-06-07")]
abbrev _root_.Tree.right {α} (t : Tree α) : Tree α := BinaryTree.right t

/-- A node with `Unit` data -/
scoped infixr:65 " △ " => BinaryTree.node ()

/-- Induction principle for `BinaryTree Unit`s -/
@[elab_as_elim]
def unitRecOn {motive : BinaryTree Unit → Sort*} (t : BinaryTree Unit) (base : motive nil)
    (ind : ∀ x y, motive x → motive y → motive (x △ y)) : motive t :=
  t.recOn base fun _u ↦ ind

set_option linter.deprecated false in
/-- **Alias** of `BinaryTree.unitRecOn`. -/
@[deprecated BinaryTree.unitRecOn (since := "2026-06-07")]
abbrev _root_.Tree.unitRecOn {motive : Tree Unit → Sort*} (t : Tree Unit) (base : motive nil)
    (ind : ∀ x y, motive x → motive y → motive (x △ y)) : motive t :=
  BinaryTree.unitRecOn t base ind

theorem left_node_right_eq_self : ∀ {x : BinaryTree Unit} (_hx : x ≠ nil), x.left △ x.right = x
  | nil, h => by trivial
  | node _ _ _, _ => rfl  -- Porting note: `a △ b` no longer works in pattern matching

end BinaryTree
