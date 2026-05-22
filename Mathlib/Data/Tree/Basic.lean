/-
Copyright (c) 2019 mathlib community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Wojciech Nawrocki, Sorrachai Yingchareonthawornchai
-/
module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Util.CompileInductive

/-!
# BinaryTree

Provides binary BinaryTree storage for values of any type, with O(lg n) retrieval.
See also `Lean.Data.RBBinaryTree` for red-black BinaryTrees - this version allows more operations
to be defined and is better suited for in-kernel computation.

We also specialize for `BinaryTree Unit`, which is a binary BinaryTree without any
additional data. We provide the notation `a △ b` for making a `BinaryTree Unit` with children
`a` and `b`.

## References

<https://leanprover-community.github.io/archive/stream/113488-general/topic/tactic.20question.html>
-/

@[expose] public section


/-- A binary BinaryTree with values stored in non-leaf nodes. -/
inductive BinaryTree.{u} (α : Type u) : Type u
  | nil : BinaryTree α
  | node (value : α) (left : BinaryTree α) (right : BinaryTree α) : BinaryTree α
  deriving DecidableEq, Repr
compile_inductive% BinaryTree

namespace BinaryTree

universe u

variable {α : Type u}

instance : Inhabited (BinaryTree α) :=
  ⟨nil⟩


/--
Do an action for every node of the BinaryTree.
Actions are taken in node -> left subBinaryTree -> right subBinaryTree recursive order.
This function is the `traverse` function for the `Traversable BinaryTree` instance.
-/
def traverse {m : Type* → Type*} [Applicative m] {α β} (f : α → m β)
: BinaryTree α → m (BinaryTree β)
  | .nil => pure nil
  | .node a l r => .node <$> f a <*> traverse f l <*> traverse f r

/-- Apply a function to each value in the BinaryTree.
This is the `map` function for the `BinaryTree` functor.
-/
def map {β} (f : α → β) : BinaryTree α → BinaryTree β
  | nil => nil
  | node a l r => node (f a) (map f l) (map f r)

theorem id_map (t : BinaryTree α) : t.map id = t := by
  induction t with
  | nil => rw [map]
  | node v l r hl hr => rw [map, hl, hr, id_eq]

theorem comp_map {β γ : Type*} (f : α → β) (g : β → γ) (t : BinaryTree α) :
    t.map (g ∘ f) = (t.map f).map g := by
  induction t with
  | nil => rw [map, map, map]
  | node v l r hl hr => rw [map, map, map, hl, hr, Function.comp_apply]

theorem traverse_pure (t : BinaryTree α) {m : Type u → Type*} [Applicative m] [LawfulApplicative m]
: t.traverse (pure : α → m α) = pure t := by
  induction t with
  | nil => rw [traverse]
  | node v l r hl hr =>
    rw [traverse, hl, hr, map_pure, pure_seq, seq_pure, map_pure, map_pure]

/-- The number of internal nodes (i.e. not including leaves) of a binary BinaryTree -/
@[simp]
def numNodes : BinaryTree α → ℕ
  | nil => 0
  | node _ a b => a.numNodes + b.numNodes + 1

/-- The number of leaves of a binary BinaryTree -/
@[simp]
def numLeaves : BinaryTree α → ℕ
  | nil => 1
  | node _ a b => a.numLeaves + b.numLeaves

/-- The height - length of the longest path from the root - of a binary BinaryTree -/
@[simp]
def height : BinaryTree α → ℕ
  | nil => 0
  | node _ a b => max a.height b.height + 1

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

/-- The left child of the BinaryTree, or `nil` if the BinaryTree is `nil` -/
@[simp]
def left : BinaryTree α → BinaryTree α
  | nil => nil
  | node _ l _r => l

/-- The right child of the BinaryTree, or `nil` if the BinaryTree is `nil` -/
@[simp]
def right : BinaryTree α → BinaryTree α
  | nil => nil
  | node _ _l r => r

/-- A node with `Unit` data -/
scoped infixr:65 " △ " => BinaryTree.node ()

/-- A tree node -/
scoped notation:65 l:66 " △[" v "] " r:66 => BinaryTree.node v l r

/--
BinaryTree membership, typically accessed via the `∈` operator.

`a ∈ T` means that `a` is an element of the binary tree `T`.
Elements are compared according to Lean's logical equality.

Examples:
* `a ∈ ((nil △[x] nil) △[y] nil) ↔ a = x ∨ a = y`
-/
inductive Mem (a : α) : BinaryTree α → Prop
| node  {l r}   : Mem a (l △[a] r)
| left  (b : α) {l r} : Mem a l → Mem a (l △[b] r)
| right (b : α) {l r} : Mem a r → Mem a (l △[b] r)

/-- Defines the `∈` notation for `BinaryTree`. -/
instance : Membership α (BinaryTree α) where
  mem l a := Mem a l

theorem mem_singleton_iff (a x : ℕ) : a ∈ ((nil △[x] nil)) ↔ a = x := by
  constructor
  · intro h
    cases h <;> trivial
  · intro h
    subst h
    apply Mem.node

def contains [BEq α] (t : BinaryTree α) (a : α) :  Bool := match t with
  | .nil        => false
  | l △[b] r => a == b || l.contains a  || r.contains a

/-- `contains` is sound and complete with respect to `Mem`. -/
theorem contains_iff {α : Type u} [inst : BEq α] [inst_1 : LawfulBEq α]
  (a : α) (t : BinaryTree α) : t.contains a = true ↔ a ∈ t := by
  fun_induction contains
  · simp_all only [Bool.false_eq_true, false_iff]
    false_or_by_contra
    expose_names
    cases h
  · expose_names
    simp only [Bool.or_eq_true, beq_iff_eq, ih2, ih1]
    constructor
    · rintro ( ⟨h | h⟩ | h)
      · subst h; exact .node
      · exact .left a_1 h
      · exact .right a_1 h
    · intro h
      cases h
      · grind
      · left
        right
        assumption
      · right; assumption

instance [BEq α] [LawfulBEq α] (a : α) (t : BinaryTree α) : Decidable (a ∈ t)  :=
  decidable_of_iff (t.contains a = true) (t.contains_iff a)

/-- Checks whether a boolean predicate holds for every node in the tree.
    Traversal order: current node, then left subtree, then right subtree. -/
def all (p : α → Bool) : BinaryTree α → Bool
  | nil        => true
  | l △[b] r => p b && all p l && all p r

theorem all_iff (p : α → Prop) [inst : DecidablePred p]
  (t : BinaryTree α) : t.all (fun x ↦ p x) = true ↔ ∀ x ∈ t, p x := by
  fun_induction all
  · simp only [true_iff]; intros; contradiction
  · expose_names
    simp only [Bool.and_eq_true, decide_eq_true_eq, ih2, ih1]
    constructor
    · rintro ⟨⟨h1,h3⟩,h2⟩ x hx
      cases hx
      · assumption
      · expose_names
        apply h3
        exact h
      · expose_names
        apply h2
        exact h
    · intro h
      exact ⟨⟨h a .node,
        fun x m => h x (.left a m)⟩,
        fun x m => h x (.right a m)⟩

/-- `Decidable` instance for bounded universal quantification over a `BinaryTree`. -/
instance decidableBAll (p : α → Prop) [DecidablePred p] (t : BinaryTree α) :
    Decidable (∀ x ∈ t, p x) :=
      decidable_of_iff (t.all (fun x => p x)) (all_iff p t)

/-- Induction principle for `BinaryTree Unit`s -/
@[elab_as_elim]
def unitRecOn {motive : BinaryTree Unit → Sort*} (t : BinaryTree Unit) (base : motive nil)
    (ind : ∀ x y, motive x → motive y → motive (x △ y)) : motive t :=
  t.recOn base fun _u ↦ ind

theorem left_node_right_eq_self : ∀ {x : BinaryTree Unit} (_hx : x ≠ nil), x.left △ x.right = x
  | nil, h => by trivial
  | node _ _ _, _ => rfl  -- Porting note: `a △ b` no longer works in pattern matching


/-- Inorder traversal into a list: left → node → right. -/
def toListInOrder : BinaryTree α → List α
  | nil          => []
  | l △[v] r  => l.toListInOrder ++ [v] ++ r.toListInOrder

/-- Preorder traversal  into a list: node → left → right. -/
def toListPreOrder : BinaryTree α → List α
  | nil          => []
  | l △[v] r  => [v] ++ l.toListPreOrder ++ r.toListPreOrder

/-- Postorder traversal  into a list: left → right → node. -/
def toListPostOrder : BinaryTree α → List α
  | nil          => []
  | l △[v] r  => l.toListPostOrder ++ r.toListPostOrder ++ [v]

end BinaryTree
