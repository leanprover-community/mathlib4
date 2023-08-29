/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Order.Compare
import Mathlib.Data.List.Defs
import Mathlib.Data.Nat.PSub
import Mathlib.Init.Data.Nat.Bitwise

#align_import data.ordmap.ordnode from "leanprover-community/mathlib"@"dd71334db81d0bd444af1ee339a29298bef40734"

/-!
# Ordered sets

This file defines a data structure for ordered sets, supporting a
variety of useful operations including insertion and deletion,
logarithmic time lookup, set operations, folds,
and conversion from lists.

The `Ordnode α` operations all assume that `α` has the structure of
a total preorder, meaning a `≤` operation that is

* Transitive: `x ≤ y → y ≤ z → x ≤ z`
* Reflexive: `x ≤ x`
* Total: `x ≤ y ∨ y ≤ x`

For example, in order to use this data structure as a map type, one
can store pairs `(k, v)` where `(k, v) ≤ (k', v')` is defined to mean
`k ≤ k'` (assuming that the key values are linearly ordered).

Two values `x,y` are equivalent if `x ≤ y` and `y ≤ x`. An `Ordnode α`
maintains the invariant that it never stores two equivalent nodes;
the insertion operation comes with two variants depending on whether
you want to keep the old value or the new value in case you insert a value
that is equivalent to one in the set.

The operations in this file are not verified, in the sense that they provide
"raw operations" that work for programming purposes but the invariants
are not explicitly in the structure. See `Ordset` for a verified version
of this data structure.

## Main definitions

* `Ordnode α`: A set of values of type `α`

## Implementation notes

Based on weight balanced trees:

 * Stephen Adams, "Efficient sets: a balancing act",
   Journal of Functional Programming 3(4):553-562, October 1993,
   <http://www.swiss.ai.mit.edu/~adams/BB/>.
 * J. Nievergelt and E.M. Reingold,
   "Binary search trees of bounded balance",
   SIAM journal of computing 2(1), March 1973.

Ported from Haskell's `Data.Set`.

## Tags

ordered map, ordered set, data structure

-/

set_option autoImplicit true



/- ./././Mathport/Syntax/Translate/Command.lean:355:30: infer kinds are unsupported in Lean 4:
  nil {} -/
/-- An `Ordnode α` is a finite set of values, represented as a tree.
  The operations on this type maintain that the tree is balanced
  and correctly stores subtree sizes at each level. -/
inductive Ordnode (α : Type u) : Type u
  | nil : Ordnode α
  | node (size : ℕ) (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α
#align ordnode Ordnode

-- Porting note: `Nat.Partrec.Code.recOn` is noncomputable in Lean4, so we make it computable.
compile_inductive% Ordnode

namespace Ordnode

variable {α : Type*}

instance : EmptyCollection (Ordnode α) :=
  ⟨nil⟩

instance : Inhabited (Ordnode α) :=
  ⟨nil⟩

/-- **Internal use only**

The maximal relative difference between the sizes of
two trees, it corresponds with the `w` in Adams' paper.

According to the Haskell comment, only `(delta, ratio)` settings
of `(3, 2)` and `(4, 2)` will work, and the proofs in
`Ordset.lean` assume `delta := 3` and `ratio := 2`. -/
@[inline]
def delta :=
  3
#align ordnode.delta Ordnode.delta

/-- **Internal use only**

The ratio between an outer and inner sibling of the
heavier subtree in an unbalanced setting. It determines
whether a double or single rotation should be performed
to restore balance. It is corresponds with the inverse
of `α` in Adam's article. -/
@[inline]
def ratio :=
  2
#align ordnode.ratio Ordnode.ratio

/-- O(1). Construct a singleton set containing value `a`.

     singleton 3 = {3} -/
@[inline]
protected def singleton (a : α) : Ordnode α :=
  node 1 nil a nil
#align ordnode.singleton Ordnode.singleton

-- mathport name: «exprι »
local prefix:arg "ι" => Ordnode.singleton

instance : Singleton α (Ordnode α) :=
  ⟨Ordnode.singleton⟩

/-- O(1). Get the size of the set.

     size {2, 1, 1, 4} = 3  -/
@[inline]
def size : Ordnode α → ℕ
  | nil => 0
  | node sz _ _ _ => sz
#align ordnode.size Ordnode.size

theorem size_nil : size (nil : Ordnode α) = 0 :=
  rfl
theorem size_node (sz : ℕ) (l : Ordnode α) (x : α) (r : Ordnode α) : size (node sz l x r) = sz :=
  rfl

attribute [eqns size_nil size_node] size
attribute [simp] size

/-- O(1). Is the set empty?

     empty ∅ = tt
     empty {1, 2, 3} = ff -/
@[inline]
def empty : Ordnode α → Bool
  | nil => true
  | node _ _ _ _ => false
#align ordnode.empty Ordnode.empty

/-- **Internal use only**, because it violates the BST property on the original order.

O(n). The dual of a tree is a tree with its left and right sides reversed throughout.
The dual of a valid BST is valid under the dual order. This is convenient for exploiting
symmetries in the algorithms. -/
@[simp]
def dual : Ordnode α → Ordnode α
  | nil => nil
  | node s l x r => node s (dual r) x (dual l)
#align ordnode.dual Ordnode.dual

/-- **Internal use only**

O(1). Construct a node with the correct size information, without rebalancing. -/
@[inline, reducible]
def node' (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α :=
  node (size l + size r + 1) l x r
#align ordnode.node' Ordnode.node'

/-- Basic pretty printing for `Ordnode α` that shows the structure of the tree.

     repr {3, 1, 2, 4} = ((∅ 1 ∅) 2 ((∅ 3 ∅) 4 ∅)) -/
def repr {α} [Repr α] (o : Ordnode α) (n : ℕ) : Std.Format :=
  match o with
  | nil => (Std.Format.text "∅")
  | node _ l x r =>
      let fmt := Std.Format.joinSep
        [repr l n, Repr.reprPrec x n, repr r n]
        " "
      Std.Format.paren fmt
#align ordnode.repr Ordnode.repr

instance {α} [Repr α] : Repr (Ordnode α) :=
  ⟨repr⟩

-- Note: The function has been written with tactics to avoid extra junk
/-- **Internal use only**

O(1). Rebalance a tree which was previously balanced but has had its left
side grow by 1, or its right side shrink by 1. -/
def balanceL (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α := by
  -- porting notes: removed `clean`
  cases' id r with rs
  -- ⊢ Ordnode α
  · cases' id l with ls ll lx lr
    -- ⊢ Ordnode α
    · exact ι x
      -- 🎉 no goals
    · cases' id ll with lls
      -- ⊢ Ordnode α
      · cases' lr with _ _ lrx
        -- ⊢ Ordnode α
        · exact node 2 l x nil
          -- 🎉 no goals
        · exact node 3 (ι lx) lrx ι x
          -- 🎉 no goals
      · cases' id lr with lrs lrl lrx lrr
        -- ⊢ Ordnode α
        · exact node 3 ll lx ι x
          -- 🎉 no goals
        · exact
            if lrs < ratio * lls then node (ls + 1) ll lx (node (lrs + 1) lr x nil)
            else
              node (ls + 1) (node (lls + size lrl + 1) ll lx lrl) lrx
                (node (size lrr + 1) lrr x nil)
  · cases' id l with ls ll lx lr
    -- ⊢ Ordnode α
    · exact node (rs + 1) nil x r
      -- 🎉 no goals
    · refine' if ls > delta * rs then _ else node (ls + rs + 1) l x r
      -- ⊢ Ordnode α
      cases' id ll with lls
      -- ⊢ Ordnode α
      · exact nil
        -- 🎉 no goals
      --should not happen
      cases' id lr with lrs lrl lrx lrr
      -- ⊢ Ordnode α
      · exact nil
        -- 🎉 no goals
      --should not happen
      exact
        if lrs < ratio * lls then node (ls + rs + 1) ll lx (node (rs + lrs + 1) lr x r)
        else
          node (ls + rs + 1) (node (lls + size lrl + 1) ll lx lrl) lrx
            (node (size lrr + rs + 1) lrr x r)
#align ordnode.balance_l Ordnode.balanceL

/-- **Internal use only**

O(1). Rebalance a tree which was previously balanced but has had its right
side grow by 1, or its left side shrink by 1. -/
def balanceR (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α := by
  -- porting notes: removed `clean`
  cases' id l with ls
  -- ⊢ Ordnode α
  · cases' id r with rs rl rx rr
    -- ⊢ Ordnode α
    · exact ι x
      -- 🎉 no goals
    · cases' id rr with rrs
      -- ⊢ Ordnode α
      · cases' rl with _ _ rlx
        -- ⊢ Ordnode α
        · exact node 2 nil x r
          -- 🎉 no goals
        · exact node 3 (ι x) rlx ι rx
          -- 🎉 no goals
      · cases' id rl with rls rll rlx rlr
        -- ⊢ Ordnode α
        · exact node 3 (ι x) rx rr
          -- 🎉 no goals
        · exact
            if rls < ratio * rrs then node (rs + 1) (node (rls + 1) nil x rl) rx rr
            else
              node (rs + 1) (node (size rll + 1) nil x rll) rlx
                (node (size rlr + rrs + 1) rlr rx rr)
  · cases' id r with rs rl rx rr
    -- ⊢ Ordnode α
    · exact node (ls + 1) l x nil
      -- 🎉 no goals
    · refine' if rs > delta * ls then _ else node (ls + rs + 1) l x r
      -- ⊢ Ordnode α
      cases' id rr with rrs
      -- ⊢ Ordnode α
      · exact nil
        -- 🎉 no goals
      --should not happen
      cases' id rl with rls rll rlx rlr
      -- ⊢ Ordnode α
      · exact nil
        -- 🎉 no goals
      --should not happen
      exact
        if rls < ratio * rrs then node (ls + rs + 1) (node (ls + rls + 1) l x rl) rx rr
        else
          node (ls + rs + 1) (node (ls + size rll + 1) l x rll) rlx
            (node (size rlr + rrs + 1) rlr rx rr)
#align ordnode.balance_r Ordnode.balanceR

/-- **Internal use only**

O(1). Rebalance a tree which was previously balanced but has had one side change
by at most 1. -/
def balance (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α := by
  -- porting notes: removed `clean`
  cases' id l with ls ll lx lr
  -- ⊢ Ordnode α
  · cases' id r with rs rl rx rr
    -- ⊢ Ordnode α
    · exact ι x
      -- 🎉 no goals
    · cases' id rl with rls rll rlx rlr
      -- ⊢ Ordnode α
      · cases id rr
        -- ⊢ Ordnode α
        · exact node 2 nil x r
          -- 🎉 no goals
        · exact node 3 (ι x) rx rr
          -- 🎉 no goals
      · cases' id rr with rrs
        -- ⊢ Ordnode α
        · exact node 3 (ι x) rlx ι rx
          -- 🎉 no goals
        · exact
            if rls < ratio * rrs then node (rs + 1) (node (rls + 1) nil x rl) rx rr
            else
              node (rs + 1) (node (size rll + 1) nil x rll) rlx
                (node (size rlr + rrs + 1) rlr rx rr)
  · cases' id r with rs rl rx rr
    -- ⊢ Ordnode α
    · cases' id ll with lls
      -- ⊢ Ordnode α
      · cases' lr with _ _ lrx
        -- ⊢ Ordnode α
        · exact node 2 l x nil
          -- 🎉 no goals
        · exact node 3 (ι lx) lrx ι x
          -- 🎉 no goals
      · cases' id lr with lrs lrl lrx lrr
        -- ⊢ Ordnode α
        · exact node 3 ll lx ι x
          -- 🎉 no goals
        · exact
            if lrs < ratio * lls then node (ls + 1) ll lx (node (lrs + 1) lr x nil)
            else
              node (ls + 1) (node (lls + size lrl + 1) ll lx lrl) lrx
                (node (size lrr + 1) lrr x nil)
    · refine'
        if delta * ls < rs then _ else if delta * rs < ls then _ else node (ls + rs + 1) l x r
      · cases' id rl with rls rll rlx rlr
        -- ⊢ Ordnode α
        · exact nil
          -- 🎉 no goals
        --should not happen
        cases' id rr with rrs
        -- ⊢ Ordnode α
        · exact nil
          -- 🎉 no goals
        --should not happen
        exact
          if rls < ratio * rrs then node (ls + rs + 1) (node (ls + rls + 1) l x rl) rx rr
          else
            node (ls + rs + 1) (node (ls + size rll + 1) l x rll) rlx
              (node (size rlr + rrs + 1) rlr rx rr)
      · cases' id ll with lls
        -- ⊢ Ordnode α
        · exact nil
          -- 🎉 no goals
        --should not happen
        cases' id lr with lrs lrl lrx lrr
        -- ⊢ Ordnode α
        · exact nil
          -- 🎉 no goals
        --should not happen
        exact
          if lrs < ratio * lls then node (ls + rs + 1) ll lx (node (lrs + rs + 1) lr x r)
          else
            node (ls + rs + 1) (node (lls + size lrl + 1) ll lx lrl) lrx
              (node (size lrr + rs + 1) lrr x r)
#align ordnode.balance Ordnode.balance

/-- O(n). Does every element of the map satisfy property `P`?

     All (fun x ↦ x < 5) {1, 2, 3} = True
     All (fun x ↦ x < 5) {1, 2, 3, 5} = False -/
def All (P : α → Prop) : Ordnode α → Prop
  | nil => True
  | node _ l x r => All P l ∧ P x ∧ All P r
#align ordnode.all Ordnode.All

instance All.decidable {P : α → Prop} : (t : Ordnode α) → [DecidablePred P] → Decidable (All P t)
  | nil => decidableTrue
  | node _ l _ r =>
    have : Decidable (All P l) := All.decidable l
    have : Decidable (All P r) := All.decidable r
    And.decidable
#align ordnode.all.decidable Ordnode.All.decidable

/-- O(n). Does any element of the map satisfy property `P`?

     Any (fun x ↦ x < 2) {1, 2, 3} = True
     Any (fun x ↦ x < 2) {2, 3, 5} = False -/
def Any (P : α → Prop) : Ordnode α → Prop
  | nil => False
  | node _ l x r => Any P l ∨ P x ∨ Any P r
#align ordnode.any Ordnode.Any

instance Any.decidable {P : α → Prop} : (t: Ordnode α ) → [DecidablePred P] → Decidable (Any P t)
  | nil => decidableFalse
  | node _ l _ r =>
    have : Decidable (Any P l) := Any.decidable l
    have : Decidable (Any P r) := Any.decidable r
    Or.decidable
#align ordnode.any.decidable Ordnode.Any.decidable

/-- O(n). Exact membership in the set. This is useful primarily for stating
correctness properties; use `∈` for a version that actually uses the BST property
of the tree.

    Emem 2 {1, 2, 3} = true
    Emem 4 {1, 2, 3} = false -/
def Emem (x : α) : Ordnode α → Prop :=
  Any (Eq x)
#align ordnode.emem Ordnode.Emem

instance Emem.decidable (x : α) [DecidableEq α] : ∀ t, Decidable (Emem x t) := by
  dsimp [Emem]; infer_instance
  -- ⊢ (t : Ordnode α) → Decidable (Any (Eq x) t)
                -- 🎉 no goals
#align ordnode.emem.decidable Ordnode.Emem.decidable

/-- O(n). Approximate membership in the set, that is, whether some element in the
set is equivalent to this one in the preorder. This is useful primarily for stating
correctness properties; use `∈` for a version that actually uses the BST property
of the tree.

    Amem 2 {1, 2, 3} = true
    Amem 4 {1, 2, 3} = false

To see the difference with `Emem`, we need a preorder that is not a partial order.
For example, suppose we compare pairs of numbers using only their first coordinate. Then:
-- Porting note: Verify below example
    emem (0, 1) {(0, 0), (1, 2)} = false
    amem (0, 1) {(0, 0), (1, 2)} = true
    (0, 1) ∈ {(0, 0), (1, 2)} = true

The `∈` relation is equivalent to `Amem` as long as the `Ordnode` is well formed,
and should always be used instead of `Amem`. -/
def Amem [LE α] (x : α) : Ordnode α → Prop :=
  Any fun y => x ≤ y ∧ y ≤ x
#align ordnode.amem Ordnode.Amem

instance Amem.decidable [LE α] [@DecidableRel α (· ≤ ·)] (x : α) :
    ∀ t, Decidable (Amem x t) := by
  dsimp [Amem]; infer_instance
  -- ⊢ (t : Ordnode α) → Decidable (Any (fun y => x ≤ y ∧ y ≤ x) t)
                -- 🎉 no goals
#align ordnode.amem.decidable Ordnode.Amem.decidable

/-- O(log n). Return the minimum element of the tree, or the provided default value.

     findMin' 37 {1, 2, 3} = 1
     findMin' 37 ∅ = 37 -/
def findMin' : Ordnode α → α → α
  | nil, x => x
  | node _ l x _, _ => findMin' l x
#align ordnode.find_min' Ordnode.findMin'

/-- O(log n). Return the minimum element of the tree, if it exists.

     findMin {1, 2, 3} = some 1
     findMin ∅ = none -/
def findMin : Ordnode α → Option α
  | nil => none
  | node _ l x _ => some (findMin' l x)
#align ordnode.find_min Ordnode.findMin

/-- O(log n). Return the maximum element of the tree, or the provided default value.

     findMax' 37 {1, 2, 3} = 3
     findMax' 37 ∅ = 37 -/
def findMax' : α → Ordnode α → α
  | x, nil => x
  | _, node _ _ x r => findMax' x r
#align ordnode.find_max' Ordnode.findMax'

/-- O(log n). Return the maximum element of the tree, if it exists.

     findMax {1, 2, 3} = some 3
     findMax ∅ = none -/
def findMax : Ordnode α → Option α
  | nil => none
  | node _ _ x r => some (findMax' x r)
#align ordnode.find_max Ordnode.findMax

/-- O(log n). Remove the minimum element from the tree, or do nothing if it is already empty.

     eraseMin {1, 2, 3} = {2, 3}
     eraseMin ∅ = ∅ -/
def eraseMin : Ordnode α → Ordnode α
  | nil => nil
  | node _ nil _ r => r
  | node _ (node sz l' y r') x r => balanceR (eraseMin (node sz l' y r')) x r
#align ordnode.erase_min Ordnode.eraseMin

/-- O(log n). Remove the maximum element from the tree, or do nothing if it is already empty.

     eraseMax {1, 2, 3} = {1, 2}
     eraseMax ∅ = ∅ -/
def eraseMax : Ordnode α → Ordnode α
  | nil => nil
  | node _ l _ nil => l
  | node _ l x (node sz l' y r') => balanceL l x (eraseMax (node sz l' y r'))
#align ordnode.erase_max Ordnode.eraseMax

/-- **Internal use only**, because it requires a balancing constraint on the inputs.

O(log n). Extract and remove the minimum element from a nonempty tree. -/
def splitMin' : Ordnode α → α → Ordnode α → α × Ordnode α
  | nil, x, r => (x, r)
  | node _ ll lx lr, x, r =>
    let (xm, l') := splitMin' ll lx lr
    (xm, balanceR l' x r)
#align ordnode.split_min' Ordnode.splitMin'

/-- O(log n). Extract and remove the minimum element from the tree, if it exists.

     split_min {1, 2, 3} = some (1, {2, 3})
     split_min ∅ = none -/
def splitMin : Ordnode α → Option (α × Ordnode α)
  | nil => none
  | node _ l x r => splitMin' l x r
#align ordnode.split_min Ordnode.splitMin

/-- **Internal use only**, because it requires a balancing constraint on the inputs.

O(log n). Extract and remove the maximum element from a nonempty tree. -/
def splitMax' : Ordnode α → α → Ordnode α → Ordnode α × α
  | l, x, nil => (l, x)
  | l, x, node _ rl rx rr =>
    let (r', xm) := splitMax' rl rx rr
    (balanceL l x r', xm)
#align ordnode.split_max' Ordnode.splitMax'

/-- O(log n). Extract and remove the maximum element from the tree, if it exists.

     split_max {1, 2, 3} = some ({1, 2}, 3)
     split_max ∅ = none -/
def splitMax : Ordnode α → Option (Ordnode α × α)
  | nil => none
  | node _ x l r => splitMax' x l r
#align ordnode.split_max Ordnode.splitMax

/-- **Internal use only**

O(log(m + n)). Concatenate two trees that are balanced and ordered with respect to each other. -/
def glue : Ordnode α → Ordnode α → Ordnode α
  | nil, r => r
  | l@(node _ _ _ _), nil => l
  | l@(node sl ll lx lr), r@(node sr rl rx rr) =>
    if sl > sr then
      let (l', m) := splitMax' ll lx lr
      balanceR l' m r
    else
      let (m, r') := splitMin' rl rx rr
      balanceL l m r'
#align ordnode.glue Ordnode.glue

/-- O(log(m + n)). Concatenate two trees that are ordered with respect to each other.

     merge {1, 2} {3, 4} = {1, 2, 3, 4}
     merge {3, 4} {1, 2} = precondition violation -/
def merge (l : Ordnode α) : Ordnode α → Ordnode α :=
  (Ordnode.recOn (motive := fun _ => Ordnode α → Ordnode α) l fun r => r)
    fun ls ll lx lr _ IHlr r =>
      (Ordnode.recOn (motive := fun _ => Ordnode α) r (node ls ll lx lr))
        fun rs rl rx rr IHrl _ =>
          if delta * ls < rs then balanceL IHrl rx rr
          else
            if delta * rs < ls then balanceR ll lx (IHlr <| node rs rl rx rr)
            else glue (node ls ll lx lr) (node rs rl rx rr)
#align ordnode.merge Ordnode.merge

/-- O(log n). Insert an element above all the others, without any comparisons.
(Assumes that the element is in fact above all the others).

    insertMax {1, 2} 4 = {1, 2, 4}
    insertMax {1, 2} 0 = precondition violation -/
def insertMax : Ordnode α → α → Ordnode α
  | nil, x => ι x
  | node _ l y r, x => balanceR l y (insertMax r x)
#align ordnode.insert_max Ordnode.insertMax

/-- O(log n). Insert an element below all the others, without any comparisons.
(Assumes that the element is in fact below all the others).

    insertMin {1, 2} 0 = {0, 1, 2}
    insertMin {1, 2} 4 = precondition violation -/
def insertMin (x : α) : Ordnode α → Ordnode α
  | nil => ι x
  | node _ l y r => balanceR (insertMin x l) y r
#align ordnode.insert_min Ordnode.insertMin

/-- O(log(m+n)). Build a tree from an element between two trees, without any
assumption on the relative sizes.

    link {1, 2} 4 {5, 6} = {1, 2, 4, 5, 6}
    link {1, 3} 2 {5} = precondition violation -/
def link (l : Ordnode α) (x : α) : Ordnode α → Ordnode α :=
  -- Porting note: Previous code was:
  -- (Ordnode.recOn l (insertMin x)) fun ls ll lx lr IHll IHlr r =>
  --   (Ordnode.recOn r (insertMax l x)) fun rs rl rx rr IHrl IHrr =>
  --     if delta * ls < rs then balanceL IHrl rx rr
  --     else if delta * rs < ls then balanceR ll lx (IHlr r) else node' l x r
  --
  -- failed to elaborate eliminator, expected type is not available.
  match l with
  | nil => insertMin x
  | node ls ll lx lr => fun r ↦
    match r with
    | nil => insertMax l x
    | node rs rl rx rr =>
      if delta * ls < rs then balanceL (link ll x rl) rx rr
      else if delta * rs < ls then balanceR ll lx (link lr x rr)
      else node' l x r
#align ordnode.link Ordnode.link

/-- O(n). Filter the elements of a tree satisfying a predicate.

     filter (fun x ↦ x < 3) {1, 2, 4} = {1, 2}
     filter (fun x ↦ x > 5) {1, 2, 4} = ∅ -/
def filter (p : α → Prop) [DecidablePred p] : Ordnode α → Ordnode α
  | nil => nil
  | node _ l x r => if p x then
                      link (filter p l) x (filter p r) else
                      merge (filter p l) (filter p r)
#align ordnode.filter Ordnode.filter

/-- O(n). Split the elements of a tree into those satisfying, and not satisfying, a predicate.

     partition (fun x ↦ x < 3) {1, 2, 4} = ({1, 2}, {3}) -/
def partition (p : α → Prop) [DecidablePred p] : Ordnode α → Ordnode α × Ordnode α
  | nil => (nil, nil)
  | node _ l x r =>
    let (l₁, l₂) := partition p l
    let (r₁, r₂) := partition p r
    if p x then (link l₁ x r₁, merge l₂ r₂) else (merge l₁ r₁, link l₂ x r₂)
#align ordnode.partition Ordnode.partition

/- warning: ordnode.map -> Ordnode.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, (α -> β) -> (Ordnode.{u1} α) -> (Ordnode.{u2} β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, (α -> β) -> (Ordnode.{u2} α) -> (Ordnode.{u1} β)
Case conversion may be inaccurate. Consider using '#align ordnode.map Ordnode.mapₓ'. -/
/-- O(n). Map a function across a tree, without changing the structure. Only valid when
the function is strictly monotone, i.e. `x < y → f x < f y`.

     partition (fun x ↦ x + 2) {1, 2, 4} = {2, 3, 6}
     partition (λ x : ℕ, x - 2) {1, 2, 4} = precondition violation -/
def map {β} (f : α → β) : Ordnode α → Ordnode β
  | nil => nil
  | node s l x r => node s (map f l) (f x) (map f r)
#align ordnode.map Ordnode.map

/- warning: ordnode.fold -> Ordnode.fold is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Sort.{u2}}, β -> (β -> α -> β -> β) -> (Ordnode.{u1} α) -> β
but is expected to have type
  forall {α : Type.{u2}} {β : Sort.{u1}}, β -> (β -> α -> β -> β) -> (Ordnode.{u2} α) -> β
Case conversion may be inaccurate. Consider using '#align ordnode.fold Ordnode.foldₓ'. -/
/-- O(n). Fold a function across the structure of a tree.

     fold z f {1, 2, 4} = f (f z 1 z) 2 (f z 4 z)

The exact structure of function applications depends on the tree and so
is unspecified. -/
def fold {β} (z : β) (f : β → α → β → β) : Ordnode α → β
  | nil => z
  | node _ l x r => f (fold z f l) x (fold z f r)
#align ordnode.fold Ordnode.fold

/- warning: ordnode.foldl -> Ordnode.foldl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Sort.{u2}}, (β -> α -> β) -> β -> (Ordnode.{u1} α) -> β
but is expected to have type
  forall {α : Type.{u2}} {β : Sort.{u1}}, (β -> α -> β) -> β -> (Ordnode.{u2} α) -> β
Case conversion may be inaccurate. Consider using '#align ordnode.foldl Ordnode.foldlₓ'. -/
/-- O(n). Fold a function from left to right (in increasing order) across the tree.

     foldl f z {1, 2, 4} = f (f (f z 1) 2) 4 -/
def foldl {β} (f : β → α → β) : β → Ordnode α → β
  | z, nil => z
  | z, node _ l x r => foldl f (f (foldl f z l) x) r
#align ordnode.foldl Ordnode.foldl

/- warning: ordnode.foldr -> Ordnode.foldr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Sort.{u2}}, (α -> β -> β) -> (Ordnode.{u1} α) -> β -> β
but is expected to have type
  forall {α : Type.{u2}} {β : Sort.{u1}}, (α -> β -> β) -> (Ordnode.{u2} α) -> β -> β
Case conversion may be inaccurate. Consider using '#align ordnode.foldr Ordnode.foldrₓ'. -/
/-- O(n). Fold a function from right to left (in decreasing order) across the tree.

     foldr f {1, 2, 4} z = f 1 (f 2 (f 4 z)) -/
def foldr {β} (f : α → β → β) : Ordnode α → β → β
  | nil, z => z
  | node _ l x r, z => foldr f l (f x (foldr f r z))
#align ordnode.foldr Ordnode.foldr

/-- O(n). Build a list of elements in ascending order from the tree.

     toList {1, 2, 4} = [1, 2, 4]
     toList {2, 1, 1, 4} = [1, 2, 4] -/
def toList (t : Ordnode α) : List α :=
  foldr List.cons t []
#align ordnode.to_list Ordnode.toList

/-- O(n). Build a list of elements in descending order from the tree.

     toRevList {1, 2, 4} = [4, 2, 1]
     toRevList {2, 1, 1, 4} = [4, 2, 1] -/
def toRevList (t : Ordnode α) : List α :=
  foldl (flip List.cons) [] t
#align ordnode.to_rev_list Ordnode.toRevList

instance [ToString α] : ToString (Ordnode α) :=
  ⟨fun t => "{" ++ String.intercalate ", " (t.toList.map toString) ++ "}"⟩

-- Porting note removed unsafe
instance [Std.ToFormat α] : Std.ToFormat (Ordnode α) where
  format := fun t => Std.Format.joinSep (t.toList.map Std.ToFormat.format) (Std.Format.text ", ")

/-- O(n). True if the trees have the same elements, ignoring structural differences.

     Equiv {1, 2, 4} {2, 1, 1, 4} = true
     Equiv {1, 2, 4} {1, 2, 3} = false -/
def Equiv (t₁ t₂ : Ordnode α) : Prop :=
  t₁.size = t₂.size ∧ t₁.toList = t₂.toList
#align ordnode.equiv Ordnode.Equiv

instance [DecidableEq α] : DecidableRel (@Equiv α) := fun _ _ => And.decidable

/-- O(2^n). Constructs the powerset of a given set, that is, the set of all subsets.

     powerset {1, 2, 3} = {∅, {1}, {2}, {3}, {1,2}, {1,3}, {2,3}, {1,2,3}} -/
def powerset (t : Ordnode α) : Ordnode (Ordnode α) :=
  insertMin nil <| foldr (fun x ts => glue (insertMin (ι x) (map (insertMin x) ts)) ts) t nil
#align ordnode.powerset Ordnode.powerset

/-- O(m * n). The cartesian product of two sets: `(a, b) ∈ s.prod t` iff `a ∈ s` and `b ∈ t`.

     prod {1, 2} {2, 3} = {(1, 2), (1, 3), (2, 2), (2, 3)} -/
protected def prod {β} (t₁ : Ordnode α) (t₂ : Ordnode β) : Ordnode (α × β) :=
  fold nil (fun s₁ a s₂ => merge s₁ <| merge (map (Prod.mk a) t₂) s₂) t₁
#align ordnode.prod Ordnode.prod

/-- O(m + n). Build a set on the disjoint union by combining sets on the factors.
`Or.inl a ∈ s.copair t` iff `a ∈ s`, and `Or.inr b ∈ s.copair t` iff `b ∈ t`.

    copair {1, 2} {2, 3} = {inl 1, inl 2, inr 2, inr 3} -/
protected def copair {β} (t₁ : Ordnode α) (t₂ : Ordnode β) : Ordnode (Sum α β) :=
  merge (map Sum.inl t₁) (map Sum.inr t₂)
#align ordnode.copair Ordnode.copair

/- warning: ordnode.pmap -> Ordnode.pmap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : α -> Prop} {β : Type.{u2}}, (forall (a : α), (P a) -> β) ->
    (forall (t : Ordnode.{u1} α), (Ordnode.All.{u1} α P t) -> (Ordnode.{u2} β))
but is expected to have type
  forall {α : Type.{u2}} {P : α -> Prop} {β : Type.{u1}}, (forall (a : α), (P a) -> β) ->
    (forall (t : Ordnode.{u2} α), (Ordnode.All.{u2} α P t) -> (Ordnode.{u1} β))S
Case conversion may be inaccurate. Consider using '#align ordnode.pmap Ordnode.pmapₓ'. -/
/-- O(n). Map a partial function across a set. The result depends on a proof
that the function is defined on all members of the set.

    pmap (fin.mk : ∀ n, n < 4 → fin 4) {1, 2} H = {(1 : fin 4), (2 : fin 4)} -/
def pmap {P : α → Prop} {β} (f : ∀ a, P a → β) : ∀ t : Ordnode α, All P t → Ordnode β
  | nil, _ => nil
  | node s l x r, ⟨hl, hx, hr⟩ => node s (pmap f l hl) (f x hx) (pmap f r hr)
#align ordnode.pmap Ordnode.pmap

/-- O(n). "Attach" the information that every element of `t` satisfies property
P to these elements inside the set, producing a set in the subtype.

    attach' (fun x ↦ x < 4) {1, 2} H = ({1, 2} : Ordnode {x // x<4}) -/
def attach' {P : α → Prop} : ∀ t, All P t → Ordnode { a // P a } :=
  pmap Subtype.mk
#align ordnode.attach' Ordnode.attach'

/-- O(log n). Get the `i`th element of the set, by its index from left to right.

     nth {a, b, c, d} 2 = some c
     nth {a, b, c, d} 5 = none -/
def nth : Ordnode α → ℕ → Option α
  | nil, _ => none
  | node _ l x r, i =>
    match Nat.psub' i (size l) with
    | none => nth l i
    | some 0 => some x
    | some (j + 1) => nth r j
#align ordnode.nth Ordnode.nth

/-- O(log n). Remove the `i`th element of the set, by its index from left to right.

     remove_nth {a, b, c, d} 2 = {a, b, d}
     remove_nth {a, b, c, d} 5 = {a, b, c, d} -/
def removeNth : Ordnode α → ℕ → Ordnode α
  | nil, _ => nil
  | node _ l x r, i =>
    match Nat.psub' i (size l) with
    | none => balanceR (removeNth l i) x r
    | some 0 => glue l r
    | some (j + 1) => balanceL l x (removeNth r j)
#align ordnode.remove_nth Ordnode.removeNth

/-- Auxiliary definition for `take`. (Can also be used in lieu of `take` if you know the
index is within the range of the data structure.)

    takeAux {a, b, c, d} 2 = {a, b}
    takeAux {a, b, c, d} 5 = {a, b, c, d} -/
def takeAux : Ordnode α → ℕ → Ordnode α
  | nil, _ => nil
  | node _ l x r, i =>
    if i = 0 then nil
    else
      match Nat.psub' i (size l) with
      | none => takeAux l i
      | some 0 => l
      | some (j + 1) => link l x (takeAux r j)
#align ordnode.take_aux Ordnode.takeAux

/-- O(log n). Get the first `i` elements of the set, counted from the left.

     take 2 {a, b, c, d} = {a, b}
     take 5 {a, b, c, d} = {a, b, c, d} -/
def take (i : ℕ) (t : Ordnode α) : Ordnode α :=
  if size t ≤ i then t else takeAux t i
#align ordnode.take Ordnode.take

/-- Auxiliary definition for `drop`. (Can also be used in lieu of `drop` if you know the
index is within the range of the data structure.)

    drop_aux {a, b, c, d} 2 = {c, d}
    drop_aux {a, b, c, d} 5 = ∅ -/
def dropAux : Ordnode α → ℕ → Ordnode α
  | nil, _ => nil
  | t@(node _ l x r), i =>
    if i = 0 then t
    else
      match Nat.psub' i (size l) with
      | none => link (dropAux l i) x r
      | some 0 => insertMin x r
      | some (j + 1) => dropAux r j
#align ordnode.drop_aux Ordnode.dropAux

/-- O(log n). Remove the first `i` elements of the set, counted from the left.

     drop 2 {a, b, c, d} = {c, d}
     drop 5 {a, b, c, d} = ∅ -/
def drop (i : ℕ) (t : Ordnode α) : Ordnode α :=
  if size t ≤ i then nil else dropAux t i
#align ordnode.drop Ordnode.drop

/-- Auxiliary definition for `splitAt`. (Can also be used in lieu of `splitAt` if you know the
index is within the range of the data structure.)

    splitAtAux {a, b, c, d} 2 = ({a, b}, {c, d})
    splitAtAux {a, b, c, d} 5 = ({a, b, c, d}, ∅) -/
def splitAtAux : Ordnode α → ℕ → Ordnode α × Ordnode α
  | nil, _ => (nil, nil)
  | t@(node _ l x r), i =>
    if i = 0 then (nil, t)
    else
      match Nat.psub' i (size l) with
      | none =>
        let (l₁, l₂) := splitAtAux l i
        (l₁, link l₂ x r)
      | some 0 => (glue l r, insertMin x r)
      | some (j + 1) =>
        let (r₁, r₂) := splitAtAux r j
        (link l x r₁, r₂)
#align ordnode.split_at_aux Ordnode.splitAtAux

/-- O(log n). Split a set at the `i`th element, getting the first `i` and everything else.

     splitAt 2 {a, b, c, d} = ({a, b}, {c, d})
     splitAt 5 {a, b, c, d} = ({a, b, c, d}, ∅) -/
def splitAt (i : ℕ) (t : Ordnode α) : Ordnode α × Ordnode α :=
  if size t ≤ i then (t, nil) else splitAtAux t i
#align ordnode.split_at Ordnode.splitAt

/-- O(log n). Get an initial segment of the set that satisfies the predicate `p`.
`p` is required to be antitone, that is, `x < y → p y → p x`.

    takeWhile (fun x ↦ x < 4) {1, 2, 3, 4, 5} = {1, 2, 3}
    takeWhile (fun x ↦ x > 4) {1, 2, 3, 4, 5} = precondition violation -/
def takeWhile (p : α → Prop) [DecidablePred p] : Ordnode α → Ordnode α
  | nil => nil
  | node _ l x r => if p x then link l x (takeWhile p r) else takeWhile p l
#align ordnode.take_while Ordnode.takeWhile

/-- O(log n). Remove an initial segment of the set that satisfies the predicate `p`.
`p` is required to be antitone, that is, `x < y → p y → p x`.

    dropWhile (fun x ↦ x < 4) {1, 2, 3, 4, 5} = {4, 5}
    dropWhile (fun x ↦ x > 4) {1, 2, 3, 4, 5} = precondition violation -/
def dropWhile (p : α → Prop) [DecidablePred p] : Ordnode α → Ordnode α
  | nil => nil
  | node _ l x r => if p x then dropWhile p r else link (dropWhile p l) x r
#align ordnode.drop_while Ordnode.dropWhile

/-- O(log n). Split the set into those satisfying and not satisfying the predicate `p`.
`p` is required to be antitone, that is, `x < y → p y → p x`.

    span (fun x ↦ x < 4) {1, 2, 3, 4, 5} = ({1, 2, 3}, {4, 5})
    span (fun x ↦ x > 4) {1, 2, 3, 4, 5} = precondition violation -/
def span (p : α → Prop) [DecidablePred p] : Ordnode α → Ordnode α × Ordnode α
  | nil => (nil, nil)
  | node _ l x r =>
    if p x then
      let (r₁, r₂) := span p r
      (link l x r₁, r₂)
    else
      let (l₁, l₂) := span p l
      (l₁, link l₂ x r)
#align ordnode.span Ordnode.span

/-- Auxiliary definition for `ofAscList`.

**Note:** This function is defined by well founded recursion, so it will probably not compute
in the kernel, meaning that you probably can't prove things like
`ofAscList [1, 2, 3] = {1, 2, 3}` by `rfl`.
This implementation is optimized for VM evaluation. -/
def ofAscListAux₁ : ∀ l : List α, ℕ → Ordnode α × { l' : List α // l'.length ≤ l.length }
  | [] => fun _ => (nil, ⟨[], le_rfl⟩)
  | x :: xs => fun s =>
    if s = 1 then (ι x, ⟨xs, Nat.le_succ _⟩)
    else
      match ofAscListAux₁ xs (s <<< 1) with
      | (t, ⟨[], _⟩) => (t, ⟨[], Nat.zero_le _⟩)
      | (l, ⟨y :: ys, h⟩) =>
        have := Nat.le_succ_of_le h
        let (r, ⟨zs, h'⟩) := ofAscListAux₁ ys (s <<< 1)
        (link l y r, ⟨zs, le_trans h' (le_of_lt this)⟩)
        termination_by ofAscListAux₁ l => l.length
#align ordnode.of_asc_list_aux₁ Ordnode.ofAscListAux₁

/-- Auxiliary definition for `ofAscList`. -/
def ofAscListAux₂ : List α → Ordnode α → ℕ → Ordnode α
  | [] => fun t _ => t
  | x :: xs => fun l s =>
    match ofAscListAux₁ xs s with
    | (r, ⟨ys, h⟩) =>
      have := Nat.lt_succ_of_le h
      ofAscListAux₂ ys (link l x r) (s <<< 1)
      termination_by ofAscListAux₂ l => l.length
#align ordnode.of_asc_list_aux₂ Ordnode.ofAscListAux₂

/-- O(n). Build a set from a list which is already sorted. Performs no comparisons.

     ofAscList [1, 2, 3] = {1, 2, 3}
     ofAscList [3, 2, 1] = precondition violation -/
def ofAscList : List α → Ordnode α
  | [] => nil
  | x :: xs => ofAscListAux₂ xs (ι x) 1
#align ordnode.of_asc_list Ordnode.ofAscList

section

variable [LE α] [@DecidableRel α (· ≤ ·)]

/-- O(log n). Does the set (approximately) contain the element `x`? That is,
is there an element that is equivalent to `x` in the order?

    1 ∈ {1, 2, 3} = true
    4 ∈ {1, 2, 3} = false

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    (1, 1) ∈ {(0, 1), (1, 2)} = true
    (3, 1) ∈ {(0, 1), (1, 2)} = false -/
def mem (x : α) : Ordnode α → Bool
  | nil => false
  | node _ l y r =>
    match cmpLE x y with
    | Ordering.lt => mem x l
    | Ordering.eq => true
    | Ordering.gt => mem x r
#align ordnode.mem Ordnode.mem

/-- O(log n). Retrieve an element in the set that is equivalent to `x` in the order,
if it exists.

    find 1 {1, 2, 3} = some 1
    find 4 {1, 2, 3} = none

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    find (1, 1) {(0, 1), (1, 2)} = some (1, 2)
    find (3, 1) {(0, 1), (1, 2)} = none -/
def find (x : α) : Ordnode α → Option α
  | nil => none
  | node _ l y r =>
    match cmpLE x y with
    | Ordering.lt => find x l
    | Ordering.eq => some y
    | Ordering.gt => find x r
#align ordnode.find Ordnode.find

instance : Membership α (Ordnode α) :=
  ⟨fun x t => t.mem x⟩

instance mem.decidable (x : α) (t : Ordnode α) : Decidable (x ∈ t) :=
  Bool.decEq _ _
#align ordnode.mem.decidable Ordnode.mem.decidable

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
If an equivalent element is already in the set, the function `f` is used to generate
the element to insert (being passed the current value in the set).

    insertWith f 0 {1, 2, 3} = {0, 1, 2, 3}
    insertWith f 1 {1, 2, 3} = {f 1, 2, 3}

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    insertWith f (1, 1) {(0, 1), (1, 2)} = {(0, 1), f (1, 2)}
    insertWith f (3, 1) {(0, 1), (1, 2)} = {(0, 1), (1, 2), (3, 1)} -/
def insertWith (f : α → α) (x : α) : Ordnode α → Ordnode α
  | nil => ι x
  | node sz l y r =>
    match cmpLE x y with
    | Ordering.lt => balanceL (insertWith f x l) y r
    | Ordering.eq => node sz l (f y) r
    | Ordering.gt => balanceR l y (insertWith f x r)
#align ordnode.insert_with Ordnode.insertWith

/-- O(log n). Modify an element in the set with the given function,
doing nothing if the key is not found.
Note that the element returned by `f` must be equivalent to `x`.

    adjustWith f 0 {1, 2, 3} = {1, 2, 3}
    adjustWith f 1 {1, 2, 3} = {f 1, 2, 3}

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    adjustWith f (1, 1) {(0, 1), (1, 2)} = {(0, 1), f (1, 2)}
    adjustWith f (3, 1) {(0, 1), (1, 2)} = {(0, 1), (1, 2)} -/
def adjustWith (f : α → α) (x : α) : Ordnode α → Ordnode α
  | nil => nil
  | _t@(node sz l y r) =>
    match cmpLE x y with
    | Ordering.lt => node sz (adjustWith f x l) y r
    | Ordering.eq => node sz l (f y) r
    | Ordering.gt => node sz l y (adjustWith f x r)
#align ordnode.adjust_with Ordnode.adjustWith

/-- O(log n). Modify an element in the set with the given function,
doing nothing if the key is not found.
Note that the element returned by `f` must be equivalent to `x`.

    updateWith f 0 {1, 2, 3} = {1, 2, 3}
    updateWith f 1 {1, 2, 3} = {2, 3}     if f 1 = none
                              = {a, 2, 3}  if f 1 = some a -/
def updateWith (f : α → Option α) (x : α) : Ordnode α → Ordnode α
  | nil => nil
  | _t@(node sz l y r) =>
    match cmpLE x y with
    | Ordering.lt => balanceR (updateWith f x l) y r
    | Ordering.eq =>
      match f y with
      | none => glue l r
      | some a => node sz l a r
    | Ordering.gt => balanceL l y (updateWith f x r)
#align ordnode.update_with Ordnode.updateWith

/-- O(log n). Modify an element in the set with the given function,
doing nothing if the key is not found.
Note that the element returned by `f` must be equivalent to `x`.

    alter f 0 {1, 2, 3} = {1, 2, 3}     if f none = none
                        = {a, 1, 2, 3}  if f none = some a
    alter f 1 {1, 2, 3} = {2, 3}     if f 1 = none
                        = {a, 2, 3}  if f 1 = some a -/
def alter (f : Option α → Option α) (x : α) : Ordnode α → Ordnode α
  | nil => Option.recOn (f none) nil Ordnode.singleton
  | _t@(node sz l y r) =>
    match cmpLE x y with
    | Ordering.lt => balance (alter f x l) y r
    | Ordering.eq =>
      match f (some y) with
      | none => glue l r
      | some a => node sz l a r
    | Ordering.gt => balance l y (alter f x r)
#align ordnode.alter Ordnode.alter

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
If an equivalent element is already in the set, this replaces it.

    insert 1 {1, 2, 3} = {1, 2, 3}
    insert 4 {1, 2, 3} = {1, 2, 3, 4}

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    insert (1, 1) {(0, 1), (1, 2)} = {(0, 1), (1, 1)}
    insert (3, 1) {(0, 1), (1, 2)} = {(0, 1), (1, 2), (3, 1)} -/
protected def insert (x : α) : Ordnode α → Ordnode α
  | nil => ι x
  | node sz l y r =>
    match cmpLE x y with
    | Ordering.lt => balanceL (Ordnode.insert x l) y r
    | Ordering.eq => node sz l x r
    | Ordering.gt => balanceR l y (Ordnode.insert x r)
#align ordnode.insert Ordnode.insert

instance : Insert α (Ordnode α) :=
  ⟨Ordnode.insert⟩

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
If an equivalent element is already in the set, the set is returned as is.

    insert' 1 {1, 2, 3} = {1, 2, 3}
    insert' 4 {1, 2, 3} = {1, 2, 3, 4}

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    insert' (1, 1) {(0, 1), (1, 2)} = {(0, 1), (1, 2)}
    insert' (3, 1) {(0, 1), (1, 2)} = {(0, 1), (1, 2), (3, 1)} -/
def insert' (x : α) : Ordnode α → Ordnode α
  | nil => ι x
  | t@(node _ l y r) =>
    match cmpLE x y with
    | Ordering.lt => balanceL (insert' x l) y r
    | Ordering.eq => t
    | Ordering.gt => balanceR l y (insert' x r)
#align ordnode.insert' Ordnode.insert'

/-- O(log n). Split the tree into those smaller than `x` and those greater than it.
If an element equivalent to `x` is in the set, it is discarded.

    split 2 {1, 2, 4} = ({1}, {4})
    split 3 {1, 2, 4} = ({1, 2}, {4})
    split 4 {1, 2, 4} = ({1, 2}, ∅)

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    split (1, 1) {(0, 1), (1, 2)} = ({(0, 1)}, ∅)
    split (3, 1) {(0, 1), (1, 2)} = ({(0, 1), (1, 2)}, ∅) -/
def split (x : α) : Ordnode α → Ordnode α × Ordnode α
  | nil => (nil, nil)
  | node _ l y r =>
    match cmpLE x y with
    | Ordering.lt =>
      let (lt, gt) := split x l
      (lt, link gt y r)
    | Ordering.eq => (l, r)
    | Ordering.gt =>
      let (lt, gt) := split x r
      (link l y lt, gt)
#align ordnode.split Ordnode.split

/-- O(log n). Split the tree into those smaller than `x` and those greater than it,
plus an element equivalent to `x`, if it exists.

    split3 2 {1, 2, 4} = ({1}, some 2, {4})
    split3 3 {1, 2, 4} = ({1, 2}, none, {4})
    split3 4 {1, 2, 4} = ({1, 2}, some 4, ∅)

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    split3 (1, 1) {(0, 1), (1, 2)} = ({(0, 1)}, some (1, 2), ∅)
    split3 (3, 1) {(0, 1), (1, 2)} = ({(0, 1), (1, 2)}, none, ∅) -/
def split3 (x : α) : Ordnode α → Ordnode α × Option α × Ordnode α
  | nil => (nil, none, nil)
  | node _ l y r =>
    match cmpLE x y with
    | Ordering.lt =>
      let (lt, f, gt) := split3 x l
      (lt, f, link gt y r)
    | Ordering.eq => (l, some y, r)
    | Ordering.gt =>
      let (lt, f, gt) := split3 x r
      (link l y lt, f, gt)
#align ordnode.split3 Ordnode.split3

/-- O(log n). Remove an element from the set equivalent to `x`. Does nothing if there
is no such element.

    erase 1 {1, 2, 3} = {2, 3}
    erase 4 {1, 2, 3} = {1, 2, 3}

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    erase (1, 1) {(0, 1), (1, 2)} = {(0, 1)}
    erase (3, 1) {(0, 1), (1, 2)} = {(0, 1), (1, 2)} -/
def erase (x : α) : Ordnode α → Ordnode α
  | nil => nil
  | _t@(node _ l y r) =>
    match cmpLE x y with
    | Ordering.lt => balanceR (erase x l) y r
    | Ordering.eq => glue l r
    | Ordering.gt => balanceL l y (erase x r)
#align ordnode.erase Ordnode.erase

/-- Auxiliary definition for `findLt`. -/
def findLtAux (x : α) : Ordnode α → α → α
  | nil, best => best
  | node _ l y r, best => if x ≤ y then findLtAux x l best else findLtAux x r y
#align ordnode.find_lt_aux Ordnode.findLtAux

/-- O(log n). Get the largest element in the tree that is `< x`.

     findLt 2 {1, 2, 4} = some 1
     findLt 3 {1, 2, 4} = some 2
     findLt 0 {1, 2, 4} = none -/
def findLt (x : α) : Ordnode α → Option α
  | nil => none
  | node _ l y r => if x ≤ y then findLt x l else some (findLtAux x r y)
#align ordnode.find_lt Ordnode.findLt

/-- Auxiliary definition for `findGt`. -/
def findGtAux (x : α) : Ordnode α → α → α
  | nil, best => best
  | node _ l y r, best => if y ≤ x then findGtAux x r best else findGtAux x l y
#align ordnode.find_gt_aux Ordnode.findGtAux

/-- O(log n). Get the smallest element in the tree that is `> x`.

     findGt 2 {1, 2, 4} = some 4
     findGt 3 {1, 2, 4} = some 4
     findGt 4 {1, 2, 4} = none -/
def findGt (x : α) : Ordnode α → Option α
  | nil => none
  | node _ l y r => if y ≤ x then findGt x r else some (findGtAux x l y)
#align ordnode.find_gt Ordnode.findGt

/-- Auxiliary definition for `findLe`. -/
def findLeAux (x : α) : Ordnode α → α → α
  | nil, best => best
  | node _ l y r, best =>
    match cmpLE x y with
    | Ordering.lt => findLeAux x l best
    | Ordering.eq => y
    | Ordering.gt => findLeAux x r y
#align ordnode.find_le_aux Ordnode.findLeAux

/-- O(log n). Get the largest element in the tree that is `≤ x`.

     findLe 2 {1, 2, 4} = some 2
     findLe 3 {1, 2, 4} = some 2
     findLe 0 {1, 2, 4} = none -/
def findLe (x : α) : Ordnode α → Option α
  | nil => none
  | node _ l y r =>
    match cmpLE x y with
    | Ordering.lt => findLe x l
    | Ordering.eq => some y
    | Ordering.gt => some (findLeAux x r y)
#align ordnode.find_le Ordnode.findLe

/-- Auxiliary definition for `findGe`. -/
def findGeAux (x : α) : Ordnode α → α → α
  | nil, best => best
  | node _ l y r, best =>
    match cmpLE x y with
    | Ordering.lt => findGeAux x l y
    | Ordering.eq => y
    | Ordering.gt => findGeAux x r best
#align ordnode.find_ge_aux Ordnode.findGeAux

-- Porting note: find_le → findGe
/-- O(log n). Get the smallest element in the tree that is `≥ x`.

     findGe 2 {1, 2, 4} = some 2
     findGe 3 {1, 2, 4} = some 4
     findGe 5 {1, 2, 4} = none -/
def findGe (x : α) : Ordnode α → Option α
  | nil => none
  | node _ l y r =>
    match cmpLE x y with
    | Ordering.lt => some (findGeAux x l y)
    | Ordering.eq => some y
    | Ordering.gt => findGe x r
#align ordnode.find_ge Ordnode.findGe

/-- Auxiliary definition for `findIndex`. -/
def findIndexAux (x : α) : Ordnode α → ℕ → Option ℕ
  | nil, _ => none
  | node _ l y r, i =>
    match cmpLE x y with
    | Ordering.lt => findIndexAux x l i
    | Ordering.eq => some (i + size l)
    | Ordering.gt => findIndexAux x r (i + size l + 1)
#align ordnode.find_index_aux Ordnode.findIndexAux

/-- O(log n). Get the index, counting from the left,
of an element equivalent to `x` if it exists.

    findIndex 2 {1, 2, 4} = some 1
    findIndex 4 {1, 2, 4} = some 2
    findIndex 5 {1, 2, 4} = none -/
def findIndex (x : α) (t : Ordnode α) : Option ℕ :=
  findIndexAux x t 0
#align ordnode.find_index Ordnode.findIndex

/-- Auxiliary definition for `isSubset`. -/
def isSubsetAux : Ordnode α → Ordnode α → Bool
  | nil, _ => true
  | _, nil => false
  | node _ l x r, t =>
    let (lt, found, gt) := split3 x t
    found.isSome && isSubsetAux l lt && isSubsetAux r gt
#align ordnode.is_subset_aux Ordnode.isSubsetAux

/-- O(m + n). Is every element of `t₁` equivalent to some element of `t₂`?

     is_subset {1, 4} {1, 2, 4} = tt
     is_subset {1, 3} {1, 2, 4} = ff -/
def isSubset (t₁ t₂ : Ordnode α) : Bool :=
  decide (size t₁ ≤ size t₂) && isSubsetAux t₁ t₂
#align ordnode.is_subset Ordnode.isSubset

/-- O(m + n). Is every element of `t₁` not equivalent to any element of `t₂`?

     disjoint {1, 3} {2, 4} = tt
     disjoint {1, 2} {2, 4} = ff -/
def disjoint : Ordnode α → Ordnode α → Bool
  | nil, _ => true
  | _, nil => true
  | node _ l x r, t =>
    let (lt, found, gt) := split3 x t
    found.isNone && disjoint l lt && disjoint r gt
#align ordnode.disjoint Ordnode.disjoint

/-- O(m * log(|m ∪ n| + 1)), m ≤ n. The union of two sets, preferring members of
  `t₁` over those of `t₂` when equivalent elements are encountered.

    union {1, 2} {2, 3} = {1, 2, 3}
    union {1, 3} {2} = {1, 2, 3}

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    union {(1, 1)} {(0, 1), (1, 2)} = {(0, 1), (1, 1)} -/
def union : Ordnode α → Ordnode α → Ordnode α
  | t₁, nil => t₁
  | nil, t₂ => t₂
  | t₁@(node s₁ l₁ x₁ r₁), t₂@(node s₂ _ x₂ _) =>
    if s₂ = 1 then insert' x₂ t₁
    else
      if s₁ = 1 then insert x₁ t₂
      else
        let (l₂', r₂') := split x₁ t₂
        link (union l₁ l₂') x₁ (union r₁ r₂')
#align ordnode.union Ordnode.union

/-- O(m * log(|m ∪ n| + 1)), m ≤ n. Difference of two sets.

    diff {1, 2} {2, 3} = {1}
    diff {1, 2, 3} {2} = {1, 3} -/
def diff : Ordnode α → Ordnode α → Ordnode α
  | t₁, nil => t₁
  | t₁, t₂@(node _ l₂ x r₂) =>
    cond t₁.empty t₂ <|
      let (l₁, r₁) := split x t₁
      let l₁₂ := diff l₁ l₂
      let r₁₂ := diff r₁ r₂
      if size l₁₂ + size r₁₂ = size t₁ then t₁ else merge l₁₂ r₁₂
#align ordnode.diff Ordnode.diff

/-- O(m * log(|m ∪ n| + 1)), m ≤ n. Intersection of two sets, preferring members of
`t₁` over those of `t₂` when equivalent elements are encountered.

    inter {1, 2} {2, 3} = {2}
    inter {1, 3} {2} = ∅ -/
def inter : Ordnode α → Ordnode α → Ordnode α
  | nil, _ => nil
  | t₁@(node _ l₁ x r₁), t₂ =>
    cond t₂.empty t₁ <|
      let (l₂, y, r₂) := split3 x t₂
      let l₁₂ := inter l₁ l₂
      let r₁₂ := inter r₁ r₂
      cond y.isSome (link l₁₂ x r₁₂) (merge l₁₂ r₁₂)
#align ordnode.inter Ordnode.inter

/-- O(n * log n). Build a set from a list, preferring elements that appear earlier in the list
in the case of equivalent elements.

    ofList [1, 2, 3] = {1, 2, 3}
    ofList [2, 1, 1, 3] = {1, 2, 3}

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    ofList [(1, 1), (0, 1), (1, 2)] = {(0, 1), (1, 1)} -/
def ofList (l : List α) : Ordnode α :=
  l.foldr insert nil
#align ordnode.of_list Ordnode.ofList

/-- O(n * log n). Adaptively chooses between the linear and log-linear algorithm depending
  on whether the input list is already sorted.

    ofList' [1, 2, 3] = {1, 2, 3}
    ofList' [2, 1, 1, 3] = {1, 2, 3} -/
def ofList' : List α → Ordnode α
  | [] => nil
  | x :: xs => if List.Chain (fun a b => ¬b ≤ a) x xs then ofAscList (x :: xs) else ofList (x :: xs)
#align ordnode.of_list' Ordnode.ofList'

/-- O(n * log n). Map a function on a set. Unlike `map` this has no requirements on
`f`, and the resulting set may be smaller than the input if `f` is noninjective.
Equivalent elements are selected with a preference for smaller source elements.

    image (fun x ↦ x + 2) {1, 2, 4} = {3, 4, 6}
    image (λ x : ℕ, x - 2) {1, 2, 4} = {0, 2} -/
def image {α β} [LE β] [@DecidableRel β (· ≤ ·)] (f : α → β) (t : Ordnode α) : Ordnode β :=
  ofList (t.toList.map f)
#align ordnode.image Ordnode.image

end

end Ordnode
