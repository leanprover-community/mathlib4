/-
Copyright (c) 2019 mathlib community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Wojciech Nawrocki
-/
import Mathlib.Data.Num.Basic
import Mathlib.Data.Tree.Basic

#align_import data.tree from "leanprover-community/mathlib"@"ed989ff568099019c6533a4d94b27d852a5710d8"

/-!
# Binary tree get operation

In this file we define `Tree.indexOf`, `Tree.get`, and `Tree.getOrElse`.
These definitions were moved from the main file to avoid a dependency on `Num`.

## References

<https://leanprover-community.github.io/archive/stream/113488-general/topic/tactic.20question.html#170999997>
-/

namespace Tree

variable {α : Type*}

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

end Tree
