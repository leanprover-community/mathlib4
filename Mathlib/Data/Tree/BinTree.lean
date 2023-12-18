/-
Copyright (c) 2019 mathlib community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Wojciech Nawrocki, Brendan Murphy
-/
import Std.Data.RBMap
import Mathlib.Util.CompileInductive
import Mathlib.Data.FinEnum
import Mathlib.Data.Tree.BinAddr
import Mathlib.Control.Bitraversable.Basic

#align_import data.tree from "leanprover-community/mathlib"@"ed989ff568099019c6533a4d94b27d852a5710d8"

/-!
# Binary tree

Provides binary tree storage with data at both the leaves and nodes.
Data at nodes can be retrieved with O(lg n) comparisons.
See also `Lean.Data.RBTree` for red-black trees - this version allows more operations
to be defined and is better suited for in-kernel computation.

We also specialize for `BinTree Unit Unit`, which is a binary tree without any
additional data. We provide the notation `a △ b` for making
a `BinTree Unit Unit` with children `a` and `b`.

## References

<https://leanprover-community.github.io/archive/stream/113488-general/topic/tactic.20question.html>
-/

-- inductive NodeType where | Inner | Leaf deriving DecidableEq, Repr
inductive FollowStatus where | Inner | Leaf | NoNode deriving DecidableEq, Repr
open FollowStatus (NoNode)

/-- A binary tree with values of one type stored in non-leaf nodes
and values of another in the leaves. -/
inductive BinTree.{u, v} (N : Type u) (L : Type v) : Type (max u v)
  | leaf : L → BinTree N L
  | branch : N → BinTree N L → BinTree N L → BinTree N L
  deriving DecidableEq, Repr

-- porting note: workaround for leanprover/lean4#2049
compile_inductive% BinTree

namespace BinTree

instance {L N} [Inhabited L] : Inhabited (BinTree N L) := ⟨leaf default⟩

universe u v w

variable {α : Type u} {β : Type v}

abbrev Leafless N := BinTree N Unit
abbrev Bare := Leafless Unit

@[match_pattern, simp, reducible]
def nil {N : Type v} : Leafless N := leaf ()

open Std (RBNode)
def ofRBNode : RBNode α → Leafless α
  | RBNode.nil => nil
  | RBNode.node _color l key r => branch key (ofRBNode l) (ofRBNode r)

def perfect (x : α) (y : β) : ℕ → BinTree α β
  | 0 => leaf y
  | n+1 => branch x (perfect x y n) (perfect x y n)

nonrec def Bare.perfect : ℕ → Bare := perfect () ()

-- Notation for making a node with `Unit` data
scoped infixr:65 " △ " => BinTree.branch ()

@[eliminator]
def recOnBare {motive : Bare → Sort*} (t : Bare) (base : motive nil)
    (ind : ∀ x y, motive x → motive y → motive (x △ y)) : motive t :=
    -- Porting note: Old proof was `t.recOn base fun u => u.recOn ind` but
    -- structure eta makes it unnecessary (https://github.com/leanprover/lean4/issues/777).
    t.recOn (fun _ => base) fun _u => ind
#align tree.unit_rec_on BinTree.recOnBare

end BinTree
