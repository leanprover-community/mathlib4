/-
Copyright (c) 2019 mathlib community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Wojciech Nawrocki, Brendan Murphy
-/
import Std.Data.RBMap
import Mathlib.Data.Num.Basic
import Mathlib.Data.PNat.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Parity
import Mathlib.Order.Basic
import Mathlib.Init.Data.Ordering.Basic
import Mathlib.Util.CompileInductive
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.FinEnum
import Mathlib.Data.StdBitVec.Lemmas

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

/-- A binary tree with values of one type stored in non-leaf nodes
and values of another in the leaves. -/
inductive BinTree.{u, v} (N : Type u) (L : Type v) : Type (max u v)
  | leaf : L → BinTree N L
  | node : N → BinTree N L → BinTree N L → BinTree N L
  deriving DecidableEq, Repr

namespace BinTree

instance {L N} [Inhabited L] : Inhabited (BinTree N L) := ⟨leaf default⟩

universe u v

variable {α : Type u}

abbrev Leafless N := BinTree N Unit
abbrev Bare := Leafless Unit

@[match_pattern, simp, reducible]
def nil {N : Type v} : Leafless N := leaf ()

open Std (RBNode BitVec)
open Std.BitVec hiding nil

def ofRBNode : RBNode α → Leafless α
  | RBNode.nil => nil
  | RBNode.node _color l key r => node key (ofRBNode l) (ofRBNode r)

structure Path where
  length : ℕ
  private bitvec : BitVec length
  deriving DecidableEq, Repr

namespace Path

def here : Path := ⟨0, 0⟩
def left (p : Path) : Path := ⟨p.length + 1, p.bitvec.cons false⟩
def right (p : Path) : Path := ⟨p.length + 1, p.bitvec.cons true⟩

@[elab_as_elim] def rec' {motive : Path → Sort u} (atHere : motive here)
  (goLeft  : (p : Path) → motive p → motive (left  p))
  (goRight : (p : Path) → motive p → motive (right p)) (p : Path) : motive p :=
  -- can't use "cond"/"bif" because this is `Sort u` not `Type u`
  let step {w} : (b : Bool) → (v : BitVec w) → motive ⟨w, v⟩ → motive ⟨w+1, v.cons b⟩
    | false, v => goLeft ⟨w, v⟩
    | true, v => goRight ⟨w, v⟩
  consRecOn (motive := fun {w} v => motive ⟨w, v⟩) atHere step p.bitvec

@[simp] lemma rec'_left {motive : Path → Sort u} (atHere : motive here)
  (goLeft  : (p : Path) → motive p → motive (left  p))
  (goRight : (p : Path) → motive p → motive (right p)) (p : Path) :
    Path.rec' atHere goLeft goRight (left p)
    = goLeft p (Path.rec' atHere goLeft goRight p) := by apply consRecOn_cons

@[simp] lemma rec'_right {motive : Path → Sort u} (atHere : motive here)
  (goLeft  : (p : Path) → motive p → motive (left  p))
  (goRight : (p : Path) → motive p → motive (right p)) (p : Path) :
    Path.rec' atHere goLeft goRight (right p)
    = goRight p (Path.rec' atHere goLeft goRight p) := by apply consRecOn_cons

def append (p q : Path) : Path := ⟨p.length + q.length, p.bitvec ++ q.bitvec⟩
instance : Append Path := ⟨append⟩

def mirror (p : Path) : Path := ⟨p.length, ~~~p.bitvec⟩
def reverse (p : Path) : Path :=
  p.rec' id (fun _ f => f ∘ Path.left) (fun _ f => f ∘ Path.right) Path.here

def isHere? (p : Path) := p.length == 0
def startsWithLeft?  (p : Path) := p.length > 0 && !p.bitvec.msb
def startsWithRight? (p : Path) := p.bitvec.msb
def endsWithLeft?  (p : Path) := p.length > 0 && !(p.bitvec.getLsb 0)
def endsWithRight? (p : Path) := p.bitvec.getLsb 0

end Path

@[reducible]
def PosNum.toPath : PosNum → Path
  | PosNum.one    => Path.here
  | PosNum.bit0 b => Path.left (PosNum.toPath b)
  | PosNum.bit1 b => Path.right (PosNum.toPath b)

@[simp]
def numNodes {N L} : BinTree N L → ℕ
  | leaf _ => 0
  | node _ a b => a.numNodes + b.numNodes + 1

-- Notation for making a node with `Unit` data
scoped infixr:65 " △ " => BinTree.node ()

-- porting note: workaround for leanprover/lean4#2049
compile_inductive% BinTree

@[elab_as_elim]
def recOnBare {motive : Bare → Sort*} (t : Bare) (base : motive nil)
    (ind : ∀ x y, motive x → motive y → motive (x △ y)) : motive t :=
    -- Porting note: Old proof was `t.recOn base fun u => u.recOn ind` but
    -- structure eta makes it unnecessary (https://github.com/leanprover/lean4/issues/777).
    t.recOn (fun _ => base) fun _u => ind
#align tree.unit_rec_on BinTree.recOnBare

end BinTree
