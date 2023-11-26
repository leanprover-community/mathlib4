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

#align_import data.tree from "leanprover-community/mathlib"@"ed989ff568099019c6533a4d94b27d852a5710d8"

section ShouldBeMoved

-- added in mathlib commit 2df406b
axiom Nat.and_two_pow (n i : ℕ) : n &&& 2 ^ i = (n.testBit i).toNat * 2 ^ i

-- added in mathlib commit 546faa6
@[simp] lemma Bool.toNat_beq_one  (b : Bool) : (b.toNat == 1) =  b := by cases b <;> rfl

-- #check Nat.mod_two_of_bodd
-- example (n : ℕ) (h : n > 0) : n &&& 1 = 1 ↔ Odd n := by
--   change n &&& 2^0 = 1 ↔ Odd n
--   rw [Nat.and_two_pow, Nat.pow_zero, Nat.mul_one, ← beq_iff_eq,
--       Bool.toNat_beq_one, Nat.testBit, Nat.shiftRight_zero]

lemma Nat.succ_shift_eq (n : ℕ) : (n <<< 1) ||| 1 = 2 * n + 1 := by
  change 2 * n ||| 1 = 2 * n + 1
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_lor]
  simp (config:={singlePass:=true}) only
    [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  cases' Nat.eq_zero_or_pos i with h h
  . simp only [h, Nat.pow_zero, Nat.div_one, Nat.bodd_succ, Nat.bodd_mul]
    refine Eq.trans (Bool.or_true _) $ Eq.symm $ congrArg _ (Bool.false_and _)
  . refine Eq.trans ?_ (Bool.or_false _)
    refine congrArg₂ _ (congrArg _ ?_) ?_
    . rw [Nat.succ_div, self_eq_add_right, ite_eq_right_iff]
      refine Not.elim $ mt (Nat.dvd_of_pow_dvd h) ?_
      exact Nat.two_not_dvd_two_mul_add_one n
    . refine Eq.trans (congrArg _ ?_) Nat.bodd_zero
      refine (Nat.div_eq_zero_iff ((pow_pos_iff h).mpr two_pos)).mpr ?_
      exact Nat.one_lt_pow _ _ h one_lt_two

end ShouldBeMoved

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

universe u v

variable {α : Type u}

abbrev Leafless N := BinTree N Unit

@[match_pattern, simp, reducible]
def nil {N : Type v} : Leafless N := leaf ()

open Std (RBNode)

def ofRBNode : RBNode α → Leafless α
  | RBNode.nil => nil
  | RBNode.node _color l key r => node key (ofRBNode l) (ofRBNode r)

structure Path where
  private bitarray : ℕ
  private hasMSB   : bitarray ≠ 0
  deriving DecidableEq, Repr, Ord

namespace Path

def here : Path := ⟨1, Nat.one_ne_zero⟩
def left (p : Path) : Path :=
  ⟨p.bitarray <<< 1, Nat.mul_ne_zero (Nat.succ_ne_zero 1) p.hasMSB⟩
def right (p : Path) : Path :=
  ⟨(p.bitarray <<< 1) ||| 1, Nat.succ_shift_eq _ ▸ Nat.succ_ne_zero _⟩

@[elab_as_elim] def rec' {motive : Path → Sort u} (atHere : motive here)
  (goLeft  : (p : Path) → motive p → motive (left  p))
  (goRight : (p : Path) → motive p → motive (right p))
  (p : Path) : motive p :=
  @Nat.binaryRecFromOne (fun n => (h : n ≠ 0) → motive ⟨n, h⟩)
    (Not.elim . rfl) (fun _ => atHere)
    (fun b n hn H h =>
      match b with
      | false =>  suffices left (⟨n, hn⟩) = ⟨Nat.bit false n, h⟩
                  from this ▸ goLeft _ (H hn)
                  by dsimp only [left]; congr; exact Nat.two_mul n
      | true => suffices right (⟨n, hn⟩) = ⟨Nat.bit true n, h⟩
                from this ▸ goRight _ (H hn)
                by  dsimp only [right]; congr
                    refine Eq.trans (Nat.succ_shift_eq n) ?_
                    exact congrArg Nat.succ (Nat.two_mul n))
    p.bitarray p.hasMSB

@[simp] lemma rec'_left {motive : Path → Sort u} (atHere : motive here)
  (goLeft  : (p : Path) → motive p → motive (left  p))
  (goRight : (p : Path) → motive p → motive (right p)) (p : Path) :
    Path.rec' atHere goLeft goRight (left p)
    = goLeft p (Path.rec' atHere goLeft goRight p) :=
  suffices ∀ n m (hn : n ≠ 0) (hm : m ≠ 0), n = 2 * m →
    HEq (Path.rec' atHere goLeft goRight ⟨n, hn⟩ : motive ⟨n, hn⟩)
        (goLeft ⟨m, hm⟩ (Path.rec' atHere goLeft goRight ⟨m, hm⟩))
  by apply eq_of_heq
     let n := p.bitarray
     let hn := p.hasMSB
     exact this (2 * n) n (Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp Nat.two_pos) hn) hn rfl
  by admit
    -- by
  -- cases' p with n h
  -- simp [left, rec', Nat.binaryRecFromOne, Nat.binaryRec']


  -- have := Nat.binaryRec_eq _ false n

  -- convert Nat.binaryRec_eq _ false n


  -- have h1 : (left p).bitarray = Nat.bit false p.bitarray := Nat.two_mul _
  -- have h2 : left p = ⟨Nat.bit false p.bitarray, h1 ▸ (left p).hasMSB⟩ :=
  --   by dsimp [left]; congr
  -- by
  --    admit
    --  refine Eq.symm ?_
    --  apply eq_of_heq
    --  refine HEq.trans ?_ (heq_of_cast_eq (congrArg motive h2.symm) rfl)



  -- dsimp only [Path.rec', Nat.binaryRecFromOne]
  -- have : (left p).bitarray = bit0 p.bitarray := sorry


  -- Nat.binaryRec_eq

    --goLeft goRight (left p) = goLeft p := sorry

def mirror (p : Path) : Path := sorry

def isHere? (p : Path) := p.bitarray == 1
def startsWithLeft?  (p : Path) := p.bitarray &&& 1 == 1
def startsWithRight? (p : Path) := (p.bitarray ^^^ 1) &&& 1 == 1

end Path

-- @[reducible]
-- def PosNum.toPath (p : PosNum) : Path :=
--   | PosNum.one    => Path.here
--   | PosNum.bit0 b => Path.left (PosNum.toPath b)
--   | PosNum.bit1 b => Path.right (PosNum.toPath b)


end BinTree
