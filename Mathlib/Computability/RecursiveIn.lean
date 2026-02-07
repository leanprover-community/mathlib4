/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
module

public import Mathlib.Computability.Partrec

/-!
# Oracle computability

This file defines oracle computability using partial recursive functions.

## Main definitions

- `RecursiveIn O f`: An inductive definition representing that a partial function `f` is partial
  recursive given access to a set of oracles O.

## Implementation notes

The type of partial functions recursive in a set of oracles `O` is the smallest type containing
the constant zero, the successor, left and right projections, each oracle `g ∈ O`,
and is closed under pairing, composition, primitive recursion, and μ-recursion.

## Tags

Computability, Oracle, Turing Degrees, Reducibility, Equivalence Relation
-/

@[expose] public section

open Primrec Nat.Partrec Part

variable {f g h : ℕ →. ℕ}

/--
The type of partial functions recursive in a set of oracles `O` is the smallest type containing
the constant zero, the successor, left and right projections, each oracle `g ∈ O`,
and is closed under pairing, composition, primitive recursion, and μ-recursion.
-/
inductive RecursiveIn (O : Set (ℕ →. ℕ)) : (ℕ →. ℕ) → Prop
  | zero : RecursiveIn O fun _ => 0
  | succ : RecursiveIn O Nat.succ
  | left : RecursiveIn O fun n => (Nat.unpair n).1
  | right : RecursiveIn O fun n => (Nat.unpair n).2
  | oracle : ∀ g ∈ O, RecursiveIn O g
  | pair {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun n => (Nat.pair <$> f n <*> h n)
  | comp {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun n => h n >>= f
  | prec {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun p =>
        let (a, n) := Nat.unpair p
        n.rec (f a) fun y IH => do
          let i ← IH
          h (Nat.pair a (Nat.pair y i))
  | rfind {f : ℕ →. ℕ} (hf : RecursiveIn O f) :
      RecursiveIn O fun a =>
        Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a n)

@[simp] lemma recursiveIn_empty_iff_partrec : RecursiveIn {} f ↔ Nat.Partrec f where
  mp fRecInNone := by
    induction fRecInNone with repeat {constructor}
    | oracle _ hg => simp at hg
    | pair | comp | prec | rfind =>
      repeat {constructor; assumption; try assumption}
  mpr pF := by
    induction pF with repeat {constructor}
    | pair _ _ ih₁ ih₂ => exact RecursiveIn.pair ih₁ ih₂
    | comp _ _ ih₁ ih₂ => exact RecursiveIn.comp ih₁ ih₂
    | prec _ _ ih₁ ih₂ => exact RecursiveIn.prec ih₁ ih₂
    | rfind _ ih => exact RecursiveIn.rfind ih
