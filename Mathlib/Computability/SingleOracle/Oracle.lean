/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Modifications:
Copyright (c) 2026 Edwin Park.
-/
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.PFun
import Mathlib.Data.Nat.Find
import Mathlib.Computability.RecursiveIn

/-!
# Oracle.lean

This file takes only the necessary definitions and theorems from Mathlib/Computability/Partrec.lean
and relativises them.

The two main predicates defined are `PrimrecIn` and `RecursiveIn`, from which we define the Turing
degrees in Order.lean.
-/

open Nat

namespace Oracle.Single

/--
`RecursiveIn O f` asserts that the partial function `f : ℕ →. ℕ` is
partial recursive in `O : ℕ → ℕ`.

We note that `rfind` constructor here actually corresponds to `rfind'`.
-/
inductive RecursiveIn (O : ℕ → ℕ) : (ℕ →. ℕ) → Prop
  | zero : RecursiveIn O fun _ => 0
  | succ : RecursiveIn O Nat.succ
  | left : RecursiveIn O fun n => (Nat.unpair n).1
  | right : RecursiveIn O fun n => (Nat.unpair n).2
  | oracle : RecursiveIn O O
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
      RecursiveIn O
        <| Nat.unpaired fun a m =>
          (Nat.rfind fun n => (fun x => x = 0) <$> f (Nat.pair a (n + m))).map (· + m)

/-- The primitive recursive functions, but with the oracle `O` as an additional initial function. -/
inductive PrimrecIn (O : ℕ → ℕ) : (ℕ → ℕ) → Prop
  | zero : PrimrecIn O fun _ => 0
  | protected succ : PrimrecIn O succ
  | left : PrimrecIn O fun n => n.unpair.1
  | right : PrimrecIn O fun n => n.unpair.2
  | oracle : PrimrecIn O O
  | pair {f g} : PrimrecIn O f → PrimrecIn O g → PrimrecIn O fun n => pair (f n) (g n)
  | comp {f g} : PrimrecIn O f → PrimrecIn O g → PrimrecIn O fun n => f (g n)
  | prec {f g} :
      PrimrecIn O f →
        PrimrecIn O g →
          PrimrecIn O (unpaired fun z n => n.rec (f z) fun y IH => g <| pair z <| pair y IH)

end Oracle.Single
