/-
Copyright (c) 2021 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/
import Mathlib.Control.Random
import Mathlib.Data.List.Perm
import Mathlib.Data.Subtype
import Mathlib.Data.Nat.Basic

/-!
# `Gen` Monad
This monad is used to formulate randomized computations with a parameter
to specify the desired size of the result.
This is a port of the Haskell QuickCheck library.

## Main definitions
  * `Gen` monad

## Tags

random testing

## References
  * https://hackage.haskell.org/package/QuickCheck
-/

namespace SlimCheck

open Random

/-- Monad to generate random examples to test properties with.
It has a `Nat` parameter so that the caller can decide on the
size of the examples. -/
abbrev Gen (α : Type u) := ReaderT (ULift Nat) Rand α

namespace Gen

/-- Lift `Random.random` to the `Gen` monad. -/
def chooseAny (α : Type u) [Random α] : Gen α :=
  λ _ => rand α

/-- Lift `BoundedRandom.randomR` to the `Gen` monad. -/
def choose (α : Type u) [Preorder α] [BoundedRandom α] (lo hi : α) (h : lo ≤ hi) : Gen {a // lo ≤ a ∧ a ≤ hi} :=
  λ _ => randBound α lo hi h

lemma chooseNatLt_aux {lo hi : Nat} (a : Nat) (h : Nat.succ lo ≤ a ∧ a ≤ hi) : lo ≤ Nat.pred a ∧ Nat.pred a < hi :=
  And.intro (Nat.le_pred_of_lt (Nat.lt_of_succ_le h.left)) <|
    show a.pred.succ ≤ hi by
       rw [Nat.succ_pred_eq_of_pos]
       exact h.right
       exact lt_of_le_of_lt (Nat.zero_le lo) h.left

/-- Generate a `Nat` example between `x` and `y` (exclusively). -/
def chooseNatLt (lo hi : Nat) (h : lo < hi) : Gen {a // lo ≤ a ∧ a < hi} :=
  Subtype.map Nat.pred chooseNatLt_aux <$> choose Nat (lo.succ) hi (Nat.succ_le_of_lt h)

/-- Get access to the size parameter of the `Gen` monad. -/
def getSize : Gen Nat :=
  return (← read).down

/-- Apply a function to the size parameter. -/
def resize (f : Nat → Nat) (x : Gen α) : Gen α :=
  withReader (ULift.up ∘ f ∘ ULift.down) x

/-- Create an `Array` of examples using `x`. The size is controlled
by the size parameter of `Gen`. -/
def arrayOf (x : Gen α) : Gen (Array α) := do
  let sz ← choose Nat 0 (←getSize) (Nat.zero_le _)
  let mut res := #[]
  for _ in [0:sz] do
    res := res.push (← x)
  pure res

/-- Create an `List` of examples using `x`. The size is controlled
by the size parameter of `Gen`. -/
def listOf (x : Gen α) : Gen (List α) :=
  arrayOf x >>= pure ∘ Array.toList

/-- Given a list of example generators, choose one to create an example. -/
def oneOf (xs : Array (Gen α)) (pos : 0 < xs.size := by decide) : Gen α := do
  let ⟨x, _, h2⟩ ← chooseNatLt 0 xs.size pos
  xs.get ⟨x, h2⟩

/-- Given a list of examples, choose one to create an example. -/
def elements (xs : List α) (pos : 0 < xs.length) : Gen α := do
  let ⟨x, _, h2⟩ ← chooseNatLt 0 xs.length pos
  pure $ xs.get ⟨x, h2⟩

open List in
/-- Generate a random permutation of a given list. -/
def permutationOf : (xs : List α) → Gen { ys // ys ~ xs }
| [] => pure ⟨[], Perm.nil⟩
| x::xs => do
  let ⟨ys, h1⟩ ← permutationOf xs
  let ⟨n, _, h3⟩ ← choose Nat 0 ys.length (Nat.zero_le _)
  pure ⟨insertNth n x ys, Perm.trans (perm_insertNth h3) (Perm.cons _ h1)⟩

/-- Given two generators produces a tuple consisting out of the result of both -/
def prodOf {α β : Type u} (x : Gen α) (y : Gen β) : Gen (α × β) := do
  pure (←x, ←y)

end Gen

/-- Execute a `Gen` inside the `IO` monad using `size` as the example size-/
def Gen.run (x : Gen α) (size : Nat) : BaseIO α :=
  IO.runRand $ ReaderT.run x ⟨size⟩


end SlimCheck
