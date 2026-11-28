/-
Copyright (c) 2026 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
module

import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# Bracketing functions

Bracketing functions `a : Fin n → Fin n` provide an elementary description of the Tamari lattice.
They correspond to the more classical encoding of binary trees as follows: Labelling the vertices
of the binary tree with the in-order traversal, i.e. recursively numbering first the left tree, then
the root, and finally the right tree, `a i` is the largest label occurring in the subtree rooted at
`i`. The partial order is then just given by componentwise comparison. This partial order is in fact
a lattice with meet given componentwise, but join given as the least bracketing function above the
pointwise maximum.

As an example, for `n = 3` one obtains the following Hasse diagram:

```
              ![2,2,2]
               /      \
              /        \
             /      ![2,1,2]
        ![0,2,2]        |
             \          |
              \     ![1,1,2]
               \       /
                \     /
                ![0,1,2]
```

## Main definitions

* `Function.IsBracketing`: A predicate on functions `a : Fin n → Fin n` to satisfy the property of
  being a bracketing function, i.e. `i ≤ a i` and `i ≤ j ≤ a i → a j ≤ a i`.
* `BracketingFunctions n`: The `Type` of all bracketing functions `Fin n → Fin n`.

## Implementation details

In the literature, bracketing functions have been defined as functions `Icc 1 n → Icc 1 n`. As is
customary, we have shifted our functions to instead go `Fin n → Fin n`.

## References

* Huang, Samuel and Tamari, Dov: Problems of Associativity: A Simple Proof for the Lattice Property
  of Systems Ordered by a Semi-associative Law, Journal of Combinatorial Theory (A) 13, 7--13 (1972)

## TODO

* Combinatorially describe the covering relation for the Tamari lattice
* Give a bijection between bracketing functions and binary trees.
* Show that the Tamari lattice is semidistributive.
* Show that the Tamari lattice is trim.

-/
variable {n : ℕ}

namespace Function

/-- A function `a : Fin n → Fin n` is bracketing if `i ≤ a i` for all `i` and for all `i` and `j`
such that `i ≤ j ≤ a i` one has `a j ≤ a i`. -/
public def IsBracketing (a : Fin n → Fin n) : Prop :=
  (∀ i, i ≤ a i) ∧ (∀ i j, i ≤ j → j ≤ a i → a j ≤ a i)
deriving Decidable

lemma IsBracketing.self_le {a : Fin n → Fin n} (ha : a.IsBracketing) (i : Fin n) : i ≤ a i :=
  ha.1 i

lemma IsBracketing.apply_le {a : Fin n → Fin n} (ha : a.IsBracketing) (i j) (hij : i ≤ j)
    (hjai : j ≤ a i) : a j ≤ a i := ha.2 i j hij hjai

lemma IsBracketing.apply_last {a : Fin (n + 1) → Fin (n + 1)} (ha : a.IsBracketing) :
    a (Fin.last n) = Fin.last n := le_antisymm (Fin.le_last _) (ha.self_le _)

lemma isBracketing_id : (id : Fin n → Fin n).IsBracketing := ⟨fun _ ↦ le_rfl, fun _ _ _ hji ↦ hji⟩

lemma isBracketing_const_last : (const _ (Fin.last n)).IsBracketing :=
  ⟨fun i ↦ i.le_last, fun _ _ _ _ ↦ le_rfl⟩

lemma IsBracketing.isFixedPt {a : Fin n → Fin n} (ha : a.IsBracketing) (i : Fin n) :
    IsFixedPt a (a i) :=
  le_antisymm (ha.apply_le _ _ (ha.self_le _) (le_refl _)) (ha.self_le _)

lemma IsBracketing.comp_self {a : Fin n → Fin n} (ha : a.IsBracketing) : a ∘ a = a := by
  funext i
  simpa only [comp_apply, IsFixedPt] using ha.isFixedPt i

end Function

/-- The `Type` of bracketing functions `Fin n → Fin n`. -/
abbrev BracketingFunctions (n : ℕ) : Type := {a : Fin n → Fin n // a.IsBracketing}

def Function.IsBracketing.toBracketingFunctions {a : Fin n → Fin n} (ha : a.IsBracketing) :
    BracketingFunctions n := ⟨a, ha⟩

lemma BracketingFunctions.isBracketing (a : BracketingFunctions n) :
    (a : Fin n → Fin n).IsBracketing := a.2
