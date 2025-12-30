/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.Convex.DoublyStochasticMatrix

/-!
# Majorization

Given two vectors `x y : n → R` (with `n` finite), we say that

* `y` submajorizes `x` (`x ≼ₛ y`) if `∀ k, ∑ i ≤ k, x↓ i ≤ ∑ i ≤ k, y↓ i` where `x↓` denotes
the values of `x` sorted in decreasing order (this notation is not used here, only in the
docstring).
* `y` supermajorizes `x` (`x ≼ˢ y`) if `∀ k, ∑ i ≤ k, y↑ i ≤ ∑ i ≤ k, x↑ i`.
* `y` majorizes `x` (`x ≼ y`) if `x ≼ₛ y` and `∑ i, x i = ∑ i, y i`.

## Implementation notes

There are several characterizations of this notion, and one that is more amenable to
formalization (since it avoids having to introduce equivs to sort values), is the one that
makes use of the fact that
`∑ i ≤ k, x↓ i = max_{s, #s = k} ∑ i ∈ s, x i`
and likewise for the increasing sum. This is what we take as the definition here.

## References

* Rajendra Bhatia, ``Matrix Analysis'', Chapter 2.
-/

@[expose] public section
