/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# Conditionally convergent sums and products

Let `f : β → α` be a function, where `α` is a commutative additive monoid with a topology and
`β` is a type equipped with a locally finite preorder (`LocallyFiniteOrder`). In this file, we
define what it means for the sum $\sum_{b \in \beta} f(b)$ to *conditionally converge* to an element
`a : α` (`HasConditionalSum`). In the important case that `β = ℕ`, this is equivalent to the
statement that the partial sums $\sum_{i = 0}^{n - 1} f(n)$ converge to `a` as `n → ∞`.

We similarly define what it means for a product in a commutative multiplicative monoid
to conditionally converge.

## Main definitions



-/

def
