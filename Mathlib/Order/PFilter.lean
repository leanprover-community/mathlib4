/-
Copyright (c) 2020 Mathieu Guay-Paquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathieu Guay-Paquet
-/
module

public import Mathlib.Order.Ideal

/-!
# Order filters

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections require more structure,
such as a bottom element, a top element, or a join-semilattice structure.

- `Order.PFilter P`: The type of nonempty, downward directed, upward closed subsets of `P`.
               This is dual to `Order.Ideal`, so it simply wraps `Order.Ideal Pᵒᵈ`.
- `Order.IsPFilter P`: a predicate for when a `Set P` is a filter.

Note the relation between `Order/Filter` and `Order/PFilter`: for any type `α`,
`Filter α` represents the same mathematical object as `PFilter (Set α)`.

## References

- <https://en.wikipedia.org/wiki/Filter_(mathematics)>

## Tags

pfilter, filter, ideal, dual

-/

deprecated_module (since := "2026-04-23") "all definitions are moved to `Order/Ideal.lean`."
