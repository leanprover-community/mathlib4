/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Join.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# Pseudofunctoriality of categorical joins

In this file, we promote the join construction to two pseudofunctors
`Join.pseudoFunctorLeft` and `Join.pseudoFunctorRight`, expressing its pseudofunctoriality in
each variable


## Main constructions
- `Join.edge c d`: the unique map from `c` to `d`.
- `Join.inclLeft : C ⥤ C ⋆ D`, the left inclusion. Its action on morphism is the main entry point
to constructs maps in `C ⋆ D` between objects coming from `C`.
- `Join.inclRight : D ⥤ C ⋆ D`, the left inclusion. Its action on morphism is the main entry point
to constructs maps in `C ⋆ D` between object coming from `D`.
- `Join.mkFunctor`, A constructor for functors out of a join of categories.
- `Join.mkNatTrans`, A constructor for natural transformations between functors out of a join
  of categories.
- `Join.mkNatIso`, A constructor for natural isomorphisms between functors out of a join
  of categories.

-/
