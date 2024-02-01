/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Algebra.AddTorsor

#align_import linear_algebra.affine_space.basic from "leanprover-community/mathlib"@"98e83c3d541c77cdb7da20d79611a780ff8e7d90"

/-!
# Affine space

In this file we introduce the following notation:

* `AffineSpace V P` is an alternative notation for `AddTorsor V P` introduced at the end of this
  file.

We tried to use an `abbreviation` instead of a `notation` but this led to hard-to-debug elaboration
errors. So, we introduce a localized notation instead. When this notation is enabled with
`open Affine`, Lean will use `AffineSpace` instead of `AddTorsor` both in input and in the
proof state.

Here is an incomplete list of notions related to affine spaces, all of them are defined in other
files:

* `AffineMap`: a map between affine spaces that preserves the affine structure;
* `AffineEquiv`: an equivalence between affine spaces that preserves the affine structure;
* `AffineSubspace`: a subset of an affine space closed w.r.t. affine combinations of points;
* `AffineCombination`: an affine combination of points;
* `AffineIndependent`: affine independent set of points;
* `AffineBasis.coord`: the barycentric coordinate of a point.

## TODO

Some key definitions are not yet present.

* Affine frames.  An affine frame might perhaps be represented as an `AffineEquiv` to a `Finsupp`
  (in the general case) or function type (in the finite-dimensional case) that gives the
  coordinates, with appropriate proofs of existence when `k` is a field.
 -/


@[inherit_doc] scoped[Affine] notation "AffineSpace" => AddTorsor
