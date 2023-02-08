/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers

! This file was ported from Lean 3 source module linear_algebra.affine_space.basic
! leanprover-community/mathlib commit 98e83c3d541c77cdb7da20d79611a780ff8e7d90
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.AddTorsor

/-!
# Affine space

In this file we introduce the following notation:

* `affine_space V P` is an alternative notation for `add_torsor V P` introduced at the end of this
  file.

We tried to use an `abbreviation` instead of a `notation` but this led to hard-to-debug elaboration
errors. So, we introduce a localized notation instead. When this notation is enabled with
`open_locale affine`, Lean will use `affine_space` instead of `add_torsor` both in input and in the
proof state.

Here is an incomplete list of notions related to affine spaces, all of them are defined in other
files:

* `affine_map`: a map between affine spaces that preserves the affine structure;
* `affine_equiv`: an equivalence between affine spaces that preserves the affine structure;
* `affine_subspace`: a subset of an affine space closed w.r.t. affine combinations of points;
* `affine_combination`: an affine combination of points;
* `affine_independent`: affine independent set of points;
* `affine_basis.coord`: the barycentric coordinate of a point.

## TODO

Some key definitions are not yet present.

* Affine frames.  An affine frame might perhaps be represented as an `affine_equiv` to a `finsupp`
  (in the general case) or function type (in the finite-dimensional case) that gives the
  coordinates, with appropriate proofs of existence when `k` is a field.
 -/


-- mathport name: add_torsor
scoped[Affine] notation "affine_space" => AddTorsor

