/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.MonoidAlgebra.PointwiseSMul

/-!
# Scalar multiplication by finitely supported functions.
Given sets `G` and `P`, with a left-cancellative vector-addition of `G` on `P`, we define an
antidiagonal function that assigns, for any element `a` in `P`, finite subset `s` of `G`, and subset
`t` in `P`, the `Set` of all pairs of an element in `s` and an element in `t` that vector-add to
`a`. When `R` is a ring and `V` is an `R`-module, we obtain a convolution-type action of the ring of
finitely supported `R`-valued functions on `G` on the space of `V`-valued functions on `P`.

## Definitions
* Finsupp.vaddAntidiagonal : The finset of pairs that vector-add to a given element.

-/

@[expose] public section

open Finset Function

noncomputable section

variable {G P F R S U V : Type*}

namespace Finsupp
@[deprecated (since := "2026-02-13")] alias finite_vaddAntidiagonal :=
  AddMonoidAlgebra.finite_vaddAntidiagonal

@[deprecated (since := "2026-02-13")] noncomputable alias vaddAntidiagonal :=
  AddMonoidAlgebra.vaddAntidiagonal

@[deprecated (since := "2026-02-13")] alias mem_vaddAntidiagonal_iff :=
  AddMonoidAlgebra.mem_vaddAntidiagonal_iff

@[deprecated (since := "2026-02-13")] alias mem_vaddAntidiagonal_of_addGroup :=
  AddMonoidAlgebra.mem_vaddAntidiagonal_of_addGroup

@[deprecated (since := "2026-02-13")] alias smul_eq := AddMonoidAlgebra.smul_eq

@[deprecated (since := "2026-02-13")] alias smul_apply_addAction :=
  AddMonoidAlgebra.smul_apply_addAction

end Finsupp
