/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/

import Mathlib.RingTheory.Teichmuller

/-!
# Untilt Function

In this file, we define the untilt function from the pretilt of a
`p`-adically complete ring to the ring itself. Note that this
is not the untilt *functor*.

## Main definition
* `PreTilt.untilt` : Given a `p`-adically complete ring `O`, this is the
  multiplicative map from `PreTilt O p` to `O` itself. Specifically, it is
  defined as the limit of `p^n`-th powers of arbitrary lifts in `O` of the
  `n`-th component from the perfection of `O/p`.

## Main theorem
* `PreTilt.mk_untilt_eq_coeff_zero` : The composition of the mod `p` map
  with the untilt function equals taking the zeroth component of the perfection.

## Reference
* [Berkeley Lectures on \( p \)-adic Geometry][MR4446467]

## Tags
Perfectoid, Tilting equivalence, Untilt
-/

open Perfection Ring.Perfection Ideal

namespace PreTilt

variable {O : Type*} [CommRing O] {p : ℕ} [Fact (Nat.Prime p)] [Fact ¬IsUnit (p : O)]
variable [IsAdicComplete (span {(p : O)}) O]

/--
Given a `p`-adically complete ring `O`, this is the
multiplicative map from `PreTilt O p` to `O` itself. Specifically, it is
defined as the limit of `p^n`-th powers of arbitrary lifts in `O` of the
`n`-th component from the perfection of `O/p`.
-/
noncomputable def untilt : PreTilt O p →* O :=
  teichmuller p _

/--
The composition of the mod `p` map
with the untilt function equals taking the zeroth component of the perfection.
-/
theorem mk_untilt_eq_coeff_zero (x : PreTilt O p) :
    Ideal.Quotient.mk (Ideal.span {(p : O)}) (x.untilt) = coeff (ModP O p) p 0 x :=
  mk_teichmuller x

/--
The composition of the mod `p` map
with the untilt function equals taking the zeroth component of the perfection.
A variation of `PreTilt.mk_untilt_eq_coeff_zero`.
-/
theorem mk_comp_untilt_eq_coeff_zero :
    Ideal.Quotient.mk (Ideal.span {(p : O)}) ∘ untilt = coeff (ModP O p) p 0 :=
  mk_comp_teichmuller' ..

end PreTilt
