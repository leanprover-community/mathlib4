/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.RingTheory.Teichmuller
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

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

@[expose] public section

open Ideal Perfection

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
@[simp]
theorem mk_untilt_eq_coeff_zero (x : PreTilt O p) :
    Ideal.Quotient.mk (Ideal.span {(p : O)}) (x.untilt) = coeff 0 x :=
  mk_teichmuller x

/--
The composition of the mod `p` map
with the untilt function equals taking the zeroth component of the perfection.
A variation of `PreTilt.mk_untilt_eq_coeff_zero`.
-/
@[simp]
theorem mk_comp_untilt_eq_coeff_zero :
    Ideal.Quotient.mk (Ideal.span {(p : O)}) ∘ untilt = coeff 0 :=
  mk_comp_teichmuller' ..

@[simp]
theorem untilt_iterate_frobeniusEquiv_symm_pow (x : PreTilt O p) (n : ℕ) :
    untilt (((frobeniusEquiv (PreTilt O p) p).symm^[n]) x) ^ p ^ n = x.untilt := by
  simp only [← map_pow]
  congr
  simp

end PreTilt
