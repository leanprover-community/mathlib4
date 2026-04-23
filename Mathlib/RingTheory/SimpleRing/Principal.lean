/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.SimpleRing.Defs
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.SimpleRing.Field
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# A commutative simple ring is a principal ideal domain

Indeed, it is a field.

-/

@[expose] public section

variable {R : Type*} [CommRing R] [IsSimpleRing R]

instance : IsSimpleOrder (Ideal R) := TwoSidedIdeal.orderIsoIdeal.symm.isSimpleOrder

instance IsPrincipalIdealRing.of_isSimpleRing :
    IsPrincipalIdealRing R :=
  ((isSimpleRing_iff_isField _).mp ‹_›).isPrincipalIdealRing

instance IsDomain.of_isSimpleRing :
    IsDomain R :=
  ((isSimpleRing_iff_isField _).mp ‹_›).isDomain
