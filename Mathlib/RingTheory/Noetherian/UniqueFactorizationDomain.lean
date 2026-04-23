/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
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
# Noetherian domains have unique factorization

## Main results

- IsNoetherianRing.wfDvdMonoid
-/

@[expose] public section

variable {R : Type*} [CommSemiring R] [IsDomain R]

-- see Note [lower instance priority]
instance (priority := 100) IsNoetherianRing.wfDvdMonoid [h : IsNoetherianRing R] :
    WfDvdMonoid R :=
  WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt h.wf.wellFoundedOn
