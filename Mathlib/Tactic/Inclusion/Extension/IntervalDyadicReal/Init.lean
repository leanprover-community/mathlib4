/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Extensions
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Inclusion.Extension.Interval.Basic
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Dyadic

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Initialization for the dyadic real interval extension family

This file initializes the `interval_dyadic_real` inclusion family and defines the `ToSet`,
`Univ` and `Coarsen` instances it uses in the `inclusion` tactic.
-/

@[expose] public section

namespace Inclusion

namespace IntervalDyadicReal

/-- Initializes the `interval_dyadic_real` inclusion family. -/
meta initialize intervalDyadicRealFamily : InclusionFamily ←
  registerInclusionFamily `interval_dyadic_real

/-- Coercion from dyadic rationals to real numbers as an additive monoid homomorphism. -/
noncomputable def castAddMonoidHom : Dyadic →+ ℝ :=
  (Rat.castHom ℝ).toAddMonoidHom.comp Dyadic.toRatAddMonoidHom

/-- Coercion from dyadic rationals to real numbers as an order embedding. -/
@[simps! apply]
noncomputable def castOrderEmbedding : Dyadic ↪o ℝ :=
  Dyadic.toRatOrderEmbedding.comp Rat.castOrderEmbedding

instance instToSetIntervalDyadicReal : ToSet (Interval Dyadic) ℝ where
  toSet I := (I.map (↑)).toSet

instance : Univ (Interval Dyadic) ℝ where
  univ := Interval.univ Dyadic
  mem_univ := Interval.mem_map_univ ((↑) : Dyadic → ℝ)

instance : Refine (Interval Dyadic) ℝ where
  refine := Interval.inter
  mem_refine := Interval.inter_mem castOrderEmbedding

instance : Coarsen (Interval Dyadic) ℝ where
  coarsen := Interval.hull
  mem_coarsen_left := Interval.hull_mem_left castOrderEmbedding
  mem_coarsen_right := Interval.hull_mem_right castOrderEmbedding

end IntervalDyadicReal

end Inclusion
