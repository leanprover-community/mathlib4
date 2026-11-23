/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Extensions
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Tactic.Inclusion.Extension.Interval.Basic

/-!
# Initialization for the integer interval extension family

This file initializes the `interval_int` inclusion family.
-/

public meta section

namespace Inclusion.IntervalInt

/-- Initializes the `interval_int` inclusion family. -/
initialize intervalIntFamily : InclusionFamily ← registerInclusionFamily `interval_int

end Inclusion.IntervalInt
