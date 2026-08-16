/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Basic
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Splitting
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Basic
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Splitting
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public meta import Mathlib.Tactic.Inclusion.ExtensionAPI.Basic
public meta import Qq

/-!
# Inclusion extensions for dyadic real intervals
-/

public meta section

open Lean Meta Qq

namespace Inclusion
namespace IntervalDyadicReal

/-- The depth to which bounded dyadic intervals are repeatedly bisected. A depth of `n` produces
`2 ^ n` pieces; unbounded intervals are left unchanged. -/
@[inclusionParam]
def binSplitParam : InclusionParamDecl where
  name := `binSplit
  type := q(ℕ)

/-- Construct the binary-splitting cover with `2 ^ n` pieces. -/
def mkBinSplitCover : InclusionM (Option Expr) := do
  let some depth ← InclusionM.getParam? `binSplit | return none
  return some (mkApp (mkConst ``BinarySplit.cover [.zero]) depth)

/-- Construct an inclusion variable for a real expression using a dyadic interval. -/
@[inclusionExt interval_dyadic_real | (_ : ℝ)]
def mkRealIVar : InclusionExt :=
  mkNDIVarExt ⟨q(ℝ), q(Interval Dyadic), q(instToSetIntervalDyadicReal)⟩ mkBinSplitCover

end IntervalDyadicReal
end Inclusion
