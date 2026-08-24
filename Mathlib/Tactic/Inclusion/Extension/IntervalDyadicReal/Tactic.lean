/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Basic
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Basic
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

/-!
# The `dyadic_interval` tactic

This file defines the `dyadic_interval` tactic which is a wrapper around the inclusion tactic
with a specific set of enabled inclusion families.
-/

public meta section

open Lean.Parser.Tactic

namespace Inclusion

/-- `dyadic_interval` runs `inclusion` with the `core` and `interval_dyadic_real` extension
families. Additional families and inclusion parameters may be supplied in brackets. -/
syntax (name := dyadicInterval) "dyadic_interval" optConfig
  (" [" inclusionArg,* "]")? : tactic

macro_rules
  | `(tactic| dyadic_interval $cfg:optConfig) =>
      `(tactic| inclusion $cfg [core, interval_dyadic_real])
  | `(tactic| dyadic_interval $cfg:optConfig [$args,*]) =>
      `(tactic| inclusion $cfg [core, interval_dyadic_real, $args,*])

/-- `dyadic_interval?` checks whether `dyadic_interval` can prove the goal without closing it. -/
syntax (name := dyadicInterval?) "dyadic_interval?" (" [" inclusionArg,* "]")? : tactic

macro_rules
  | `(tactic| dyadic_interval?) =>
      `(tactic| inclusion? [core, interval_dyadic_real])
  | `(tactic| dyadic_interval? [$args,*]) =>
      `(tactic| inclusion? [core, interval_dyadic_real, $args,*])

end Inclusion
