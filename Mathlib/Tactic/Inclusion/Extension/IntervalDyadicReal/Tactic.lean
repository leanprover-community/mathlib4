/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Extension.Core.Core
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Extensions

/-!
# The `dyadic_interval` tactic

This file defines the `dyadic_interval` tactic which is a wrapper around the inclusion tactic
with a specific set of enabled inclusion families.
-/

public meta section

open Lean.Parser.Tactic

namespace Inclusion

/-- `dyadic_interval` runs `inclusion` with the `core` and `interval_dyadic_real` extension
families. Inclusion parameters may be supplied using `dyadic_interval [name := value, ...]`. -/
syntax (name := dyadicInterval) "dyadic_interval" optConfig
  (" [" inclusionParam,* "]")? : tactic

macro_rules
  | `(tactic| dyadic_interval $cfg:optConfig $[[$params:inclusionParam,*]]?) =>
      `(tactic| inclusion $cfg [core, interval_dyadic_real] $[($params,*)]?)

/-- `dyadic_interval?` checks whether `dyadic_interval` can prove the goal without closing it. -/
syntax (name := dyadicInterval?) "dyadic_interval?" (" [" inclusionParam,* "]")? : tactic

macro_rules
  | `(tactic| dyadic_interval? $[[$params:inclusionParam,*]]?) =>
      `(tactic| inclusion? [core, interval_dyadic_real] $[($params,*)]?)

end Inclusion
