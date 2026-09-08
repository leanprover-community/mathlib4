/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Elab
public meta import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# The `dyadic_interval` tactic

This file defines the `dyadic_interval` tactic which is a wrapper around the inclusion tactic
with a specific set of enabled inclusion families.
-/

public meta section

open Lean.Parser.Tactic

namespace Inclusion

/-- `dyadic_interval` proves real number equalities, inequalities and interval memberships by
approximating as an interval of dyadic rational numbers.

This tactic is implemented as a family for the `inclusion` tactic: `dyadic_interval` is the same as
`inclusion [core, interval_dyadic_real]`.

* `dyadic_interval [binSplit := n]` splits each interval `n` times, into `2^n` pieces. Higher values
  of `n` make the tactic slower but able to prove more. Default: no splitting.
* `dyadic_interval [prec := n]` uses a precision of `2^-n` when constructing the approximation.
  Higher values of `n` make the tactic slower but able to prove more. Default value: 0.
* `dyadic_interval [fam₁, ... famₙ]` uses the inclusion families `fam₁`, ..., `famₙ` for additional
  reasoning capabilities.
* `dyadic_interval (config := cfg)` uses `cfg` as a configuration for the `inclusion` tactic.
  (See there for further details.)
-/
syntax (name := dyadicInterval) "dyadic_interval" optConfig
  (" [" inclusionArg,* "]")? : tactic

macro_rules
  | `(tactic| dyadic_interval $cfg:optConfig) =>
      `(tactic| inclusion $cfg [core, interval_dyadic_real])
  | `(tactic| dyadic_interval $cfg:optConfig [$args,*]) =>
      `(tactic| inclusion $cfg [core, interval_dyadic_real, $args,*])

/-- `dyadic_interval?` is a proof writing aid that quickly checks if `dyadic_interval` would close
the goal, without doing the expensive kernel computation that actually closes the goal. -/
syntax (name := dyadicInterval?) "dyadic_interval?" (" [" inclusionArg,* "]")? : tactic

macro_rules
  | `(tactic| dyadic_interval?) =>
      `(tactic| inclusion? [core, interval_dyadic_real])
  | `(tactic| dyadic_interval? [$args,*]) =>
      `(tactic| inclusion? [core, interval_dyadic_real, $args,*])

end Inclusion
