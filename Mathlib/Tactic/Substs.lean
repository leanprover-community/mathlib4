/-
Copyright (c) 2022 Evan Lohn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Lohn, Mario Carneiro
-/
import Lean

namespace Mathlib.Tactic.Substs
open Lean Meta Elab
open Tactic

/--
Applies the `subst` tactic to all given hypotheses from left to right.
-/
syntax (name := substs) "substs" (colGt ppSpace ident)* : tactic

macro_rules
| `(tactic| substs $xs:ident*) => `(tactic| ($[subst $xs]*))
