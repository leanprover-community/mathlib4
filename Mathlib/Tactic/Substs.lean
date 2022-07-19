/-
Copyright (c) 2022 Evan Lohn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Evan Lohn, Mario Carneiro
-/
import Lean

namespace Mathlib.Tactic.Substs
open Lean Meta Elab
open Tactic

syntax (name := substs) "substs" (colGt ppSpace ident)* : tactic

/--
Applies the `subst` tactic to all given hypotheses from left to right
-/
macro_rules
| `(tactic| substs $xs:ident*) => `(tactic| ($[subst $xs;]*))
