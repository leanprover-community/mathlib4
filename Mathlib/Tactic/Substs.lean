import Lean

namespace Mathlib.Tactic.Substs
open Lean Meta Elab
open Tactic

syntax (name := substs) "substs" (colGt ppSpace ident)* : tactic

macro_rules
| `(tactic| substs $xs:ident*) =>
  `(tactic| ($[subst $xs;]*))
