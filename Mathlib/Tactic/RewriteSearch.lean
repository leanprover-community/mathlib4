/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Init
import Lean.Elab.Tactic.Basic

/-!
# The `rw_search` tactic has been removed from Mathlib.
-/
namespace Mathlib.Tactic.RewriteSearch

open Lean Meta
open Elab Tactic Lean.Parser.Tactic

/--
`rw_search` has been removed from Mathlib.
-/
syntax "rw_search" (rewrites_forbidden)? : tactic

elab_rules : tactic |
    `(tactic| rw_search $[[ $[-$forbidden],* ]]?) => withMainContext do
  logError "The `rw_search` tactic has been removed from Mathlib, as it was unmaintained,\
    broken on v4.23.0, and rarely used."

end RewriteSearch

end Mathlib.Tactic
