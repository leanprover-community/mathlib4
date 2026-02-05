/-
Copyright (c) 2026 Pavel Grigorenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pavel Grigorenko
-/
module

public import Mathlib.Init

/-! # `assumption?` tactic -/

meta section

namespace Mathlib.Tactic.AssumptionQuestion

open Lean.Elab.Tactic
open Lean.Meta
open Lean.Meta.Tactic.TryThis (addExactSuggestion)

/--
* TODO
-/
tactic_extension Lean.Parser.Tactic.assumption

@[tactic_alt Lean.Parser.Tactic.assumption]
macro (name := assumption?) "assumption?" : tactic => `(tactic| { show_term { assumption } })

end Mathlib.Tactic.AssumptionQuestion
