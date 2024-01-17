/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean.Meta.Tactic.Simp.Types
import Std.Data.RBMap.Alter
import Std.Lean.Meta.DiscrTree

/-!
## `fprop` 

this file defines enviroment extension for `fprop`
-/


namespace Mathlib
open Lean Meta

namespace Meta.FProp


initialize registerTraceClass `Meta.Tactic.fprop.attr
initialize registerTraceClass `Meta.Tactic.fprop
initialize registerTraceClass `Meta.Tactic.fprop.step
initialize registerTraceClass `Meta.Tactic.fprop.unify
initialize registerTraceClass `Meta.Tactic.fprop.discharge
initialize registerTraceClass `Meta.Tactic.fprop.apply
initialize registerTraceClass `Meta.Tactic.fprop.cache


-- initialize registerTraceClass `Meta.Tactic.fprop.missing_rule
-- -- initialize registerTraceClass `Meta.Tactic.fprop.normalize_let
-- initialize registerTraceClass `Meta.Tactic.fprop.rewrite
-- initialize registerTraceClass `Meta.Tactic.fprop.discharge
-- initialize registerTraceClass `Meta.Tactic.fprop.unify
-- initialize registerTraceClass `Meta.Tactic.fprop.apply


/-- -/
structure Config where
  -- config

/-- -/
structure State where
  /-- Simp's cache is used as the `fprop` tactic is designed to be used inside of simp and utilize its cache -/
  cache        : Simp.Cache := {}

/-- -/
abbrev FPropM := ReaderT FProp.Config $ StateRefT FProp.State MetaM

/-- Result of `fprop`, it is a proof of function property `P f` and list of 
pending subgoals. These subgoals are meant to be solved by the user or passed to another automation.
-/
structure Result where
  proof : Expr
  subgoals : List MVarId
