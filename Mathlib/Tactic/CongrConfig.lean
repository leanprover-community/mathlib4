/-
Copyright (c) 2023 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
import Std

/-!
## Additional config for `congr`
The `MetaM` version of `congr` (`Lean.MVarId.congrN`) has 2 configs: `closePre` and `closePost`.
Especially, `closePost` is significant to prevent timeout.
This file adds a config for the `congr` & `rcongr` tactic.
-/

namespace Lean.Parser.Tactic

@[inherit_doc Lean.Parser.Tactic.congr]
syntax (name := congrConfig) "congr" config (ppSpace num)? : tactic

@[inherit_doc Std.Tactic.congrWith]
syntax (name := congrConfigWith) "congr" config (ppSpace num)? " with" (ppSpace colGt rintroPat)*
  (" : " num)? : tactic

@[inherit_doc Std.Tactic.rcongr]
syntax (name := rcongrConfig) "rcongr" Lean.Parser.Tactic.config (ppSpace colGt rintroPat)*
  : tactic

end Lean.Parser.Tactic

namespace Mathlib.Tactic
open Lean Meta Elab Tactic Std.Tactic

structure Congr.Config where
  /-- If `closePre := true`, it will attempt to close new goals using `Eq.refl`, `HEq.refl`, and
  `assumption` with reducible transparency. -/
  closePre : Bool := true
  /-- If `closePost := true`, it will try again on goals on which `congr` failed to make progress
  with default transparency. -/
  closePost : Bool := true

declare_config_elab Congr.elabConfig Congr.Config

elab_rules : tactic
  | `(tactic| congr $cfg:config $[$n?]?) => do
    let config ← Congr.elabConfig (mkOptionalNode cfg)
    let hugeDepth := 1000000
    let depth := n?.map (·.getNat) |>.getD hugeDepth
    liftMetaTactic fun mvarId =>
      mvarId.congrN depth (closePre := config.closePre) (closePost := config.closePost)

macro_rules
  | `(tactic| congr $config:config $(depth)? with $ps* $[: $n]?) =>
    `(tactic| congr $config:config $(depth)? <;> ext $ps* $[: $n]?)

@[inherit_doc Std.Tactic.rcongrCore]
partial def rcongrConfigCore (g : MVarId) (config : Congr.Config) (pats : List (TSyntax `rcasesPat))
    (acc : Array MVarId) : TermElabM (Array MVarId) := do
  let mut acc := acc
  for (g, qs) in (← Ext.extCore g pats (failIfUnchanged := false)).2 do
    let s ← saveState
    let gs ← g.congrN 1000000 (closePre := config.closePre) (closePost := config.closePost)
    if ← not <$> g.isAssigned <||> gs.anyM fun g' => return (← g'.getType).eqv (← g.getType) then
      s.restore
      acc := acc.push g
    else
      for g in gs do
        acc ← rcongrCore g qs acc
  pure acc

elab_rules : tactic
  | `(tactic| rcongr $cfg:config $[$ps:rintroPat]*) => do
    let gs ← rcongrConfigCore (← getMainGoal) (← Congr.elabConfig (mkOptionalNode cfg))
      (RCases.expandRIntroPats ps).toList #[]
    replaceMainGoal gs.toList

end Mathlib.Tactic
