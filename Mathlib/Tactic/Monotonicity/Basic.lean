import Mathlib.Tactic.Monotonicity.Attr
import Mathlib.Tactic.SolveByElim

open Lean Meta Elab Tactic Syntax
open Mathlib Tactic SolveByElim

syntax (name := mono) "mono" (&" only")? (args)? : tactic

elab_rules : tactic | `(tactic| mono $[only%$o]? $[$t:args]?) => do
  let (_, add, _) := parseArgs t
  let cfg ← elabApplyRulesConfig <| mkNullNode #[]
  let cfg := if o.isNone then { cfg with maxDepth := 1 } else cfg
  let cfg := { cfg.noBackTracking with
    failAtMaxDepth := false }
  liftMetaTactic fun g => solveByElim.processSyntax cfg true false add [] #[mkIdent `mono] [g]
