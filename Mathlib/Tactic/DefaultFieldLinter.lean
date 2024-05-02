/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Lean


register_option linter.structureDiamondDefaults : Bool := {
  defValue := true
  descr :=
    "Linter to check if structure fields that are often implicated in typeclass diamonds are " ++
    "using implicit default values." }

/-- ``exact_with_diamond_warning `foo `foo_default "cause issues with Foo"`` is `exact foo_default`
but with a linter warning about the provided field name and default -/
elab "exact_with_diamond_warning" tgt:name default:name msg:str: tactic => do
  -- stupid games because `ident` isn't allowed in the syntax parser (lean4#3328)
  let tgt' := Lean.mkIdent tgt.getName
  let default' := Lean.mkIdent default.getName
  -- TODO: use "Try this" somehow, but we don't have the position info we need
  let stx ← `(Lean.Parser.Command.whereStructField| $tgt' := $default')
  Lean.Linter.logLintIf linter.structureDiamondDefaults tgt <|
    m!"Using default value {stx}, which may {msg.getString}.\n" ++
      m!"If you are sure this is not an issue, write {stx} explicitly"
  Lean.Elab.Tactic.evalTactic <| ← `(tactic| exact $default')
