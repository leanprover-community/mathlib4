/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Lean
/-!
# The `linter.structureDiamondDefaults` linter
-/

/--
Linter to check if structure fields that are often implicated in typeclass diamonds are using
implicit default values.
-/
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
  let tac ← `(tactic| exact $default')
  try
    Lean.Elab.Tactic.withoutRecover <| Lean.Elab.Tactic.evalTactic <| tac
  catch e =>
    throwErrorAt e.getRef m!"While evaluating default {stx}:{Lean.indentD e.toMessageData}"
  Lean.Linter.logLintIf linter.structureDiamondDefaults tgt <|
    m!"Using default value{Lean.indentD stx}\n" ++
    m!"which may {msg.getString}.\n" ++
    m!"To silence this warning, write the above in your instance definition, " ++
    m!"optionally replacing {default'} with a better implementation."
