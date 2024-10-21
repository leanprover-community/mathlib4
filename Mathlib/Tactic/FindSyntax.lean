/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command

/-!
#  The `#find_syntax` command

The `#find_syntax` command takes as input a string `str` and retrieves from the environment
all the candidates for `syntax` terms that contain the string `str`.

It also makes a very crude effort at regenerating what the syntax looks like, by inspecting the
`Expr`ession tree of the corresponding parser.
-/

namespace Mathlib.FindSyntax

open Lean Elab Command

/--
`extractSymbols expr` takes as input an `Expr`ession `expr`, assuming that it is the value
of a "parser".
It returns the array of all subterms of `expr` that are the `Expr.lit` argument to
`Lean.ParserDescr.symbol` and `Lean.ParserDescr.nonReservedSymbol` applications.

The output array serves as a way of regenerating what the syntax tree of input parser.
-/
def extractSymbols : Expr → Array Expr
  | .app a b =>
    let rest := extractSymbols a ++ extractSymbols b
    match a.constName with
      | ``Lean.ParserDescr.symbol | ``Lean.ParserDescr.nonReservedSymbol => rest.push b
      | _ => rest
  | .letE _ a b c _ => extractSymbols a ++ extractSymbols b ++ extractSymbols c
  | .lam _ a b _ => extractSymbols a ++ extractSymbols b
  | .forallE _ a b _ => extractSymbols a ++ extractSymbols b
  | .mdata _ a => extractSymbols a
  | .proj _ _ a => extractSymbols a
  | _ => #[]

/--
`litToString expr` converts the input `Expr`ession `expr` into the "natural" string that
it corresponds to, in case `expr` is a `String`/`Nat`-linteral, returning the empty string `""`
otherwise.
-/
def litToString : Expr → String
  | .lit (.natVal v) => s!"{v}"
  | .lit (.strVal v) => v
  | _ => ""

/--
The `#find_syntax` command takes as input a string `str` and retrieves from the environment
all the candidates for `syntax` terms that contain the string `str`.

It also makes a very crude effort at regenerating what the syntax looks like:
this is supposed to be just indicative of what the syntax may look like, but there is no
guarantee or expectation of correctness.
-/
elab "#find_syntax " id:str : command => do
  let prsr : Array Expr := #[.const ``ParserDescr [], .const ``TrailingParserDescr []]
  let mut symbs : Std.HashSet (Name × Array Expr) := {}
  -- We scan the environment in search of "parsers" whose name is not internal and that
  -- contain some `symbol` information and we store them in `symbs`
  for (declName, cinfo) in (← getEnv).constants do
    if prsr.contains cinfo.type && cinfo.hasValue then
      let ls := extractSymbols cinfo.value!
      if !declName.isInternal && !ls.isEmpty then symbs := symbs.insert (declName, ls)
  -- From among the parsers in `symbs`, we extract the ones whose `symbols` contain the input `str`
  let mut msgs := #[]
  for (nm, ar) in symbs.toList do
    let rem : String := " _ ".intercalate (ar.map litToString).toList
    -- If either the name of the parser or the regenerated syntax stub contains the input string,
    -- then we include an entry into the final message.
    if 2 ≤ (nm.toString.splitOn id.getString).length || 2 ≤ (rem.splitOn id.getString).length then
      msgs := msgs.push <| .ofConstName nm ++ m!":\n  '{rem.trim}'\n"
  let uses := msgs.size
  let head := m!"Found {uses} use{if uses == 1 then "" else "s"} \
                among {symbs.size} syntax declarations"
  logInfo <| .joinSep (head::(msgs.push "").toList) "\n---\n\n"

end Mathlib.FindSyntax
