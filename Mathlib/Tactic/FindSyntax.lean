/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public meta import Lean.Elab.Command
public import Mathlib.Init

/-!
# The `#find_syntax` command

The `#find_syntax` command takes as input a string `str` and retrieves from the environment
all the candidates for `syntax` terms that contain the string `str`.

It also makes a very crude effort at regenerating what the syntax looks like, by inspecting the
`ParserDescr`iptor of the corresponding parser.
-/

public meta section

namespace Mathlib.FindSyntax

open Lean Elab Command

/--
`extractSymbols descr acc` takes as input a `ParserDescr`iptor `descr` and an accumulator array
`acc`. It accumulates all symbols in `descr` corresponding to `Lean.ParserDescr.symbol`,
`Lean.ParserDescr.nonReservedSymbol` or `Lean.ParserDescr.unicodeSymbol`.

The output array serves as a way of regenerating what the syntax tree of the input parser is.
-/
def extractSymbols : ParserDescr → Array String → Array String
  | .symbol s, acc | .nonReservedSymbol s _, acc | .unicodeSymbol s _ _, acc =>
    acc.push s
  | .parser _, acc | .const _, acc | .cat _ _, acc =>
    acc
  | .node _ _ descr, acc
  | .trailingNode _ _ _ descr, acc
  | .nodeWithAntiquot _ _ descr, acc
  | .unary _ descr, acc =>
    extractSymbols descr acc
  | .binary _ l r, acc =>
    extractSymbols r (extractSymbols l acc)
  | .sepBy p _ psep _, acc | .sepBy1 p _ psep _, acc =>
    extractSymbols psep (extractSymbols p acc)

/--
The `#find_syntax` command takes as input a string `str` and retrieves from the environment
all the candidates for `syntax` terms that contain the string `str`.

It also makes a very crude effort at regenerating what the syntax looks like:
this is supposed to be just indicative of what the syntax may look like, but there is no
guarantee or expectation of correctness.

The optional trailing `approx`, as in `#find_syntax "∘" approx`, is only intended to make tests
more stable: rather than outputting the exact count of the overall number of existing syntax
declarations, it returns its round-down to the previous multiple of 100.
-/
elab "#find_syntax " id:str d:(&" approx")? : command => do
  let prsr : Array Expr := #[.const ``ParserDescr [], .const ``TrailingParserDescr []]
  let mut symbs : Std.HashSet (Name × List String) := {}
  -- We scan the environment in search of "parsers" whose name is not internal and that
  -- contain some `symbol` information and we store them in `symbs`
  for (declName, cinfo) in (← getEnv).constants do
    if prsr.contains cinfo.type && !declName.isInternal then
      let descr ← unsafe evalConst ParserDescr declName
      let ls := extractSymbols descr #[]
      unless ls.isEmpty do
        symbs := symbs.insert (declName, ls.toList)
  -- From among the parsers in `symbs`, we extract the ones whose `symbols` contain the input `str`
  let mut match_results : NameMap (Array (Name × String)) := {}
  for (nm, ar) in symbs.toList do
    let rem : String := " _ ".intercalate ar
    -- If either the name of the parser or the regenerated syntax stub contains the input string,
    -- then we include an entry into the final message.
    if 2 ≤ (nm.toString.splitOn id.getString).length || 2 ≤ (rem.splitOn id.getString).length then
      let mod := (← findModuleOf? nm).getD (← getMainModule)
      match_results := match_results.insert mod <| (match_results.getD mod #[]).push
        (nm, rem.trimAscii.copy)
  -- We sort the messages to produce a more stable output.
  let sorted_results := match_results.toArray.qsort (·.1.lt ·.1)
  let sorted_results := sorted_results.map fun (mod, msgs) => (mod, msgs.qsort (·.1.lt ·.1))
  let mods := (sorted_results.toList).map fun (mod, msgs) =>
    m!"In `{mod}`:" ++ (MessageData.nest 2 <|
      m!"".joinSep <| msgs.toList.map fun (decl, patt) =>
        m!"\n{MessageData.ofConstName decl}: '{patt}'")
  let uses := (sorted_results.toList.map fun (_, msgs) => msgs.size).sum
  let numSymbs := if d.isSome then s!"over {(symbs.size / 100) * 100}" else s!"{symbs.size}"
  let head := m!"Found {uses} use{if uses == 1 then "" else "s"} \
                among {numSymbs} syntax declarations"
  logInfo <| head ++ m!"\n" ++ m!"\n\n".joinSep mods
end Mathlib.FindSyntax
