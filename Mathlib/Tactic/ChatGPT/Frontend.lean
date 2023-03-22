import Mathlib.Tactic.ChatGPT.Lean
import Mathlib.Data.Option.Defs
import Mathlib.Util.Whatsnew

open Lean Elab Meta

namespace Mathlib.Tactic.ChatGPT

/--
A modified version of `Lean.Elab.Frontend`, that returns messages and info trees.
-/
def runFrontend (input : String) (opts : Options) (fileName : String) (mainModuleName : Name) :
    IO (Environment × List Message × List InfoTree) := do
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx
  let env := env.setMainModule mainModuleName
  let mut commandState := Command.mkState env messages opts
  commandState := { commandState with infoState.enabled := true }
  let s ← IO.processCommands inputCtx parserState commandState
  pure (s.commandState.env,
    s.commandState.messages.msgs.toList,
    s.commandState.infoState.trees.toList)

/--
Given a token (e.g. a tactic invocation), we read the current source file,
and find the first blank line before that token, and the first blank line after that token.
We then return everything up to the earlier blank line,
along with everything between the two blank lines.

That is, modulo some assumptions about there being blank lines before and after declarations,
we return everything up to the current declaration, and the current declaration.
-/
def getSourceUpTo (s : Syntax) : CoreM (String × String) := do
  let fileMap := (← readThe Core.Context).fileMap
  let ({ line := line, column := _ }, _) := stxRange fileMap s
  let lines := fileMap.source.splitOn "\n"
  let blanks : List Nat := lines.enum.filterMap fun ⟨n, l⟩ =>
    if l.trim = "" then some (n + 1) else none
  let before := blanks.takeWhile (· < line) |>.maximum? |>.getD 0
  let after := blanks.dropWhile (· ≤ line) |>.minimum? |>.getD lines.length
  pure (String.intercalate "\n" <| lines.take before,
    String.intercalate "\n" <| lines.take after |>.drop before)
