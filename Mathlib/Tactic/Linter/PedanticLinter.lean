/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
import Lean.Linter.Util
import Batteries.Data.String.Matcher

/-!
#  The "pedantic" linter

The "pedantic" linter emits a warning when the syntax of a command differs substantially
from the pretty-printed version of itself.
-/
open Lean Elab Command

namespace Mathlib.Linter

/--
The "pedantic" linter emits a warning when the syntax of a command differs substantially
from the pretty-printed version of itself.
-/
register_option linter.pedantic : Bool := {
  defValue := true
  descr := "enable the pedantic linter"
}

/-- `polishPP s` takes as input a `String` `s`, assuming that it is the output of
pretty-printing a lean command.
The main intent is to convert `s` to a reasonable candidate for a desirable source code format.
The function first replaces consecutive whitespace sequences into a single space (` `), in an
attempt to side-step line-break differences.
After that, it applies some pre-emptive changes:
* doc-module beginnings tend to have some whitespace following it, so we add a space back in;
* name quotations such as ``` ``Nat``` get pretty-printed as ``` `` Nat```, so we remove a space
  after double back-ticks, but take care of adding one more for triple (or more) back-ticks;
* `notation3` is not followed by a pretty-printer space, so we add it here (#15515).
-/
def polishPP (s : String) : String :=
  let s := s.split (·.isWhitespace)
  (" ".intercalate (s.filter (!·.isEmpty)))
    |>.replace "/-!" "/-! "
    |>.replace "``` " "```  " -- avoid losing an existing space after the triple back-ticks
                              -- as a consequence of the following replacement
    |>.replace "`` " "``" -- weird pp ```#eval ``«Nat»``` pretty-prints as ```#eval `` «Nat»```
    |>.replace "notation3(" "notation3 ("
    |>.replace "notation3\"" "notation3 \""
    --|>.replace "{" "{"   -- probably better?

/-- `polishSource s` is similar to `polishPP s`, but expects the input to be actual source code.
For this reason, `polishSource s` performs more conservative changes:
it only replace all whitespace starting from a linebreak (`\n`) with a single whitespace. -/
def polishSource (s : String) : String × Array Nat :=
  let split := s.split (· == '\n')
  --let lengths := split.map (·.length)
  let preWS := split.foldl (init := #[]) fun p q =>
    let txt := q.trimLeft.length
    (p.push (q.length - txt)).push txt
  let preWS := preWS.eraseIdx 0
  --dbg_trace "(spaces, sum, total): {(preWS, preWS.foldl (· + ·) 0, s.length)}"
  let s := (split.map .trimLeft).filter (!· == "")
  (" ".intercalate (s.filter (!·.isEmpty)), preWS)

def posToShiftedPos (lths : Array Nat) (offset diff : Nat) : Nat := Id.run do
  let mut ws := offset
  let mut noWS := 0
  for con in [:lths.size / 2] do
    let curr := lths[2 * con]!
    if noWS + curr < diff then
      noWS := noWS + curr
      ws := ws + lths[2 * con + 1]!
    else
      break
  return ws

def zoomString (str : String) (centre offset : Nat) : Substring :=
  { str := str, startPos := ⟨centre - offset⟩, stopPos := ⟨centre + offset⟩ }

namespace Pedantic

/-- Gets the value of the `linter.pedantic` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.pedantic o

def capSourceInfo (s : SourceInfo) (p : Nat) : SourceInfo :=
  match s with
    | .original leading pos trailing endPos =>
      .original leading pos {trailing with stopPos := ⟨min endPos.1 p⟩} ⟨min endPos.1 p⟩
    | .synthetic pos endPos canonical =>
      .synthetic pos ⟨min endPos.1 p⟩ canonical
    | .none => s

partial
def capSyntax (stx : Syntax) (p : Nat) : Syntax :=
  match stx with
    | .node si k args => .node (capSourceInfo si p) k (args.map (capSyntax · p))
    | .atom si val => .atom (capSourceInfo si p) (val.take p)
    | .ident si r v pr => .ident (capSourceInfo si p) { r with stopPos := ⟨min r.stopPos.1 p⟩ } v pr
    | s => s

@[inherit_doc Mathlib.Linter.linter.pedantic]
def pedantic : Linter where run := withSetOptionIn fun stx ↦ do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    let stx:= capSyntax stx (stx.getTailPos?.getD default).1
    let origSubstring := stx.getSubstring?.getD default
    let (real, lths) := polishSource origSubstring.toString
    let fmt ← (liftCoreM do PrettyPrinter.ppCategory `command stx <|> (do
      Linter.logLint linter.pedantic stx
        m!"The pedantic linter had some parsing issues: \
           feel free to silence it with `set_option linter.pedantic false in` \
           and report this error!"
      return real))
    let st := polishPP fmt.pretty
    if st != real then
      let diff := real.firstDiffPos st
      let pos := posToShiftedPos lths origSubstring.startPos.1 diff.1
      --let toEnd : Substring := { str := real, startPos := diff, stopPos := ⟨real.length⟩ }
      --let diffToNonWS := toEnd.takeWhile (·.isWhitespace)
      --let toHighlight := (({diffToNonWS with startPos := diffToNonWS.stopPos, stopPos := ⟨real.length⟩}).takeWhile (!·.isWhitespace))--.takeWhile (!·.isWhitespace)
      --dbg_trace "diff, ws, nws: {(diff, diffToNonWS.stopPos, toHighlight.stopPos)}\n'{toHighlight}' '{{ toHighlight with startPos := diff }}'\n"
      --let toHighlightPlus : Substring := { toHighlight with startPos := diff, stopPos := toHighlight.stopPos}
      let toDiff : Substring := { origSubstring with startPos := diff + ⟨pos⟩ } --, stopPos := origSubstring.stopPos }
      let fin := toDiff.toString.takeWhile (· != st.get diff)
      dbg_trace "diff: {diff}"
      dbg_trace "st.get diff: {st.get diff}"
      dbg_trace "fin: {fin}"
      let f := origSubstring.str.drop (diff.1 + pos)
      let extraLth := (f.takeWhile (· != st.get diff)).length
      --dbg_trace "alternate: '{f.take extraLth}'"
      --dbg_trace "toDiff.toString: {toDiff.toString}"
      --dbg_trace (st.get diff, fin, toDiff.toString)
      --let finpos := posToShiftedPos lths origSubstring.startPos.1 (diff.1 + extraLth) --fin.stopPos.1
      let srcCtxt := zoomString real diff.1 5
      let ppCtxt  := zoomString st diff.1 5

      --let origHighlight := origSubstring.findSubstr? toHighlightPlus
      --if let some sstr := origHighlight then
        --dbg_trace "this is pos: {pos}, this is diff: {diff}"
        --dbg_trace (origHighlight.getD default).stopPos
      --dbg_trace "ranges: {(diff + ⟨pos⟩, finpos)}"
      Linter.logLint linter.pedantic (.ofRange ⟨diff + ⟨pos⟩, diff + ⟨pos + extraLth + 1⟩⟩) --m!"{pos}"
        --Linter.logLint linter.pedantic (.ofRange ⟨sstr.startPos, sstr.stopPos + ⟨1⟩⟩)
         m!"---\n\
          '{srcCtxt}' is in the source\n\
          '{ppCtxt}' is how it is pretty-printed\n---"
      --else
      --  if srcCtxt.toString == ppCtxt.toString then logInfo m!"{diff}\n{real}\n{ppCtxt}"
      --  Linter.logLint linter.pedantic stx m!"---\n\
      --    '{srcCtxt}' is in the source\n\
      --    '{ppCtxt}' is how it is pretty-printed\n---"

/-
#eval
  let str := "1234567"
  let sstr : Substring := {str := str, startPos := ⟨2⟩, stopPos := ⟨str.length⟩}
  dbg_trace sstr.takeWhile (· != '6')
  0

run_cmd
  let s1 := "· 2"
  let s2 := "·12"
  let diff : String.Pos := s1.firstDiffPos s2
  logInfo m!"Difference at: {diff}\n\
        s1: '{({ str := s1, startPos := diff - ⟨1⟩, stopPos := diff + ⟨1⟩ } : Substring)}'\n\
        s2: '{({ str := s2, startPos := diff - ⟨1⟩, stopPos := diff + ⟨1⟩ } : Substring)}'"
-/

initialize addLinter pedantic

end Pedantic
