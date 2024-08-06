/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
import Lean.Linter.Util

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

The linter makes an effort to start the highlighting at the first difference.
However, it may not always be successful.
It also prints both the source code and the "expected code" in a 5-character radius from
the first difference.
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

/-- `posToShiftedPos lths diff` takes as input an array `lths` of natural number,
and one further natural number `diff`.
It adds up the elements of `lths` occupying the odd positions, until the sum of the elements in
the even positions does not exceed `diff`.
It returns the sum of the accumulated odds and `diff`.
This is useful to figure out the difference between the output of `polishSource s` and `s` itself.
It plays a role similar to the `fileMap`. -/
def posToShiftedPos (lths : Array Nat) (diff : Nat) : Nat := Id.run do
  let mut (ws, noWS) := (diff, 0)
  for con in [:lths.size / 2] do
    let curr := lths[2 * con]!
    if noWS + curr < diff then
      noWS := noWS + curr
      ws := ws + lths[2 * con + 1]!
    else
      break
  return ws

/-- `zoomString str centre offset` returns the substring of `str` consisting of the `offset`
characters around the `centre`th character. -/
def zoomString (str : String) (centre offset : Nat) : Substring :=
  { str := str, startPos := ⟨centre - offset⟩, stopPos := ⟨centre + offset⟩ }

/-- `capSourceInfo s p` "shortens" all end-position information in the `SourceInfo` `s` to be
at most `p`, trimming down also the relevant substrings. -/
def capSourceInfo (s : SourceInfo) (p : Nat) : SourceInfo :=
  match s with
    | .original leading pos trailing endPos =>
      .original leading pos {trailing with stopPos := ⟨min endPos.1 p⟩} ⟨min endPos.1 p⟩
    | .synthetic pos endPos canonical =>
      .synthetic pos ⟨min endPos.1 p⟩ canonical
    | .none => s

/-- `capSyntax stx p` applies `capSourceInfo · s` to all `SourceInfo`s in all
`node`s, `atom`s and `ident`s contained in `stx`.

This is used to trim away all "fluff" that follows a command: comments and whitespace after
a command get removed with `capSyntax stx stx.getTailPos?.get!`.
-/
partial
def capSyntax (stx : Syntax) (p : Nat) : Syntax :=
  match stx with
    | .node si k args => .node (capSourceInfo si p) k (args.map (capSyntax · p))
    | .atom si val => .atom (capSourceInfo si p) (val.take p)
    | .ident si r v pr => .ident (capSourceInfo si p) { r with stopPos := ⟨min r.stopPos.1 p⟩ } v pr
    | s => s

namespace Pedantic

/-- Gets the value of the `linter.pedantic` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.pedantic o

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
      let pos := posToShiftedPos lths diff.1 + origSubstring.startPos.1
      let f := origSubstring.str.drop (pos)
      let extraLth := (f.takeWhile (· != st.get diff)).length
      let srcCtxt := zoomString real diff.1 5
      let ppCtxt  := zoomString st diff.1 5
      Linter.logLint linter.pedantic (.ofRange ⟨⟨pos⟩, ⟨pos + extraLth + 1⟩⟩)
        m!"source context\n'{srcCtxt}'\n'{ppCtxt}'\npretty-printed context"

initialize addLinter pedantic

end Pedantic
