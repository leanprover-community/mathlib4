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
-/
register_option linter.pedantic : Bool := {
  defValue := true
  descr := "enable the pedantic linter"
}

def collapseWhitespace (s : String) : String :=
  let s := s.split (·.isWhitespace)
  (" ".intercalate (s.filter (!·.isEmpty)))
    |>.replace "/-!" "/-! "
    |>.replace "``` " "```  " -- avoid losing an existing space after the triple back-ticks
                              -- as a consequence of the following replacement
    |>.replace "`` " "``" -- weird pp ```#eval ``«Nat»``` pretty-prints as ```#eval `` «Nat»```
    |>.replace "notation3(" "notation3 ("
    --|>.replace "{" "{"   -- probably better?

def collapseLineBreaksPlusSpaces (st : String) : String :=
  let s := ((st.split (· == '\n')).map .trimLeft).filter (!· == "")
  " ".intercalate (s.filter (!·.isEmpty))

def zoomString (str : String) (centre offset : Nat) : Substring :=
  ({ str := str, startPos := ⟨centre - offset⟩, stopPos := ⟨centre + offset⟩ } : Substring)

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
    let real := collapseLineBreaksPlusSpaces (stx.getSubstring?.getD default).toString
    let fmt ← (liftCoreM do PrettyPrinter.ppCategory `command stx <|> (do
      Linter.logLint linter.pedantic stx
        m!"The pedantic linter had some parsing issues: \
           feel free to silence it with `set_option linter.pedantic false in` \
           and report this error!"
      return real))
    let st := collapseWhitespace fmt.pretty
    if st != real then
      let diff := real.firstDiffPos st
      let srcCtxt := zoomString real diff.byteIdx 5
      let ppCtxt  := ({ str := st,   startPos := diff - ⟨4⟩, stopPos := diff + ⟨5⟩ } : Substring)
      if srcCtxt.toString == ppCtxt.toString then logInfo m!"{diff}\n{real}\n{ppCtxt}"
      Linter.logLint linter.pedantic stx m!"---\n\
        '{srcCtxt}' is in the source\n\
        '{ppCtxt}' is how it is pretty-printed\n---"

/-
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
