/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Parser.Syntax
import Mathlib.Tactic.Linter.Header
/-!
#  The `commandStart` linter

The `commandStart` linter emits a warning if
* either a command does not start at the beginning of a line;
* or the "hypotheses segment" of a declaration does not coincide with its pretty-printed version.
-/

open Lean Elab Command Linter

private def String.norm (s : String) : String :=
  s.replace "\n" "⏎"

namespace Mathlib.Linter

/--
The `commandStart` linter emits a warning if
* either a command does not start at the beginning of a line;
* or the "hypotheses segment" of a declaration does not coincide with its pretty-printed version.

In practice, this makes sure that the spacing in a typical declaration looks like
```lean
example (a : Nat) {R : Type} [Add R] : <not linted part>
```
as opposed to
```lean
example (a: Nat) {R:Type}  [Add  R] : <not linted part>
```
-/
register_option linter.style.commandStart : Bool := {
  defValue := false
  descr := "enable the commandStart linter"
}

/-- If the `linter.style.commandStart.verbose` option is `true`, the `commandStart` linter
reports some helpful diagnostic information. -/
register_option linter.style.commandStart.verbose : Bool := {
  defValue := false
  descr := "enable the commandStart linter"
}

/-- If the command starts with one of the `SyntaxNodeKind`s in `skipped`, then the
`commandStart` linter ignores the command. -/
def skipped : Std.HashSet SyntaxNodeKind := Std.HashSet.emptyWithCapacity
  |>.insert ``Parser.Command.moduleDoc
  |>.insert ``Parser.Command.elab_rules
  |>.insert ``Lean.Parser.Command.syntax
  |>.insert `Aesop.Frontend.Parser.declareRuleSets

/--
`CommandStart.endPos stx` returns the position up until the `commandStart` linter checks the
formatting.
This is every declaration until the type-specification, if there is one, or the value,
as well as all `variable` commands.
-/
def CommandStart.endPos (stx : Syntax) : Option String.Pos :=
  --dbg_trace stx.getKind
  if skipped.contains stx.getKind then none else
  if let some cmd := stx.find? (#[``Parser.Command.declaration, `lemma].contains ·.getKind) then
    if let some ind := cmd.find? (·.isOfKind ``Parser.Command.inductive) then
      match ind.find? (·.isOfKind ``Parser.Command.optDeclSig) with
      | none => dbg_trace "unreachable?"; none
      | some _sig => stx.getTailPos? --sig.getTailPos?
    else
    match cmd.find? (·.isOfKind ``Parser.Term.typeSpec) with
      | some _s => stx.getTailPos? --s[0].getTailPos? -- `s[0]` is the `:` separating hypotheses and the type
      | none => match cmd.find? (·.isOfKind ``Parser.Command.declValSimple) with
        | some _s => stx.getTailPos? --s.getPos?
        | none => stx.getTailPos? --none
  else if stx.isOfKind ``Parser.Command.variable || stx.isOfKind ``Parser.Command.omit then
    stx.getTailPos?
  else stx.getTailPos?

/--
A `FormatError` is the main structure tracking how some surface syntax differs from its
pretty-printed version.

In case of deviations, it contains the deviation's location within an ambient string.
-/
-- Some of the information contained in `FormatError` is redundant, however, it is useful to convert
-- between the `String.pos` and `String` length conveniently.
structure FormatError where
  /-- The distance to the end of the source string, as number of characters -/
  srcNat : Nat
  /-- The distance to the end of the source string, as number of string positions -/
  srcEndPos : String.Pos
  /-- The distance to the end of the formatted string, as number of characters -/
  fmtPos : Nat
  /-- The kind of formatting error. For example: `extra space`, `remove line break` or
  `missing space`.

  Strings starting with `Oh no` indicate an internal error.
  -/
  msg : String
  /-- The length of the mismatch, as number of characters. -/
  length : Nat
  /-- The starting position of the mismatch, as a `String.pos`. -/
  srcStartPos : String.Pos
  deriving Inhabited

instance : ToString FormatError where
  toString f :=
    s!"srcNat: {f.srcNat}, srcPos: {f.srcEndPos}, fmtPos: {f.fmtPos}, \
      msg: {f.msg}, length: {f.length}\n"

/--
Produces a `FormatError` from the input data.  It expects
* `ls` to be a "user-typed" string;
* `ms` to be a "pretty-printed" string;
* `msg` to be a custom error message, such as `extra space` or `remove line break`;
* `length` (optional with default `1`), how many characters the error spans.

In particular, it extracts the position information within the string, both as number of characters
and as `String.Pos`.
-/
def mkFormatError (ls ms : String) (msg : String) (length : Nat := 1) : FormatError where
  srcNat := ls.length
  srcEndPos := ls.endPos
  fmtPos := ms.length
  msg := msg
  length := length
  srcStartPos := ls.endPos

/--
Add a new `FormatError` `f` to the array `fs`, trying, as much as possible, to merge the new
`FormatError` with the last entry of `fs`.
-/
def pushFormatError (fs : Array FormatError) (f : FormatError) : Array FormatError :=
  -- If there are no errors already, we simply add the new one.
  if fs.isEmpty then fs.push f else
  let back := fs.back!
  -- If the latest error is of a different kind than the new one, we simply add the new one.
  if back.msg != f.msg || back.srcNat - back.length != f.srcNat then fs.push f else
  -- Otherwise, we are adding a further error of the same kind and we therefore merge the two.
  fs.pop.push {back with length := back.length + f.length, srcStartPos := f.srcEndPos}

/--
Compares the two substrings `s1` and `s2`, with the expectation that `s2` starts with `s1`,
and that the characters where this is not true satisfy `f`.

If the expectation is correct, then it returns `some (s2 \ s1)`, otherwise, it returns `none`.

The typical application uses `f = invisible`.
-/
partial
def consumeIgnoring (s1 s2 : Substring) (f : String → Bool) : Option Substring :=
  -- The expected end of the process: `s1` is fully consumed, we return `s2`.
  if s1.isEmpty || s2.isEmpty then s2 else
  -- Otherwise, we compare the first available character of each string.
  let a1 := s1.take 1
  let a2 := s2.take 1
  -- If they agree, we move one step over and continue.
  if a1 == a2 then
    consumeIgnoring (s1.drop 1) (s2.drop 1) f
  else
    -- Also if every character of `a1` or `a2` satisfies `f`, then we drop that and continue.
    if f a1.toString then consumeIgnoring (s1.drop 1) s2 f else
    if f a2.toString then consumeIgnoring s1 (s2.drop 1) f
    -- If all else failed, then we return `none`.
    else some s2

--def invisible (c : Char) : Bool :=
--  c.isWhitespace || #['«', '»'].contains c

def invisible (s : String) : Bool :=
  s.all fun c => c.isWhitespace || #['«', '»'].contains c

/-- Extract the `leading` and the `trailing` substring of a `SourceInfo`. -/
def _root_.Lean.SourceInfo.getLeadTrail : SourceInfo → String × String
  | .original lead _ trail _ => (lead.toString, trail.toString)
  | _ => default

def compareLeaf (tot : Array Nat) (leadTrail : String × String) (orig s : String) : Array Nat := Id.run do
    let (l, t) := leadTrail
    let mut newTot := tot
    if !l.isEmpty then
      newTot := newTot.push s.length
    if !s.startsWith orig then newTot := newTot.push s.length
    let rest := s.drop orig.length
    if t.trim.isEmpty then if t == " " || t == "\n" then return newTot
    if (t.dropWhile (· == ' ')).take 2 == "--" || (t.dropWhile (· == ' ')).take 1 == "\n" then return newTot
    return newTot.push rest.length

/--
Analogous to `Lean.PrettyPrinter.ppCategory`, but does not run the parenthesizer,
so that the output should only differ from the source syntax in whitespace.
-/
def ppCategory' (cat : Name) (stx : Syntax) : CoreM Format := do
  let opts ← getOptions
  let stx := (sanitizeSyntax stx).run' { options := opts }
  -- the next line starts with `parenthesizeCategory cat stx` in `Lean.PrettyPrinter.ppCategory`
  stx >>= PrettyPrinter.formatCategory cat

/-- Replaces each consecutive run of whitespace in the input `s` with a single space. -/
def reduceWhitespace (s : String) : String :=
  " ".intercalate <| (s.split (·.isWhitespace)).filter (!·.isEmpty)

/-- Converts the input syntax into a string using the pretty-printer and then collapsing
consecuting whitespace into a single space. -/
def pretty (stx : Syntax) : CommandElabM (Option String) := do
  let fmt : Option Format := ←
      try
        liftCoreM <| ppCategory' `command stx
      catch _ =>
        Linter.logLintIf linter.style.commandStart.verbose (stx.getHead?.getD stx)
          m!"The `commandStart` linter had some parsing issues: \
            feel free to silence it and report this error!"
        return none
  if let some fmt := fmt then
    let st := fmt.pretty (width := 100000)
    return reduceWhitespace st
  else
    return none

/--
Splays the input syntax into a string.

There is a slight subtlety about `choice` nodes, that are traversed only once.
-/
partial
def _root_.Lean.Syntax.regString : Syntax → String
  | .node _ `choice args => (args.take 1).foldl (init := "") (· ++ ·.regString)
  | .node _ _ args => args.foldl (init := "") (· ++ ·.regString)
  | .ident i raw _ _ => let (l, t) := i.getLeadTrail; l ++ raw.toString ++ t
  | .atom i s => let (l, t) := i.getLeadTrail; l ++ s ++ t
  | .missing => ""

/-- Replaces the leading and trailing substrings in a `SourceInfo` with `"".toSubstring`. -/
def _root_.Lean.SourceInfo.removeSpaces : SourceInfo → SourceInfo
  | .original _ p _ q => .original "".toSubstring p "".toSubstring q
  | s => s
  --| .synthetic p q c => .synthetic p q c
  --| .none => .none

/-- For every node of the input syntax, replace the leading and trailing substrings in every
`SourceInfo` with `"".toSubstring`. -/
partial
def _root_.Lean.Syntax.eraseLeadTrailSpaces : Syntax → Syntax
  | .node i k args => .node i.removeSpaces k (args.map (·.eraseLeadTrailSpaces))
  | .ident i raw v p => .ident i.removeSpaces raw v p
  | .atom i s => .atom i.removeSpaces s
  | .missing => .missing

def withVerbose {α} (v : Bool) (s : String) (a : α) : α :=
  if v then
    dbg_trace s
    a
  else
    a

/-- Answers whether a `Substring` starts with a space (` `), contains possibly more spaces,
until there is either `/ -` (without the space between `/` and `-`) or `--`. -/
def onlineComment (s : Substring) : Bool :=
  (s.take 1).toString == " " &&
    #[ "/-", "--"].contains ((s.dropWhile (· == ' ')).take 2).toString

/--
Assumes that `pp` is either empty or a single space, as this is satisfied by the intended
application.

Checks whether `orig` is an "acceptable version" of `pp`:
1. if `pp` is a space, check that `orig` starts either
   * with a line break, or
   * with a single space and then a non-space character,
   * with at least one space and then a `onlineComment`;
2. if `pp` is empty, check that `orig` is empty as well or starts either
   * with a non-whitespace character,
   * with at least one space and then a `onlineComment`.

TODO: should item 2. actually check that there is no space and that's it?
-/
def validateSpaceAfter (orig pp : Substring) : Bool :=
  -- An empty `pp`ed tail sould correspond to
  -- an empty `orig`,
  -- something starting with a line break,
  -- something starting with some spaces and then a comment
  let orig1 := (orig.take 1).toString
  let orig2 := (orig.take 2).toString
  dbg_trace
    "pp.isEmpty {pp.isEmpty}\n\
    if {pp.isEmpty}:\n  \
      orig.takeWhile (·.isWhitespace): {orig.takeWhile (·.isWhitespace)}\n  \
      or\n  \
      onlineComment orig: {onlineComment orig}\n\
    if {!pp.isEmpty}:\n  \
      (orig1 == \"⏎\"): {(orig1 == "\n")}\n  \
      or\n  \
      onlineComment orig: {onlineComment orig}\n  \
      or\n  \
      orig1 == \" \" && !orig2.trim.isEmpty: {orig1 == " " && !orig2.trim.isEmpty}"
  (pp.isEmpty && ((orig.takeWhile (·.isWhitespace)).isEmpty || onlineComment orig)) ||
    (
      (!pp.isEmpty) && ((orig1 == "\n") || onlineComment orig || (orig1 == " " && !orig2.trim.isEmpty))
    )

#eval show TermElabM _ from do
  let space : Substring := " ".toSubstring
  let spaceChar : Substring := " f".toSubstring
  let doublespaceChar : Substring := "  f".toSubstring
  let doublespace : Substring := "  ".toSubstring
  let noSpace : Substring := "".toSubstring
  let linebreak : Substring := "\n".toSubstring
  let commentInline : Substring := "  --".toSubstring
  let commentMultiline : Substring := "  /-".toSubstring
  -- `true`
  guard <| onlineComment commentInline
  guard <| onlineComment commentMultiline
  guard <| validateSpaceAfter spaceChar space
  guard <| validateSpaceAfter linebreak space
  guard <| validateSpaceAfter commentInline space
  guard <| validateSpaceAfter commentMultiline space
  guard <| validateSpaceAfter noSpace noSpace
  guard <| validateSpaceAfter "a".toSubstring noSpace
  -- `false`
  guard <| !onlineComment space
  guard <| !onlineComment doublespace
  guard <| !onlineComment noSpace
  guard <| !onlineComment linebreak
  -- A space not followed by a character is not accepted.
  guard <| !validateSpaceAfter space space
  guard <| !validateSpaceAfter doublespaceChar space
  guard <| !validateSpaceAfter space noSpace
  guard <| !validateSpaceAfter spaceChar noSpace
  guard <| !validateSpaceAfter doublespaceChar noSpace

/-- Assume both substrings come from actual trails. -/
def validateSpaceAfter' (orig pp : Substring) : Bool :=
  -- An empty `pp`ed tail sould correspond to
  -- an empty `orig`,
  -- something starting with a line break,
  -- something starting with some spaces and then a comment
  let orig1 := (orig.take 1).toString
  let orig2 := (orig.take 2).toString
  let answer := (orig1 == "\n") ||
    (pp.isEmpty && ((orig.takeWhile (·.isWhitespace)).isEmpty || onlineComment orig)) ||
      (
        (!pp.isEmpty) && (onlineComment orig || (orig1 == " " && orig2 != "  "))
      )
  withVerbose (!answer)
    s!"\
    orig1 == \"⏎\": {orig1 == "\n"}\n\
    or\n  \
    pp.isEmpty {pp.isEmpty}\n\
    if {pp.isEmpty}:\n  \
      orig.takeWhile (·.isWhitespace): {orig.takeWhile (·.isWhitespace)}\n  \
      or\n  \
      onlineComment orig: {onlineComment orig}\n\
    if {!pp.isEmpty}:\n  \
      onlineComment orig: {onlineComment orig}\n  \
      or\n  \
      orig1 == \" \" && orig1 == orig2: {orig1 == " " && orig1 == orig2}"
      answer

#eval show TermElabM _ from do
  let space : Substring := " ".toSubstring
  let spaceChar : Substring := " f".toSubstring
  let doublespaceChar : Substring := "  f".toSubstring
  let doublespace : Substring := "  ".toSubstring
  let noSpace : Substring := "".toSubstring
  let linebreak : Substring := "\n".toSubstring
  let commentInline : Substring := "  --".toSubstring
  let commentMultiline : Substring := "  /-".toSubstring
  -- `true`
  guard <| validateSpaceAfter' spaceChar space
  guard <| validateSpaceAfter' linebreak space
  guard <| validateSpaceAfter' commentInline space
  guard <| validateSpaceAfter' commentMultiline space
  guard <| validateSpaceAfter' noSpace noSpace
  guard <| validateSpaceAfter' "a".toSubstring noSpace
  -- A space not followed by a character *is accepted*.
  guard <| validateSpaceAfter' space space
  guard <| !validateSpaceAfter' doublespaceChar space
  -- `false`
  guard <| !validateSpaceAfter' space noSpace
  guard <| !validateSpaceAfter' spaceChar noSpace
  guard <| !validateSpaceAfter' doublespaceChar noSpace

#eval
  let origStr := "intro      --hi"
  let str := "intro hi"
  let orig : Substring := {origStr.toSubstring with startPos := ⟨"intro".length⟩}
  let pp : Substring := {str.toSubstring with startPos := ⟨"intro".length⟩}
  let pp : Substring := "".toSubstring
  dbg_trace "pp.isEmpty: {pp.isEmpty}, validate {validateSpaceAfter orig pp}"
  validateSpaceAfter orig pp
#eval validateSpaceAfter' " ".toSubstring " ".toSubstring
structure Exceptions where
  orig : String
  pp : String
  pos : String.Pos
  kind : SyntaxNodeKind
  reason : String

instance : ToString Exceptions where
  toString
  | {orig := o, pp := pp, pos := p, kind := k, reason := r} =>
    s!"Exception\npos:  {p}\nkind: '{k}'\norig: '{o.norm}'\npret: '{pp.norm}'\nreason: {r}\n---"

def addException (e : Array Exceptions) (orig pp : String) (p : String.Pos) (k : SyntaxNodeKind) (reason : String) :
    Array Exceptions :=
  e.push <| Exceptions.mk orig pp p k reason

def validateAtomOrId (tot : Array Exceptions) (kind : SyntaxNodeKind) (i1 i2 : SourceInfo) (s1 s2 : String) (str : Substring) :
    Substring × Array Exceptions :=
  let (l1, t1) := i1.getLeadTrail
  --let (l2, t2) := i2.getLeadTrail
  --dbg_trace "removing '{s2}'"
  let stripString := consumeIgnoring s2.toSubstring str invisible|>.getD default --str.drop s2.length
  let trail := stripString.takeWhile (·.isWhitespace)
  --withVerbose (trail.isEmpty != t1.isEmpty) s!"Discrepancy at {s1}, orig: '{t1}' pped: '{trail}'"
  let isValid := validateSpaceAfter' t1.toSubstring trail
  --dbg_trace "{isValid} -- {(s1, s2)}: '{t1}', '{trail}'\n"
  let tot1 := if isValid then
                tot
              else
                dbg_trace "invalid with '{s1}' '{s2}' '{t1}' '{trail.toString}' '{stripString.startPos}' '{kind}'"
                addException tot t1 trail.toString stripString.startPos kind "invalid"
--consumeIgnoring s2.toSubstring str invisible
  --if ((!str.toString.startsWith s1) || (!str.toString.startsWith s2)) then
  if (((consumeIgnoring s1.toSubstring str invisible).isNone) ||
      ((consumeIgnoring s2.toSubstring str invisible).isNone)) then
    dbg_trace s!"something went wrong\n\
      --- All pretty {kind} ---\n{str.toString}\ndoes not start with either of the following\n\
      --- Orig ---\n'{s1.norm}'\n--- Pretty---\n'{s2.norm}'\n---\n{tot1}"
    match consumeIgnoring s2.toSubstring str invisible with
    | some leftOver =>
      (leftOver, addException tot1 t1 trail.toString stripString.startPos kind
        s!"wrong:\n'{s1}' or\n'{s2}' is not the start of\n'{str.toString}'")
    | none =>
      (stripString |>.dropWhile (·.isWhitespace), addException tot1 t1 trail.toString stripString.startPos kind s!"wrong: '{s1}' or '{s2}' is not the start of '{str.toString}'")
  else
    ( --withVerbose (!isValid) s!"Discrepancy at {s1}, orig: '{t1}' pped: '{trail}'"
      stripString |>.dropWhile (·.isWhitespace), tot1)
#eval validateSpaceAfter' " ".toSubstring " ".toSubstring
def exclusions : NameSet := NameSet.empty
  |>.insert ``Parser.Command.docComment

def scanWatching (verbose? : Bool) :
    Array Exceptions → SyntaxNodeKind → Syntax → Syntax → Substring → Substring × Array Exceptions
  | tot, k, .ident i1 s1 n1 p1, .ident i2 s2 n2 p2, str =>
    withVerbose verbose? "idents" <|
      validateAtomOrId tot k i1 i2 s1.toString s2.toString str
  | tot, k, .atom i1 s1, .atom i2 s2, str =>
    withVerbose verbose? "atoms" <|
      validateAtomOrId tot k i1 i2 s1 s2 str
  | tot, k, .node i1 s1 as1, ppstx@(.node i2 s2 as2), str =>
    let s1 := if s1 == `null then k else s1
    --if exclusions.contains s1 then
    --  dbg_trace "skipping {s1}"
    --  let endPos := ppstx.getTrailingTailPos?.get!
    --  let endPos := as2.back!.getTrailingTailPos?.get!
    --  let endPos := as2.back!.getRange?.get!.stop
    --  let endPos := ppstx.getRange?.get!.stop
    --  ({str with startPos := endPos}, tot)
    --else
    withVerbose (as1.size != as2.size) "** Error! **" <|
    withVerbose verbose? "nodes" <| Id.run do
      let mut pos := str.startPos
      let mut tots := tot
      for h : i in [:as1.size] do
        let a1 := as1[i]
        let a2 := as2[i]?.getD default
        let ({startPos := sp,..}, news) := scanWatching verbose? tots s1 a1 a2 {str with startPos := pos}
        pos := sp
        tots := news
      ({str with startPos := pos}, tots)
  | tot, k, s1, s2, str =>
    withVerbose verbose? "rest" <|
      (str, tot)

def modifyTail (si : SourceInfo) (newTrail : Substring) : SourceInfo :=
  match si with
  | .original lead pos _ endPos => .original lead pos newTrail endPos
  | _ => si

/--
Compares the two substrings `s` and `t`, with the expectation that `t` starts with `s`,
up to whitespace.

It returns the substring of `t` that starts from the first position where it differs from `s`,
after it erased potential whitespace, taking care of preserving the last whitespace, if present.

The typical application is when `s` is the value of an atom/identifier leaf in `Syntax` and
`t` is the pretty-printed version of the whole syntax tree.
The main goal is to figure out what is the trailing whitespace substring
(usually either empty `""` or a single space `" "`).
-/
partial
def readWhile (s t : Substring) : Substring :=
  if s.isEmpty || t.isEmpty then t else
  let s1 := s.take 1
  let t1 := t.take 1
  if s1 == t1 then
    readWhile (s.drop 1) (t.drop 1)
  else
    if t1.trim.isEmpty then
      readWhile s t.trimLeft
    else
    if s1.trim.isEmpty then
      readWhile s.trimLeft t
    else
      t

#eval show Lean.Elab.Term.TermElabM _ from do
  let s := "/- alsdkj la l    asklj  ew ljr  wer-/".toSubstring
  let t := "/- alsdkj la l asklj ew ljr    wer-/ theorem".toSubstring
  guard <| (readWhile s t).toString == " theorem"
  let t := "/- alsdkj la l asklj ew ljr    wer-/theorem".toSubstring
  guard <| (readWhile s t).toString == "theorem"

#eval show Lean.Elab.Term.TermElabM _ from do
  let s := "example".toSubstring
  let t := "example := 0".toSubstring
  guard <| (readWhile s t).toString == " := 0"
  let t := ":= 0".toSubstring
  guard <| (readWhile (" :=".toSubstring) t).toString == " 0"
  guard <| (readWhile (" := ".toSubstring) t).toString == "0"

def _root_.Substring.toRange (s : Substring) : String.Range where
  start := s.startPos
  stop := s.stopPos

structure mex where
  rg : String.Range
  error : String
  kinds : Array SyntaxNodeKind

def mex.toString {m} [Monad m] [MonadFileMap m] (ex : mex) : m String := do
  let fm ← getFileMap
  return s!"{ex.error} {(fm.toPosition ex.rg.start, fm.toPosition ex.rg.stop)} ({ex.kinds})"

/--
A structure combining the various exceptions to the `commandStart` linter.
* `kinds` is the array of `SyntaxNodeKind`s that are ignored by the `commandStart` linter.
* `depth` represents how many `SyntaxNodeKind`s the `commandStart` linter climbs, in search of an
  exception.

  A depth of `none`, means that the linter ignores nodes starting with the given `SyntaxNodeKind`
  and any sub-node.

  A depth of `some n` means that the linter will only ignore the first `n` `SyntaxNodeKind`s
  starting from the given `SyntaxNodeKind` and resumes checking for all deeper nodes.
-/
structure ExcludedSyntaxNodeKind where
  /-- `kinds` is the array of `SyntaxNodeKind`s that are ignored by the `commandStart` linter. -/
  kinds : Array SyntaxNodeKind
  /--
  `depth` represents how many `SyntaxNodeKind`s the `commandStart` linter climbs, in search of an
  exception.

  A depth of `none`, means that the linter ignores nodes starting with the given `SyntaxNodeKind`
  and any sub-node.

  A depth of `some n` means that the linter will only ignore the first `n` `SyntaxNodeKind`s
  starting from the given `SyntaxNodeKind` and resumes checking for all deeper nodes.
  -/
  depth : Option Nat

/--
`unparseable` are the `SyntaxNodeKind`s that block the `commandStart` linter: their appearance
anywhere in the syntax tree makes the linter ignore the whole command.

This is the reason their `depth` is `none`.
-/
def unparseable : ExcludedSyntaxNodeKind where
  kinds := #[
    ``Parser.Command.macro_rules,
    ``runCmd,
  ]
  depth := none

/--
These are the `SyntaxNodeKind`s for which we want to ignore the pretty-printer.

Deeper nodes are *not* inspected.
-/
def totalExclusions : ExcludedSyntaxNodeKind where
  kinds := #[
    ``Parser.Command.docComment, -- Prevents formatting of doc-strings.
    ``Parser.Command.moduleDoc, -- Prevents formatting of module docs.
    `Mathlib.Meta.setBuilder, -- Prevents formatting of `{a | ...}`.
    ``Parser.Tactic.tacticSeqBracketed, -- Prevents formatting of `{ tactics }`.
    ``Parser.Command.macro, -- Prevents formatting of `macro`.
    ``Parser.Command.elab, -- Prevents formatting of `elab`.
    ``Parser.Command.elab_rules, -- Prevents formatting of `elab_rules`.
    `Mathlib.Meta.«term{_|_}», -- Prevents formatting of `{ f x y | (x : X) (y : Y) }`.
    ``«term[_]», -- Prevents formatting of lists.
    ``«term#[_,]», -- Prevents formatting of arrays.
    ``Parser.Term.anonymousCtor, -- Prevents formatting of `⟨...⟩`.
    ``Parser.Command.syntax, -- Prevents formatting of `syntax ...`.
  ]
  depth := none

/--
These are the `SyntaxNodeKind`s for which the pretty-printer would likely not space out from the
following nodes, but we overrule it and place a space anyway.
-/
def forceSpaceAfter : ExcludedSyntaxNodeKind where
  kinds := #[
    `token.«·», -- the focusing dot `·` in `conv` mode
    ``termThrowError__, -- `throwError "message"`
    -- Syntax nodes that do not pretty-print with a space, if followed by a parenthesis `()`
    ``Parser.Tactic.rcases, -- `rcases (a)`
    ``Parser.Tactic.replace, -- `replace (a)`
    ``Parser.Term.let, -- `let (a)` in term mode.
    ``Parser.Term.whereDecls, -- `where`
  ]
  depth := some 2

def forceSpaceAfter' : ExcludedSyntaxNodeKind where
  kinds := #[
    `atom.«have», -- `have (a)` in term mode.
  ]
  depth := some 1

/--
These are the `SyntaxNodeKind`s for which the pretty-printer would likely space out from the
following nodes, but we overrule it and do not place a space.
-/
def forceNoSpaceAfter : ExcludedSyntaxNodeKind where
  kinds := #[
    --``Parser.Term.doubleQuotedName,
    `atom.«`», -- useful for double-quoted names
  ]
  depth := some 2

/--
Checks whether the input array `ks` of `SyntaxNodeKind`s matches the conditions implied by
the `ExcludedSyntaxNodeKind` `exc`.

The function takes into account what the `SyntaxNodeKind`s in `ks` are, as well as their
depth, as required by `exc.depth`.
-/
def ExcludedSyntaxNodeKind.contains (exc : ExcludedSyntaxNodeKind) (ks : Array SyntaxNodeKind) :
    Bool :=
  let lastNodes := if let some n := exc.depth then ks.drop (ks.size - n) else ks
  !(lastNodes.filter exc.kinds.contains).isEmpty

def filterSortExceptions (as : Array mex) : Array mex :=
  let filtered := as.filter (!totalExclusions.contains ·.kinds)
  filtered.qsort (·.rg.start < ·.rg.start)

def processAtomOrIdent {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (k : Array SyntaxNodeKind) (val str : Substring) : m (Substring × Substring × Substring) := do
  --dbg_trace "forceSpaceAfter.contains {k}: {forceSpaceAfter.contains k}\nStarting with '{val}'\n"
  let read := readWhile val str
  if read == str && (!read.isEmpty) && (!k.contains `hygieneInfo) then
    logWarning m!"No change at '{read}' {k}"
  --dbg_trace k
  let (next, strNew) :=
    -- Case `read = " "`
    if (read.take 1).toString == " "
    then
      -- Case `read = " "` but we do not want a space after
      if forceNoSpaceAfter.contains k then
        ("".toSubstring, read.drop 1)
      else
        (" ".toSubstring, read.drop 1)
    else
    -- Case `read = ""` but we want a space after anyway
    if forceSpaceAfter.contains k || forceSpaceAfter'.contains k then
      --dbg_trace "adding a space at '{read}'\n"
      (" ".toSubstring, read)
    -- Case `read = ""` and we follow the pretty-printer recommendation
    else
      ("".toSubstring, read)
  pure (next, strNew, read)

/--
`insertSpacesAux verbose? noSpaceStx prettyString`
scans the syntax tree `noSpaceStx` and, whenever it finds an `atom` or `ident` node,
it compares it with the substring `prettyString`, consuming the value of the `atom`/`ident` and
appending the following whitespace as trailing substring in the `SourceInfo`, if such a space is
present.

This essentially converts `noSpaceStx` into a `Syntax` tree whose traversal reconstructs exactly
`prettyString`.
-/
def insertSpacesAux {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (verbose? : Bool) :
    Array SyntaxNodeKind → Syntax → Substring → m (Syntax × Substring)
  | k, .ident info rawVal val pre, str => do
    --let read := readWhile rawVal str
    --if read == str && !read.isEmpty then
    --  logWarning m!"No change at '{read}'"
    --let (next, strNew) :=
    --  if (read.take 1).toString == " " || forceSpaceAfter.contains k
    --  then
    --    (" ".toSubstring, read.drop 1)
    --  else
    --    ("".toSubstring, read)
    let (next, strNew, read) ← processAtomOrIdent (k.push (.str `ident rawVal.toString)) rawVal str
    if verbose? then
      dbg_trace
        s!"* ident '{rawVal}'\nStr: '{str}'\nRed: '{read}'\nNxt: '{next}'\nNew: '{strNew}'\n"
    pure (.ident (modifyTail info next) rawVal val pre, strNew)
  | k, .atom info val, str => do
    --let read := readWhile val.toSubstring str
    --if read == str && !read.isEmpty then
    --  logWarning m!"No change at '{read}'"
    --let (next, strNew) :=
    --  if (read.take 1).toString == " " || forceSpaceAfter.contains k
    --  then
    --    (" ".toSubstring, read.drop 1)
    --  else
    --    ("".toSubstring, read)
    let (next, strNew, read) ← processAtomOrIdent (k.push (.str `atom val)) val.toSubstring str
    if verbose? then
      dbg_trace
        s!"* atom '{val}'\nStr: '{str}'\nRed: '{read}'\nNxt: '{next}'\nNew: '{strNew}'\n"
    pure (.atom (modifyTail info next) val, strNew)
  | k, .node info kind args, str => do
    --let kind := if kind == `null then k else kind
    let mut str' := str
    let mut stxs := #[]
    for arg in args do
      let (newStx, strNew) ← insertSpacesAux verbose? (k.push kind) arg str'
      if verbose? then
        dbg_trace s!"'{strNew}' intermediate string at {k.push kind}"
      str' := strNew.trimLeft
      stxs := stxs.push newStx
    pure (.node info kind stxs, str')
  | _, stx, str => do
    pure (stx, str)

open Lean in
/--
`insertSpaces verbose? stx` first replaces in `stx` every `trailing` substring in every `SourceInfo`
with either `"".toSubstring` or `" ".toSubstring`, according to what the pretty-printer would
place there.

In particular, it erases all comments embedded in `SourceInfo`s.
-/
def insertSpaces (verbose? : Bool) (stx : Syntax) : CommandElabM (Option Syntax) := do
  let stxNoSpaces := stx.eraseLeadTrailSpaces
  if let some pretty := ← Mathlib.Linter.pretty stxNoSpaces then
    let withSpaces ← insertSpacesAux verbose? #[stx.getKind] stx pretty.toSubstring
    return withSpaces.1
  else return none

def allowedTrail (ks : Array SyntaxNodeKind) (orig pp : Substring) : Option mex :=
  let orig1 := (orig.take 1).toString
  if orig.toString == pp.toString then none else
  -- Case `pp = ""`
  if pp.isEmpty then
    match orig1 with
    | " " => some ⟨orig.toRange, "remove space", ks⟩
    | "\n" => some ⟨orig.toRange, "remove line break", ks⟩
    | _ => some ⟨orig.toRange, "please, report this issue!", ks⟩ -- is this an unreachable case?
  -- Case `pp = " "`
  else
    if orig.isEmpty then
      let misformat : Substring := {orig with stopPos := orig.stopPos + ⟨1⟩}
      some ⟨misformat.toRange, "add space", ks⟩
    else
    -- Allow line breaks
    if (orig.take 1).toString == "\n" then
      none
    else
    -- Allow comments
    if onlineComment orig then
      none
    else
    if (2 ≤ orig.toString.length) then
      some ⟨(orig.drop 1).toRange, if (orig.take 1).toString == "\n" then "remove line break" else "remove space", ks⟩
    else
      default

def _root_.Lean.SourceInfo.compareSpaces (ks : Array SyntaxNodeKind) :
    SourceInfo → SourceInfo → Option mex
  | .original _ _ origTrail .., .original _ _ ppTrail .. =>
    allowedTrail ks origTrail ppTrail
  | _, _ => none

partial
def _root_.Lean.Syntax.compareSpaces : Array SyntaxNodeKind → Array mex → Syntax → Syntax → Array mex
  | kinds, tot, .node _ kind a1, .node _ _ a2 =>
    a1.zipWith (fun a b => a.compareSpaces (kinds.push kind) tot b) a2 |>.flatten
  | kinds, tot, .ident origInfo rawVal .., .ident ppInfo .. =>
    --let val := rawVal--.toString
    if let some e := origInfo.compareSpaces (kinds.push (.str `ident rawVal.toString)) ppInfo
    then
      tot.push e else tot
  | kinds, tot, .atom origInfo val .., .atom ppInfo .. =>
    if let some e := origInfo.compareSpaces (kinds.push (.str `atom val)) ppInfo
    then
      tot.push e else tot
  | _, tot, _, _ => tot
--  | tot, .missing .., .missing .. => tot
--  | tot, .node _ k _, _ => tot
--  | tot, _, .node _ k _ => tot
--  | tot, .atom .., _ => tot
--  | tot, _, .atom .. => tot
--  | tot, .ident .., _ => tot
--  | tot, _, .ident .. => tot

open Parser in
/-- `captureException env s input` uses the given `Environment` `env` to parse the `String` `input`
using the `ParserFn` `s`.

This is a variation of `Lean.Parser.runParserCategory`.
-/
def captureException (env : Environment) (s : ParserFn) (input : String) : Except String Syntax :=
  let ictx := mkInputContext input "<input>"
  let s := s.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if !s.allErrors.isEmpty then
    .error (s.toErrorMsg ictx)
  else if ictx.input.atEnd s.pos then
    .ok s.stxStack.back
  else
    .error ((s.mkError "end of input").toErrorMsg ictx)

/-- Returning `none` denotes a processing error. -/
def getExceptions (stx : Syntax) : CommandElabM (Option (Array mex)) := do
  let stxNoTrail := stx.unsetTrailing
  if let some stxNoSpaces ← insertSpaces false stx then
    return stxNoTrail.compareSpaces #[] #[] stxNoSpaces
  else
    return none

--/
/-
def finalScan (stx : Syntax) (verbose? : Bool) : CommandElabM (Array Exceptions) := do
  let ustx := stx.eraseLeadTrailSpaces
  let simplySpaced ← pretty ustx <|> return default

  return scanWatching verbose? #[] stx.getKind stx ustx (simplySpaced).toSubstring |>.2
-/

/-
#eval True ∧ 0 ^ 0 = 1

open Lean Elab Command in
elab "#compare " v:(&"v ")? stx:command : command => do
  elabCommand stx <|> return
  if (← get).messages.hasErrors then
    return
  let ustx := stx.raw.eraseLeadTrailSpaces
  let simplySpaced ← pretty ustx <|> return default
  logInfo m!"Source:\n\
            {stx.raw.getSubstring?.get!}|||\n\
            Regenerated:\n{simplySpaced}|||\n\
            {scanWatching v.isSome #[] stx ustx (simplySpaced).toSubstring}"

--#compare/-- -/ theorem le : True ∧  0 ^0=  1 :=
--  sorry
--#exit
/-
#compare
example : True  ∧ 0 ^ 0 = 0 :=
by
  constructor -- here we split
  · refine ?_
    -- Now we know how to prove it
    exact trivial
  · apply ?_
    exact .intro  -- We use the constructor
-/


/--
info: Source:
example : True  ∧ True := by
  constructor -- here we split
  · refine ?_
    -- Now we know how to prove it
    exact trivial
  · apply ?_
    exact .intro  -- We use the constructor


|||
Regenerated:
example : True ∧ True := by constructor · refine ?_ exact trivial · apply ?_ exact .intro|||
(, [])
-/
#guard_msgs in
#compare
example : True  ∧ True := by
  constructor -- here we split
  · refine ?_
    -- Now we know how to prove it
    exact trivial
  · apply ?_
    exact .intro  -- We use the constructor
--/


/--
Scan the two input strings `L` and `M`, assuming `M` is the pretty-printed version of `L`.
This almost means that `L` and `M` only differ in whitespace.

While scanning the two strings, accumulate any discrepancies --- with some heuristics to avoid
flagging some line-breaking changes.
(The pretty-printer does not always produce desirably formatted code.)

The `rebuilt` input gets updated, matching the input `L`, whenever `L` is preferred over `M`.
When `M` is preferred, `rebuilt` gets appended the string
* `addSpace`, if `L` should have an extra space;
* `removeSpace`, if `L` should not have this space;
* `removeLine`, if this line break should not be present.

With the exception of `addSpace`, in the case in which `removeSpace` and `removeLine` consist
of a single character, then number of characters added to `rebuilt` is the same as the number of
characters removed from `L`.
-/
partial
def parallelScanAux (as : Array FormatError) (rebuilt : String) (L M : Substring)
    (addSpace removeSpace removeLine : String) :
    String × Array FormatError :=
  if M.trim.isEmpty then (rebuilt ++ L.toString, as) else
  -- We try as hard as possible to scan the strings one character at a time.
  -- However, single line comments introduced with `--` pretty-print differently than `/--`.
  -- So, we first look ahead for `/--`: the linter will later ignore doc-strings, so it does not
  -- matter too much what we do here and we simply drop `/--` from the original string and the
  -- pretty-printed one, before continuing.
  -- Next, if we already dealt with `/--`, finding a `--` means that this is a single line comment
  -- (or possibly a comment embedded in a doc-string, which is ok, since we eventually discard
  -- doc-strings).  In this case, we drop everything until the following line break in the
  -- original syntax, and for the same amount of characters in the pretty-printed one, since the
  -- pretty-printer *erases* the line break at the end of a single line comment.
  --dbg_trace (L.take 3, M.take 3)
  if (L.take 3).toString == "/--" && (M.take 3).toString == "/--" then
    parallelScanAux as (rebuilt ++ "/--") (L.drop 3) (M.drop 3) addSpace removeSpace removeLine else
  if (L.take 2).toString == "--" then
    let newL := L.dropWhile (· != '\n')
    let diff := L.toString.length - newL.toString.length
    -- Assumption: if `L` contains an embedded inline comment, so does `M`
    -- (modulo additional whitespace).
    -- This holds because we call this function with `M` being a pretty-printed version of `L`.
    -- If the pretty-printer changes in the future, this code may need to be adjusted.
    let newM := M.dropWhile (· != '-') |>.drop diff
    parallelScanAux as (rebuilt ++ (L.takeWhile (· != '\n')).toString ++ (newL.takeWhile (·.isWhitespace)).toString) newL.trimLeft newM.trimLeft addSpace removeSpace removeLine else
  if (L.take 2).toString == "-/" then
    let newL := L.drop 2 |>.trimLeft
    let newM := M.drop 2 |>.trimLeft
    parallelScanAux as (rebuilt ++ "-/" ++ ((L.drop 2).takeWhile (·.isWhitespace)).toString) newL newM addSpace removeSpace removeLine else
  let ls := L.drop 1
  let ms := M.drop 1
  match L.get 0, M.get 0 with
  | ' ', m =>
    if m.isWhitespace then
      parallelScanAux as (rebuilt.push ' ') ls ms.trimLeft addSpace removeSpace removeLine
    else
      parallelScanAux (pushFormatError as (mkFormatError L.toString M.toString "extra space")) (rebuilt ++ removeSpace) ls M addSpace removeSpace removeLine
  | '\n', m =>
    if m.isWhitespace then
      parallelScanAux as (rebuilt ++ (L.takeWhile (·.isWhitespace)).toString) ls.trimLeft ms.trimLeft addSpace removeSpace removeLine
    else
      parallelScanAux (pushFormatError as (mkFormatError L.toString M.toString "remove line break")) (rebuilt ++ removeLine ++ (ls.takeWhile (·.isWhitespace)).toString) ls.trimLeft M addSpace removeSpace removeLine
  | l, m => -- `l` is not whitespace
    if l == m then
      parallelScanAux as (rebuilt.push l) ls ms addSpace removeSpace removeLine
    else
      if m.isWhitespace then
        parallelScanAux (pushFormatError as (mkFormatError L.toString M.toString "missing space")) ((rebuilt ++ addSpace).push ' ') L ms.trimLeft addSpace removeSpace removeLine
    else
      -- If this code is reached, then `L` and `M` differ by something other than whitespace.
      -- This should not happen in practice.
      (rebuilt, pushFormatError as (mkFormatError ls.toString ms.toString "Oh no! (Unreachable?)"))

@[inherit_doc parallelScanAux]
def parallelScan (src fmt : String) : Array FormatError :=
  let (_expected, formatErrors) := parallelScanAux ∅ "" src.toSubstring fmt.toSubstring "🐩" "🦤" "😹"
  --dbg_trace "src:\n{src}\n---\nfmt:\n{fmt}\n---\nexpected:\n{expected}\n---"
  formatErrors

partial
def _root_.Lean.Syntax.compareToString : Array FormatError → Syntax → String → Array FormatError
  | tot, .node _ `choice args, s => (args.take 1).foldl (init := tot) (· ++ ·.compareToString tot s)
  | tot, .node _ _ args, s => args.foldl (init := tot) (· ++ ·.compareToString tot s)
  | tot, .ident i raw _ _, s =>
    let (l, t) := i.getLeadTrail
    let (_r, f) := parallelScanAux tot "" (l ++ raw.toString ++ t).toSubstring s.toSubstring "🐩" "🦤" "😹"
    --dbg_trace "'{r}'"
    f
  | tot, .atom i s', s => --compareLeaf tot i.getLeadTrail s' s
    let (l, t) := i.getLeadTrail
    let (_r, f) := parallelScanAux tot "" (l ++ s' ++ t).toSubstring s.toSubstring "🐩" "🦤" "😹"
    --dbg__trace "'{r}'"
    f
  | tot, .missing, _s => tot

partial
def _root_.Lean.Syntax.compare : Syntax → Syntax → Array SyntaxNodeKind
  | .node _ _ a1, .node _ _ a2 => a1.zipWith (fun a b => a.compare b) a2 |>.flatten
  | .ident .., .ident .. => #[]
  | .atom .., .atom .. => #[]
  | .missing .., .missing .. => #[]
  | .node _ k _, _ => #[k ++ `left]
  | _, .node _ k _ => #[k ++ `right]
  | .atom .., _ => #[`atomLeft]
  | _, .atom .. => #[`atomRight]
  | .ident .., _ => #[`identLeft]
  | _, .ident .. => #[`identRight]

/-
open Lean Elab Command in
elab "#comp " cmd:command : command => do
  elabCommand cmd
  let cmdString := cmd.raw.regString
  let pp ← pretty cmd
  dbg_trace "---\n{cmdString}\n---\n{pp}\n---"
  let comps := cmd.raw.compareToString #[] pp
  dbg_trace comps
--  dbg_trace "From start: {comps.map (cmdString.length - ·) |>.reverse}"
  --logInfo m!"{cmd}"
-/

namespace Style.CommandStart

/--
`unlintedNodes` contains the `SyntaxNodeKind`s for which there is no clear formatting preference:
if they appear in surface syntax, the linter will ignore formatting.

Currently, the unlined nodes are mostly related to `Subtype`, `Set` and `Finset` notation and
list notation.
-/
abbrev unlintedNodes := #[
  -- # set-like notations, have extra spaces around the braces `{` `}`

  -- subtype, the pretty-printer prefers `{ a // b }`
  ``«term{_:_//_}»,
  -- set notation, the pretty-printer prefers `{ a | b }`
  `«term{_}»,
  -- empty set, the pretty-printer prefers `{ }`
  ``«term{}»,
  -- various set builder notations, the pretty-printer prefers `{ a : X | p a }`
  `Mathlib.Meta.setBuilder,
  `Mathlib.Meta.«term{_|_}»,

  -- The pretty-printer lacks a few spaces.
  ``Parser.Command.syntax,

  -- # misc exceptions

  -- We ignore literal strings.
  `str,

  -- list notation, the pretty-printer prefers `a :: b`
  ``«term_::_»,

  -- negation, the pretty-printer prefers `¬a`
  ``«term¬_»,

  -- declaration name, avoids dealing with guillemets pairs `«»`
  ``Parser.Command.declId,

  `Mathlib.Tactic.superscriptTerm, `Mathlib.Tactic.subscript,

  -- notation for `Bundle.TotalSpace.proj`, the total space of a bundle
  -- the pretty-printer prefers `π FE` over `π F E` (which we want)
  `Bundle.termπ__,

  -- notation for `MeasureTheory.condExp`, the spaces around `|` may or may not be present
  `MeasureTheory.«term__[_|_]»,

  -- notation for `Finset.slice`, the pretty-printer prefers `𝒜 #r` over `𝒜 # r` (mathlib style)
  `Finset.«term_#_»,

  -- The docString linter already takes care of formatting doc-strings.
  ``Parser.Command.docComment,

  -- The pretty-printer adds a space between the backticks and the actual name.
  ``Parser.Term.doubleQuotedName,

  -- the `f!"..."` for interpolating a string
  ``Std.termF!_,

  -- `{structure}`
  ``Parser.Term.structInst,

  -- `let (a) := 0` pretty-prints as `let(a) := 0`, similarly for `rcases`.
  ``Parser.Term.let,
  ``Parser.Tactic.rcases,

  -- sometimes, where there are multiple fields, it is convenient to end a line with `⟨` and then
  -- align the indented fields on the successive lines, before adding the closing `⟩`.
  ``Parser.Term.anonymousCtor,
  -- similarly, we ignore lists and arrays
  ``«term[_]», ``«term#[_,]»,

  -- the `{ tacticSeq }` syntax pretty prints without a space on the left and with a space on the
  -- right.
  ``Parser.Tactic.tacticSeqBracketed,

  -- in `conv` mode, the focusing dot (`·`) is *not* followed by a space
  ``Parser.Tactic.Conv.«conv·._»,

  -- The pretty printer does not place spaces around the braces`{}`.
  ``Parser.Term.structInstField,

  -- `throwError "Sorry"` does not pretty-print the space before the opening `"`.
  ``termThrowError__,

  -- Ignore term-mode `have`, since it does not print a space between `have` and the identifier,
  -- if there is a parenthesis in-between.
  ``Parser.Term.have,
  -- For a similar reason, we also ignore tactic `replace`.
  ``Parser.Tactic.replace,

  -- If two `induction ... with` arms are "merged", then the pretty-printer
  -- does not put a space before the `|`s
  ``Parser.Tactic.inductionAlt,
  ]

/--
Given an array `a` of `SyntaxNodeKind`s, we accumulate the ranges of the syntax nodes of the
input syntax whose kind is in `a`.

The linter uses this information to avoid emitting a warning for nodes with kind contained in
`unlintedNodes`.
-/
def getUnlintedRanges (a : Array SyntaxNodeKind) :
    Std.HashSet String.Range → Syntax → Std.HashSet String.Range
  | curr, s@(.node _ kind args) =>
    let new := args.foldl (init := curr) (·.union <| getUnlintedRanges a curr ·)
    if a.contains kind then
      --dbg_trace "adding {s} at {s.getRange?.getD default}"
      new.insert (s.getRange?.getD default)
    else
      new
  -- We special case `where` statements, since they may be followed by an indented doc-string.
  | curr, .atom info "where" =>
    if let some trail := info.getRangeWithTrailing? then
      curr.insert trail
    else
      curr
  | curr, _ => curr

/-- Given a `HashSet` of `String.Range`s `rgs` and a further `String.Range` `rg`,
`isOutside rgs rg` returns `false` if and only if `rgs` contains a range that completely contains
`rg`.

The linter uses this to figure out which nodes should be ignored.
-/
def isOutside (rgs : Std.HashSet String.Range) (rg : String.Range) : Bool :=
  rgs.all fun {start := a, stop := b} ↦ !(a ≤ rg.start && rg.stop ≤ b)

def mkWindowSubstring (orig : Substring) (start : String.Pos) (ctx : Nat) : String :=
  let head : Substring := {orig with stopPos := start} -- `orig`, up to the beginning of the discrepancy
  let middle : Substring := {orig with startPos := start}
  let headCtx := head.takeRightWhile (!·.isWhitespace)
  let tail := middle.drop ctx |>.takeWhile (!·.isWhitespace)
  s!"{headCtx}{middle.take ctx}{tail}"

/--
We think of `orig` as `orig = ...<wordLeft><whitespaceLeft>|<whitespaceRight><wordRight>...`
where
* `<wordLeft>`  and `<wordLeft>` are maximal consecutive sequences of non-whitespace characters,
* `<whitespaceLeft>` and `<whitespaceRight>` are maximal consecutive sequences of whitespace
  characters,
* the `|` denotes the input position `start`.

We carve out the substring `<wordLeft><whitespaceLeft><whitespaceRight><wordRight>`.
-/
def mkWindowSubstring' (orig : Substring) (start : String.Pos) : String :=
  -- Starting from the first discrepancy, we move to the right, consuming all subsequent
  -- contiguous whitespace and then all subsequent contiguous non-whitespace.
  let fromError : Substring := {orig with startPos := start}
  let extRight := fromError.dropWhile (·.isWhitespace) |>.dropWhile (!·.isWhitespace)
  -- Ending at the first discrepancy, we move to the left, consuming all previous
  -- contiguous whitespace and then all previous contiguous non-whitespace.
  let toError : Substring := {orig with stopPos := start}
  let extLeft := toError.dropRightWhile (·.isWhitespace) |>.dropRightWhile (!·.isWhitespace)
  -- Carve the substring using the starting and ending positions determined above.
  {orig with startPos := extLeft.stopPos, stopPos := extRight.startPos}.toString

def _root_.Mathlib.Linter.mex.mkWindow (orig : Substring) (m : mex) (ctx : Nat := 4) : String :=
  let lth := ({orig with startPos := m.rg.start, stopPos := m.rg.stop}).toString.length
  mkWindowSubstring orig m.rg.start (ctx + lth)

/-- `mkWindow orig start ctx` extracts from `orig` a string that starts at the first
non-whitespace character before `start`, then expands to cover `ctx` more characters
and continues still until the first non-whitespace character.

In essence, it extracts the substring of `orig` that begins at `start`, continues for `ctx`
characters plus expands left and right until it encounters the first whitespace character,
to avoid cutting into "words".

*Note*. `start` is the number of characters *from the right* where our focus is!
-/
def mkWindow (orig : String) (start ctx : Nat) : String :=
  let head := orig.dropRight (start + 1) -- `orig`, up to one character before the discrepancy
  let middle := orig.takeRight (start + 1)
  let headCtx := head.takeRightWhile (!·.isWhitespace)
  let tail := middle.drop ctx |>.takeWhile (!·.isWhitespace)
  s!"{headCtx}{middle.take ctx}{tail}"

@[inherit_doc Mathlib.Linter.linter.style.commandStart]
def commandStartLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.style.commandStart (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  --if stx.getSubstring?.map toString != some stx.regString then
  --  dbg_trace stx.regString
  if stx.find? (unparseable.contains #[·.getKind]) |>.isSome then
    return
  let comps := (← getMainModule).components
  --dbg_trace "lint0"
  if comps.contains `Tactic ||
     comps.contains `Util ||
     comps.contains `Lean ||
     comps.contains `Meta
  then
    --dbg_trace comps
    return
  -- If a command does not start on the first column, emit a warning.
  --dbg_trace "lint1"
  let orig := stx.getSubstring?.getD default
  if let some mexs ← getExceptions stx then
  for m in filterSortExceptions mexs do
    --logInfoAt (.ofRange m.rg) m!"{m.error} ({m.kinds})"
    --dbg_trace "{m.mkWindow orig}"
    let origWindow := mkWindowSubstring' orig m.rg.start
    Linter.logLint linter.style.commandStart (.ofRange m.rg)
      m!"{m.error} in the source\n\n\
      This part of the code\n  '{origWindow.trim}'\
      "
        --should be written as\n  '{expectedWindow}'\n"

/-
  if let some pos := stx.getPos? then
    let colStart := ((← getFileMap).toPosition pos).column
    if colStart ≠ 0 then
      Linter.logLint linter.style.commandStart stx
        m!"'{stx}' starts on column {colStart}, \
          but all commands should start at the beginning of the line."
  -- We skip `macro_rules`, since they cause parsing issues.
  if (stx.find? fun s =>
    #[``Parser.Command.macro_rules, ``Parser.Command.macro, ``Parser.Command.elab].contains
      s.getKind ) |>.isSome then
    return
  let some upTo := CommandStart.endPos stx | return

  let fmt : Option Format := ←
      try
        liftCoreM <| ppCategory' `command stx --PrettyPrinter.ppCategory `command stx
      catch _ =>
        Linter.logLintIf linter.style.commandStart.verbose (stx.getHead?.getD stx)
          m!"The `commandStart` linter had some parsing issues: \
            feel free to silence it and report this error!"
        return none
  if let some fmt := fmt then
    let st := fmt.pretty
    let parts := st.split (·.isWhitespace) |>.filter (!·.isEmpty)
    --for p in parts do dbg_trace "'{p}'"
    let st := " ".intercalate parts
    let origSubstring := stx.getSubstring?.getD default
    let orig := origSubstring.toString
    if (! Parser.isTerminalCommand stx) && st.trim.isEmpty then logInfo m!"Empty on {stx}"
    else
    --dbg_trace "here"
    let slimStx := captureException (← getEnv) Parser.topLevelCommandParserFn st <|>
      .ok (.node default ``Parser.Command.eoi #[])
    --dbg_trace "there"
    if let .ok slimStx := slimStx then
      let diffs := stx.compare slimStx
      if !diffs.isEmpty then
        logInfo m!"{diffs}"
        dbg_trace stx
        dbg_trace slimStx
    else
      logWarning m!"Parsing error!\n{stx.getKind}|||\n---"
      dbg_trace stx
    --let parts := orig.split (·.isWhitespace) |>.filter (!·.isEmpty)
    --if ! ("".intercalate parts).startsWith (st.replace " " "" |>.replace "«" "" |>.replace "»" "") then
    --  logWarning m!"A\n{st.replace " " "" |>.replace "«" "" |>.replace "»" ""}\n---\n{"".intercalate parts}"

    let scan := parallelScan orig st
    let (o, n) := (scan.size, (← finalScan stx false).size)
    if o != n then
      dbg_trace "(old, new): ({o}, {n})"
      dbg_trace scan
      for e in (← finalScan stx false) do
        dbg_trace e
      let ustx := stx.eraseLeadTrailSpaces
      let simplySpaced ← pretty ustx <|> return default
      dbg_trace simplySpaced
    let docStringEnd := stx.find? (·.isOfKind ``Parser.Command.docComment) |>.getD default
    let docStringEnd := docStringEnd.getTailPos? |>.getD default
    let forbidden := getUnlintedRanges unlintedNodes ∅ stx
    --dbg_trace forbidden.fold (init := #[]) fun tot ⟨a, b⟩ => tot.push (a, b)
    for s in scan do
      --logInfo m!"Scanning '{s}'"
      let center := origSubstring.stopPos - s.srcEndPos
      let rg : String.Range := ⟨center, center + s.srcEndPos - s.srcStartPos + ⟨1⟩⟩
      if s.msg.startsWith "Oh no" then
        Linter.logLintIf linter.style.commandStart.verbose (.ofRange rg)
          m!"This should not have happened: please report this issue!"
        Linter.logLintIf linter.style.commandStart.verbose (.ofRange rg)
          m!"Formatted string:\n{fmt}\nOriginal string:\n{origSubstring}"
        continue
      --logInfo m!"Outside '{s}'? {isOutside forbidden rg}"
      unless isOutside forbidden rg do
        continue
      unless rg.stop ≤ upTo do return
      unless docStringEnd ≤ rg.start do return

      let ctx := 4 -- the number of characters after the mismatch that linter prints
      let srcWindow := mkWindow orig s.srcNat (ctx + s.length)
      let expectedWindow := mkWindow st s.fmtPos (ctx + (1))
      Linter.logLint linter.style.commandStart (.ofRange rg)
        m!"{s.msg} in the source\n\n\
          This part of the code\n  '{srcWindow}'\n\
          should be written as\n  '{expectedWindow}'\n"
      Linter.logLintIf linter.style.commandStart.verbose (.ofRange rg)
        m!"Formatted string:\n{fmt}\nOriginal string:\n{origSubstring}"
-/

initialize addLinter commandStartLinter

open Lean Elab Command in
elab tk:"#mex " cmd:(command)? : command => do
  let tktxt := "#mex"
  if let some cmd := cmd then if let some cmdSubstring := cmd.raw.getSubstring? then
  if let .error .. :=
    captureException (← getEnv) Parser.topLevelCommandParserFn cmd.raw.getSubstring?.get!.toString
  then
    logWarningAt tk m!"{tktxt}: Parsing failed"
    return
  elabCommand cmd
  --dbg_trace "here: {cmd}"
  if (← get).messages.hasErrors then
    logWarningAt tk "{tktxt}: Command has errors"
    return
  match ← getExceptions cmd with
  | none => logWarning m!"{tktxt}: Processing error"
  | some mexs =>
    if mexs.isEmpty then
      logInfo "No whitespace issues found!"
      return
    let (reported, unreported) := mexs.partition (!totalExclusions.contains ·.kinds)
    logInfo m!"{mexs.size} whitespace issue{if mexs.size == 1 then "" else "s"} found: \
        {reported.size} reported and {unreported.size} unreported."
    let fm ← getFileMap
    for m in reported do
      logWarningAt (.ofRange m.rg)
        m!"reported: {m.error}\n  '{mkWindowSubstring' cmdSubstring m.rg.start}'\n\
          {(fm.toPosition m.rg.start, fm.toPosition m.rg.stop)}\n\n\
          {m.kinds.map MessageData.ofConstName}"
    for m in unreported do
      logInfoAt (.ofRange m.rg)
        m!"unreported: {m.error} {(fm.toPosition m.rg.start, fm.toPosition m.rg.stop)}\n\n\
          {m.kinds.map MessageData.ofConstName}"

#mex
theorem X(_  :Nat) : True:=     --
  by  trivial;  done


end Style.CommandStart

end Mathlib.Linter
