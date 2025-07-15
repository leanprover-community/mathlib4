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

/-- Extract the `leading` and the `trailing` substring of a `SourceInfo`. -/
def _root_.Lean.SourceInfo.getLeadTrail : SourceInfo → String × String
  | .original lead _ trail _ => (lead.toString, trail.toString)
  | _ => default

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
def parallelScanAux (as : Array FormatError) (rebuilt L M : String)
    (addSpace removeSpace removeLine : String) :
    String × Array FormatError :=
  if M.trim.isEmpty then (rebuilt ++ L, as) else
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
  if L.take 3 == "/--" && M.take 3 == "/--" then
    parallelScanAux as (rebuilt ++ "/--") (L.drop 3) (M.drop 3) addSpace removeSpace removeLine else
  if L.take 2 == "--" then
    let newL := L.dropWhile (· != '\n')
    let diff := L.length - newL.length
    -- Assumption: if `L` contains an embedded inline comment, so does `M`
    -- (modulo additional whitespace).
    -- This holds because we call this function with `M` being a pretty-printed version of `L`.
    -- If the pretty-printer changes in the future, this code may need to be adjusted.
    let newM := M.dropWhile (· != '-') |>.drop diff
    parallelScanAux as (rebuilt ++ L.takeWhile (· != '\n') ++ newL.takeWhile (·.isWhitespace)) newL.trimLeft newM.trimLeft addSpace removeSpace removeLine else
  if L.take 2 == "-/" then
    let newL := L.drop 2 |>.trimLeft
    let newM := M.drop 2 |>.trimLeft
    parallelScanAux as (rebuilt ++ "-/" ++ (L.drop 2).takeWhile (·.isWhitespace)) newL newM addSpace removeSpace removeLine else
  let ls := L.drop 1
  let ms := M.drop 1
  match L.get 0, M.get 0 with
  | ' ', m =>
    if m.isWhitespace then
      parallelScanAux as (rebuilt.push ' ') ls ms.trimLeft addSpace removeSpace removeLine
    else
      parallelScanAux (pushFormatError as (mkFormatError L M "extra space")) (rebuilt ++ removeSpace) ls M addSpace removeSpace removeLine
  | '\n', m =>
    if m.isWhitespace then
      parallelScanAux as (rebuilt ++ L.takeWhile (·.isWhitespace)) ls.trimLeft ms.trimLeft addSpace removeSpace removeLine
    else
      parallelScanAux (pushFormatError as (mkFormatError L M "remove line break")) (rebuilt ++ removeLine ++ ls.takeWhile (·.isWhitespace)) ls.trimLeft M addSpace removeSpace removeLine
  | l, m => -- `l` is not whitespace
    if l == m then
      parallelScanAux as (rebuilt.push l) ls ms addSpace removeSpace removeLine
    else
      if m.isWhitespace then
        parallelScanAux (pushFormatError as (mkFormatError L M "missing space")) ((rebuilt ++ addSpace).push ' ') L ms.trimLeft addSpace removeSpace removeLine
    else
      -- If this code is reached, then `L` and `M` differ by something other than whitespace.
      -- This should not happen in practice.
      (rebuilt, pushFormatError as (mkFormatError ls ms "Oh no! (Unreachable?)"))

@[inherit_doc parallelScanAux]
def parallelScan (src fmt : String) : Array FormatError :=
  let (_expected, formatErrors) := parallelScanAux ∅ "" src fmt "🐩" "🦤" "😹"
  --dbg_trace "src:\n{src}\nfmt:\n{fmt}\nexpected:\n{expected}\n---"
  formatErrors

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
  if stx.getSubstring?.map toString != some stx.regString then
    dbg_trace stx.regString
  if stx.find? (·.isOfKind ``runCmd) |>.isSome then
    return
  let comps := (← getMainModule).components
  if comps.contains `Tactic ||
     comps.contains `Util ||
     comps.contains `Lean ||
     comps.contains `Meta
  then
    return
  -- If a command does not start on the first column, emit a warning.
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
        liftCoreM <| PrettyPrinter.ppCategory `command stx
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

    let scan := parallelScan orig st

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

initialize addLinter commandStartLinter

end Style.CommandStart

end Mathlib.Linter
