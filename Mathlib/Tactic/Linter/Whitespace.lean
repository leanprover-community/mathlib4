/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public meta import Mathlib.Tactic.Linter.Header
import Lean.Parser.Syntax
import Init.Data.String.TakeDrop

/-!
# The `whitespace` linter

The `whitespace` linter emits a warning if
* either a command does not start at the beginning of a line;
* or the "hypotheses segment" of a declaration does not coincide with its pretty-printed version.
-/

meta section

open Lean Elab Command Linter

/--
Replaces line-breaks with `⏎`.
It also replaces the slash `/` in `/-` and `-/` with the U+29F8 Big Solidus Unicode Character `⧸`
so that the output of `#guard_msgs` does not accidentally comment everything that follows it.
-/
private def String.norm (s : String) : String :=
  ((s.replace "\n" "⏎").replace "/-" "⧸-").replace "-/" "-⧸"

namespace Mathlib.Linter

/--
The `whitespace` linter emits a warning if
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
public register_option linter.style.whitespace : Bool := {
  defValue := false
  descr := "enable the whitespace linter"
}

/-- Deprecated in favour of `linter.style.whitespace -/
@[deprecated linter.style.whitespace (since := "2026-01-07")]
public register_option linter.style.commandStart : Bool := {
  defValue := false
  descr := "deprecated: use the `linter.style.whitespace` option instead"
}

/-- If the `linter.style.whitespace.verbose` option is `true`, the `whitespace` linter
reports some helpful diagnostic information. -/
public register_option linter.style.whitespace.verbose : Bool := {
  defValue := false
  descr := "report diagnostics about the whitespace linter"
}

/-- Extract the `leading` and the `trailing` substring of a `SourceInfo`. -/
def _root_.Lean.SourceInfo.getLeadTrail : SourceInfo → String × String
  | .original lead _ trail _ => (lead.toString, trail.toString)
  | _ => default

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
  " ".intercalate <| (s.splitToList (·.isWhitespace)).filter (!·.isEmpty)

/-- Converts the input syntax into a string using the pretty-printer and then collapsing
consecuting whitespace into a single space. -/
def pretty (stx : Syntax) : CommandElabM (Option String) := do
  let fmt : Option Format := ←
      try
        liftCoreM <| ppCategory' `command stx
      catch _ =>
        Linter.logLintIf linter.style.whitespace.verbose (stx.getHead?.getD stx)
          m!"The `whitespace` linter had some parsing issues: \
            feel free to silence it and report this error!"
        return none
  if let some fmt := fmt then
    let st := fmt.pretty (width := 100000)
    return reduceWhitespace st
  else
    return none

/--
`getChoiceNode kind args n` is a convenience function for handling `choice` nodes in syntax trees.

* If `kind` is not `choice`, then it returns `args`.
* If `kind` is `choice`, then it returns the array containing only the `n`-th entry of `args`,
  or `#[]` if `args` has fewer than `n` entries.

The argument `n` is optional and equals `0` by default.

The reason for this function is that we traverse the syntax tree to regenerate the expected
string.
If we traversed all of `choice`s children, we would regenerate duplicate parts of the syntax.
For this reason, we make a default choice of which single child to follow.
-/
def getChoiceNode (kind : SyntaxNodeKind) (args : Array Syntax) (n : Nat := 0) : Array Syntax :=
  if kind == `choice then #[args[n]?].reduceOption else args

/-- Replaces the leading and trailing substrings in a `SourceInfo` with `"".toSubstring`. -/
def _root_.Lean.SourceInfo.removeSpaces : SourceInfo → SourceInfo
  | .original _ p _ q => .original "".toRawSubstring p "".toRawSubstring q
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

/-- Answers whether a `Substring` starts with a space (` `), contains possibly more spaces,
until there is either `/ -` (without the space between `/` and `-`) or `--`. -/
def onlineComment (s : Substring.Raw) : Bool :=
  (s.take 1).toString == " " &&
    #[ "/-", "--"].contains ((s.dropWhile (· == ' ')).take 2).toString

/--
Convert a single-character subscript string into the corresponding normal single-character string.
-/
def unSubscript : String → String
  | "₀" => "0"
  | "₁" => "1"
  | "₂" => "2"
  | "₃" => "3"
  | "₄" => "4"
  | "₅" => "5"
  | "₆" => "6"
  | "₇" => "7"
  | "₈" => "8"
  | "₉" => "9"
  | "₊" => "+"
  | "ₙ" => "n"
  | "ₘ" => "m"
  | s => s

/--
Convert a single-character superscript string into the corresponding normal single-character string.
-/
def unSuperscript : String → String
  | "⁰" => "0"
  | "¹" => "1"
  | "²" => "2"
  | "³" => "3"
  | "⁴" => "4"
  | "⁵" => "5"
  | "⁶" => "6"
  | "⁷" => "7"
  | "⁸" => "8"
  | "⁹" => "9"
  | "⁺" => "+"
  | "ⁿ" => "n"
  | "ᵐ" => "m"
  | s => s

/--
Compares the two substrings `s` and `t`, with the expectation that `t` starts with `s`,
up to whitespace and guillemets (`«` and `»`).

It returns the substring of `t` that starts from the first position where it differs from `s`,
after it erased potential whitespace, taking care of preserving the last whitespace, if present.

The typical application is when `s` is the value of an atom/identifier leaf in `Syntax` and
`t` is the pretty-printed version of the whole syntax tree.
The main goal is to figure out what is the trailing whitespace substring
(usually either empty `""` or a single space `" "`).
-/
partial
def readWhile (s t : Substring.Raw) : Substring.Raw :=
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
    if #["«", "»"].contains t1.toString then
      readWhile s (t.drop 1)
    else
    if #["«", "»"].contains s1.toString then
      readWhile (s.drop 1) t
    else
    if unSubscript t1.toString == s1.toString then
      let tdrop := if unSubscript ((t.drop 2).take 1).toString == ((t.drop 2).take 1).toString then
        t.drop 1
      else
        t.drop 2
      readWhile (s.drop 1) tdrop
    else if unSuperscript t1.toString == s1.toString then
      let tdrop := if unSuperscript ((t.drop 2).take 1).toString == ((t.drop 2).take 1).toString then
        t.drop 1
      else
        t.drop 2
      readWhile (s.drop 1) tdrop
    else
      t

#eval show Lean.Elab.Term.TermElabM _ from do
  let s := "/- alsdkj la l    asklj  ew ljr  wer-/".toRawSubstring
  let t := "/- alsdkj la l asklj ew ljr    wer-/ theorem".toRawSubstring
  guard <| (readWhile s t).toString == " theorem"
  let t := "/- alsdkj la l asklj ew ljr    wer-/theorem".toRawSubstring
  guard <| (readWhile s t).toString == "theorem"

#eval show Lean.Elab.Term.TermElabM _ from do
  let s := "example".toRawSubstring
  let t := "example := 0".toRawSubstring
  guard <| (readWhile s t).toString == " := 0"
  let t := ":= 0".toRawSubstring
  guard <| (readWhile (" :=".toRawSubstring) t).toString == " 0"
  guard <| (readWhile (" := ".toRawSubstring) t).toString == "0"

structure mex where
  rg : Lean.Syntax.Range
  error : String
  kinds : Array SyntaxNodeKind

def mex.toString {m} [Monad m] [MonadFileMap m] (ex : mex) : m String := do
  let fm ← getFileMap
  return s!"{ex.error} {(fm.toPosition ex.rg.start, fm.toPosition ex.rg.stop)} ({ex.kinds})"

/--
A structure combining the various exceptions to the `whitespace` linter.
* `kinds` is the array of `SyntaxNodeKind`s that are ignored by the `whitespace` linter.
* `depth` represents how many `SyntaxNodeKind`s the `whitespace` linter climbs, in search of an
  exception.

  A depth of `none`, means that the linter ignores nodes starting with the given `SyntaxNodeKind`
  and any sub-node.

  A depth of `some n` means that the linter will only ignore the first `n` `SyntaxNodeKind`s
  starting from the given `SyntaxNodeKind` and resumes checking for all deeper nodes.
-/
structure ExcludedSyntaxNodeKind where
  /-- `kinds` is the array of `SyntaxNodeKind`s that are ignored by the `whitespace` linter. -/
  kinds : Array SyntaxNodeKind
  /--
  `depth` represents how many `SyntaxNodeKind`s the `whitespace` linter climbs, in search of an
  exception.

  A depth of `none`, means that the linter ignores nodes starting with the given `SyntaxNodeKind`
  and any sub-node.

  A depth of `some n` means that the linter will only ignore the first `n` `SyntaxNodeKind`s
  starting from the given `SyntaxNodeKind` and resumes checking for all deeper nodes.
  -/
  depth : Option Nat

/--
`unparseable` are the `SyntaxNodeKind`s that block the `whitespace` linter: their appearance
anywhere in the syntax tree makes the linter ignore the whole command.

This is the reason their `depth` is `none`.
-/
def unparseable : ExcludedSyntaxNodeKind where
  kinds := #[
    ``Parser.Command.macro_rules,
    ``runCmd,
    ``Parser.Command.meta,
  ]
  depth := none

/--
These are the `SyntaxNodeKind`s for which we want to ignore the pretty-printer.

Deeper nodes are *not* inspected.
-/
def totalExclusions : ExcludedSyntaxNodeKind where
  kinds := #[
    -- Each entry prevents the formatting of...
    ``Parser.Command.docComment, -- of doc-strings.
    ``Parser.Command.moduleDoc, -- of module docs.
    ``«term{_:_//_}», -- of `{a // ...}`.
    ``«term{_}», -- of a singleton `{a}`.
    ``«term{}»,  -- of the empty set, the pretty-printer prefers `{ }`
    `Mathlib.Meta.setBuilder, -- of `{a | ...}`.
    ``Parser.Tactic.tacticSeqBracketed, -- of `{ tactics }`.
    ``Parser.Command.macro, -- of `macro`.
    ``Parser.Command.elab, -- of `elab`.
    ``Parser.Command.elab_rules, -- of `elab_rules`.
    `Mathlib.Meta.«term{_|_}», -- of `{ f x y | (x : X) (y : Y) }`.
    ``«term[_]», -- of lists.
    ``«term#[_,]», -- of arrays.
    ``Parser.Term.anonymousCtor, -- of `⟨...⟩`.
    ``Parser.Command.syntax, -- of `syntax ...`.
    `Aesop.Frontend.Parser.declareRuleSets, -- of `declare_aesop_rule_sets`.
    `Aesop.Frontend.Parser.featIdent, -- of `attribute [aesop safe (rule_sets := [CategoryTheory])] Subsingleton.elim`
    ``«term_::_», -- of lists.
    `Stream'.«term_::_», -- of `Stream'` notation, analogous to lists.
    `Batteries.Util.LibraryNote.commandLibrary_note___, -- of `library_note "Title"/-- Text -/`.
    `Mathlib.Notation3.notation3, -- of `notation3`.
    ``Parser.Term.structInstField, -- of the `where` fields: the LHS pps with virtually no spaces.
    ``Parser.Term.structInst, -- of the `where` fields: the LHS pps with virtually no spaces.
    `Lean.Parser.Command.grindPattern, -- `grind_pattern A => x, y` prints no space after `,`,
    -- Unification hints currently pretty-print without a space after the ⊢ (lean4#11780)
    ``Lean.«command__Unif_hint____Where_|_-⊢_»,
    -- logical negation, the pretty-printer prefers `¬a` (while the correct style is not as obvious)
    ``«term¬_»,
  ]
  depth := none

def ignoreSpaceAfter : ExcludedSyntaxNodeKind where
  kinds := #[
    ``«term¬_»,
    -- notation for `upShadow`, the pretty-printer prefers `∂⁺ ` over `∂⁺` *always*
    `FinsetFamily.«term∂⁺»,
    `Mathlib.Tactic.superscriptTerm, `Mathlib.Tactic.subscript,
    -- negation, the pretty-printer prefers `-b` in every case (even for expressions `-b + a`)
    ``«term-_»,
    -- subtraction, the pretty-printer prefers `a-b` in every case
    ``«term_-_»,
    -- the `suffices` tactic; the pretty-printer does not take line length into account
    ``Lean.Parser.Term.suffices,
  ]
  depth := some 2

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
    ``Parser.Term.whereDecls, -- `where`
  ]
  depth := some 2

def forceSpaceAfter' : ExcludedSyntaxNodeKind where
  kinds := #[
    `atom.«have», -- `have (a)` in term mode.
    `atom.«let», -- `let (a)` in term mode.
  ]
  depth := some 1

def forceSpaceAfter'' : ExcludedSyntaxNodeKind where
  kinds := #[
    `Bundle.termπ__,
  ]
  depth := some 3

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

--def filterSortExceptions (as : Array mex) : Array mex :=
--  let filtered := as.filter fun a =>
--    (!totalExclusions.contains a.kinds) && (!ignoreSpaceAfter.contains a.kinds)
--  filtered.qsort (·.rg.start < ·.rg.start)

structure PPref where
  pos : String.Pos.Raw
  ok : Bool
  bracket : Option String.Pos.Raw := none
  kinds : Array SyntaxNodeKind
  deriving Inhabited

/-- A mapping from each start/ending position of each atom in the string generating the original
syntax with the corresponding start/ending position in the pretty-printed string generated by
stripping all comments and whitespace. -/
abbrev Correspondence := Std.HashMap String.Pos.Raw PPref

def atomOrIdentEndPos {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (verbose? : Bool) (k : Array SyntaxNodeKind) (orig pp : Substring.Raw) :
    m String.Pos.Raw := do
  let ppDropOrig := readWhile orig pp
  if verbose? then
    if ppDropOrig == pp && (!ppDropOrig.isEmpty) then
      -- Temporary change, to reduce warning spam.
      if !(k.contains `hygieneInfo && !k.contains `choice) && False then
        logWarning m!"No change at{indentD m!"'{ppDropOrig}'"}\n{k.map MessageData.ofConstName}\n\n\
        Maybe because the `SyntaxNodeKind`s contain:\n\
        hygieneInfo: {k.contains `hygieneInfo}\n\
        choice: {k.contains `choice}"
  --dbg_trace "ppDropOrig[{ppDropOrig.startPos}]: '{ppDropOrig.toString.norm}'"
  pure ppDropOrig.startPos

partial
def generateCorrespondence {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (verbose? : Bool) :
    Correspondence → Array SyntaxNodeKind → Syntax → Substring.Raw → m (Substring.Raw × Correspondence)
  | corr, k, .ident info rawVal _val _pre, str => do
    --dbg_trace "kinds:\n{k}"
    --dbg_trace "rawVal: '{rawVal}'"
    let ppEndPos ← atomOrIdentEndPos verbose? (k.push (.str `ident rawVal.toString)) rawVal str
    let (_, tail) := info.getLeadTrail
    --dbg_trace "(tail: '{tail.norm}', (tail[0], str[{ppEndPos}]) ('{(tail.take 1).norm}' '{(str.get ppEndPos)}'))\n({str.startPos}, {str.stopPos})\n"
    let cond := tail.take 1 == (str.take 1).toString
    pure (
      {str with startPos := ppEndPos},
      -- Is `getD default` a good idea?  It resolves some panics, but there may be a better default
      corr.alter ((info.getTrailing?.getD default).startPos) fun a => if (a.getD default).bracket.isSome then a else PPref.mk ppEndPos cond none (k.push (.str `ident rawVal.toString)))
  | corr, k, .atom info val, str => do
    --dbg_trace "kinds:\n{k}"
    --dbg_trace "val: '{val}'"
    let ppEndPos ← atomOrIdentEndPos verbose? (k.push (.str `atom val)) val.toRawSubstring str
    let (_, tail) := info.getLeadTrail
    --dbg_trace "(tail: '{tail.norm}', (tail[0], str[{ppEndPos}]) ('{(tail.take 1).norm}' '{(str.get ppEndPos)}'))\n"
    let cond := tail.take 1 == "".push (str.get ppEndPos)
    pure (
      {str with startPos := ppEndPos},
      -- Is `getD default` a good idea?  It resolves some panics, but there may be a better default
      corr.alter ((info.getTrailing?.getD default).startPos) fun a => if (a.getD default).bracket.isSome then a else PPref.mk ppEndPos cond none (k.push (.str `atom val)))
  | corr, k, _stx@(.node _info kind args), str => do
    --let corr :=
    --  if (k.back?.getD .anonymous) == ``Parser.Term.structInst then
    --    --dbg_trace "inserting {stx} {(stx.getRange?.map fun | {start := a, stop := b} => (a, b))}\n"
    --    corr
    --    --corr.insert stx.getTailPos?.get! <| PPref.mk stx.getPos?.get! true (some stx.getPos?.get!)
    --  else
    --    --dbg_trace "not inserting\n"
    --    corr
    (getChoiceNode kind args).foldlM (init := (str, corr)) fun (str, corr) arg => do
      generateCorrespondence verbose? corr (k.push kind) arg str
  | corr, _, _stx, str => do
    pure (str, corr)

partial
def _root_.String.Slice.mkGroups (s : String.Slice) (n : Nat) : List String.Slice :=
  if n == 0 || s.positions.count ≤ n then [s] else
  s.take n :: (s.drop n).mkGroups n

-- TODO: fix this and re-enable it!
-- def byTens (s : String) (n : Nat := 9) : String.Slice :=
--   "\n".intercalate <| ("".intercalate <| (List.range n).map (fun n => s!"{(n + 1) % 10}")) :: (s.toSlice.mkGroups n)

def mkRangeError (ks : Array SyntaxNodeKind) (orig pp : Substring.Raw) :
    Option (Lean.Syntax.Range × MessageData × String) := Id.run do
  let origWs := orig.takeWhile (·.isWhitespace)
  --dbg_trace "here for '{(orig.take 10).toString}'\n{ks}\n"
  --dbg_trace ks
  if forceSpaceAfter.contains ks || forceSpaceAfter'.contains ks || forceSpaceAfter''.contains ks then
    --dbg_trace "forceSpaceAfter"
    let space := if (pp.take 1).trim.isEmpty then "" else " "
    if origWs.isEmpty then
      return some (⟨origWs.startPos, origWs.next origWs.startPos⟩, "add space in the source", space)
    else
    if origWs.toString.length == 1 || (orig.take 1).toString == "\n" then
      return none
    else
      let origWsNext := origWs.drop 1
      return some (⟨origWsNext.startPos, origWsNext.stopPos⟩, "remove space in the source", space)
  else if forceNoSpaceAfter.contains ks then
    --dbg_trace "forceNoSpaceAfter"
    if !origWs.isEmpty then
      return some (⟨origWs.startPos, origWs.stopPos⟩, "remove space in the source", "")
    else
      return none
  else
  let ppNext := pp.take 1
  -- The next pp-character is a space
  if ppNext.trim.isEmpty then
    --dbg_trace "next is whitespace"
    if onlineComment orig then
      return none
    if origWs.isEmpty then
      return some (⟨orig.startPos, orig.next orig.startPos⟩, "add space in the source", "")
    let origWsNext := origWs.drop 1
    let pastSpaces := origWs.dropWhile (· == ' ')
    if (origWs.take 1).toString == " " && (pastSpaces.take 1).toString == "\n" then
      return some (⟨origWs.startPos, pastSpaces.stopPos⟩, "Please remove spaces before line breaks", "")
    else
      if (origWs.take 1).toString != "\n" && (!origWsNext.isEmpty) then
        return some (⟨origWsNext.startPos, origWsNext.stopPos⟩, "remove space in the source", "")
  -- The next pp-character is not a space
  if !ppNext.trim.isEmpty then
    --dbg_trace "next is not whitespace"
    if !origWs.isEmpty then
      let wsName := if (origWs.take 1).toString == " " then "space" else "line break"
      let s := if origWs.toString.length == 1 || (origWs.take 1).toString == "\n" then "" else "s"
      return some (⟨origWs.startPos, origWs.stopPos⟩, m!"remove {wsName}{s} in the source", "")
  return none

/-- Assumes that the `startPos` of the string is where the "center" of the window will be. -/
def mkWdw (s : Substring.Raw) (mid : String := "") : String :=
  let p := s.startPos
  let fromStart := {s with startPos := 0, stopPos := p}
  let toEnd := {s with startPos := p, stopPos := s.str.rawEndPos}
  let leftWhitespaceAndWord := fromStart.trimRight.dropRightWhile (!·.isWhitespace)
  let rightWhitespaceAndWord := toEnd.trimLeft.dropWhile (!·.isWhitespace)
  s!"\
    {{s with startPos := leftWhitespaceAndWord.stopPos, stopPos := p}}\
    {mid}\
    {{s with startPos := p, stopPos := rightWhitespaceAndWord.startPos}}".trimAscii.toString.norm

/-
This part of the code\n  '{origWindow.trim}'\n\
should be written as\n  '{expectedWindow}'\n"
-/

namespace Style.Whitespace

/--
We think of `orig` as `orig = ...<wordLeft><whitespaceLeft>|<whitespaceRight><wordRight>...`
where
* `<wordLeft>`  and `<wordLeft>` are maximal consecutive sequences of non-whitespace characters,
* `<whitespaceLeft>` and `<whitespaceRight>` are maximal consecutive sequences of whitespace
  characters,
* the `|` denotes the input position `start`.

We carve out the substring `<wordLeft><whitespaceLeft><whitespaceRight><wordRight>`.
-/
def mkWindowSubstring' (orig : Substring.Raw) (start : String.Pos.Raw) : String :=
  -- Starting from the first discrepancy, we move to the right, consuming all subsequent
  -- contiguous whitespace and then all subsequent contiguous non-whitespace.
  let fromError : Substring.Raw := {orig with startPos := start}
  let extRight := fromError.dropWhile (·.isWhitespace) |>.dropWhile (!·.isWhitespace)
  -- Ending at the first discrepancy, we move to the left, consuming all previous
  -- contiguous whitespace and then all previous contiguous non-whitespace.
  let toError : Substring.Raw := {orig with stopPos := start}
  let extLeft := toError.dropRightWhile (·.isWhitespace) |>.dropRightWhile (!·.isWhitespace)
  -- Carve the substring using the starting and ending positions determined above.
  {orig with startPos := extLeft.stopPos, stopPos := extRight.startPos}.toString

def mkExpectedWindow (orig : Substring.Raw) (start : String.Pos.Raw) : String :=
  -- Ending at the first discrepancy, we move to the left, consuming all previous
  -- contiguous whitespace and then all previous contiguous non-whitespace.
  let toError : Substring.Raw := {orig with stopPos := start}
  let extLeft := toError.dropRightWhile (·.isWhitespace) |>.dropRightWhile (!·.isWhitespace)

  -- Starting from the first discrepancy, we move to the right, consuming all subsequent
  -- contiguous whitespace and then all subsequent contiguous non-whitespace.
  let fromError : Substring.Raw := {orig with startPos := start}
  let first := fromError.take 1
  let afterWhitespace := fromError.dropWhile (·.isWhitespace) |>.takeWhile (!·.isWhitespace)
  --dbg_trace "first: '{first}'"
  --dbg_trace "afterWhitespace: '{afterWhitespace}'"
  if first.trim.isEmpty then
    -- Case 1: `first` consists of whitespace, so we discard all consecutive whitespace and
    -- keep the following non-whitespace block.
    {orig with startPos := extLeft.stopPos, stopPos := start}.toString ++ afterWhitespace.toString
  else
    -- Case 2: `first` is not whitespace, so we simply add a space and then the
    -- following non-whitespace block.
    {orig with startPos := extLeft.stopPos, stopPos := start}.toString ++ " " ++
      {afterWhitespace with startPos := start}.toString

#guard mkExpectedWindow "0123 abcdef    \n ghi".toRawSubstring ⟨8⟩ == "abc def"

#guard mkExpectedWindow "0123 abc    \n def ghi".toRawSubstring ⟨9⟩ == "abc def"

def _root_.Mathlib.Linter.mex.toLinterWarning (m : mex) (orig : Substring.Raw) : MessageData :=
  let origWindow := mkWindowSubstring' orig m.rg.start
  let expectedWindow := mkExpectedWindow orig m.rg.start
  m!"{m.error} in the source\n\n\
  This part of the code\n  '{origWindow.trimAscii}'\n\
  should be written as\n  '{expectedWindow}'\n"

@[inherit_doc Mathlib.Linter.linter.style.whitespace]
def whitespaceLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.style.whitespace (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  -- If the file is mostly a "meta" file, then do not lint.  The heuristic for this is to look
  -- at the name of the module.
  let comps : ExcludedSyntaxNodeKind := .mk (← getMainModule).components.toArray none
  if comps.contains #[`Tactic, `Util, `Lean, `Meta] then
    return
  -- Skip `eoi` and `#exit`.
  if Parser.isTerminalCommand stx then return
  -- Some `SyntaxNodeKind`s are prone to produce incorrect pretty-printed text, so we skip
  -- commands that contain them.
  if stx.find? (unparseable.contains #[·.getKind]) |>.isSome then
    return
  -- If a command does not start on the first column, emit a warning.
  --dbg_trace "lint1"
  let orig := stx.getSubstring?.getD default

  let stxNoSpaces := stx.eraseLeadTrailSpaces
  if let some pretty := ← Mathlib.Linter.pretty stxNoSpaces then
    let pp := pretty.toRawSubstring
    let (_, corr) ← generateCorrespondence true Std.HashMap.emptyWithCapacity #[] stx pretty.toRawSubstring
    let (reported, excluded) := corr.partition fun _ {kinds := ks,..} =>
      (!totalExclusions.contains ks && !ignoreSpaceAfter.contains ks)
    let fm ← getFileMap
    -- Sort by position to stabilize output.
    let reported := reported.toArray.qsort (·.1 < ·.1)
    -- Counts the number of times that a `Bundle.termπ__` potential exception appears and
    -- ignores each third one: in `π a b`, spaces after `b` are ignored.
    let mut con : Nat := 0
    for (origPos, ppR) in reported do
      let ppPos := ppR.pos
      let origAtPos := {orig with startPos := origPos}
      let ppAtPos := {pp with startPos := ppPos}
      -- Check for `Bundle.termπ__` at the correct depth, increase the counter and skip, as needed
      if (ppR.kinds.drop (ppR.kinds.size - 3)).contains `Bundle.termπ__ then
        con := con + 1
        if con % 3 == 0 then continue
      if let some (rg, msg, mid) := mkRangeError ppR.kinds origAtPos ppAtPos then
        -- TODO: temporary change, hopefully reduces no-op warning spew
        if mkWdw origAtPos != mkWdw ppAtPos mid then
          Linter.logLint linter.style.whitespace (.ofRange rg)
            m!"{msg}\n\n\
            This part of the code\n  '{mkWdw origAtPos}'\n\
            should be written as\n  '{mkWdw ppAtPos mid}'\n"

    for (origPos, ppR) in excluded.filter (fun _ _ => false) do
      let ppPos := ppR.pos
      let origAtPos := {orig with startPos := origPos}
      let ppAtPos := {pp with startPos := ppPos}
      if let some (rg, msg, mid) := mkRangeError ppR.kinds origAtPos ppAtPos then
        -- TODO: temporary change, hopefully reduces no-op warning spew
        if mkWdw origAtPos != mkWdw ppAtPos mid then
          logInfoAt (.ofRange rg)
            m!"{msg}\n\n\
            This part of the code\n  '{mkWdw origAtPos}'\n\
            should be written as\n  '{mkWdw ppAtPos mid}'\n\n{ppR.kinds}\n"

initialize addLinter whitespaceLinter

open Lean Elab Command in
/-- Show correlations between string positions and syntax nodes
in a command `cmd`. This logic is the backbone of how the linter matches the input string with the
pretty printed one.

This function is not used for the actual linter, but kept for debugging odd linter behaviour. -/
elab "#show_corr " cmd:command : command => do
  elabCommand cmd
  let orig := cmd.raw.getSubstring?.getD default
  let stxNoSpaces := cmd.raw.eraseLeadTrailSpaces
  if let some pretty := ← Mathlib.Linter.pretty stxNoSpaces then
    let pp := pretty.toRawSubstring
    let (_, corr) ← generateCorrespondence true Std.HashMap.emptyWithCapacity #[] cmd pretty.toRawSubstring
    for (origPos, ppR) in corr do
      let ppPos := ppR.pos
      let origAtPos := {orig with startPos := origPos}
      let ppAtPos := {pp with startPos := ppPos}
      if let some (rg, msg) := mkRangeError ppR.kinds origAtPos ppAtPos then
        -- TODO: temporary change, hopefully reduces false positives!
        if mkWdw origAtPos != mkWdw ppAtPos then
          logWarningAt (.ofRange rg)
            m!"{msg}\n\
            This part of the code\n  '{mkWdw origAtPos}'\n\
            should be written as\n  '{indentD <| mkWdw ppAtPos}'\n"
    let fm ← getFileMap
    let sorted := corr.toArray.qsort (·.1 < ·.1)
    let mut msgs := #[]
    for (a, b) in sorted do
      msgs := msgs.push (
        {fm.toPosition a with column := (fm.toPosition a).column + 1},
          b.pos,
          "'".push (pretty.toRawSubstring.get (pretty.toRawSubstring.prev b.pos))
            |>.push (pretty.toRawSubstring.get b.pos)
            |>.push (pretty.toRawSubstring.get (pretty.toRawSubstring.next b.pos))
            |>.push '\'',
          b.ok,
          b.bracket,
        )
    -- TODO: fix `byTens` and re-enable this logging output
    --logInfo <| .joinSep (msgs.toList.map (m!"{·}") ++ [m!"{byTens pretty (min pretty.length 100)}"]) "\n"
  else logWarning "Error"

-- #show_corr
-- --inspect
-- #check (  { default := (/-  -/) }:    Inhabited   Unit
-- )

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
  else if ictx.atEnd s.pos then
    .ok s.stxStack.back
  else
    .error ((s.mkError "end of input").toErrorMsg ictx)

structure AfterAtom where
  /-- `next` is either `" ".toSubstring` or `"".toSubstring`, depending on whether the
  character following the current identifier/atom is required to be followed by a space or not. -/
  next : Substring.Raw
  /-- `read` is the pretty-printed substring, starting from after the current identifier/atom,
  dropping also eventual leading whitespace. -/
  strNew : Substring.Raw

structure PPinstruction where
  pos : String.Pos.Raw
  after : Bool := true
  space : Bool := true
  deriving Inhabited

def processAtomOrIdent {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (verbose? : Bool) (k : Array SyntaxNodeKind) (val str : Substring.Raw) :
    m (AfterAtom × PPinstruction) := do
  --dbg_trace "forceSpaceAfter.contains {k}: {forceSpaceAfter.contains k}\nStarting with '{val}'\n"
  let read := readWhile val str
  if verbose? then
    if read == str && (!read.isEmpty) then
      logWarning m!"No change at{indentD m!"'{read}'"}\n{k.map MessageData.ofConstName}\n\n\
      Maybe because the `SyntaxNodeKind`s contain:\n\
      hygieneInfo: {k.contains `hygieneInfo}\n\
      choice: {k.contains `choice}"
  let (next, strNew, ppInstr) :=
    -- Case `read = " "`
    if (read.take 1).toString == " "
    then
      -- Case `read = " "` but we do not want a space after
      if forceNoSpaceAfter.contains k then
        ("".toRawSubstring, read.drop 1, {pos := (read.drop 1).startPos, space := false})
      else
        (" ".toRawSubstring, read.drop 1, {pos := (read.drop 1).startPos})
    else
    -- Case `read = ""` but we want a space after anyway
    if forceSpaceAfter.contains k || forceSpaceAfter'.contains k then
      --dbg_trace "adding a space at '{read}'\n"
      (" ".toRawSubstring, read, {pos := read.startPos})
    -- Case `read = ""` and we follow the pretty-printer recommendation
    else
      ("".toRawSubstring, read, {pos := read.startPos, space := false})
  pure (AfterAtom.mk next strNew, ppInstr)

def modifyTail (si : SourceInfo) (newTrail : Substring.Raw) : SourceInfo :=
  match si with
  | .original lead pos _ endPos => .original lead pos newTrail endPos
  | _ => si

/--
`insertSpacesAux verbose? noSpaceStx prettyString`
scans the syntax tree `noSpaceStx` and, whenever it finds an `atom` or `ident` node,
it compares it with the substring `prettyString`, consuming the value of the `atom`/`ident` and
appending the following whitespace as trailing substring in the `SourceInfo`, if such a space is
present.

This essentially converts `noSpaceStx` into a `Syntax` tree whose traversal reconstructs exactly
`prettyString`.
-/
partial
def insertSpacesAux {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (verbose? : Bool) :
    Array SyntaxNodeKind → Syntax → Substring.Raw → m (Syntax × Substring.Raw)
  | k, .ident info rawVal val pre, str => do
    let (⟨next, strNew⟩, _) ← processAtomOrIdent verbose? (k.push (.str `ident rawVal.toString)) rawVal str
    if false then
      dbg_trace
        s!"* ident '{rawVal}'\nStr: '{str}'\nNxt: '{next}'\nNew: '{strNew}'\n"
    pure (.ident (modifyTail info next) rawVal val pre, strNew)
  | k, .atom info val, str => do
    let (⟨next, strNew⟩, _) ← processAtomOrIdent verbose? (k.push (.str `atom val)) val.toRawSubstring str
    if false then
      dbg_trace
        s!"* atom '{val}'\nStr: '{str}'\nNxt: '{next}'\nNew: '{strNew}'\n"
    pure (.atom (modifyTail info next) val, strNew)
  | k, .node info kind args, str => do
    --let kind := if kind == `null then k else kind
    let mut str' := str
    let mut stxs := #[]
    for arg in getChoiceNode kind args do
      let (newStx, strNew) ← insertSpacesAux verbose? (k.push kind) arg str'
      if false then
        logInfo m!"'{strNew}' intermediate string at {k.push kind}"
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
    let withSpaces ← insertSpacesAux verbose? #[stx.getKind] stx pretty.toRawSubstring
    return withSpaces.1
  else return none

def _root_.Substring.Raw.toRange (s : Substring.Raw) : Lean.Syntax.Range where
  start := s.startPos
  stop := s.stopPos

def allowedTrail (ks : Array SyntaxNodeKind) (orig pp : Substring.Raw) : Option mex :=
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
      let misformat : Substring.Raw := {orig with stopPos := orig.stopPos.increaseBy 1}
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
    let (a1, a2) := (getChoiceNode kind a1, getChoiceNode kind a2)
    a1.zipWith (fun a b => a.compareSpaces (kinds.push kind) tot b) a2 |>.flatten
  | kinds, tot, .ident origInfo rawVal .., .ident ppInfo .. =>
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

/-- Returning `none` denotes a processing error. -/
def getExceptions (stx : Syntax) (verbose? : Bool := false) :
    CommandElabM (Option (Array mex)) := do
  let stxNoTrail := stx.unsetTrailing
  let s ← get
  let insertSpace ← insertSpaces verbose? stx
  set s
  if let some stxNoSpaces := insertSpace then
    if verbose? then
      logInfo m!"Pretty-printed syntax:\n{stxNoSpaces}"
    return stxNoTrail.compareSpaces #[] #[] stxNoSpaces
  else
    return none


/-- If `s` is a `Substring` and `p` is a `String.Pos`, then `s.break p` is the pair consisting of
the `Substring` `s` ending at `p` and of the `Substring` `s` starting from `p`. -/
def _root_.Substring.Raw.break (s : Substring.Raw) (p : String.Pos.Raw) : Substring.Raw × Substring.Raw :=
  ({s with stopPos := p}, {s with startPos := p})

/--
Assume that `ms` is a sorted array of `String.Pos` that are within the `startPos` and the `stopPos`
of `orig`.
Successively `break` `orig` at all the positions in `ms`.
For each piece thus created, except for the very first one, check if it starts with whitespace.
Only if it does, wedge a `" ".toSubstring` between this piece and the previous one.
In all cases, drop all leading whitespace from the pieces.

Return the concatenation of the possibly-trimmed-pieces with the appropriate `" ".toSubstring`
separators.

The intuition is that the positions listed in `ms` correspond to places where there is a
discrepancy between an expected boundary between words and the actual string.
The expectation is that up to the current position, everything is well-formatted and, if a space
was available, then it has been used. The convention is that no more than one consecutive space
is used to separate words at the positions in `ms`.

Thus, if a position in `ms` falls where the following character is not a space, then a space should
be added before that word.  Hence, the script adds a `" ".toSubstring`.

If, instead, there is a space after a position in `ms`, then it, and all the following streak of
whitespace, is redundant and gets trimmed.
-/
def mkStrings (orig : Substring.Raw) (ms : Array String.Pos.Raw) : Array Substring.Raw :=
  let (tot, orig) := ms.foldl (init := (#[], orig)) fun (tot, orig) pos =>
    let (start, follow) := orig.break pos
    let newTot := tot.push start ++ if (follow.take 1).trim.isEmpty then #[] else #[" ".toRawSubstring]
    (newTot, follow.trimLeft)
  tot.push orig

def reportedAndUnreportedExceptions (as : Array mex) : Array mex × Array mex :=
  as.partition fun a =>
    (!totalExclusions.contains a.kinds) && (!ignoreSpaceAfter.contains a.kinds)

end Style.Whitespace

end Mathlib.Linter
