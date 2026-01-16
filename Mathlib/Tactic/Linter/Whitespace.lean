/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Tactic.Linter.Header  -- shake: keep
public import Mathlib.Util.Superscript
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
consecutive whitespace into a single space. -/
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

open Mathlib.Tactic.Superscript

/--
Convert a single-character subscript string into the corresponding normal single-character string.
-/
def unSubscript : String → String := fun s ↦
  if s.length == 1 then
    (unSubscript' s.front).toString
  else s

/--
Convert a single-character superscript string into the corresponding normal single-character string.
-/
def unSuperscript : String → String := fun s ↦
  if s.length == 1 then
    (unSuperscript' s.front).toString
  else s

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
  /-- `kinds` is the `NameSet` of `SyntaxNodeKind`s that are ignored by the `whitespace` linter. -/
  kinds : NameSet
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
  kinds := .ofArray #[
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
  kinds := .ofArray #[
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
    `Lean.Parser.Command.grindPattern, -- `grind_pattern A => x, y` prints no space after `,`,
    -- Unification hints currently pretty-print without a space after the ⊢ (lean4#11780)
    ``Lean.«command__Unif_hint____Where_|_-⊢_»,
    -- `inductive`s with docstrings for their constructors have undesirable printing
    ``Parser.Command.inductive,
    -- `name_poly_vars` asks for a space after the last variable name; fixing this is not obvious.
    `Mathlib.Tactic.namePolyVarsOver
  ]
  depth := none

def ignoreSpaceAfter : ExcludedSyntaxNodeKind where
  kinds := .ofArray #[
    ``«term¬_»,
    -- notation for `upShadow`, the pretty-printer prefers `∂⁺ ` over `∂⁺` *always*
    `FinsetFamily.«term∂⁺»,
    `Mathlib.Tactic.superscriptTerm, `Mathlib.Tactic.subscript,
    -- negation, the pretty-printer prefers `-b` in every case (even for expressions `-b + a`)
    ``«term-_»,
    -- subtraction, the pretty-printer prefers `a-b` in every case
    ``«term_-_»,
    -- logical negation, the pretty-printer prefers `¬a` (while the correct style is not as obvious)
    ``«term¬_»,
  ]
  depth := some 2

/--
`suffices` requires a higher depth, since it inserts a further `hygieneInfo` node into the syntax.
-/
-- TODO: this still ignores a bit too much, since also some spaces after `suffices` are ignored.
def ignoreSpaceAfter3 : ExcludedSyntaxNodeKind where
  kinds := .ofArray #[
    ``Parser.Term.sufficesDecl,
  ]
  depth := some 3

/--
These are the `SyntaxNodeKind`s for which the pretty-printer would likely not space out from the
following nodes, but we overrule it and place a space anyway.
-/
def forceSpaceAfter : ExcludedSyntaxNodeKind where
  kinds := .ofArray #[
    ``termThrowError__, -- `throwError "message"`
    ``Parser.Term.whereDecls, -- `where`
  ]
  depth := some 2

def forceSpaceAfter3 : ExcludedSyntaxNodeKind where
  kinds := .ofArray #[
    `Bundle.termπ__,
  ]
  depth := some 3

/--
These are the `SyntaxNodeKind`s for which the pretty-printer would likely space out from the
following nodes, but we overrule it and do not place a space.
-/
def forceNoSpaceAfter : ExcludedSyntaxNodeKind where
  kinds := .ofArray #[
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
  lastNodes.any exc.kinds.contains

structure PPref where
  pos : String.Pos.Raw
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
      -- TODO: this warns about every library note, which is too noisy: thus, disabled.
      if !(k.contains `hygieneInfo && !k.contains `choice) && False then
        logWarning m!"No change at{indentD m!"'{ppDropOrig}'"}\n{k.map MessageData.ofConstName}\n\n\
        Maybe because the `SyntaxNodeKind`s contain:\n\
        hygieneInfo: {k.contains `hygieneInfo}\n\
        choice: {k.contains `choice}"
  pure ppDropOrig.startPos

partial
def generateCorrespondence {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (verbose? : Bool) :
    Correspondence → Array SyntaxNodeKind → Syntax → Substring.Raw → m (Substring.Raw × Correspondence)
  | corr, k, .ident info rawVal _val _pre, str => do
    let ppEndPos ← atomOrIdentEndPos verbose? (k.push (.str `ident rawVal.toString)) rawVal str
    pure (
      {str with startPos := ppEndPos},
      -- Is `getD default` a good idea?  It resolves some panics, but there may be a better default
      corr.alter ((info.getTrailing?.getD default).startPos) fun _ =>
        PPref.mk ppEndPos (k.push (.str `ident rawVal.toString)))
  | corr, k, .atom info val, str => do
    let ppEndPos ← atomOrIdentEndPos verbose? (k.push (.str `atom val)) val.toRawSubstring str
    pure (
      {str with startPos := ppEndPos},
      -- Is `getD default` a good idea?  It resolves some panics, but there may be a better default
      corr.alter ((info.getTrailing?.getD default).startPos) fun _ =>
        PPref.mk ppEndPos (k.push (.str `atom val)))
  | corr, k, .node _info kind args, str => do
    (getChoiceNode kind args).foldlM (init := (str, corr)) fun (str, corr) arg => do
      generateCorrespondence verbose? corr (k.push kind) arg str
  | corr, _, _stx, str => do
    pure (str, corr)

partial
def _root_.String.Slice.mkGroups (s : String.Slice) (n : Nat) : List String :=
  if n == 0 || s.positions.count ≤ n then [s.toString] else
  (s.take n).toString :: (s.drop n).mkGroups n

-- TODO: fix this and re-enable it!
def byTens (s : String) (n : Nat := 9) : String :=
  "\n".intercalate <| ("".intercalate <| (List.range n).map (fun n => s!"{(n + 1) % 10}")) :: (s.toSlice.mkGroups n)

def mkRangeError (ks : Array SyntaxNodeKind) (orig pp : Substring.Raw) :
    Option (Lean.Syntax.Range × MessageData × String) := Id.run do
  let origWs := orig.takeWhile (·.isWhitespace)
  if forceSpaceAfter.contains ks || forceSpaceAfter3.contains ks then
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
    if !origWs.isEmpty then
      return some (⟨origWs.startPos, origWs.stopPos⟩, "remove space in the source", "")
    else
      return none
  else
  let ppNext := pp.take 1
  -- The next pp-character is a space
  if ppNext.trim.isEmpty then
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
  else
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

@[inherit_doc Mathlib.Linter.linter.style.whitespace]
def whitespaceLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.style.whitespace (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  -- If the file is mostly a "meta" file, then do not lint.  The heuristic for this is to look
  -- at the name of the module.
  let comps : ExcludedSyntaxNodeKind := .mk (.ofList (← getMainModule).components) none
  if comps.contains #[`Tactic, `Util, `Lean, `Meta] then
    return
  -- Skip `eoi` and `#exit`.
  if Parser.isTerminalCommand stx then return
  -- Some `SyntaxNodeKind`s are prone to produce incorrect pretty-printed text, so we skip
  -- commands that contain them.
  if stx.find? (unparseable.contains #[·.getKind]) |>.isSome then
    return
  -- If a command does not start on the first column, emit a warning.
  let orig := stx.getSubstring?.getD default

  let stxNoSpaces := stx.eraseLeadTrailSpaces
  if let some pretty := ← Mathlib.Linter.pretty stxNoSpaces then
    let pp := pretty.toRawSubstring
    let (_, corr) ← generateCorrespondence true ∅ #[] stx pp
    let (reported, excluded) := corr.partition fun _ {kinds := ks,..} =>
      (!totalExclusions.contains ks && !ignoreSpaceAfter.contains ks && !ignoreSpaceAfter3.contains ks)
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
        -- TODO: investigate why some suggested changes are no-ops (e.g. in Data/Nat/BinaryRec:80)
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
        -- TODO: investigate why some suggested changes are no-ops (e.g. in Data/Nat/BinaryRec:80)
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
        )
    -- TODO: fix `byTens` and re-enable this logging output
    logInfo <| m!"\n".joinSep (byTens pretty (min pretty.length 100) ::"":: msgs.toList.map (m!"{·}"))
  else logWarning "Error"

-- #show_corr
-- --inspect
-- #check (  { default := (/-  -/) }:    Inhabited   Unit
-- )

end Style.Whitespace

end Mathlib.Linter
