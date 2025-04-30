/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Tactic.Linter.PPRoundtrip

/-!
#  The `commandStart` linter

The `commandStart` linter emits a warning if
* a command does not start at the beginning of a line;
* the "hypotheses segment" of a declaration does not coincide with its pretty-printed version.
-/

open Lean Elab Command

namespace Mathlib.Linter

/--
The `commandStart` linter emits a warning if
* a command does not start at the beginning of a line;
* the "hypotheses segment" of a declaration does not coincide with its pretty-printed version.

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
  defValue := true
  descr := "enable the commandStart linter"
}

/-- If the `linter.style.commandStart.verbose` is `true`, the `commandStart` linter
reports some helpful diagnostic information. -/
register_option linter.style.commandStart.verbose : Bool := {
  defValue := false
  descr := "enable the commandStart linter"
}

/-- `lintUpTo stx` returns the position up until the `commandStart` linter checks the formatting.
This is every declaration until the type-specification, if there is one, or the value,
as well as all `variable` commands.
-/
def lintUpTo (stx : Syntax) : Option String.Pos :=
  if let some cmd := stx.find? (·.isOfKind ``Lean.Parser.Command.declaration) then
    match cmd.find? (·.isOfKind ``Lean.Parser.Term.typeSpec) with
      | some s => s.getPos?
      | none => match cmd.find? (·.isOfKind ``Lean.Parser.Command.declValSimple) with
        | some s => s.getPos?
        | none => none
  else if stx.isOfKind ``Lean.Parser.Command.variable then
    stx.getTailPos?
  else none

structure FormatError where
  /-- The distance to the end of the source string, as number of characters. -/
  srcNat : Nat
  /-- The distance to the end of the source string, as number of string positions. -/
  srcEndPos : String.Pos
  /-- The distance to the end of the formatted string, as number of characters. -/
  fmtPos : Nat
  /-- The kind of formatting error: `extra space`, `remove line break` or `missing space`. -/
  msg : String
  /-- The length of the mismatch, as number of characters. -/
  length : Nat
  /-- The length of the mismatch, as a `String.pos`. -/
  srcStartPos : String.Pos
  deriving Inhabited

instance : ToString FormatError where
  toString f :=
    s!"srcNat: {f.srcNat}, srcPos: {f.srcEndPos}, fmtPos: {f.fmtPos}, \
      msg: {f.msg}, length: {f.length}\n"

def mkFormatError (ls ms : String) (msg : String) (length : Nat := 1) : FormatError where
  srcNat := ls.length
  srcEndPos := ls.endPos
  fmtPos := ms.length
  msg := msg
  length := length
  srcStartPos := ls.endPos

def pushFormatError (fs : Array FormatError) (f : FormatError) : Array FormatError :=
  -- If there are no errors already, we simply add the new one.
  if fs.isEmpty then fs.push f else
  let back := fs.back!
  -- If the latest error is of a different kind that then new one, we simply add the new one.
  if back.msg != f.msg || back.srcNat - back.length != f.srcNat then fs.push f else
  -- Otherwise, we are adding a further error of the same kind and we therefore merge the two.
  fs.pop.push {back with length := back.length + f.length, srcStartPos := f.srcEndPos}

partial
def parallelScanAux (as : Array FormatError) (L M : String) : Array FormatError :=
  --dbg_trace "'{L}'\n'{M}'\n---\n"
  if M.trim.isEmpty then as else
  if L.take 3 == "/--" && M.take 3 == "/--" then
    parallelScanAux as (L.drop 3) (M.drop 3) else
  if L.take 2 == "--" then
    let newL := (L.dropWhile (· != '\n')).drop 1
    let diff := L.length - newL.length - 1
    let newM := M.dropWhile (· != '-') |>.drop diff
    parallelScanAux as newL newM else
  if L.take 2 == "-/" then
    let newL := L.drop 2 |>.trimLeft
    let newM := M.drop 2 |>.trimLeft
    parallelScanAux as newL newM else
  let ls := L.drop 1
  let ms := M.drop 1
  match L.get 0, M.get 0 with
  | ' ', m =>
    if m.isWhitespace then
      parallelScanAux as ls ms.trimLeft
    else
      parallelScanAux (pushFormatError as (mkFormatError L M "extra space")) ls M
  | '\n', m =>
    if m.isWhitespace then
      parallelScanAux as ls.trimLeft ms.trimLeft
    else
      parallelScanAux (pushFormatError as (mkFormatError L M "remove line break")) ls.trimLeft M
  | l, m => -- `l` is not whitespace
    if l == m then
      parallelScanAux as ls ms
    else
      if m.isWhitespace then
        parallelScanAux (pushFormatError as (mkFormatError L M "missing space")) L ms.trimLeft
    else
      pushFormatError as (mkFormatError ls ms "Oh no! (Unreachable?)")


def parallelScan (src fmt : String) : Array FormatError :=
  parallelScanAux ∅ src fmt

/--
Returns the pair consisting of
* longest initial segment of `s` that does not contain `pattern` as a substring;
* the rest of the string `s`.

In particular, concatenating the two factors yields `s`.
-/
partial
def findString (s pattern : String) : String × String :=
  if pattern.isEmpty then (s, pattern) else
  if s.length < pattern.length then (s, pattern) else
  let candidatePos := s.find ("".push · == pattern.take 1)
  let notContains := {s.toSubstring with stopPos := candidatePos}.toString
  let rest := {s.toSubstring with startPos := candidatePos}.toString
  if rest.startsWith pattern then
    (notContains, rest)
  else
    let (init, tail) := findString (rest.drop 1) pattern
    (notContains ++ (pattern.take 1) ++ init, tail)

/--
`TrimComments s` eliminates comments from `s`, disregarding nesting.

If `compressDocs` is `true`, then it also compresses doc-strings that might be present in `s`,
by collapsing consecutive sequences of at least one space into a single space.
-/
partial
def trimComments (s : String) (compressDocs : Bool) : String :=
  if s.length ≤ 1 then s else
  let (beforeFirstDash, rest) := findString s "-"
  if rest.length ≤ 1 then s else
  match beforeFirstDash.takeRight 1, (rest.take 2).drop 1 with
  | "/", "-" => -- this is a doc-string
    let (takeDocs, rest) := findString (rest.drop 2) "-/"
    let finalDocs :=
      -- Replace each consecutive group of at least one space in `takeDocs` with a single space.
      -- The begin/end `|`-markers take care of preserving initial and terminal spaces, if there
      -- are any.  We remove them in the next step.
      if compressDocs then
        let intermediate := ("|" ++ takeDocs ++ "|").splitOn " " |>.filter (!·.isEmpty)
        " ".intercalate intermediate |>.drop 1 |>.dropRight 1 |>.replace "¬" "¬ "
      else
        takeDocs
    beforeFirstDash ++ "--" ++ finalDocs ++ trimComments rest compressDocs
  | "/", _ => -- this is a multiline comment
    let (_comment, rest) := findString (rest.drop 2) "-/"
    --let rest := if rest.startsWith "-/" then rest.drop 2 else rest
    (beforeFirstDash.dropRight 1).trimRight ++ trimComments (rest.drop 2) compressDocs
  | _, "-" => -- this is a single line comment
    let dropComment := rest.dropWhile (· != '\n')
    beforeFirstDash.trimRight ++ trimComments dropComment compressDocs
  | _, _ => beforeFirstDash ++ "-" ++ trimComments (rest.drop 1) compressDocs

/--
These are some replacements that we do to align the input syntax with the pretty-printed one,
mostly in cases where there is no real rule for what style to use.
-/
def furtherFormatting (s : String) : String :=
  s |>.replace "¬ " "¬"
               -- https://github.com/leanprover-community/aesop/pull/203/files
    |>.replace "aesop (rule_sets" "aesop(rule_sets"
    |>.replace " Prop." " «Prop»."
    |>.replace " Type." " «Type»."

namespace Style.CommandStart

/--
`unlintedNodes` contains the `SyntaxNodeKind`s for which there is no clear formatting preference:
if they appear in surface syntax, the linter will ignore formatting.

Currently, the unlined nodes are mostly related to `Subtype`, `Set` and `Finset` notation and
list notation.
-/
abbrev unlintedNodes := #[
  -- set-like notations, have extra spaces around the braces `{` `}`
  ``«term{_:_//_}», -- subtype, prefers `{ a // b }`
  `«term{_}»,  -- set notation, prefers `{ a | b }`
  `Mathlib.Meta.setBuilder, -- set builder notation, prefers `{ a : X | p a }`
  ``«term{}», -- empty set, prefers `{ }`

  ``«term_::_», -- list notation, prefers `a :: b`

  ``«term¬_», -- negation, prefers `¬a`

  ``Parser.Command.declId, -- declaration name, avoids dealing with guillemets pairs `«»`

  `Mathlib.Tactic.superscriptTerm,

  `Bundle.termπ__, -- notation for `Bundle.TotalSpace.proj`, the total space of a bundle
                   -- the pretty-printer prefers `π FE` over `π F E` (which we want)

 `Finset.«term_#_», -- notation for `Finset.slice`,
                    -- the pretty-printer prefers `𝒜 #r` over `𝒜 # r` (mathlib style)

  --`ToAdditive.toAdditiveRest, -- the `existing` in `[to_additive existing]`

  ``Parser.Command.docComment, -- The docString linter already takes care of formatting doc-strings.

  ``Parser.Command.omit, -- `omit [A] [B]` prints as `omit [A][B]`, see https://github.com/leanprover/lean4/pull/8169
  ]

/--
Given an array `a` of `SyntaxNodeKind`s, we accumulate the ranges of the syntax nodes of the
input syntax whose kind is in `a`.

The linter uses this information to avoid emitting a warning for nodes with kind contained in
`unlintedNodes`.
-/
def getUnlintedRanges(a : Array SyntaxNodeKind) :
    Std.HashSet String.Range → Syntax → Std.HashSet String.Range
  | curr, s@(.node _ kind args) =>
    let new := args.foldl (init := curr) (·.union <| getUnlintedRanges a curr ·)
    if a.contains kind then
      new.insert (s.getRange?.getD default)
    else
      new
  | curr, _ => curr

/-- Given a `HashSet` of `String.Ranges` `rgs` and a further `String.Range` `rg`,
`outside rgs rg` returns `true` if and only if `rgs` contains a range the completely contains
`rg`.

The linter uses this to figure out which nodes should be ignored.
-/
def outside? (rgs : Std.HashSet String.Range) (rg : String.Range) : Bool :=
  let superRanges := rgs.filter fun {start := a, stop := b} => (a ≤ rg.start && rg.stop ≤ b)
  superRanges.isEmpty

/-
instance : ToString String.Range where
  toString | {start := a, stop := b} => s!"⟨{a}, {b}⟩"

open Lean Elab Command in
elab "ff " cmd:command : command => do
  elabCommand cmd
  let gu := getUnlintedRanges unlintedNodes ∅ cmd
  dbg_trace gu.toArray.qsort (·.start < ·.start)
  --logInfo m!"{cmd}"

run_cmd
  let stx ← `(¬ true)
  dbg_trace stx

ff example (a : ¬ {b // b = 0} = default) : {v // v = 1} := sorry --⟨a.1+1, by cases a; simp_all⟩
-/

@[inherit_doc Mathlib.Linter.linter.style.commandStart]
def commandStartLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.style.commandStart (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  -- If a command does not start on the first column, emit a warning.
  if let some pos := stx.getPos? then
    let colStart := ((← getFileMap).toPosition pos).column
    if colStart ≠ 0 then
      Linter.logLint linter.style.commandStart stx
        m!"'{stx}' starts on column {colStart}, \
          but all commands should start at the beginning of the line."
  -- We skip `macro_rules`, since they cause parsing issues.
  if stx.find? (·.isOfKind ``Lean.Parser.Command.macro_rules) |>.isSome then
    return

  let fmt : Option Format := ←
      try
        liftCoreM <| PrettyPrinter.ppCategory `command stx
      catch _ =>
        Linter.logLintIf linter.style.commandStart.verbose (stx.getHead?.getD stx)
          m!"The `commandStart` linter had some parsing issues: \
            feel free to silence it and report this error!"
        return none
  if let some fmt := fmt then
    --let st := polishPP fmt.pretty
    let st := fmt.pretty
    let origSubstring := stx.getSubstring?.getD default
    let orig := origSubstring.toString
    let scan := parallelScan orig st
    --dbg_trace scan.map (·.srcPos)

    let some upTo := lintUpTo stx | return
    let docStringEnd := stx.find? (·.isOfKind ``Parser.Command.docComment) |>.getD default
    let docStringEnd := docStringEnd.getTailPos? |>.getD default
    --dbg_trace docStringEnd
    let forbidden := getUnlintedRanges unlintedNodes ∅ stx
    for s in scan do
      let center := origSubstring.stopPos - s.srcEndPos
      let rg : String.Range := ⟨center, center + s.srcEndPos - s.srcStartPos + ⟨1⟩⟩
      unless outside? forbidden rg do
        continue
      --let mut (center', orig') := (origSubstring.stopPos, orig)
      --for i in [:orig.length - s.srcPos] do
      --  --dbg_trace "{center'}, '{orig'.get (center' - origSubstring.stopPos)}' {orig'}"
      --  center' := orig'.next center' -- ⟨1⟩
      --  orig' := orig'.dropRight 1
      --let center := center' + origSubstring.stopPos - origSubstring.startPos
      unless rg.stop ≤ upTo do return
      unless docStringEnd ≤ rg.start do return

      let ctx := 5 -- the number of characters before and after of the mismatch that linter prints
      let srcWindow :=
        orig.takeRight (s.srcNat + ctx) |>.take (s.length + 2 * ctx -  1) |>.replace "\n" "⏎"
      let expectedWindow :=
        st.takeRight (s.fmtPos + ctx) |>.take (2 * ctx) |>.replace "\n" "⏎"
      Linter.logLint linter.style.commandStart (.ofRange rg)
        m!"{s.msg}\n\n\
          Current syntax:  '{srcWindow}'\n\
          Expected syntax: '{expectedWindow}'\n"
      Linter.logLintIf linter.style.commandStart.verbose (.ofRange rg)
        m!"Formatted string:\n{fmt}\nOriginal string:\n{origSubstring}"

  ---- We only lint up to the position given by `lintUpTo`
  --if let some finalLintPos := lintUpTo stx then
  --  if let some stype := stx.find? (unlintedNodes.contains ·.getKind) then
  --    Linter.logLintIf linter.style.commandStart.verbose (stx.getHead?.getD stx)
  --      m!"Found a '{stype.getKind}' node in '{stype}'"
  --    if let some pos := stype.getPos? then
  --      if pos ≤ finalLintPos && stype.getKind != `ToAdditive.toAdditiveRest then
  --        return
  --    -- we allow the linter to inspect declarations with a `to_additive` doc-string, as long as
  --    -- it fits in a single line.  Otherwise, getting the right formatting is hard.
  --    if stype.getKind == `ToAdditive.toAdditiveRest then
  --      let addDoc :=  stype.find? (·.isAtom) |>.map (·.getAtomVal) |>.getD ""
  --      if addDoc.contains '\n' then
  --        Linter.logLintIf linter.style.commandStart.verbose (stx.getHead?.getD stx)
  --          m!"Stop linting, since {addDoc} is a multiline additive docstring"
  --        return
    --let stx := capSyntax stx finalLintPos.1
    --let origSubstringTrunc : Substring := {origSubstring with stopPos := finalLintPos}
    --let (real, lths) := polishSource origSubstringTrunc.toString
    --if let some fmt := fmt then
    --  let st := polishPP fmt.pretty
    --  --let scan := parallelScan origSubstring.toString fmt.pretty
    --  --if !scan.isEmpty then logInfo m!"{scan}"
    --  Linter.logLintIf linter.style.commandStart.verbose (stx.getHead?.getD stx)
    --    m!"slightly polished source:\n'{real}'\n\n\
    --      actually used source:\n'{furtherFormatting (trimComments real true)}'\n\n\
    --      reference formatting:\n'{st}'\n\n\
    --      intermediate reference formatting:\n'{fmt}'\n"
    --  if ! st.startsWith (furtherFormatting (trimComments real true)) then
    --    let diff := real.firstDiffPos st
    --    let pos := posToShiftedPos lths diff.1 + origSubstringTrunc.startPos.1
    --    let f := origSubstringTrunc.str.drop (pos)
    --    let extraLth := (f.takeWhile (· != st.get diff)).length
    --    let srcCtxt := zoomString real diff.1 5
    --    let ppCtxt  := zoomString st diff.1 5
    --    --Linter.logLint linter.style.commandStart (.ofRange ⟨⟨pos⟩, ⟨pos + extraLth + 1⟩⟩)
    --    --  m!"Current syntax:  '{srcCtxt}'\nExpected syntax: '{ppCtxt}'\n"
initialize addLinter commandStartLinter

end Style.CommandStart

end Mathlib.Linter
