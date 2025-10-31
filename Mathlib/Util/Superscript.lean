/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Init
import Batteries.Tactic.Lint

/-!
# A parser for superscripts and subscripts

This is intended for use in local notations. Basic usage is:
```
local syntax:arg term:max superscript(term) : term
local macro_rules | `($a:term $b:superscript) => `($a ^ $b)
```
where `superscript(term)` indicates that it will parse a superscript, and the `$b:superscript`
antiquotation binds the `term` argument of the superscript. Given a notation like this,
the expression `2⁶⁴` parses and expands to `2 ^ 64`.

The superscript body is considered to be the longest contiguous sequence of superscript tokens and
whitespace, so no additional bracketing is required (unless you want to separate two superscripts).
However, note that Unicode has a rather restricted character set for superscripts and subscripts
(see `Mapping.superscript` and `Mapping.subscript` in this file), so you should not use this
parser for complex expressions.
-/

universe u

namespace Mathlib.Tactic

open Lean Parser PrettyPrinter Delaborator Std

namespace Superscript

instance : Hashable Char := ⟨fun c => hash c.1⟩

/-- A bidirectional character mapping. -/
structure Mapping where
  /-- Map from "special" (e.g. superscript) characters to "normal" characters. -/
  toNormal : Std.HashMap Char Char := {}
  /-- Map from "normal" text to "special" (e.g. superscript) characters. -/
  toSpecial : Std.HashMap Char Char := {}
  deriving Inhabited

/-- Constructs a mapping (intended for compile time use). Panics on violated invariants. -/
def mkMapping (s₁ s₂ : String) : Mapping := Id.run do
  let mut toNormal := {}
  let mut toSpecial := {}
  assert! s₁.length == s₂.length
  for sp in s₁.toSubstring, nm in s₂ do
    assert! !toNormal.contains sp
    assert! !toSpecial.contains nm
    toNormal := toNormal.insert sp nm
    toSpecial := toSpecial.insert nm sp
  pure { toNormal, toSpecial }

/-- A mapping from superscripts to and from regular text. -/
def Mapping.superscript := mkMapping
  "⁰¹²³⁴⁵⁶⁷⁸⁹ᵃᵇᶜᵈᵉᶠᵍʰⁱʲᵏˡᵐⁿᵒᵖ𐞥ʳˢᵗᵘᵛʷˣʸᶻᴬᴮᴰᴱᴳᴴᴵᴶᴷᴸᴹᴺᴼᴾꟴᴿᵀᵁⱽᵂᵝᵞᵟᵋᶿᶥᶹᵠᵡ⁺⁻⁼⁽⁾"
  "0123456789abcdefghijklmnopqrstuvwxyzABDEGHIJKLMNOPQRTUVWβγδεθιυφχ+-=()"

/-- A mapping from subscripts to and from regular text. -/
def Mapping.subscript := mkMapping
  "₀₁₂₃₄₅₆₇₈₉ₐₑₕᵢⱼₖₗₘₙₒₚᵣₛₜᵤᵥₓᴀʙᴄᴅᴇꜰɢʜɪᴊᴋʟᴍɴᴏᴘꞯʀꜱᴛᴜᴠᴡʏᴢᵦᵧᵨᵩᵪ₊₋₌₍₎"
  "0123456789aehijklmnoprstuvxABCDEFGHIJKLMNOPQRSTUVWYZβγρφχ+-=()"

/-- Collects runs of text satisfying `p` followed by whitespace. Fails if the first character does
not satisfy `p`. If `many` is true, it will parse 1 or more many whitespace-separated runs,
otherwise it will parse only 1. If successful, it passes the result to `k` as an array `(a, b, c)`
where `a..b` is a token and `b..c` is whitespace.
-/
partial def satisfyTokensFn (p : Char → Bool) (errorMsg : String) (many := true)
    (k : Array (String.Pos.Raw × String.Pos.Raw × String.Pos.Raw) → ParserState → ParserState) :
    ParserFn := fun c s =>
  let start := s.pos
  let s := takeWhile1Fn p errorMsg c s
  if s.hasError then s else
  let stop := s.pos
  let s := whitespace c s
  let toks := #[(start, stop, s.pos)]
  if many then
    let rec /-- Loop body of `satisfyTokensFn` -/
    loop (toks) (s : ParserState) : ParserState :=
      let start := s.pos
      let s := takeWhileFn p c s
      if s.pos == start then k toks s else
        let stop := s.pos
        let s := whitespace c s
        let toks := toks.push (start, stop, s.pos)
        loop toks s
    loop toks s
  else k toks s

variable {α : Type u} [Inhabited α] (as : Array α) (leftOfPartition : α → Bool) in
/-- Given a predicate `leftOfPartition` which is true for indexes `< i` and false for `≥ i`,
returns `i`, by binary search. -/
@[specialize]
def partitionPoint (lo := 0) (hi := as.size) : Nat :=
  if lo < hi then
    let m := (lo + hi)/2
    let a := as[m]!
    if leftOfPartition a then
      partitionPoint (m+1) hi
    else
      partitionPoint lo m
  else lo
  termination_by hi - lo

/-- The core function for super/subscript parsing. It consists of three stages:

1. Parse a run of superscripted characters, skipping whitespace and stopping when we hit a
   non-superscript character.
2. Un-superscript the text and pass the body to the inner parser (usually `term`).
3. Take the resulting `Syntax` object and align all the positions to fit back into the original
   text (which as a side effect also rewrites all the substrings to be in subscript text).

If `many` is false, then whitespace (and comments) are not allowed inside the superscript.
-/
partial def scriptFnNoAntiquot (m : Mapping) (errorMsg : String) (p : ParserFn)
    (many := true) : ParserFn := fun c s =>
  let start := s.pos
  satisfyTokensFn m.toNormal.contains errorMsg many c s (k := fun toks s => Id.run do
    let mut newStr := ""
    -- This consists of a sorted array of `(from, to)` pairs, where indexes `from+i` in `newStr`
    -- such that `from+i < from'` for the next element of the array, are mapped to `to+i`.
    let mut aligns := #[((0 : String.Pos.Raw), start)]
    for (start, stopTk, stopWs) in toks do
      let mut pos := start
      while pos < stopTk do
        let ch := c.get pos
        let ch' := m.toNormal[ch]!
        newStr := newStr.push ch'
        pos := pos + ch
        if ch.utf8Size != ch'.utf8Size then
          aligns := aligns.push (newStr.rawEndPos, pos)
      newStr := newStr.push ' '
      if stopWs.1 - stopTk.1 != 1 then
        aligns := aligns.push (newStr.rawEndPos, stopWs)
    let ictx := mkInputContext newStr "<superscript>"
    let s' := p.run ictx c.toParserModuleContext c.tokens (mkParserState newStr)
    let rec /-- Applies the alignment mapping to a position. -/
    align (pos : String.Pos.Raw) :=
      let i := partitionPoint aligns (·.1 ≤ pos)
      let (a, b) := aligns[i - 1]!
      pos.unoffsetBy a |>.offsetBy b
    let s := { s with pos := align s'.pos, errorMsg := s'.errorMsg }
    if s.hasError then return s
    let rec
    /-- Applies the alignment mapping to a `Substring`. -/
    alignSubstr : Substring → Substring
      | ⟨_newStr, start, stop⟩ => c.substring (align start) (align stop),
    /-- Applies the alignment mapping to a `SourceInfo`. -/
    alignInfo : SourceInfo → SourceInfo
      | .original leading pos trailing endPos =>
        -- Marking these as original breaks semantic highlighting,
        -- marking them as canonical breaks the unused variables linter. :(
        .original (alignSubstr leading) (align pos) (alignSubstr trailing) (align endPos)
      | .synthetic pos endPos canonical =>
        .synthetic (align pos) (align endPos) canonical
      | .none => .none,
     /-- Applies the alignment mapping to a `Syntax`. -/
     alignSyntax : Syntax → Syntax
      | .missing => .missing
      | .node info kind args => .node (alignInfo info) kind (args.map alignSyntax)
      | .atom info val =>
        -- We have to preserve the unsubscripted `val` even though it breaks `Syntax.reprint`
        -- because basic parsers like `num` read the `val` directly
        .atom (alignInfo info) val
      | .ident info rawVal val preresolved =>
        .ident (alignInfo info) (alignSubstr rawVal) val preresolved
    s.pushSyntax (alignSyntax s'.stxStack.back)
  )

/-- The super/subscript parser.

* `m`: the character mapping
* `antiquotName`: the name to use for antiquotation bindings `$a:antiquotName`.
  Note that the actual syntax kind bound will be the body kind (parsed by `p`), not `kind`.
* `errorMsg`: shown when the parser does not match
* `p`: the inner parser (usually `term`), to be called on the body of the superscript
* `many`: if false, whitespace is not allowed inside the superscript
* `kind`: the term will be wrapped in a node with this kind;
  generally this is a name of the parser declaration itself.
-/
def scriptParser (m : Mapping) (antiquotName errorMsg : String) (p : Parser)
    (many := true) (kind : SyntaxNodeKind := by exact decl_name%) : Parser :=
  let tokens := "$" :: (m.toNormal.toArray.map (·.1.toString) |>.qsort (·<·)).toList
  let antiquotP := mkAntiquot antiquotName `term (isPseudoKind := true)
  let p := Superscript.scriptFnNoAntiquot m errorMsg p.fn many
  node kind {
    info.firstTokens := .tokens tokens
    info.collectTokens := (tokens ++ ·)
    fn := withAntiquotFn antiquotP.fn p (isCatAntiquot := true)
  }

/-- Parenthesizer for the script parser. -/
def scriptParser.parenthesizer (k : SyntaxNodeKind) (p : Parenthesizer) : Parenthesizer :=
  Parenthesizer.node.parenthesizer k p

/-- Map over the strings in a `Format`. -/
def _root_.Std.Format.mapStringsM {m} [Monad m] (f : Format) (f' : String → m String) : m Format :=
  match f with
  | .group f b => (.group · b) <$> Std.Format.mapStringsM f f'
  | .tag t g => .tag t <$> Std.Format.mapStringsM g f'
  | .append f g => .append <$> Std.Format.mapStringsM f f' <*> Std.Format.mapStringsM g f'
  | .nest n f => .nest n <$> Std.Format.mapStringsM f f'
  | .text s => .text <$> f' s
  | .align _ | .line | .nil => pure f

/-- Formatter for the script parser. -/
def scriptParser.formatter (name : String) (m : Mapping) (k : SyntaxNodeKind) (p : Formatter) :
    Formatter := do
  let stack ← modifyGet fun s => (s.stack, {s with stack := #[]})
  Formatter.node.formatter k p
  let st ← get
  let transformed : Except String _ := st.stack.mapM (·.mapStringsM fun s => do
    let some s := s.toList.mapM (m.toSpecial.insert ' ' ' ').get? | .error s
    .ok (String.ofList s))
  match transformed with
  | .error err =>
    -- TODO: this only appears if the caller explicitly calls the pretty-printer
    Lean.logErrorAt (← get).stxTrav.cur s!"Not a {name}: '{err}'"
    set { st with stack := stack ++ st.stack }
  | .ok newStack =>
    set { st with stack := stack ++ newStack }

end Superscript

/--
The parser `superscript(term)` parses a superscript. Basic usage is:
```
local syntax:arg term:max superscript(term) : term
local macro_rules | `($a:term $b:superscript) => `($a ^ $b)
```
Given a notation like this, the expression `2⁶⁴` parses and expands to `2 ^ 64`.

Note that because of Unicode limitations, not many characters can actually be typed inside the
superscript, so this should not be used for complex expressions. Legal superscript characters:
```
⁰¹²³⁴⁵⁶⁷⁸⁹ᵃᵇᶜᵈᵉᶠᵍʰⁱʲᵏˡᵐⁿᵒᵖ𐞥ʳˢᵗᵘᵛʷˣʸᶻᴬᴮᴰᴱᴳᴴᴵᴶᴷᴸᴹᴺᴼᴾꟴᴿᵀᵁⱽᵂᵝᵞᵟᵋᶿᶥᶹᵠᵡ⁺⁻⁼⁽⁾
```
-/
def superscript (p : Parser) : Parser :=
  Superscript.scriptParser .superscript "superscript" "expected superscript character" p
/-- Formatter for the superscript parser. -/
@[combinator_parenthesizer superscript]
def superscript.parenthesizer := Superscript.scriptParser.parenthesizer ``superscript
/-- Formatter for the superscript parser. -/
@[combinator_formatter superscript]
def superscript.formatter :=
  Superscript.scriptParser.formatter "superscript" .superscript ``superscript

/-- Shorthand for `superscript(term)`.

This is needed because the initializer below does not always run, and if it has not run then
downstream parsers using the combinators will crash.

See https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Non-builtin.20parser.20aliases/near/365125476
for some context. -/
@[term_parser]
def superscriptTerm := leading_parser (withAnonymousAntiquot := false) superscript termParser

initialize register_parser_alias superscript

/--
The parser `subscript(term)` parses a subscript. Basic usage is:
```
local syntax:arg term:max subscript(term) : term
local macro_rules | `($a:term $i:subscript) => `($a $i)
```
Given a notation like this, the expression `(a)ᵢ` parses and expands to `a i`. (Either parentheses
or a whitespace as in `a ᵢ` is required, because `aᵢ` is considered as an identifier.)

Note that because of Unicode limitations, not many characters can actually be typed inside the
subscript, so this should not be used for complex expressions. Legal subscript characters:
```
₀₁₂₃₄₅₆₇₈₉ₐₑₕᵢⱼₖₗₘₙₒₚᵣₛₜᵤᵥₓᴀʙᴄᴅᴇꜰɢʜɪᴊᴋʟᴍɴᴏᴘꞯʀꜱᴛᴜᴠᴡʏᴢᵦᵧᵨᵩᵪ₊₋₌₍₎
```
-/
def subscript (p : Parser) : Parser :=
  Superscript.scriptParser .subscript "subscript" "expected subscript character" p
/-- Formatter for the subscript parser. -/
@[combinator_parenthesizer subscript]
def subscript.parenthesizer := Superscript.scriptParser.parenthesizer ``subscript
/-- Formatter for the subscript parser. -/
@[combinator_formatter subscript]
def subscript.formatter := Superscript.scriptParser.formatter "subscript" .subscript ``subscript

/-- Shorthand for `subscript(term)`.

This is needed because the initializer below does not always run, and if it has not run then
downstream parsers using the combinators will crash.

See https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Non-builtin.20parser.20aliases/near/365125476
for some context. -/
@[term_parser]
def subscriptTerm := leading_parser (withAnonymousAntiquot := false) subscript termParser

initialize register_parser_alias subscript

/-- Returns true if every character in `stx : Syntax` can be superscripted
(or subscripted). -/
private partial def Superscript.isValid (m : Mapping) : Syntax → Bool
  | .node _ kind args => kind == hygieneInfoKind || (!(scripted kind) && args.all (isValid m))
  | .atom _ s => valid s
  | .ident _ _ s _ => valid s.toString
  | _ => false
where
  valid (s : String) : Bool :=
    s.all ((m.toSpecial.insert ' ' ' ').contains ·)
  scripted : SyntaxNodeKind → Bool :=
    #[``subscript, ``superscript].contains

/-- Successfully delaborates only if the resulting expression can be superscripted.

See `Mapping.superscript` in this file for legal superscript characters. -/
def delabSuperscript : Delab := do
  let stx ← delab
  if Superscript.isValid .superscript stx.raw then pure stx else failure

/-- Successfully delaborates only if the resulting expression can be subscripted.

See `Mapping.subscript` in this file for legal subscript characters. -/
def delabSubscript : Delab := do
  let stx ← delab
  if Superscript.isValid .subscript stx.raw then pure stx else failure

end Mathlib.Tactic
