/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

/-!
# `NoExpose.SourceScan` — classify how each top-level decl is exposed

The env walk in `NoExpose.Env` tells us *that* a constant's body is in
the exported view, but not *why*: the `@[expose]` attribute is consumed
at elaboration and not stored on the constant (see
`Lean.Elab.MutualDef`). We reconstruct the source by re-reading the
file, walking it line by line, and tracking the section stack and
pending decl-modifier state.

For each top-level declaration the scanner emits one `ExposeSource`:

* `.explicit`    — `@[expose]` is on the decl line or directly above
* `.sectionAttr` — enclosed in `@[expose] (public)? section`
* `.metaExposed` — decl is `meta` or in a `(public)? meta section`
* `.unknown`     — none of the above (suspicious; treated as not
                   edit-eligible by `Verdict.classify`)

Text-level: macros, attributes split across lines, and unusual
indentation can fool the scanner. Uncertain cases come out as
`.unknown` and are conservatively treated as not edit-eligible.
-/

namespace NoExpose

/-- Why a declaration's body is in the exported view. -/
inductive ExposeSource where
  | explicit
  | sectionAttr
  | metaExposed
  | unknown
  deriving Repr, BEq

instance : Inhabited ExposeSource := ⟨.unknown⟩

def ExposeSource.toJsonString : ExposeSource → String
  | .explicit    => "explicit"
  | .sectionAttr => "section"
  | .metaExposed => "meta"
  | .unknown     => "unknown"

def ExposeSource.ofJsonString? : String → Option ExposeSource
  | "explicit" => some .explicit
  | "section"  => some .sectionAttr
  | "meta"     => some .metaExposed
  | "unknown"  => some .unknown
  | _          => none

namespace SourceScan

private structure Frame where
  hasExpose : Bool := false
  isMeta : Bool := false
  deriving Inhabited

private def modifierPrefixes : Array String :=
  #["private ", "protected ", "public ", "noncomputable ",
    "partial ", "unsafe ", "scoped "]

/-- Strip leading decl/section modifier words, returning the rest of
the string and whether `meta` was among them. -/
private partial def stripMods (s : String) : String × Bool := Id.run do
  let mut s := s
  let mut sawMeta := false
  let mut changed := true
  while changed do
    changed := false
    if s.startsWith "meta " then
      sawMeta := true
      s := (s.drop 5).toString
      changed := true
    else
      for m in modifierPrefixes do
        if s.startsWith m then
          s := (s.drop m.length).toString
          changed := true
          break
  return (s, sawMeta)

private def declKws : Array String :=
  #["def ", "theorem ", "lemma ", "instance ", "abbrev ",
    "structure ", "inductive ", "class ", "axiom ", "opaque ",
    "example ",
    -- `syntax` / `macro` / `notation` / `elab` declarations also
    -- produce constants the env walk picks up. Without these the
    -- scanner couldn't classify e.g. notation-defined terms and they
    -- showed up as `.unknown`.
    "syntax ", "macro ", "macro_rules ", "notation ", "elab ",
    "elab_rules ", "infix ", "infixl ", "infixr ", "prefix ",
    "postfix "]

private def isDeclHead (s : String) : Bool :=
  declKws.any (fun kw => s.startsWith kw)

private def isSectionHead (s : String) : Bool :=
  s.startsWith "section" || s.startsWith "namespace "

private def isEndHead (s : String) : Bool :=
  s == "end" || s.startsWith "end "

/-- True iff `body` (the content between `@[` and `]`) contains
`expose` as a comma-separated token (so `no_expose` doesn't match). -/
private def bodyHasExposeToken (body : String) : Bool := Id.run do
  for tok in body.splitOn "," do
    if tok.trimAscii.toString == "expose" then return true
  return false

/-- Walk past every leading `@[...]` block (and any whitespace between
them). Returns `(rest, sawExpose)`: the line with the attribute prefix
removed, and whether any of those blocks contained `@[expose]`.

For lines that don't start with `@[`, this is `(s, false)` after a
single `startsWith` check — so the scanner pays nothing on the common
case. Hot path uses byte-level scanning to avoid `splitOn`-style
per-line allocation. ASCII chars `@`, `[`, `]`, space, tab are
single-byte in UTF-8, so byte scanning is safe for them. -/
private partial def consumeAttrs (s : String) : String × Bool :=
  if !s.startsWith "@[" then (s, false)
  else Id.run do
    let bytes := s.toUTF8
    let n := bytes.size
    let mut sawExpose := false
    let mut i : Nat := 0
    while true do
      if i + 1 >= n then break
      if bytes[i]! != 0x40 || bytes[i + 1]! != 0x5B then break  -- '@['
      let bodyStart := i + 2
      let mut p := bodyStart
      while p < n && bytes[p]! != 0x5D do p := p + 1  -- ']'
      if p == n then break  -- malformed: no closing `]`
      if bodyHasExposeToken (String.fromUTF8! (bytes.extract bodyStart p)) then
        sawExpose := true
      i := p + 1
      while i < n && (bytes[i]! == 0x20 || bytes[i]! == 0x09) do i := i + 1
    return (String.fromUTF8! (bytes.extract i n), sawExpose)

end SourceScan

open SourceScan in
/-- Walk `text` once, classifying each top-level declaration. Returns
`(blockStartLine, headLine, ExposeSource)` per decl, both lines 1-based.
`blockStartLine` is the first line of any leading doc-comment or
attribute block; `headLine` is the line containing the actual decl
keyword (`def`/`theorem`/`macro`/…). They differ when a multi-line
doc-comment or attribute list precedes the keyword.
`Lean.findDeclarationRanges?.range.pos.line` returns the block-start
for `def`-shaped decls and the head line for `macro`/`syntax` shapes,
so callers need to look up against *either*. -/
partial def scanFile (text : String) : Array (Nat × Nat × ExposeSource) := Id.run do
  let lines := (text.splitOn "\n").toArray
  let mut stack : List Frame := []
  let mut blockStart : Option Nat := none
  let mut pendingExpose : Bool := false
  let mut inBlockComment : Bool := false
  let mut out : Array (Nat × Nat × ExposeSource) := #[]
  let mut i := 0
  while i < lines.size do
    let line := lines[i]!
    let trimmed := line.trimAscii.toString
    let lineNum := i + 1
    i := i + 1
    if inBlockComment then
      if trimmed.endsWith "-/" then inBlockComment := false
      continue
    if trimmed.isEmpty || trimmed.startsWith "--" then continue
    -- Module doc resets the pending decl block.
    if trimmed.startsWith "/-!" then
      if !trimmed.endsWith "-/" then inBlockComment := true
      blockStart := none; pendingExpose := false
      continue
    -- Doc comment starts/continues the pending decl block.
    if trimmed.startsWith "/--" then
      if blockStart.isNone then blockStart := some lineNum
      let isOneLine := trimmed.length > "/----/".length && trimmed.endsWith "-/"
      if !isOneLine then inBlockComment := true
      continue
    -- Block comment (not module doc, not doc comment).
    if trimmed.startsWith "/-" then
      if !trimmed.endsWith "-/" then inBlockComment := true
      continue
    if blockStart.isNone then blockStart := some lineNum
    if isEndHead trimmed then
      match stack with
      | _ :: rest => stack := rest
      | []        => ()
      blockStart := none; pendingExpose := false
      continue
    -- `mutual ... end`: push a placeholder so the matching `end` is balanced.
    if trimmed == "mutual" || trimmed.startsWith "mutual " then
      stack := ({} : Frame) :: stack
      blockStart := none; pendingExpose := false
      continue
    let (afterAttrs, lineHasExpose) := consumeAttrs trimmed
    let (afterMods, sawMeta) := stripMods afterAttrs
    if isSectionHead afterMods then
      stack := { hasExpose := lineHasExpose || pendingExpose, isMeta := sawMeta } :: stack
      blockStart := none; pendingExpose := false
      continue
    if isDeclHead afterMods then
      let startLine := blockStart.getD lineNum
      let src : ExposeSource :=
        if lineHasExpose || pendingExpose then .explicit
        else if sawMeta then .metaExposed
        else if stack.any (·.hasExpose) then .sectionAttr
        else if stack.any (·.isMeta) then .metaExposed
        else .unknown
      out := out.push (startLine, lineNum, src)
      blockStart := none; pendingExpose := false
      continue
    -- Attribute-only line (e.g. `@[expose]` on its own).
    if trimmed.startsWith "@[" then
      if lineHasExpose then pendingExpose := true
      continue
    -- Anything else (`open`, `variable`, `import`, `attribute …`): reset.
    blockStart := none; pendingExpose := false
  return out

end NoExpose
