/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

/-!
# `NoExpose.SourceScan` — locate `@[expose]` occurrences in source

The tool can only edit `@[expose]` attributes that actually exist in
source text, so we drive candidate selection from those occurrences
rather than from an env-walk of every body-exposed `def` (which over-
collects by ~50x once macro-generated and `meta`-section decls are
counted).

For each `@[expose]` text occurrence in a `.lean` file we emit one
`ExposeOccurrence` carrying:

* `attrLine`/`attrCol` — position of the literal `@[expose]` text.
* `scope` — either `.decl` (attaches to the next declaration) or
  `.section_ closeLine` (attaches to every declaration whose own
  start line falls in `[attrLine, closeLine]`).

The companion mapping from source ranges to env constants happens in
`NoExpose.Env`, using `Lean.findDeclarationRanges?` as the authority
for names and ranges.
-/

namespace NoExpose

/-- How a `@[expose]` attribute attaches to source. -/
inductive ExposeScope where
  /-- `@[expose]` (possibly bundled with other attributes) immediately
  preceding a declaration. -/
  | decl
  /-- `@[expose] (public)? (meta)? section ...` covering everything
  through the matching `end` on line `closeLine`. -/
  | section_ (closeLine : Nat)
  deriving Repr, Inhabited

structure ExposeOccurrence where
  /-- 1-based line of the literal `@[expose]` text. -/
  attrLine : Nat
  /-- 1-based column of the `@` of `@[expose]`. -/
  attrCol : Nat
  scope : ExposeScope
  deriving Repr, Inhabited

namespace SourceScan

/-- Does `body` (content between `@[` and `]`) contain `expose` as a
comma-separated token? Avoids matching `no_expose`, `exposes`, etc. -/
private def bodyHasExposeToken (body : String) : Bool := Id.run do
  for tok in body.splitOn "," do
    if tok.trimAscii.toString == "expose" then return true
  return false

/-- If `s` starts with `@[`, return `(col, body, restOfLine)` where
`col` is the 0-based offset of the `@`, `body` is the content between
`@[` and the matching `]`, and `restOfLine` is what comes after `]`.
Returns `none` if no `@[` opens at `s.firstNonWhitespace`. Tab/space
prefixes are tolerated. -/
private partial def consumeOneAttr (s : String) : Option (Nat × String × String) := Id.run do
  let bytes := s.toUTF8
  let n := bytes.size
  let mut i : Nat := 0
  -- skip leading whitespace
  while i < n && (bytes[i]! == 0x20 || bytes[i]! == 0x09) do i := i + 1
  if i + 1 >= n then return none
  if bytes[i]! != 0x40 || bytes[i + 1]! != 0x5B then return none  -- not `@[`
  let attCol := i
  let bodyStart := i + 2
  let mut p := bodyStart
  while p < n && bytes[p]! != 0x5D do p := p + 1                   -- ']'
  if p == n then return none
  let body := String.fromUTF8! (bytes.extract bodyStart p)
  let rest := String.fromUTF8! (bytes.extract (p + 1) n)
  return some (attCol, body, rest)

/-- Strip every leading `@[...]` block, returning `(rest, sawExpose)`.
`sawExpose` is true if any of the stripped blocks contained the
`expose` token. -/
private partial def consumeAttrs (s : String) : String × Bool := Id.run do
  let mut s := s
  let mut sawExpose := false
  while true do
    match consumeOneAttr s with
    | none => break
    | some (_, body, rest) =>
      if bodyHasExposeToken body then sawExpose := true
      s := rest
  return (s.trimAscii.toString, sawExpose)

private def sectionModifiers : Array String :=
  #["public ", "private ", "protected ", "meta ", "noncomputable ",
    "partial ", "unsafe ", "scoped "]

/-- Strip leading section/decl modifier words. -/
private partial def stripMods (s : String) : String := Id.run do
  let mut s := s
  let mut changed := true
  while changed do
    changed := false
    for m in sectionModifiers do
      if s.startsWith m then
        s := (s.drop m.length).toString
        changed := true
        break
  return s

/-- Does the line (after attribute and modifier prefixes) open a
section or namespace? Both contribute frames to the open-scope stack
so that `end` matches the right opener. -/
private def opensScope (afterMods : String) : Bool :=
  afterMods == "section" || afterMods.startsWith "section " ||
  afterMods.startsWith "namespace "

/-- Does the trimmed line start an `end ...` command? -/
private def isEndLine (trimmed : String) : Bool :=
  trimmed == "end" || trimmed.startsWith "end "

end SourceScan

open SourceScan in
/-- Walk `text` line by line, tracking nested sections/namespaces and
emitting one `ExposeOccurrence` per `@[expose]` occurrence we find.
For section-style occurrences we record the line of the matching
`end`; for decl-style ones the next declaration command line is the
attachment point (resolved by the caller against env declaration
ranges, not parsed from text).

This scanner is deliberately text-level and small: it only needs to
find `@[expose]` text, recognise `section`/`namespace`/`end` openers,
and balance them. Mathlib's notation extensions don't affect any of
those tokens, so we don't need the full Lean parser. -/
partial def scanExposeOccurrences (text : String) : Array ExposeOccurrence := Id.run do
  let lines := (text.splitOn "\n").toArray
  -- Stack of open scopes, each with `Some attrLineCol` iff opened by
  -- `@[expose] section`. Namespaces and non-expose sections push
  -- `none` and contribute only to balance.
  let mut stack : List (Option (Nat × Nat)) := []
  let mut out : Array ExposeOccurrence := #[]
  let mut inBlockComment : Bool := false
  for h : i in [:lines.size] do
    let line := lines[i]
    let trimmed := line.trimAscii.toString
    let lineNum := i + 1
    -- Handle multi-line block / module-doc comments.
    if inBlockComment then
      if trimmed.endsWith "-/" then inBlockComment := false
      continue
    if trimmed.isEmpty || trimmed.startsWith "--" then continue
    if trimmed.startsWith "/-" && !trimmed.startsWith "/--" then
      if !trimmed.endsWith "-/" then inBlockComment := true
      continue
    if trimmed.startsWith "/--" then
      let isOneLine := trimmed.length > "/----/".length && trimmed.endsWith "-/"
      if !isOneLine then inBlockComment := true
      continue
    -- `end` balances the stack regardless of expose-ness.
    if isEndLine trimmed then
      match stack with
      | some (openLine, openCol) :: rest =>
        out := out.push
          { attrLine := openLine, attrCol := openCol,
            scope := .section_ lineNum }
        stack := rest
      | none :: rest => stack := rest
      | []           => ()
      continue
    -- Consume any leading `@[...]` attribute blocks, recording whether
    -- one of them carried `expose`.
    let (afterAttrs, hasExpose) := consumeAttrs trimmed
    let afterMods := stripMods afterAttrs
    -- This line opens a section/namespace.
    if opensScope afterMods then
      if hasExpose && afterMods.startsWith "section" then
        -- attrCol is approximated by the leading-whitespace count.
        let col := (line.takeWhile Char.isWhitespace).length
        stack := some (lineNum, col + 1) :: stack
      else
        stack := none :: stack
      continue
    -- Decl-level `@[expose]` on this line, attaching to the next decl
    -- the env walk will identify.
    if hasExpose then
      let col := (line.takeWhile Char.isWhitespace).length
      out := out.push
        { attrLine := lineNum, attrCol := col + 1, scope := .decl }
      continue
    -- An `@[expose]` could be on its own line followed by a decl
    -- whose modifiers/keyword sit on later lines. The decl-level
    -- branch above already covers `@[expose]` alone (afterMods becomes
    -- empty, `opensScope` false). We don't need a separate pending
    -- state because the caller resolves decl attachment by source
    -- range, not by syntactic adjacency.
  -- Sections that run to EOF without an explicit `end` still cover
  -- everything between their opener and the last line of the file.
  -- Flush any remaining `@[expose]` frames.
  for frame in stack do
    match frame with
    | some (openLine, openCol) =>
      out := out.push
        { attrLine := openLine, attrCol := openCol,
          scope := .section_ lines.size }
    | none => ()
  return out

end NoExpose
