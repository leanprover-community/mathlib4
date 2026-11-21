/-
Copyright (c) 2026 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public import Mathlib.Init

/-!
# 2D diagram blocks: scanning and grid reading

A *block* is a contiguous byte range of the source file starting at a `⌜`. It consists of one or
more *boxes*, each delimited by corner glyphs:

* one-row box:   `⌜ … ⌟`
* multi-row box: `⌜ … ⌝` on its first row, `⌞ … ⌟` on its last row, corners column-aligned.

Between boxes, dashed *connectives* `⇢ ⇠ ⇣ ⇡` denote morphisms, and `⟶` a type of morphisms.
Inside boxes, labels are runs of identifier-ish characters (`a=b` glues names into one point), and
solid arrows `→ ← ↔ ↓ ↑ ↕ ↘ ↖ ⤡ ↙ ↗ ⤢` are specialization edges (`x → y` means
`y ∈ closure {x}`).

Columns are measured in **codepoints**, so every glyph allowed inside a block must render one
column wide; anything not on the allowlist is rejected with a positioned error.

## Layout rules

* **Boxes.** All four corners of a multi-row box must be column-aligned; a misaligned corner is a
  parse error pointing at it (this replaces an indentation rule). Interior rows must be blank on
  the box's edge columns.
* **Block extent.** A block runs from its opening `⌜` to its last `⌟`. Ordinary Lean code may
  precede the first `⌜` and follow the last `⌟`. Inside the block but outside the boxes, only
  spaces and dashed connectives are allowed. There is no requirement that `⌜` be the first
  non-blank character on its line: if code before it shifts the first row, the corner check
  catches it.
* **Continuing on the same row.** Once all boxes are closed, the block continues along that row
  only through a dashed connective. So `f ⌜a b⌟ ⌜a=b⌟` passes two arguments, and `⌜a⌟ → Prop` is
  an ordinary function type. For the same reason solid `→` is not a connective.
* **Inside boxes.** Labels are runs of `[A-Za-z0-9_'=*(),]`, Greek letters, and most sub- and
  superscript digits and letters (see `labelChar`). `=` glues names into one point, outside
  parentheses: `(a,c)=(b,c)`. A `,` must be inside parentheses, so `⌜a, b⌟` is an error. In a
  morphism, a label may end with an *ascription* `(=…)`, as in `a=b(=o)`: the point's names in
  its space, while the names before it only say which points of the two boxes correspond. A bare
  `_` is a point that matches nothing, named by the expected type of the morphism.
  Each solid arrow casts a ray both ways, and both rays must hit a label.
* **Between boxes.** Each dashed connective casts a ray both ways, and each ray must hit a box or
  a *node*: ordinary Lean code, which extends along its row up to two consecutive spaces, a box,
  a connective or the edge of the block. Any other text outside the boxes is an error.
* **Type ascriptions.** Inside a block, ` : ` (with a space on each side) separates a diagram
  from its type, which is again made of boxes, terms and `⟶`. So a multi-row `(d : A ⟶ B)` can be
  written as one block.
* **Width safety.** Tabs are rejected, as is any glyph not on the allowlist (the error names its
  codepoint). Most arrows in U+2190–21FF have East Asian Width *Ambiguous*, so the allowlist
  should be kept to glyphs that are one column wide in common editor fonts. `⟶` is the exception:
  it is one column wide only in a few fonts (e.g. JuliaMono, JetBrains Mono, Fira Code), but it is
  the notation for types of morphisms.

## Box-drawing glyphs

Several of the glyphs above (`⌜ ⌝ ⌞ ⌟`, the diagonal arrows, `⇢` and `⟶`) are missing from common
editor fonts, notably Consolas (VS Code's default on Windows), and the fallback glyphs are wider
than one column, so diagrams drift out of alignment. Each has an alternative drawn with
box-drawing glyphs, which those fonts have at one column, and the two can be mixed freely:

* corners `┌ ┐ └ ┘` (or rounded, `╭ ╮ ╰ ╯`);
* inside boxes, headless edges `╲ ╱ │`, which point down the page (like `↘ ↙ ↓`);
* between boxes, *drawn* connectives: a shaft followed by an arrowhead `→ ← ↓ ↑` (or preceded by
  it), dashed (`╌╌→`, `╎` above `↓`) for morphisms, and solid (`──→`, `│` above `↓`) for types of
  morphisms.

The delaborator uses them for multi-row diagrams when `pp.gavDiagrams.boxDrawing` is set.

Errors in the extent of a block (unmatched or misaligned corners, tabs) are found by the parser,
and so are parse errors, which abandon the whole command. Everything else (glyphs, edge columns,
rays) is checked by the elaborator.

Everything here is pure code (no `MetaM`). It is shared by the parser
(`Mathlib.Tactic.Gavrilovich.Parser`), which only needs the extent of a block, and the elaborator
(`Mathlib.Tactic.Gavrilovich.Elab.Full`), which reads the block's contents.
-/

public meta section

namespace Mathlib.Tactic.Gavrilovich

/-- A character of the source file, with its byte offset. -/
structure Cell where
  /-- The character. -/
  ch : Char
  /-- Its byte offset in the file. -/
  pos : Nat
deriving Inhabited

/-- An error with a byte range in the file, for a precise red squiggle. -/
structure Err where
  /-- Byte offset of the start of the offending range. -/
  start : Nat
  /-- Byte offset just past the offending range. -/
  stop : Nat
  /-- The error message. -/
  msg : String
deriving Inhabited, Repr

/-- An error located at this cell. -/
def Cell.err (c : Cell) (msg : String) : Err := ⟨c.pos, c.pos + c.ch.utf8Size, msg⟩

/-- A box, in row/column coordinates relative to its block (columns count codepoints). -/
structure Box where
  /-- Row of `⌜`. -/
  top : Nat
  /-- Column of `⌜`. -/
  left : Nat
  /-- Column of `⌟`. -/
  right : Nat
  /-- Row of `⌟`. -/
  bottom : Nat
  /-- Byte offset of `⌜`. -/
  startPos : Nat
  /-- Byte offset just past `⌟`. -/
  stopPos : Nat
deriving Inhabited, Repr

/-- An error located at the whole box. -/
def Box.err (b : Box) (msg : String) : Err := ⟨b.startPos, b.stopPos, msg⟩

/-- The extent of a diagram block, as found by `scanBlock`. -/
structure Block where
  /-- The lines of the block; row 0 is the line containing the opening `⌜`. -/
  rows : Array (Array Cell)
  /-- On row 0, columns `< col0` belong to ordinary Lean code. -/
  col0 : Nat
  /-- On the last row, columns `≥ stopCol` belong to ordinary Lean code. -/
  stopCol : Nat
  /-- Byte offset just past the block. -/
  stop : Nat
  /-- The boxes of the block. -/
  boxes : Array Box
deriving Inhabited

/-- Is `c` a dashed connective (a morphism between boxes)? -/
def isConnective (c : Char) : Bool := c == '⇢' || c == '⇠' || c == '⇣' || c == '⇡'

/-- The shaft of a drawn connective (such as `╌╌→`): `some (vertical, solid)`. Dashed shafts
`╌ ╎` make morphisms, and solid ones `─ │` types of morphisms. -/
def shaftKind? : Char → Option (Bool × Bool)
  | '╌' => some (false, false) | '─' => some (false, true)
  | '╎' => some (true, false)  | '│' => some (true, true)
  | _ => none

/-- Does a connective start at column `k` of `row`: a dashed connective, or a drawn one
(`╌╌→`, `──→`, `←╌╌`, `←──`)? -/
def startsConnective (row : Array Cell) (k : Nat) : Bool :=
  match row[k]? with
  | some cell =>
    isConnective cell.ch || cell.ch == '╌' || cell.ch == '─' ||
      (cell.ch == '←' && match row[k+1]? with
        | some n => n.ch == '╌' || n.ch == '─'
        | none => false)
  | none => false

/-- The kind of a box corner: `0` top left (`⌜ ┌ ╭`), `1` top right (`⌝ ┐ ╮`), `2` bottom left
(`⌞ └ ╰`), `3` bottom right (`⌟ ┘ ╯`). The box-drawing corners align in more fonts. -/
def cornerKind? : Char → Option Nat
  | '⌜' | '┌' | '╭' => some 0
  | '⌝' | '┐' | '╮' => some 1
  | '⌞' | '└' | '╰' => some 2
  | '⌟' | '┘' | '╯' => some 3
  | _ => none

/-- Is `c` one of the box corners? -/
def isCorner (c : Char) : Bool := (cornerKind? c).isSome

/-! ## Reading lines -/

/-- Cells of the line starting at byte `p`, and the byte offset of the next line (if any). -/
partial def readRow (s : String) (p : Nat) : Array Cell × Option Nat :=
  go ⟨p⟩ #[]
where
  /-- Loop for `readRow`. -/
  go (i : String.Pos.Raw) (acc : Array Cell) : Array Cell × Option Nat :=
    if i.byteIdx ≥ s.rawEndPos.byteIdx then (acc, none)
    else
      let ch := String.Pos.Raw.get s i
      let j := String.Pos.Raw.next s i
      if ch == '\n' then (acc, some j.byteIdx)
      else if ch == '\r' then go j acc
      else go j (acc.push ⟨ch, i.byteIdx⟩)

/-- Byte offset of the start of the line containing byte `p`. -/
partial def lineStart (s : String) (p : Nat) : Nat :=
  if p == 0 then 0
  else
    let q := String.Pos.Raw.prev s ⟨p⟩
    if String.Pos.Raw.get s q == '\n' then p else lineStart s q.byteIdx

/-! ## Scanning: find the extent of a block and its boxes -/

/-- A box that is still being scanned. -/
structure PBox where
  /-- Row of `⌜`. -/
  top : Nat
  /-- Column of `⌜`. -/
  left : Nat
  /-- Column of `⌝`, once seen. -/
  right : Option Nat := none
  /-- Byte offset of `⌜`. -/
  startPos : Nat
  /-- The `⌞` seen on the current row, if any. -/
  closing : Option Cell := none
deriving Inhabited

/-- State of `scanBlock`. -/
structure ScanState where
  /-- Boxes opened but not yet closed. -/
  opened : Array PBox := #[]
  /-- Boxes closed so far. -/
  boxes : Array Box := #[]
  /-- Column and byte offset just past the last `⌟`, if it was on the current row. -/
  lastClose : Option (Nat × Nat) := none

/-- Process one row. Returns the new state, and `some (stopCol, stopByte)` if the block ends here.
-/
def scanRow (r : Nat) (row : Array Cell) (startC : Nat) (st : ScanState) :
    Except Err (ScanState × Option (Nat × Nat)) := do
  let mut st := st
  let mut c := startC
  while c < row.size do
    let cell := row[c]!
    match cornerKind? cell.ch, cell.ch with
    | some 0, _ =>
      let inside := st.opened.any fun b =>
        b.left < c && match b.right with | some R => c < R | none => b.top == r
      if inside then throw <| cell.err "`⌜` inside another box (missing `⌝`/`⌟`?)"
      st := { st with opened := st.opened.push { top := r, left := c, startPos := cell.pos } }
    | some 1, _ =>
      match st.opened.findIdx? (fun b => b.top == r && b.right.isNone) with
      | none => throw <| cell.err "`⌝` without a `⌜` to its left on this row"
      | some i => st := { st with opened := st.opened.modify i ({ · with right := some c }) }
    | some 2, _ =>
      match st.opened.findIdx? (fun b => b.top < r && b.left == c && b.right.isSome) with
      | some i => st := { st with opened := st.opened.modify i ({ · with closing := some cell }) }
      | none =>
        let above := st.opened.filter (fun b => b.top < r)
        if above.isEmpty then throw <| cell.err "`⌞` without an open box above it"
        let cols := ", ".intercalate (above.toList.map (s!"{·.left}"))
        throw <| cell.err s!"`⌞` at column {c} doesn't line up with any open box's `⌜` \
          (open boxes start at column {cols})"
    | some _, _ =>
      let close (i : Nat) (b : PBox) : ScanState :=
        let box : Box := { top := b.top, left := b.left, right := c, bottom := r,
                           startPos := b.startPos, stopPos := cell.pos + cell.ch.utf8Size }
        { st with opened := st.opened.eraseIdx! i, boxes := st.boxes.push box,
                  lastClose := some (c + 1, cell.pos + cell.ch.utf8Size) }
      if let some i := st.opened.findIdx? (fun b => b.top == r && b.right.isNone) then
        st := close i st.opened[i]!
      else
        -- the `⌞` nearest to the left on this row
        let cands := (st.opened.mapIdx (·, ·)).filter fun (_, b) =>
          match b.closing with | some _ => b.left < c | none => false
        match cands.toList.foldl (fun acc (i, b) =>
            match acc with
            | some (_, b') => if b.left > b'.left then some (i, b) else acc
            | none => some (i, b)) none with
        | none => throw <| cell.err "`⌟` without a matching `⌜` (same row) or `⌞` (to its left)"
        | some (i, b) =>
          if b.right != some c then
            throw <| cell.err s!"`⌟` at column {c} doesn't line up with this box's `⌝` \
              (column {b.right.getD 0})"
          st := close i b
      if st.opened.isEmpty then
        -- the block continues on this row only through a dashed connective
        let mut k := c + 1
        while k < row.size && row[k]!.ch == ' ' do k := k + 1
        unless startsConnective row k do
          return (st, st.lastClose)
    | _, '\t' => throw <| cell.err "tab character inside a diagram (columns would be ambiguous)"
    | _, _ => pure ()
    c := c + 1
  -- end of row
  for b in st.opened do
    if b.top == r && b.right.isNone then
      throw ⟨b.startPos, b.startPos + '⌜'.utf8Size,
        "box has no `⌝` (or `⌟`, for a one-row box) on its first row"⟩
    if let some k := b.closing then
      throw <| k.err "`⌞` without a `⌟` on the same row"
  if st.opened.isEmpty then return (st, st.lastClose)
  return (st, none)

/-- Find the block starting at byte `start` (which must hold `⌜`). -/
partial def scanBlock (s : String) (start : Nat) : Except Err Block := do
  let ls := lineStart s start
  let rec loop (r : Nat) (p? : Option Nat) (rows : Array (Array Cell)) (col0 : Nat)
      (st : ScanState) : Except Err Block := do
    let some p := p? |
      let b := st.opened[0]!
      throw ⟨b.startPos, b.startPos + '⌜'.utf8Size, "box is never closed (no `⌞ … ⌟` below it)"⟩
    let (row, next) := readRow s p
    let col0 ← if r == 0 then
        match row.findIdx? (·.pos == start) with
        | some i => pure i
        | none => throw ⟨start, start + 1, "internal: block start not found"⟩
      else pure col0
    let (st, stop?) ← scanRow r row (if r == 0 then col0 else 0) { st with lastClose := none }
    let rows := rows.push row
    match stop? with
    | some (stopCol, stop) => return { rows, col0, stopCol, stop, boxes := st.boxes }
    | none => loop (r + 1) next rows col0 st
  loop 0 (some ls) #[] 0 {}

/-! ## Reading the grid -/

/-- Characters allowed in labels. The sub- and superscripts are those that both Consolas and
DejaVu Sans Mono have (so not `ₕ ₖ ₗ ₘ ₙ ₚ ₛ ₜ`, missing from Consolas, nor most Greek ones, missing
from DejaVu Sans Mono), and `₌ ⁼` are left out as too easily confused with `=`. -/
def labelChar (c : Char) : Bool :=
  c.isAlphanum || "_'=*(),".contains c ||
  (0x2080 ≤ c.toNat && c.toNat ≤ 0x2089) ||                       -- subscript digits
  "₊₋₍₎ₐₑₒₓₔᵢᵣᵤᵥⱼ".contains c ||                                   -- other subscripts
  "⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁽⁾ⁱⁿᵃᵇᶜᵈᵉᶠᵍʰʲᵏˡᵐᵒᵖʳˢᵗᵘᵛʷˣʸᶻᴬᴮᴰᴱᴳᴴᴵᴶᴷᴸᴹᴺᴼᴾᴿᵀᵁⱽᵂᵅᶿ".contains c ||  -- superscripts
  (0x391 ≤ c.toNat && c.toNat ≤ 0x3C9 && c.toNat != 0x3A2)        -- Greek

/-- The names glued together in the label `text`, and the names in its *ascription*, if any: its
parts between the `=`s outside parentheses, and then those inside a trailing `(=…)`, as in
`a=b(=o=p)`. An ascription gives the point's names in its space, so that the names before it only
say which points of the two boxes of a morphism correspond (see
`Mathlib.Tactic.Gavrilovich.Elab.Full`).

Parentheses must balance, and `,` and `=` can only be inside and outside them respectively, as in
`(a,c)=(b,c)` (and inside `(=…)`, as in `o(=(a,c))`); this catches `⌜a, b⌟`, which would
otherwise be the points `a,` and `b`. -/
def labelParts (text : String) : Except String (List String × List String) := do
  let cs := text.toList.toArray
  let mut names : Array String := #[]
  let mut extra : Array String := #[]
  let mut cur := ""
  let mut depth := 0
  -- inside a `(=…)` group, whose `(` is at depth 1
  let mut group := false
  let mut groups := 0
  let mut i := 0
  while h : i < cs.size do
    let ch := cs[i]
    let opensGroup := depth == 0 && ch == '(' && cs[i + 1]? == some '='
    if depth == 0 && groups > 0 && !opensGroup then
      throw s!"an ascription `(=…)` must come at the end of the label '{text}'"
    if opensGroup then
      if groups == 0 then names := names.push cur
      cur := ""; depth := 1; group := true; groups := groups + 1; i := i + 2
      continue
    -- the depth at which names are separated
    let top := if group then 1 else 0
    match ch with
    | '(' => depth := depth + 1
    | ')' =>
      if depth == 0 then throw s!"unbalanced `)` in label '{text}'"
      depth := depth - 1
      if group && depth == 0 then
        extra := extra.push cur; cur := ""; group := false; i := i + 1
        continue
    | ',' =>
      if depth == top then
        throw s!"`,` outside parentheses in label '{text}' (labels are separated by spaces; \
          a `,` can only be part of a name such as `(a,b)`)"
    | '=' =>
      if depth == top then
        if group then extra := extra.push cur else names := names.push cur
        cur := ""; i := i + 1
        continue
      throw s!"`=` inside parentheses in label '{text}' (glue whole names, as in `(a,c)=(b,c)`)"
    | _ => pure ()
    cur := cur.push ch
    i := i + 1
  if depth != 0 then throw s!"unbalanced `(` in label '{text}'"
  if groups == 0 then names := names.push cur
  if names == #[""] && groups > 0 then
    throw s!"the label '{text}' has an ascription but no name before it (write e.g. `a(=o)`, or \
      `_(=o)` for a point that nothing maps to)"
  if names.any (·.isEmpty) || extra.any (·.isEmpty) then
    throw s!"malformed glued label '{text}' (write `a=b` or `a(=o)`, no spaces)"
  return (names.toList, extra.toList)

/-- Solid arrows (inside boxes): direction `(dr, dc)` from tail to head, and bidirectionality. -/
def arrowDir : Char → Option (Int × Int × Bool)
  | '→' => some (0, 1, false)  | '←' => some (0, -1, false)  | '↔' => some (0, 1, true)
  | '↓' => some (1, 0, false)  | '↑' => some (-1, 0, false)  | '↕' => some (1, 0, true)
  | '↘' => some (1, 1, false)  | '↖' => some (-1, -1, false) | '⤡' => some (1, 1, true)
  | '↙' => some (1, -1, false) | '↗' => some (-1, 1, false)  | '⤢' => some (1, -1, true)
  -- headless, pointing down the page; these align in more fonts
  | '╲' => some (1, 1, false)  | '╱' => some (1, -1, false)  | '│' => some (1, 0, false)
  | _ => none

/-- Connectives (between boxes): direction `(dr, dc)` from source to target. The dashed ones
`⇢ ⇠ ⇣ ⇡` are morphisms, and `⟶` is a type of morphisms. (Drawn connectives such as `╌╌→` are
found from their arrowheads; see `Block.drawnConnective?`.) -/
def connDir : Char → Option (Int × Int)
  | '⇢' => some (0, 1) | '⇠' => some (0, -1) | '⇣' => some (1, 0) | '⇡' => some (-1, 0)
  | '⟶' => some (0, 1)
  | _ => none

/-- Is `c` the connective `⟶`, a type of morphisms (rather than a morphism)? -/
def isHomType (c : Char) : Bool := c == '⟶'

/-- The arrowheads of drawn connectives, with their directions. -/
def headDir : Char → Option (Int × Int)
  | '→' => some (0, 1) | '←' => some (0, -1) | '↓' => some (1, 0) | '↑' => some (-1, 0)
  | _ => none

/-- A label in a box: one point, possibly with several glued names. -/
structure Label where
  /-- Row of the label. -/
  row : Nat
  /-- First column of the label. -/
  c0 : Nat
  /-- One past the last column of the label. -/
  c1 : Nat
  /-- The label as written, e.g. `a=b`. -/
  text : String
  /-- The glued names of the point in its space, e.g. `["a", "b"]` for `a=b`, and `["o"]` for
  `a=b(=o)`. -/
  names : List String
  /-- The names that match this point with points of the other box of a morphism: those before
  its ascription, if any, except `_`. E.g. `["a", "b"]` for `a=b(=o)` (and for `a=b`). -/
  matchNames : List String
  /-- Does the label have an ascription `(=…)`? -/
  ascribed : Bool := false
  /-- Byte offset of the label. -/
  start : Nat
  /-- Byte offset just past the label. -/
  stop : Nat
deriving Inhabited, Repr

/-- An error located at this label. -/
def Label.err (l : Label) (msg : String) : Err := ⟨l.start, l.stop, msg⟩

/-- The contents of a box. -/
structure BoxD where
  /-- The box. -/
  box : Box
  /-- Its labels (points). -/
  labels : Array Label
  /-- Its arrows, as pairs `(tail, head)` of label indices. -/
  edges : Array (Nat × Nat)
deriving Inhabited

/-- A *node*: ordinary Lean code inside a block, outside the boxes, that a connective points at.
It extends along its row up to two consecutive spaces, a box, a connective, or the edge of the
block. -/
structure Node where
  /-- Row of the node. -/
  row : Nat
  /-- First column of the node. -/
  c0 : Nat
  /-- One past the last column of the node. -/
  c1 : Nat
  /-- Byte offset of the node. -/
  start : Nat
  /-- Byte offset just past the node. -/
  stop : Nat
deriving Inhabited, Repr

/-- An end of a connective: a box or a node, by index. -/
inductive Obj where
  /-- The box with this index. -/
  | box (i : Nat)
  /-- The node with this index. -/
  | node (i : Nat)
deriving BEq, Inhabited, Repr

/-- A dashed connective. -/
structure Link where
  /-- The source. -/
  src : Obj
  /-- The target. -/
  tgt : Obj
  /-- The connective glyph (the arrowhead, for a drawn connective such as `╌╌→`). -/
  cell : Cell
  /-- Is it a type of morphisms (`⟶`, `──→`), rather than a morphism? -/
  homType : Bool := false

/-- The contents of a block. -/
structure Diagram where
  /-- The boxes. -/
  boxes : Array BoxD
  /-- The nodes. -/
  nodes : Array Node
  /-- The connectives between them. -/
  links : Array Link
  /-- The ` : ` of a type ascription inside the block, if any, and its column: the boxes, nodes
  and connectives to its left are the term, and those to its right its type. -/
  colon : Option (Cell × Nat) := none

/-- The internal name of the `k`-th hole `_` of a box. It can't be written in a box (`#` isn't a
label character), so it never clashes with a name. -/
def holeName (k : Nat) : String := s!"_#{k}"

/-- Is `n` the internal name of a hole `_`? -/
def isHoleName (n : String) : Bool := n.startsWith "_#"

/-- The display name of a name: `_` for a hole. -/
def displayName (n : String) : String := if isHoleName n then "_" else n

namespace Block

/-- The index of the last row. -/
def lastRow (B : Block) : Nat := B.rows.size - 1

/-- Is `(r, c)` part of the block (as opposed to ordinary code on the first/last line)? -/
def inBlock (B : Block) (r c : Nat) : Bool :=
  r < B.rows.size && !(r == 0 && c < B.col0) && !(r == B.lastRow && c ≥ B.stopCol)

/-- The character at `(r, c)`, or a space if out of range. -/
def chAt (B : Block) (r c : Nat) : Char :=
  match B.rows[r]? >>= (·[c]?) with | some cell => cell.ch | none => ' '

/-- The index of the box containing `(r, c)`, if any. -/
def boxAt (B : Block) (r c : Nat) : Option Nat :=
  B.boxes.findIdx? fun b => b.top ≤ r && r ≤ b.bottom && b.left ≤ c && c ≤ b.right

/-- Is `(r, c)` the colon of a type ascription, ` : ` (outside the boxes)? -/
def isColon (B : Block) (r c : Nat) : Bool :=
  B.inBlock r c && (B.boxAt r c).isNone && B.chAt r c == ':' && c ≥ 1 &&
    B.chAt r (c - 1) == ' ' && B.chAt r (c + 1) == ' '

/-- If `(r, c)` is the arrowhead of a drawn connective (such as `╌╌→`, `──→` or `╎` above `↓`),
outside the boxes: its direction, and whether it is a type of morphisms (a solid shaft). -/
def drawnConnective? (B : Block) (r c : Nat) : Option (Int × Int × Bool) := do
  guard <| B.inBlock r c && (B.boxAt r c).isNone
  let (dr, dc) ← headDir (B.chAt r c)
  let (r', c') := ((r : Int) - dr, (c : Int) - dc)
  guard <| r' ≥ 0 && c' ≥ 0 && B.inBlock r'.toNat c'.toNat && (B.boxAt r'.toNat c'.toNat).isNone
  let (vert, solid) ← shaftKind? (B.chAt r'.toNat c'.toNat)
  guard <| vert == (dr != 0)
  return (dr, dc, solid)

/-- The cells of the shaft behind the arrowhead of the drawn connective at `(r, c)`. -/
partial def shaftCells (B : Block) (r c : Nat) (dr dc : Int) : List (Nat × Nat) :=
  let (r', c') := ((r : Int) - dr, (c : Int) - dc)
  if r' < 0 || c' < 0 || !B.inBlock r'.toNat c'.toNat || (B.boxAt r'.toNat c'.toNat).isSome then
    []
  else match shaftKind? (B.chAt r'.toNat c'.toNat) with
    | some (vert, _) =>
      if vert == (dr != 0) then (r'.toNat, c'.toNat) :: B.shaftCells r'.toNat c'.toNat dr dc
      else []
    | none => []

/-- Can `(r, c)` be part of a node? -/
def isNodeCell (B : Block) (r c : Nat) : Bool :=
  let ch := B.chAt r c
  B.inBlock r c && (B.boxAt r c).isNone && ch != ' ' && (connDir ch).isNone && !isCorner ch &&
    !B.isColon r c && (shaftKind? ch).isNone && (B.drawnConnective? r c).isNone

/-- The node containing the cell `(r, c)` (which must satisfy `isNodeCell`). -/
def nodeAt (B : Block) (r c : Nat) : Node := Id.run do
  let ok := B.isNodeCell r
  let gap (k : Nat) : Bool := B.inBlock r k && B.chAt r k == ' '
  let mut c0 := c
  while c0 ≥ 1 && (ok (c0 - 1) || (c0 ≥ 2 && gap (c0 - 1) && ok (c0 - 2))) do
    c0 := if ok (c0 - 1) then c0 - 1 else c0 - 2
  let mut c1 := c + 1
  while ok c1 || (gap c1 && ok (c1 + 1)) do
    c1 := if ok c1 then c1 + 1 else c1 + 2
  let row := B.rows[r]!
  return { row := r, c0, c1, start := row[c0]!.pos,
           stop := row[c1 - 1]!.pos + row[c1 - 1]!.ch.utf8Size }

/-- The width of the widest row. -/
def maxCol (B : Block) : Nat := B.rows.foldl (fun m row => max m row.size) 0

/-- The error for a glyph that is not on the allowlist. -/
def badGlyph (cell : Cell) : Err :=
  cell.err s!"glyph '{cell.ch}' (U+{String.ofList (Nat.toDigits 16 cell.ch.toNat) |>.toUpper}) is \
    not on the diagram allowlist: alignment is by codepoint, so only glyphs known to render \
    one column wide are allowed"

/-- Check every cell of the block for being the right kind of glyph in the right place. Cells
outside boxes may be blank, connectives (`drawn` are the cells of drawn connectives), or part of
one of `nodes`. -/
def validate (B : Block) (nodes : Array Node) (drawn : Array (Nat × Nat)) : Except Err Unit := do
  for h : r in [0:B.rows.size] do
    let row := B.rows[r]
    for h : c in [0:row.size] do
      let cell := row[c]
      if !B.inBlock r c then continue
      match B.boxAt r c with
      | some i =>
        let b := B.boxes[i]!
        if c == b.left || c == b.right then
          let expected : Option Nat :=
            if b.top == b.bottom then (if c == b.left then some 0 else some 3)
            else if r == b.top then (if c == b.left then some 0 else some 1)
            else if r == b.bottom then (if c == b.left then some 2 else some 3)
            else none
          let ok := match expected with
            | some k => cornerKind? cell.ch == some k
            | none => cell.ch == ' '
          if !ok then
            throw <| cell.err s!"'{cell.ch}' sits on this box's edge column ({c}); \
              is this row misaligned?"
        else if cell.ch == ' ' || labelChar cell.ch || (arrowDir cell.ch).isSome then pure ()
        else if isCorner cell.ch then throw <| cell.err "stray corner glyph inside a box"
        else if (connDir cell.ch).isSome then
          throw <| cell.err "connectives go between boxes; inside a box use solid arrows"
        else throw (badGlyph cell)
      | none =>
        if cell.ch == ' ' || (connDir cell.ch).isSome || B.isColon r c then pure ()
        else if drawn.contains (r, c) then pure ()
        else if nodes.any (fun n => n.row == r && n.c0 ≤ c && c < n.c1) then pure ()
        else if labelChar cell.ch then
          throw <| cell.err "label outside any box (outside boxes, only terms that a connective \
            points at are allowed)"
        else if (shaftKind? cell.ch).isSome then
          throw <| cell.err "this connective has no arrowhead (write e.g. `╌╌→`, or `╎` above `↓`)"
        else if (arrowDir cell.ch).isSome then
          throw <| cell.err "solid arrows go inside boxes; between boxes use `⇢ ⇠ ⇣ ⇡` or a drawn \
            connective such as `╌╌→`"
        else throw (badGlyph cell)

/-- Labels of box `b`: maximal horizontal runs of label characters in its interior. A bare `_` is a
*hole*: a point that matches nothing, named by the expected type of the morphism; each one gets
its own internal name (see `holeName`). -/
def labelsOf (B : Block) (b : Box) : Except Err (Array Label) := do
  let mut out := #[]
  let mut holes := 0
  for r in [b.top:b.bottom+1] do
    let row := B.rows[r]!
    let mut c := b.left + 1
    while c < b.right do
      if c < row.size && labelChar row[c]!.ch then
        let c0 := c
        while c < b.right && c < row.size && labelChar row[c]!.ch do c := c + 1
        let text := String.ofList ((row.extract c0 c).toList.map (·.ch))
        let start := row[c0]!.pos
        let stop := row[c-1]!.pos + row[c-1]!.ch.utf8Size
        let (plain, asc) ← (labelParts text).mapError (⟨start, stop, ·⟩)
        if plain.length > 1 && plain.contains "_" then
          throw ⟨start, stop, s!"`_` can't be glued to names in the label '{text}' (`_` matches \
            nothing, so `_=a` is just `a`)"⟩
        let hole := plain == ["_"] && asc.isEmpty
        let names := if hole then [holeName holes] else if asc.isEmpty then plain else asc
        if hole then holes := holes + 1
        let matchNames := plain.filter (· != "_")
        let ascribed := !asc.isEmpty
        out := out.push { row := r, c0, c1 := c, text, start, stop, names, matchNames, ascribed }
      else c := c + 1
  return out

/-- Follow the ray from the arrow `from_` at `(r, c)` in direction `(dr, dc)`, through blanks, to
a label of box `b`; return the label's index. -/
partial def rayToLabel (B : Block) (b : Box) (labels : Array Label) (from_ : Cell)
    (r c : Int) (dr dc : Int) : Except Err Nat := do
  let r' := r + dr; let c' := c + dc
  if r' < b.top || r' > b.bottom || c' ≤ b.left || c' ≥ b.right then
    throw <| from_.err "this arrow points at nothing (its ray leaves the box)"
  let ch := B.chAt r'.toNat c'.toNat
  if ch == ' ' then rayToLabel B b labels from_ r' c' dr dc
  else if labelChar ch then
    match labels.findIdx? (fun l => l.row == r'.toNat && l.c0 ≤ c'.toNat && c'.toNat < l.c1) with
    | some i => pure i
    | none => throw <| from_.err "internal: label not found"
  else throw <| from_.err s!"this arrow's ray runs into '{ch}' before reaching a label"

/-- Follow the ray from the connective `from_` at `(r, c)` in direction `(dr, dc)`, through
blanks, to a box (returning its index) or a node (returning the cell hit). -/
partial def rayToObj (B : Block) (from_ : Cell) (r c : Int) (dr dc : Int) :
    Except Err (Nat ⊕ (Nat × Nat)) := do
  let r' := r + dr; let c' := c + dc
  if r' < 0 || c' < 0 || r' ≥ B.rows.size || c' > B.maxCol ||
      !B.inBlock r'.toNat c'.toNat then
    throw <| from_.err "this connective doesn't point at a box or a term"
  match B.boxAt r'.toNat c'.toNat with
  | some i => pure (.inl i)
  | none =>
    let ch := B.chAt r'.toNat c'.toNat
    -- through blanks, and the shaft of a drawn connective along the ray
    let shaft := match shaftKind? ch with
      | some (vert, _) => vert == (dr != 0)
      | none => false
    if ch == ' ' || shaft then rayToObj B from_ r' c' dr dc
    else if B.isNodeCell r'.toNat c'.toNat then pure (.inr (r'.toNat, c'.toNat))
    else if B.isColon r'.toNat c'.toNat then
      throw <| from_.err "this connective's ray runs into the `:` of a type ascription before \
        reaching a box"
    else throw <| from_.err s!"this connective's ray runs into '{ch}' before reaching a box"

/-- Read the boxes, labels, arrows, nodes and connectives of a block. -/
def read (B : Block) : Except Err Diagram := do
  let mut nodes : Array Node := #[]
  let mut links := #[]
  let mut drawn : Array (Nat × Nat) := #[]
  let mut colon : Option (Cell × Nat) := none
  for h : r in [0:B.rows.size] do
    let row := B.rows[r]
    for h : c in [0:row.size] do
      let cell := row[c]
      if !B.inBlock r c || (B.boxAt r c).isSome then continue
      if B.isColon r c then
        if colon.isSome then throw <| cell.err "a second type ascription `:` in this block"
        if let some i := B.boxes.findIdx? (fun b => b.left ≤ c && c ≤ b.right) then
          throw <| B.boxes[i]!.err "this box spans the column of the `:` of a type ascription"
        for (dc, side) in [((-1 : Int), "before"), (1, "after")] do
          match B.rayToObj cell r c 0 dc with
          | .ok (.inr (r', c')) =>
            let n := B.nodeAt r' c'
            unless nodes.any (·.start == n.start) do nodes := nodes.push n
          | .ok (.inl _) => pure ()
          | .error _ => throw <| cell.err s!"nothing {side} the `:` of this type ascription"
        colon := some (cell, c)
        continue
      let some (dr, dc, homType) :=
          (connDir cell.ch).map (fun (dr, dc) => (dr, dc, isHomType cell.ch)) <|>
            B.drawnConnective? r c |
        continue
      if (connDir cell.ch).isNone then
        drawn := drawn.push (r, c) ++ (B.shaftCells r c dr dc).toArray
      let mut ends := #[]
      for (dr, dc) in [(dr, dc), (-dr, -dc)] do
        match ← B.rayToObj cell r c dr dc with
        | .inl i => ends := ends.push (Obj.box i)
        | .inr (r', c') =>
          let n := B.nodeAt r' c'
          match nodes.findIdx? (·.start == n.start) with
          | some i => ends := ends.push (.node i)
          | none => nodes := nodes.push n; ends := ends.push (.node (nodes.size - 1))
      let (tgt, src) := (ends[0]!, ends[1]!)
      if src == tgt then throw <| cell.err "connective from something to itself"
      links := links.push { src, tgt, cell, homType }
  B.validate nodes drawn
  let mut boxes := #[]
  for b in B.boxes do
    let labels ← B.labelsOf b
    -- duplicate names, among those matched by and among those ascribed. (A name can be a name of
    -- one point in the space, and match another, as in `⌜b(=a)  a(=b)⌟`; and a plain name is a name
    -- in the space only if the box keeps its own names, which `checkOwnNames` checks then.)
    for names in [Label.matchNames, fun l => if l.ascribed then l.names else []] do
      let mut seen : List String := []
      for l in labels do
        for n in names l do
          if seen.contains n then throw <| l.err s!"name '{n}' appears twice in this box"
          seen := n :: seen
    let mut edges := #[]
    for r in [b.top:b.bottom+1] do
      for c in [b.left+1:b.right] do
        let some cell := B.rows[r]!.toList[c]? | continue
        let some (dr, dc, both) := arrowDir cell.ch | continue
        let head ← rayToLabel B b labels cell r c dr dc
        let tail ← rayToLabel B b labels cell r c (-dr) (-dc)
        edges := edges.push (tail, head)
        if both then edges := edges.push (head, tail)
    boxes := boxes.push { box := b, labels, edges }
  return { boxes, nodes, links, colon }

end Block

/-- The part of the diagram to the left (`left`) or right of column `col`: its boxes and nodes,
and the connectives between them. -/
def Diagram.side (d : Diagram) (left : Bool) (col : Nat) : Diagram :=
  let inSide (c : Nat) := if left then c < col else c > col
  let bIdx := (Array.range d.boxes.size).filter (inSide d.boxes[·]!.box.left)
  let nIdx := (Array.range d.nodes.size).filter (inSide d.nodes[·]!.c0)
  let remap : Obj → Option Obj
    | .box i => (bIdx.findIdx? (· == i)).map .box
    | .node i => (nIdx.findIdx? (· == i)).map .node
  { boxes := bIdx.map (d.boxes[·]!), nodes := nIdx.map (d.nodes[·]!),
    links := d.links.filterMap fun l => do
      return { l with src := ← remap l.src, tgt := ← remap l.tgt } }

/-! ## Canonical form of a box -/

/-- Canonical data for a box: points (each a sorted list of glued names, points sorted by first
name), the full (irreflexive) specialization closure as sorted index pairs, and the map from
label index to canonical point index. -/
structure Canon where
  /-- The points, each a sorted list of glued names, sorted by first name. -/
  L : List (List String)
  /-- The full irreflexive specialization closure, as sorted index pairs. -/
  E : List (Nat × Nat)
  /-- Map from label index to canonical point index. -/
  perm : Array Nat
deriving Repr

/-- `≤` on strings, as a `Bool`. -/
def strLe (a b : String) : Bool := !(b < a)

/-- The canonical form of the space with points named `names` (each a list of glued names) and
arrows `edges` between them (as pairs of indices into `names`). -/
def canonOf (names : Array (List String)) (edges : Array (Nat × Nat)) : Canon := Id.run do
  let n := names.size
  let sorted : Array (List String) := names.map (·.mergeSort strLe)
  let order : List Nat :=
    (List.range n).mergeSort fun i j => strLe sorted[i]!.head! sorted[j]!.head!
  let mut perm := Array.replicate n 0
  for h : k in [0:order.length] do perm := perm.set! order[k] k
  -- reachability (Floyd–Warshall) in canonical indices
  let mut reach : Array (Array Bool) := Array.replicate n (Array.replicate n false)
  for (t, h) in edges do
    reach := reach.modify perm[t]! (·.set! perm[h]! true)
  for k in [0:n] do
    for i in [0:n] do
      if reach[i]![k]! then
        for j in [0:n] do
          if reach[k]![j]! then reach := reach.modify i (·.set! j true)
  let mut E := #[]
  for i in [0:n] do
    for j in [0:n] do
      if i != j && reach[i]![j]! then E := E.push (i, j)
  return { L := order.map (sorted[·]!), E := E.toList, perm }

/-- The canonical form of a box: the names of its points are their names in the space (those of
their ascriptions, if any). -/
def canon (bd : BoxD) : Canon := canonOf (bd.labels.map (·.names)) bd.edges

/-- The names matching each canonical point of the box `bd` (whose canonical form is `c`) with the
points of the other box of a morphism. -/
def canonMatchNames (bd : BoxD) (c : Canon) : Array (List String) := Id.run do
  let mut out := Array.replicate c.L.length []
  for h : i in [0:bd.labels.size] do
    out := out.set! c.perm[i]! bd.labels[i].matchNames
  return out

/-- The ascribed names of each point of the canonical form `c` of `bd` (`[]` for a point without
an ascription). -/
def canonAscribedNames (bd : BoxD) (c : Canon) : List (List String) := Id.run do
  let mut out := Array.replicate c.L.length []
  for h : i in [0:bd.labels.size] do
    let l := bd.labels[i]
    if l.ascribed then out := out.set! c.perm[i]! l.names
  return out.toList

/-- In a box that keeps its own names, those of its points must be distinct: a plain name, which
is then a name in the space, can't also be ascribed to another point. -/
def checkOwnNames (bd : BoxD) : Except Err Unit := do
  let mut seen : List String := []
  for l in bd.labels do
    for n in l.names do
      if seen.contains n then
        throw <| l.err s!"name '{n}' appears twice in this box. It is relabelled only if the \
          morphism has a type that says which space this box is; otherwise its plain names are \
          names in it."
      seen := n :: seen

end Mathlib.Tactic.Gavrilovich
