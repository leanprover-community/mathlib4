/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.Data.Json
import Std.Data.HashMap

/-!
# Cross-reference tag tooling

A single standalone script supporting review of PRs that add `@[stacks ...]`,
`@[kerodon ...]`, or `@[wikidata ...]` attributes. It exposes two subcommands:

```sh
lake env lean --run scripts/crossref.lean snippet <db> <tag>...
lake env lean --run scripts/crossref.lean extract [--file <path>...] [--diff <range>] [--db <db>]
```

* `snippet` fetches a one-line `(title, description)` for each given tag from
  the upstream database. Wikidata uses the `wbgetentities` API (with recovery
  when one bad QID poisons a batch); Stacks and Kerodon use the documented
  Gerby `/data/tag/<TAG>/content/statement` endpoint with a tolerant
  HTML→text strip that survives `<` inside math. Exit codes distinguish
  all-resolved (0) from missing (2) from transient network failure (3).
  When `CROSSREF_CACHE_DIR` is set, responses are memoised per
  `(database, tag)` so repeat lookups are instant.

* `extract` walks a `.lean` file (or the added lines of a git diff range) and
  emits TSV of every cross-reference attribute it finds, paired with the
  declaration it decorates. A byte-level scanner correctly skips string
  literals and line/block comments, handles multi-attribute blocks
  (`@[simp, stacks 01AB]`), multi-line attribute blocks, doc comments between
  attribute and declaration, and modifier keywords (`private`,
  `noncomputable`, …). Signatures are collapsed to one line for downstream
  consumption.

The script imports only Lean core (plus `Std.Data.HashMap` for batching), so
it can be invoked directly with `lake env lean --run` without any Mathlib
build. The CI workflow `crossref_review.yml` and the LSP widget in
`Mathlib/Tactic/Widget/CrossRefHover.lean` drive it.
-/

open Lean

/-! ## Shared: the `Database` enum -/

/-- The three supported cross-reference databases.

When adding a new case, also update each of these:
- `Database.ofString?`, `Database.name`, `Database.fetch`, `gerbyBase?` below;
- the `Mathlib.CrossRef.Database` enum in `Mathlib/Tactic/CrossRef/Fetch.lean`
  along with its `databaseURL` / `databaseLabel` and `fetchSnippet` dispatch,
  plus the parser / attribute registration / `#X_tags` trace command in
  `Mathlib/Tactic/CrossRefAttribute.lean`;
- the `pretty` dict in `mathlib-ci`'s `scripts/crossref_review/crossref-pr-comment.py`.

Within this file, the `ofString?_name` roundtrip theorem catches drift between
`name` and `ofString?` at compile time. -/
inductive Database where
  | wikidata
  | stacks
  | kerodon
  deriving BEq, Inhabited

/-- Parse the database argument from a CLI / attribute keyword. -/
def Database.ofString? : String → Option Database
  | "wikidata" => some .wikidata
  | "stacks"   => some .stacks
  | "kerodon"  => some .kerodon
  | _          => none

/-- Short name used in cache filenames, attribute keywords, and error messages. -/
def Database.name : Database → String
  | .wikidata => "wikidata"
  | .stacks   => "stacks"
  | .kerodon  => "kerodon"

/-- `Database.name` and `Database.ofString?` roundtrip. This catches at compile time
any drift between the two when a new case is added to `Database`. -/
theorem Database.ofString?_name (d : Database) : Database.ofString? d.name = some d := by
  cases d <;> rfl

/-! ## `snippet` subcommand: fetch one-line snippets

For each given tag, fetch a short label/description from the upstream database
and write one TSV record per tag to stdout:

```
<tag>\t<title>\t<description>
<tag>\tERROR\tmissing
<tag>\tERROR\tnetwork
```
-/

/-- Outcome of fetching the snippet for a single tag. -/
inductive Result where
  | ok (title : String) (snippet : String)
  | missing
  | network (reason : String)

/-- The `User-Agent` curl sends. Wikidata's API will throttle anonymous clients
without one, so we identify ourselves. -/
def userAgent : String :=
  "mathlib-crossref-bot/1 (https://github.com/leanprover-community/mathlib4)"

/-- Make a GET request and return `(http-status, body)`. Status is `0` if curl
itself failed. We append the HTTP status to the body via `-w '\n%{http_code}'`
and recover it from the final line — that avoids juggling a temp file. -/
def fetchUrl (url : String) : IO (Nat × String) := do
  let output ← IO.Process.output {
    cmd := "curl"
    args := #["-sSL", "--max-time", "10", "-A", userAgent,
              "-w", "\n%{http_code}", url]
  }
  if output.exitCode != 0 then return (0, "")
  let parts := output.stdout.splitOn "\n"
  match parts.reverse with
  | last :: rest =>
    let body := "\n".intercalate rest.reverse
    let status := last.trimAscii.toString.toNat?.getD 0
    return (status, body)
  | [] => return (0, "")

/-- Replace any tab, newline, or carriage return with a single space and collapse
runs of whitespace. The TSV output is one record per line, so we have to keep
each field on one line; markdown-table escaping is a downstream concern. -/
def flattenWhitespace (s : String) : String :=
  let go : Char → (String × Bool) → (String × Bool) := fun c (acc, prevSpace) =>
    let isWs := c == ' ' || c == '\t' || c == '\n' || c == '\r'
    if isWs then
      if prevSpace || acc.isEmpty then (acc, true)
      else (acc.push ' ', true)
    else
      (acc.push c, false)
  let (out, _) := s.toList.foldl (fun st c => go c st) ("", false)
  out.trimAscii.toString

/-- Best-effort HTML→text: drop everything from `<x` (where `x` is a letter,
`/`, or `!`) up to and including the matching `>`, decode a handful of
entities, collapse whitespace. The first-character check matters because
the Stacks/Kerodon snippets embed LaTeX math like `0 < 1`, and a dumber
strip-everything-between-angle-brackets pass would eat the rest of the line. -/
def stripHtml (html : String) : String :=
  let chars := html.toList
  let rec go : List Char → Bool → String → String
    | [], _, acc => acc
    | '<' :: rest, false, acc =>
      match rest with
      | c :: _ =>
        if c.isAlpha || c == '/' || c == '!' then
          go rest true acc
        else
          go rest false (acc.push '<')
      | [] => acc.push '<'
    | '>' :: rest, true, acc => go rest false acc
    | _ :: rest, true,  acc => go rest true  acc
    | c :: rest, false, acc => go rest false (acc.push c)
  let raw := go chars false ""
  let decoded := raw
    |>.replace "&nbsp;" " "
    |>.replace "&amp;" "&"
    |>.replace "&lt;" "<"
    |>.replace "&gt;" ">"
    |>.replace "&quot;" "\""
    |>.replace "&#39;" "'"
  flattenWhitespace decoded

/-- Walk a path of object keys in a `Json` value, returning the leaf as a string
if every step succeeds and the leaf is a string. -/
def jsonStrPath? (j : Json) (path : List String) : Option String :=
  let rec go (cur : Json) : List String → Option String
    | [] => cur.getStr?.toOption
    | k :: rest =>
      match cur.getObjVal? k with
      | .ok next => go next rest
      | .error _ => none
  go j path

/-- Take elements of a list in fixed-size chunks. -/
partial def chunkList (n : Nat) (xs : List α) : List (List α) :=
  if xs.isEmpty then []
  else
    let k := n.max 1
    (xs.take k) :: chunkList n (xs.drop k)

/-- Locate the per-tag cache file, if `CROSSREF_CACHE_DIR` is set. -/
def cacheFile? (db : Database) (tag : String) : IO (Option System.FilePath) := do
  match ← IO.getEnv "CROSSREF_CACHE_DIR" with
  | none => return none
  | some dir =>
    let path : System.FilePath := dir
    IO.FS.createDirAll path
    return some (path / s!"{db.name}-{tag}.json")

/-- Read a cached raw response body, if one exists. -/
def cacheLoad (db : Database) (tag : String) : IO (Option String) := do
  match ← cacheFile? db tag with
  | none => return none
  | some f =>
    if ← f.pathExists then
      return some (← IO.FS.readFile f)
    else
      return none

/-- Save a raw response body to the cache. Empty body marks "known missing". -/
def cacheStore (db : Database) (tag : String) (body : String) : IO Unit := do
  match ← cacheFile? db tag with
  | none => return ()
  | some f => IO.FS.writeFile f body

/-! ### Wikidata -/

/-- Wikidata's `wbgetentities` endpoint supports up to 50 IDs per request; we
batch to amortise the HTTP cost. -/
def wikidataBatchSize : Nat := 50

/-- Pull the English label and description out of one entity payload. -/
def wikidataResultOf (ent : Json) : Result :=
  match ent.getObjVal? "missing" with
  | .ok _ => .missing
  | _ =>
    let label := jsonStrPath? ent ["labels", "en", "value"] |>.getD ""
    let desc  := jsonStrPath? ent ["descriptions", "en", "value"] |>.getD ""
    .ok (flattenWhitespace label) (flattenWhitespace desc)

/-- Outcome of inspecting one parsed Wikidata response. -/
inductive WikidataParse where
  /-- Per-QID results for every input id. -/
  | results (rs : List (String × Result))
  /-- Wikidata refused the whole batch because one specific id was malformed
  (`no-such-entity`). We pull that id out, mark it missing, and retry the rest. -/
  | retryWithout (badId : String)
  /-- Transient failure (`maxlag`, `ratelimit`, …) — every id maps to `network`. -/
  | transient (reason : String)

/-- Inspect a parsed `wbgetentities` response. Wikidata returns a per-batch
top-level `error` rather than a per-id flag when any single id is malformed,
so we have to read `error.id` and retry without it. -/
def parseWikidataResponse (qids : List String) (json : Json) : WikidataParse :=
  match json.getObjVal? "error" with
  | .ok err =>
    let code := jsonStrPath? err ["code"] |>.getD ""
    let info := jsonStrPath? err ["info"] |>.getD code
    if code == "no-such-entity" then
      match jsonStrPath? err ["id"] with
      | some bad => .retryWithout bad
      | none => .results (qids.map fun q => (q, .missing))
    else
      .transient s!"wikidata {code}: {info}"
  | _ =>
    match json.getObjVal? "entities" with
    | .error _ => .transient "wikidata: no `entities` field"
    | .ok entities =>
      .results <| qids.map fun q =>
        match entities.getObjVal? q with
        | .error _ => (q, .missing)
        | .ok ent => (q, wikidataResultOf ent)

/-- Fetch one batch of QIDs from the live Wikidata API. Retries with the
offending id removed whenever Wikidata refuses the whole batch over a single
malformed identifier. -/
partial def fetchWikidataBatch (qids : List String) : IO (List (String × Result)) := do
  if qids.isEmpty then return []
  let ids := "|".intercalate qids
  -- `maxlag` is intended for bots performing writes; reads should not throttle.
  let url := s!"https://www.wikidata.org/w/api.php?action=wbgetentities&ids={ids}\
              &languages=en&props=labels%7Cdescriptions&format=json"
  let (status, body) ← fetchUrl url
  if status != 200 then
    return qids.map fun q => (q, .network s!"wikidata HTTP {status}")
  match Json.parse body with
  | .error e => return qids.map fun q => (q, .network s!"wikidata json: {e}")
  | .ok json =>
    match parseWikidataResponse qids json with
    | .transient r => return qids.map fun q => (q, .network r)
    | .retryWithout bad =>
      let rest := qids.filter (· != bad)
      let restResults ← fetchWikidataBatch rest
      cacheStore .wikidata bad ""
      let table : Std.HashMap String Result :=
        restResults.foldl (fun m (k, v) => m.insert k v) ∅
      return qids.map fun q =>
        if q == bad then (q, .missing)
        else (q, table.getD q (.network "wikidata: lost from response"))
    | .results results =>
      if let .ok entities := json.getObjVal? "entities" then
        for (q, _) in results do
          if let .ok ent := entities.getObjVal? q then
            cacheStore .wikidata q ent.compress
      for (q, r) in results do
        match r with
        | .missing => cacheStore .wikidata q ""
        | _ => pure ()
      return results

/-- Public Wikidata fetch: serve cached entries directly, batch the rest. -/
def fetchWikidata (qids : List String) : IO (List (String × Result)) := do
  let mut cached : Std.HashMap String Result := ∅
  let mut todo : Array String := #[]
  for q in qids do
    match ← cacheLoad .wikidata q with
    | some body =>
      if body.isEmpty then
        cached := cached.insert q .missing
      else
        match Json.parse body with
        | .ok ent => cached := cached.insert q (wikidataResultOf ent)
        | .error _ => todo := todo.push q
    | none => todo := todo.push q
  let mut fresh : Std.HashMap String Result := ∅
  for batch in chunkList wikidataBatchSize todo.toList do
    for (q, r) in (← fetchWikidataBatch batch) do
      fresh := fresh.insert q r
  return qids.map fun q =>
    if let some r := cached[q]? then (q, r)
    else if let some r := fresh[q]? then (q, r)
    else (q, .network "missing from response")

/-! ### Stacks / Kerodon (Gerby) -/

/-- The base URL for a Gerby-style database. -/
def Database.gerbyBase? : Database → Option String
  | .stacks   => some "https://stacks.math.columbia.edu"
  | .kerodon  => some "https://kerodon.net"
  | .wikidata => none

/-- Return the substring of `s` after the first occurrence of `needle`,
or `none` if `needle` is absent. -/
def afterFirst? (s needle : String) : Option String :=
  let parts := s.splitOn needle
  match parts with
  | _ :: rest@(_ :: _) => some (needle.intercalate rest)
  | _ => none

/-- Take everything up to (but not including) the first occurrence of `c`. -/
def takeUntilChar (s : String) (c : Char) : String :=
  String.ofList (s.toList.takeWhile (· != c))

/-- Pull the environment type (`Lemma`, `Proposition`, …) and reference number
from the `/content/statement` HTML. Both Stacks and Kerodon wrap each tag in
`<article class="env-{TYPE}" id="{TAG}">` and lead with
`<a ...>Lemma <span data-tag="...">14.32.3</span>.</a>`. -/
def parseGerbyTitle (html : String) : String :=
  let envType :=
    match afterFirst? html "class=\"env-" with
    | none => ""
    | some rest => takeUntilChar rest '"'
  let reference :=
    match afterFirst? html "data-tag=\"" with
    | none => ""
    | some afterAttr =>
      match afterFirst? afterAttr ">" with
      | none => ""
      | some inside => takeUntilChar inside '<'
  let cap := envType.capitalize
  flattenWhitespace (if reference.isEmpty then cap else s!"{cap} {reference}")

/-- Fetch one tag from a Gerby-based database. The `/content/statement`
endpoint is defined for every tag (the `/structure` endpoint only resolves for
nodes with children) and gives us the rendered statement directly. -/
def fetchGerby (db : Database) (tag : String) : IO Result := do
  if let some cached ← cacheLoad db tag then
    if cached.isEmpty then return .missing
    let title := parseGerbyTitle cached
    let snippet := stripHtml cached
    return .ok title snippet
  let some base := db.gerbyBase? | return .network s!"{db.name}: no Gerby base"
  let url := s!"{base}/data/tag/{tag}/content/statement"
  let (status, body) ← fetchUrl url
  if status != 200 then
    return .network s!"{db.name} HTTP {status}"
  if body.trimAscii.toString == "This tag does not exist." then
    cacheStore db tag ""
    return .missing
  cacheStore db tag body
  let title := parseGerbyTitle body
  let snippet := stripHtml body
  if title.isEmpty && snippet.isEmpty then
    return .network s!"{db.name}: could not parse statement"
  return .ok title snippet

def fetchGerbyAll (db : Database) (tags : List String) : IO (List (String × Result)) :=
  tags.mapM fun t => return (t, ← fetchGerby db t)

/-! ### Top-level dispatch for `snippet` -/

def Database.fetch (db : Database) (tags : List String) : IO (List (String × Result)) :=
  match db with
  | .wikidata => fetchWikidata tags
  | .stacks   => fetchGerbyAll db tags
  | .kerodon  => fetchGerbyAll db tags

def Result.emit (tag : String) : Result → IO Unit
  | .ok title snippet => IO.println s!"{tag}\t{title}\t{snippet}"
  | .missing          => IO.println s!"{tag}\tERROR\tmissing"
  | .network reason   => IO.println s!"{tag}\tERROR\tnetwork: {reason}"

def snippetUsage : IO Unit := do
  IO.eprintln "Usage: lake env lean --run scripts/crossref.lean snippet <database> <tag> [<tag>...]"
  IO.eprintln "  <database>: wikidata | stacks | kerodon"

def snippetMain (args : List String) : IO UInt32 := do
  match args with
  | dbStr :: tag :: rest =>
    let some db := Database.ofString? dbStr
      | snippetUsage; return 64
    let results ← db.fetch (tag :: rest)
    let mut sawMissing := false
    let mut sawNetwork := false
    for (t, r) in results do
      r.emit t
      match r with
      | .missing    => sawMissing := true
      | .network _  => sawNetwork := true
      | _           => pure ()
    if sawMissing then return 2
    if sawNetwork then return 3
    return 0
  | _ => snippetUsage; return 64

/-! ## `extract` subcommand: find cross-reference attributes

For one or more Lean source files (or for the added lines of a git diff range),
emit one TSV record per `@[stacks ...]`, `@[kerodon ...]`, or `@[wikidata ...]`
attribute found:

```
<database>\t<file>\t<line>\t<tag>\t<comment>\t<decl_kind>\t<decl_name>\t<sig_first_line>
```

Implementation: we scan each file character-by-character, tracking whether we
are inside a string literal or a line/block comment so that an `@[` inside
those contexts is correctly ignored. When we exit a real `@[...]` block, we
inspect its contents for `wikidata`/`stacks`/`kerodon` clauses, then scan
forward past doc comments, further attribute blocks, and modifier keywords
(`private`, `noncomputable`, …) to find the declaration the attribute decorates
and capture its signature.

This is deliberately a text-only tool: no Lean elaboration runs, no Mathlib
build is required. That's what lets the companion CI workflow operate on PR
files as data, without executing PR code under a privileged GitHub token.
-/

/-! ### Tokenisation -/

/-- Reader state. We don't try to fully tokenise the file — we only need to
distinguish "outside everything" from "inside a context that can hide an `@[`",
so that `@[wikidata Q42]` appearing in a string literal or a comment is
correctly ignored. -/
inductive Mode where
  /-- Outside strings/comments. -/
  | normal
  /-- Inside a string literal `"…"`; the `Bool` is "previous char was `\`". -/
  | str (escaping : Bool)
  /-- Inside a `-- …` line comment. -/
  | lineComment
  /-- Inside a `/- … -/` block comment of the given nesting depth. -/
  | blockComment (depth : Nat)
  deriving BEq

/-- Source span by 1-based `(line, column)` offsets. -/
structure SrcPos where
  line : Nat
  col : Nat
  deriving Inhabited

/-- One `@[...]` block found in a source file. -/
structure AttrBlock where
  /-- Position of the `@` that opens the block. -/
  start : SrcPos
  /-- Byte offset where the closing `]` ends. Used as the starting point for
  the "find the following declaration" pass. -/
  endIdx : Nat
  /-- The text between `@[` and `]` (not including the brackets themselves). -/
  body : String
  deriving Inhabited

/-- Convert a byte slice of `src` back into a `String`, returning `""` on
malformed UTF-8 (which should not happen for our inputs). -/
def byteSlice (src : String) (lo hi : Nat) : String :=
  let bs := src.toUTF8
  let lo := min lo bs.size
  let hi := min hi bs.size
  String.fromUTF8? (bs.extract lo hi) |>.getD ""

/-- Scan the source text and return every top-level `@[...]` attribute block,
correctly skipping ones that appear inside strings or comments. We work over
UTF-8 bytes: every interesting lexeme (`@`, `[`, `]`, `"`, `-`, `/`, `\n`) is
ASCII, so byte-level scanning is correct for Unicode-rich Mathlib files. -/
partial def collectAttrBlocks (src : String) : Array AttrBlock := Id.run do
  let bs := src.toUTF8
  let stepPosByte (p : SrcPos) (b : UInt8) : SrcPos :=
    if b == 0x0a then { line := p.line + 1, col := 1 } else { p with col := p.col + 1 }
  let mut out : Array AttrBlock := #[]
  let mut i : Nat := 0
  let mut pos : SrcPos := { line := 1, col := 1 }
  let mut mode : Mode := .normal
  while i < bs.size do
    let b := bs.get! i
    let nextB? : Option UInt8 := if i + 1 < bs.size then some (bs.get! (i + 1)) else none
    match mode with
    | .normal =>
      if b == 0x22 then
        mode := .str false; i := i + 1; pos := stepPosByte pos b
      else if b == 0x2d && nextB? == some 0x2d then
        mode := .lineComment; i := i + 2; pos := { pos with col := pos.col + 2 }
      else if b == 0x2f && nextB? == some 0x2d then
        mode := .blockComment 1; i := i + 2; pos := { pos with col := pos.col + 2 }
      else if b == 0x40 && nextB? == some 0x5b then
        let openPos := pos
        let bodyStart := i + 2
        let mut j := bodyStart
        let mut innerPos : SrcPos := { pos with col := pos.col + 2 }
        let mut depth : Nat := 1
        let mut innerMode : Mode := .normal
        while depth > 0 && j < bs.size do
          let bb := bs.get! j
          let nb? : Option UInt8 := if j + 1 < bs.size then some (bs.get! (j + 1)) else none
          match innerMode with
          | .normal =>
            if bb == 0x22 then
              innerMode := .str false; j := j + 1; innerPos := stepPosByte innerPos bb
            else if bb == 0x2d && nb? == some 0x2d then
              innerMode := .lineComment; j := j + 2
              innerPos := { innerPos with col := innerPos.col + 2 }
            else if bb == 0x2f && nb? == some 0x2d then
              innerMode := .blockComment 1; j := j + 2
              innerPos := { innerPos with col := innerPos.col + 2 }
            else if bb == 0x5b then
              depth := depth + 1; j := j + 1; innerPos := stepPosByte innerPos bb
            else if bb == 0x5d then
              depth := depth - 1; j := j + 1; innerPos := stepPosByte innerPos bb
            else
              j := j + 1; innerPos := stepPosByte innerPos bb
          | .str esc =>
            if esc then
              innerMode := .str false; j := j + 1; innerPos := stepPosByte innerPos bb
            else if bb == 0x5c then
              innerMode := .str true; j := j + 1; innerPos := stepPosByte innerPos bb
            else if bb == 0x22 then
              innerMode := .normal; j := j + 1; innerPos := stepPosByte innerPos bb
            else
              j := j + 1; innerPos := stepPosByte innerPos bb
          | .lineComment =>
            if bb == 0x0a then innerMode := .normal
            j := j + 1; innerPos := stepPosByte innerPos bb
          | .blockComment d =>
            if bb == 0x2d && nb? == some 0x2f then
              innerMode := if d == 1 then .normal else .blockComment (d - 1)
              j := j + 2; innerPos := { innerPos with col := innerPos.col + 2 }
            else if bb == 0x2f && nb? == some 0x2d then
              innerMode := .blockComment (d + 1)
              j := j + 2; innerPos := { innerPos with col := innerPos.col + 2 }
            else
              j := j + 1; innerPos := stepPosByte innerPos bb
        if depth == 0 then
          let body := byteSlice src bodyStart (j - 1)
          out := out.push { start := openPos, endIdx := j, body }
          i := j; pos := innerPos; mode := .normal
        else
          i := bs.size
      else
        i := i + 1; pos := stepPosByte pos b
    | .str esc =>
      if esc then mode := .str false
      else if b == 0x5c then mode := .str true
      else if b == 0x22 then mode := .normal
      i := i + 1; pos := stepPosByte pos b
    | .lineComment =>
      if b == 0x0a then mode := .normal
      i := i + 1; pos := stepPosByte pos b
    | .blockComment d =>
      if b == 0x2d && nextB? == some 0x2f then
        mode := if d == 1 then .normal else .blockComment (d - 1)
        i := i + 2; pos := { pos with col := pos.col + 2 }
      else if b == 0x2f && nextB? == some 0x2d then
        mode := .blockComment (d + 1)
        i := i + 2; pos := { pos with col := pos.col + 2 }
      else
        i := i + 1; pos := stepPosByte pos b
  return out

/-! ### Parsing the contents of an `@[...]` block -/

/-- A cross-reference clause found inside an `@[...]` block. -/
structure Clause where
  database : Database
  tag : String
  comment : String
  deriving Inhabited

/-- Split the body of an `@[...]` block on top-level commas. We don't track
balanced brackets inside the body because Lean attribute syntax doesn't allow
unbalanced `[`/`]` within an attribute instance; commas inside string literals
are handled. -/
def splitAttrInstances (body : String) : List String :=
  let chars := body.toList
  let rec go (cs : List Char) (mode : Mode) (acc : String) (out : List String) : List String :=
    match cs with
    | [] => (acc :: out).reverse
    | c :: rest =>
      match mode with
      | .normal =>
        match c, rest with
        | ',', _ => go rest .normal "" (acc :: out)
        | '"', _ => go rest (.str false) (acc.push c) out
        | _, _ => go rest .normal (acc.push c) out
      | .str esc =>
        if esc then go rest (.str false) (acc.push c) out
        else if c == '\\' then go rest (.str true) (acc.push c) out
        else if c == '"' then go rest .normal (acc.push c) out
        else go rest (.str false) (acc.push c) out
      | _ => go rest mode (acc.push c) out
  go chars .normal "" []

/-- Strip a leading run of letters from `s`, returning `(word, rest)`. -/
def takeIdent (s : String) : String × String :=
  let cs := s.toList
  let ident := String.ofList (cs.takeWhile (·.isAlpha))
  let rest := String.ofList (cs.dropWhile (·.isAlpha))
  (ident, rest)

/-- Strip a leading run of `Char.isAlphanum` from `s`. -/
def takeTag (s : String) : String × String :=
  let cs := s.toList
  let tag := String.ofList (cs.takeWhile (·.isAlphanum))
  let rest := String.ofList (cs.dropWhile (·.isAlphanum))
  (tag, rest)

/-- If a leading `"…"` is present in `s`, return its contents and the remainder
of the string. We honour `\"` and `\\` escapes. -/
def takeString (s : String) : Option (String × String) :=
  let cs := s.toList
  match cs with
  | '"' :: rest =>
    let rec go : List Char → String → Option (String × List Char)
      | [], _ => none
      | '\\' :: c :: rest, acc => go rest (acc.push c)
      | '"' :: rest, acc => some (acc, rest)
      | c :: rest, acc => go rest (acc.push c)
    match go rest "" with
    | none => none
    | some (contents, rest') => some (contents, String.ofList rest')
  | _ => none

/-- Try to parse one attribute instance as a cross-reference clause. The leading
keyword is matched against `Database.ofString?`, so adding a new database to
the `Database` enum automatically picks it up here. -/
def parseClause (attrText : String) : Option Clause :=
  let trimmed := attrText.trimAscii.toString
  let (kw, rest) := takeIdent trimmed
  match Database.ofString? kw with
  | none => none
  | some db =>
    let rest := rest.trimAsciiStart.toString
    let (tag, rest) := takeTag rest
    if tag.isEmpty then none
    else
      let rest := rest.trimAsciiStart.toString
      let comment := (takeString rest).map (·.1) |>.getD ""
      some { database := db, tag, comment }

/-! ### Finding the declaration that follows an attribute block -/

/-- Lean declaration kinds we care about. -/
def declKeywords : List String :=
  ["theorem", "lemma", "def", "instance", "abbrev", "structure", "class", "opaque"]

/-- Modifier keywords that may precede the declaration keyword. -/
def modifierKeywords : List String :=
  ["private", "protected", "noncomputable", "public", "scoped", "local",
   "partial", "nonrec", "unsafe", "axiom"]

/-- Convert a substring of `src` (by byte range) back into a string. -/
def utf8Slice (src : String) (lo hi : Nat) : String :=
  let bs := src.toUTF8
  let lo := min lo bs.size
  let hi := min hi bs.size
  match String.fromUTF8? (bs.extract lo hi) with
  | some s => s
  | none => ""

/-- Skip whitespace, line comments, block comments, doc comments, and other
`@[...]` attribute blocks. Returns the byte index in `src` of the next
non-trivial token, or `none` if EOF. -/
partial def skipTrivia (src : String) (start : Nat) : Nat :=
  let bs := src.toUTF8
  let rec go (i : Nat) : Nat :=
    if i ≥ bs.size then i
    else
      let c := bs.get! i
      if c == 0x20 || c == 0x09 || c == 0x0a || c == 0x0d then go (i + 1)
      else if c == 0x2d && i + 1 < bs.size && bs.get! (i + 1) == 0x2d then
        let rec skipLine (j : Nat) :=
          if j ≥ bs.size then j
          else if bs.get! j == 0x0a then j + 1
          else skipLine (j + 1)
        go (skipLine (i + 2))
      else if c == 0x2f && i + 1 < bs.size && bs.get! (i + 1) == 0x2d then
        let rec skipBlock (j : Nat) (depth : Nat) : Nat :=
          if j ≥ bs.size then j
          else if j + 1 < bs.size && bs.get! j == 0x2d && bs.get! (j + 1) == 0x2f then
            if depth == 1 then j + 2
            else skipBlock (j + 2) (depth - 1)
          else if j + 1 < bs.size && bs.get! j == 0x2f && bs.get! (j + 1) == 0x2d then
            skipBlock (j + 2) (depth + 1)
          else skipBlock (j + 1) depth
        go (skipBlock (i + 2) 1)
      else if c == 0x40 && i + 1 < bs.size && bs.get! (i + 1) == 0x5b then
        let rec skipAttr (j : Nat) (depth : Nat) (inStr : Bool) (esc : Bool) : Nat :=
          if j ≥ bs.size then j
          else
            let d := bs.get! j
            if inStr then
              if esc then skipAttr (j + 1) depth inStr false
              else if d == 0x5c then skipAttr (j + 1) depth inStr true
              else if d == 0x22 then skipAttr (j + 1) depth false false
              else skipAttr (j + 1) depth true false
            else if d == 0x22 then skipAttr (j + 1) depth true false
            else if d == 0x5b then skipAttr (j + 1) (depth + 1) false false
            else if d == 0x5d then
              if depth == 1 then j + 1 else skipAttr (j + 1) (depth - 1) false false
            else skipAttr (j + 1) depth false false
        go (skipAttr (i + 2) 1 false false)
      else i
  go start

/-- Read a leading identifier-like word (letters / digits / `_` / `'`). -/
def readWord (src : String) (start : Nat) : String × Nat :=
  let bs := src.toUTF8
  let rec go (i : Nat) (acc : Array UInt8) : String × Nat :=
    if i ≥ bs.size then
      (String.fromUTF8? (.mk acc) |>.getD "", i)
    else
      let c := bs.get! i
      if (c ≥ 0x41 && c ≤ 0x5a) || (c ≥ 0x61 && c ≤ 0x7a) ||
         (c ≥ 0x30 && c ≤ 0x39) || c == 0x5f || c == 0x27 then
        go (i + 1) (acc.push c)
      else
        (String.fromUTF8? (.mk acc) |>.getD "", i)
  go start #[]

/-- A located declaration header that an attribute block decorates. -/
structure DeclHeader where
  kind : String
  name : String
  sigFirstLine : String
  deriving Inhabited

/-- Read a Lean identifier (letters / digits / `_` / `'` / namespace `.`). -/
def readIdent (src : String) (start : Nat) : String × Nat :=
  let bs := src.toUTF8
  let rec go (i : Nat) (acc : Array UInt8) : String × Nat :=
    if i ≥ bs.size then
      (String.fromUTF8? (.mk acc) |>.getD "", i)
    else
      let c := bs.get! i
      if (c ≥ 0x41 && c ≤ 0x5a) || (c ≥ 0x61 && c ≤ 0x7a) ||
         (c ≥ 0x30 && c ≤ 0x39) || c == 0x5f || c == 0x27 || c == 0x2e then
        go (i + 1) (acc.push c)
      else
        (String.fromUTF8? (.mk acc) |>.getD "", i)
  go start #[]

/-- Skip past modifier keywords starting at `start`. -/
partial def skipModifiers (src : String) (start : Nat) : Nat :=
  let i := skipTrivia src start
  let (w, j) := readWord src i
  if modifierKeywords.contains w then skipModifiers src j else i

/-- Collapse a multi-line signature into a single line for the TSV output. -/
def collapseSignature (s : String) : String :=
  let cs := s.toList
  let collapse : Char → (String × Bool) → (String × Bool) := fun c (acc, prevWs) =>
    let isWs := c == ' ' || c == '\t' || c == '\n' || c == '\r'
    if isWs then
      if prevWs || acc.isEmpty then (acc, true)
      else (acc.push ' ', true)
    else (acc.push c, false)
  let (out, _) := cs.foldl (fun s c => collapse c s) ("", false)
  out.trimAscii.toString

/-- Locate the declaration that an attribute block at `startIdx` decorates. -/
def findDecl (src : String) (startIdx : Nat) : Option DeclHeader := Id.run do
  let i := skipModifiers src startIdx
  let (kw, j) := readWord src i
  if !declKeywords.contains kw then return none
  let k := skipTrivia src j
  let (name, _) := readIdent src k
  if name.isEmpty then return none
  let bs := src.toUTF8
  let rec findEnd (p : Nat) : Nat :=
    if p ≥ bs.size then p
    else if p + 1 < bs.size && bs.get! p == 0x3a && bs.get! (p + 1) == 0x3d then p
    else if p + 4 < bs.size
        && bs.get! p == 0x77 && bs.get! (p + 1) == 0x68 && bs.get! (p + 2) == 0x65
        && bs.get! (p + 3) == 0x72 && bs.get! (p + 4) == 0x65 then p
    else if p + 1 < bs.size && bs.get! p == 0x0a && bs.get! (p + 1) == 0x0a then p
    else findEnd (p + 1)
  let endIdx := findEnd i
  let sig := utf8Slice src i endIdx
  some { kind := kw, name, sigFirstLine := collapseSignature sig }

/-! ### Driving the extraction -/

/-- One emitted record. -/
structure Record where
  database : Database
  file : String
  line : Nat
  tag : String
  comment : String
  declKind : String
  declName : String
  sigFirstLine : String

/-- TSV-friendly escape: replace tabs / newlines / carriage returns with a
single space. -/
def tsvEscape (s : String) : String :=
  collapseSignature s

def Record.emit (r : Record) : IO Unit := do
  IO.println <| "\t".intercalate [
    r.database.name, r.file, toString r.line, r.tag, tsvEscape r.comment,
    r.declKind, r.declName, tsvEscape r.sigFirstLine]

/-- Extract all records from a single file. -/
def extractFromFile (path : String) : IO (Array Record) := do
  let src ← IO.FS.readFile path
  let blocks := collectAttrBlocks src
  let mut out : Array Record := #[]
  for block in blocks do
    let clauses := (splitAttrInstances block.body).filterMap parseClause
    if clauses.isEmpty then continue
    let header := (findDecl src block.endIdx).getD
      { kind := "?", name := "?", sigFirstLine := "?" }
    for cl in clauses do
      out := out.push {
        database := cl.database
        file := path
        line := block.start.line
        tag := cl.tag
        comment := cl.comment
        declKind := header.kind
        declName := header.name
        sigFirstLine := header.sigFirstLine
      }
  return out

/-! ### Diff mode -/

/-- One `(file, addedLines)` group parsed from `git diff --unified=0` output. -/
structure DiffHunks where
  file : String
  addedLines : Array (Nat × Nat)

/-- Parse `git diff --unified=0` output. -/
def parseDiff (out : String) : Array DiffHunks := Id.run do
  let mut result : Array DiffHunks := #[]
  let mut current : Option DiffHunks := none
  for line in out.splitOn "\n" do
    if line.startsWith "+++ b/" then
      if let some d := current then result := result.push d
      current := some { file := (line.drop 6).toString, addedLines := #[] }
    else if line.startsWith "@@" then
      let after :=
        line.splitOn "+" |>.tail? |>.getD [] |>.headD ""
      let spec := after.splitOn " " |>.headD ""
      let parts := spec.splitOn ","
      let firstLine := (parts.headD "0").toNat?.getD 0
      let count := (parts.tail?.getD [] |>.headD "1").toNat?.getD 1
      if let some d := current then
        current := some { d with addedLines := d.addedLines.push (firstLine, count) }
    else continue
  if let some d := current then result := result.push d
  return result

/-- Run `git diff --unified=0 <range> -- '*.lean'` and parse the result. -/
def gitDiffLeanFiles (range : String) : IO (Array DiffHunks) := do
  let output ← IO.Process.output {
    cmd := "git"
    args := #["diff", "--unified=0", range, "--", "*.lean"]
  }
  if output.exitCode != 0 then
    IO.eprintln s!"git diff failed:\n{output.stderr}"
    return #[]
  return parseDiff output.stdout

def recordInHunks (hunks : Array (Nat × Nat)) (line : Nat) : Bool :=
  hunks.any fun (start, count) =>
    line ≥ start && line < start + (max count 1)

/-! ### CLI for `extract` -/

def extractUsage : IO Unit := do
  IO.eprintln "Usage:"
  IO.eprintln "  lake env lean --run scripts/crossref.lean extract --file <path>..."
  IO.eprintln "  lake env lean --run scripts/crossref.lean extract --diff <range> [--db <database>]"

def parseExtractArgs (args : List String) :
    IO (Option (Array (String × Option (Array (Nat × Nat))) × Option String)) := do
  let mut files : Array (String × Option (Array (Nat × Nat))) := #[]
  let mut dbFilter : Option String := none
  let mut i := 0
  let argv := args.toArray
  while i < argv.size do
    let a := argv[i]!
    if a == "--file" then
      if i + 1 ≥ argv.size then
        IO.eprintln "--file expects a path"; return none
      files := files.push (argv[i + 1]!, none)
      i := i + 2
    else if a == "--diff" then
      if i + 1 ≥ argv.size then
        IO.eprintln "--diff expects a range"; return none
      let hunks ← gitDiffLeanFiles argv[i + 1]!
      for h in hunks do files := files.push (h.file, some h.addedLines)
      i := i + 2
    else if a == "--db" then
      if i + 1 ≥ argv.size then
        IO.eprintln "--db expects a value"; return none
      dbFilter := some argv[i + 1]!
      i := i + 2
    else
      IO.eprintln s!"unknown argument: {a}"; return none
  return some (files, dbFilter)

def extractMain (args : List String) : IO UInt32 := do
  match ← parseExtractArgs args with
  | none => extractUsage; return 64
  | some (files, dbFilter) =>
    if files.isEmpty then extractUsage; return 64
    for (path, lineFilter) in files do
      let exists? ← System.FilePath.pathExists path
      if !exists? then
        IO.eprintln s!"skipping non-existent file: {path}"
        continue
      let records ← extractFromFile path
      for r in records do
        if let some db := dbFilter then if r.database.name != db then continue
        match lineFilter with
        | none => r.emit
        | some hunks => if recordInHunks hunks r.line then r.emit
    return 0

/-! ## Top-level dispatch -/

def usage : IO Unit := do
  IO.eprintln "Usage: lake env lean --run scripts/crossref.lean <subcommand> <args...>"
  IO.eprintln "Subcommands:"
  IO.eprintln "  snippet <database> <tag> [<tag>...]"
  IO.eprintln "  extract [--file <path>...] [--diff <range>] [--db <database>]"

def main (args : List String) : IO UInt32 := do
  match args with
  | "snippet" :: rest => snippetMain rest
  | "extract" :: rest => extractMain rest
  | _ => usage; return 64
