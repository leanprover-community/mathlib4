/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean
import Std.Data.HashMap
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cross-reference tag tooling

Supports review of PRs that add `@[stacks ...]`, `@[kerodon ...]`, or
`@[wikidata ...]` attributes. Two subcommands:

```sh
lake env lean --run scripts/crossref.lean snippet <db> <tag>...
lake env lean --run scripts/crossref.lean check --diff <range> --tsv <path>
```

* `snippet` fetches a one-line `(title, description)` for each given tag from
  the upstream database. Wikidata uses the `wbgetentities` API (with recovery
  when one bad QID poisons a batch); Stacks and Kerodon use the documented
  Gerby `/data/tag/<TAG>/content/statement` endpoint with a tolerant
  HTML→text strip that survives `<` inside math. Exit codes distinguish
  all-resolved (0) from missing (2) from transient network failure (3).
  When `CROSSREF_CACHE_DIR` is set, responses are memoised per
  `(database, tag)` so repeat lookups are instant.

* `check` runs after a Mathlib build (the CI lint phase), loads the
  elaborated environment via `withImportModules`, walks
  `Mathlib.CrossRef.tagExt`, and emits a TSV of every cross-reference tag
  whose source file is touched by the given git diff range. The privileged
  companion workflow consumes the TSV, fetches snippets, and constructs
  the bot comment in trusted code, so `check` never makes network calls.

`check` depends on Mathlib being built (the post-build CI runner already
satisfies this). It uses `importModules (loadExts := true)` rather than the
`withImportModules` wrapper, because the latter passes `loadExts := false`
and would leave `tagExt` empty for imported modules. The state we read
lives in regular `.olean` files (the `tagExt` persistent extension is
serialised there, not in `.olean.server`).

The LSP widget in `Mathlib/Tactic/Widget/CrossRefHover.lean` does not use
this script; it calls the fetch logic in
`Mathlib/Tactic/CrossRef/Fetch.lean` directly.
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


/-! ## `check` subcommand: enumerate cross-reference tags in a built Mathlib

Loads the elaborated Mathlib environment, walks `Mathlib.CrossRef.tagExt`, and
emits a TSV of every `@[stacks ...]` / `@[kerodon ...]` / `@[wikidata ...]`
tag whose declaration lives in a file touched by the given git diff range.

Unlike the old text-based `extract` subcommand, this one **requires Mathlib
to be built** (`.olean.server` files included) — it is meant to run in CI's
post-build lint phase, where the build is already complete. The privileged
companion workflow consumes the TSV, fetches snippets server-side, and
constructs the bot comment in trusted code, so this subcommand never makes
network calls and never decides whether a tag is "missing".

Output (one row per match, tab-separated):

```
<database>\t<tag>\t<declName>\t<file>\t<comment>
```

Exit codes:
* `0` — extraction succeeded (TSV may be empty).
* `1` — extraction error (e.g. couldn't load Mathlib, git diff failed).

Usage:
```sh
lake env lean --run scripts/crossref.lean check \
  --diff origin/master...HEAD \
  --tsv crossref-added.tsv
```
-/

open Lean Mathlib.CrossRef in
/-- Run `git diff --name-only <range>` and return the set of changed paths.
A failed `git diff` is a hard error: we deliberately do **not** turn it into
an empty change set, because that would silently pass CI on PRs whose base
hasn't been fetched. -/
def gitChangedFiles (range : String) : IO (Std.HashSet String) := do
  let output ← IO.Process.output {
    cmd := "git"
    args := #["diff", "--name-only", range]
  }
  if output.exitCode != 0 then
    throw <| .userError s!"`git diff --name-only {range}` failed (exit \
      {output.exitCode}). Make sure the base ref is fetched.\n\
      Stderr:\n{output.stderr}"
  let mut s : Std.HashSet String := ∅
  for line in output.stdout.splitOn "\n" do
    let trimmed := line.trimAscii.toString
    if !trimmed.isEmpty then s := s.insert trimmed
  return s

/-- Convert a module name like `` `Mathlib.Algebra.Foo `` to its source file
path (e.g. `"Mathlib/Algebra/Foo.lean"`). Mathlib's layout is `Foo.Bar.Baz`
→ `Foo/Bar/Baz.lean`. -/
def moduleToFilePath (m : Name) : String :=
  m.toString.replace "." "/" ++ ".lean"

open Lean Mathlib.CrossRef in
/-- Emit one TSV record per tagged declaration whose source file is in the
diff. We use `importModules (loadExts := true)` rather than the
`withImportModules` wrapper because the latter bypasses env-extension
loading and would leave `tagExt` empty for imported modules. -/
unsafe def runCheck (diffRange : String) (tsvOut : System.FilePath) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let changedFiles ← gitChangedFiles diffRange
  let env ← importModules (loadExts := true) #[`Mathlib] {} 1024
  let tagsPair : List Tag × Array (Array Tag) := PersistentEnvExtension.getState tagExt env
  let allTags := tagsPair.2.flatten.appendList tagsPair.1
  let mut rows : Array String := #[]
  for tag in allTags do
    let some mod := env.getModuleFor? tag.declName | continue
    let file := moduleToFilePath mod
    if changedFiles.contains file then
      let escapedComment := tag.comment.replace "\t" " " |>.replace "\n" " "
      rows := rows.push s!"{tag.database.name}\t{tag.tag}\t{tag.declName}\t{file}\t{escapedComment}"
  IO.FS.writeFile tsvOut (String.intercalate "\n" rows.toList ++ if rows.isEmpty then "" else "\n")
  IO.eprintln s!"Loaded {allTags.size} cross-reference tag(s) from Mathlib; \
    {rows.size} fall within the diff."
  return 0

def checkUsage : IO Unit := do
  IO.eprintln "Usage:"
  IO.eprintln "  lake env lean --run scripts/crossref.lean check --diff <range> --tsv <path>"

structure CheckArgs where
  diff : Option String := none
  tsv  : Option System.FilePath := none

def parseCheckArgs (args : List String) : IO (Option CheckArgs) := do
  let mut out : CheckArgs := {}
  let mut i := 0
  let argv := args.toArray
  while i < argv.size do
    let a := argv[i]!
    if a == "--diff" then
      if i + 1 ≥ argv.size then
        IO.eprintln "--diff expects a value"; return none
      out := { out with diff := some argv[i + 1]! }
      i := i + 2
    else if a == "--tsv" then
      if i + 1 ≥ argv.size then
        IO.eprintln "--tsv expects a value"; return none
      out := { out with tsv := some argv[i + 1]! }
      i := i + 2
    else
      IO.eprintln s!"unknown argument: {a}"; return none
  return some out

unsafe def checkMain (args : List String) : IO UInt32 := do
  match ← parseCheckArgs args with
  | none => checkUsage; return 64
  | some { diff := some range, tsv := some path } => runCheck range path
  | _ => checkUsage; return 64

/-! ## Top-level dispatch -/

def usage : IO Unit := do
  IO.eprintln "Usage: lake env lean --run scripts/crossref.lean <subcommand> <args...>"
  IO.eprintln "Subcommands:"
  IO.eprintln "  snippet <database> <tag> [<tag>...]"
  IO.eprintln "  check --diff <range> --tsv <path>"

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | "snippet" :: rest => snippetMain rest
  | "check"   :: rest => checkMain rest
  | _ => usage; return 64
