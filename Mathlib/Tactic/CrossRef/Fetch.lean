/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import Lean.Data.Json
public import Mathlib.Init

/-!
# Fetching cross-reference snippets

The Mathlib counterpart of `scripts/crossref-snippet.lean`: given a database
(`stacks`, `kerodon`, or `wikidata`) and a tag, fetch a one-line
`(title, description)` snippet from the upstream site.

This module is used by `Mathlib/Tactic/Widget/CrossRefHover.lean` so that the
LSP widget on a cross-reference attribute can call back into the server to
resolve a snippet on demand. The script in PR 1 of this stack reimplements
roughly the same logic; we keep that script self-contained (no Mathlib import,
runs via `lake env lean --run`) and this module isolated from `IO.Process`
dependency-wise, so the two evolve in parallel.

The `Database` enum and its `URL` / `label` projections also live here; they
are re-exported through `Mathlib.Tactic.CrossRefAttribute` for the attribute
infrastructure.
-/

namespace Mathlib.CrossRef

/-- The supported external databases.

When adding a new case, also update each of these:
- `databaseURL`, `databaseLabel`, `Database.name`, `Database.ofName?`,
  the per-database branch in `fetchSnippet`, and `gerbyBase?` below;
- the parser, `syntax (name := ...)`, `registerBuiltinAttribute`, and
  `#X_tags` trace command in `Mathlib/Tactic/CrossRefAttribute.lean`;
- the parallel `Database` enum and per-database fetch implementation in
  `scripts/crossref-snippet.lean`;
- the `databases` list in `scripts/extract-crossref-tags.lean`;
- the `pretty` dict in `mathlib-ci`'s
  `scripts/crossref_review/crossref-pr-comment.py`. -/
public inductive Database where
  | kerodon
  | stacks
  | wikidata
  deriving BEq, Hashable, Repr

/-- The base URL for an external database's tag pages. Always ends with `/`. -/
public def databaseURL : Database → String
  | .kerodon  => "https://kerodon.net/tag/"
  | .stacks   => "https://stacks.math.columbia.edu/tag/"
  | .wikidata => "https://www.wikidata.org/wiki/"

/-- The display label used in docstring links and trace output. -/
public def databaseLabel : Database → String
  | .kerodon  => "Kerodon Tag"
  | .stacks   => "Stacks Tag"
  | .wikidata => "Wikidata"

/-- A short machine-readable tag (`"kerodon"`, `"stacks"`, `"wikidata"`)
that's stable to round-trip through JSON. Used by the widget. -/
public def Database.name : Database → String
  | .kerodon  => "kerodon"
  | .stacks   => "stacks"
  | .wikidata => "wikidata"

/-- Parse the short name back into a `Database`. -/
public def Database.ofName? : String → Option Database
  | "kerodon"  => some .kerodon
  | "stacks"   => some .stacks
  | "wikidata" => some .wikidata
  | _          => none

/-- `Database.name` and `Database.ofName?` roundtrip. This catches at compile time
any drift between the two when a new case is added to `Database`. -/
public theorem Database.ofName?_name (d : Database) : Database.ofName? d.name = some d := by
  cases d <;> rfl

/-- A successfully fetched snippet from an upstream database. -/
public structure Snippet where
  /-- The display title (e.g. `"Lemma 14.32.3"`). May be empty. -/
  title : String
  /-- The natural-language description. May be empty. -/
  description : String
  deriving Repr

/-- A problem encountered while fetching a snippet. -/
public inductive SnippetError where
  /-- A transient problem (network, parse, …). -/
  | network (reason : String)
  deriving Repr

/-- The outcome of trying to fetch a snippet.

* `.ok (some s)` — upstream returned a snippet (either field of `s` may be empty).
* `.ok none`     — the tag was authoritatively missing upstream.
* `.error e`     — a transient problem (network, parse, …). -/
public abbrev SnippetOutcome := Except SnippetError (Option Snippet)

/-- The `User-Agent` curl sends. Wikidata's API will throttle anonymous clients
without one, so we identify ourselves. -/
private def userAgent : String :=
  "mathlib-crossref-widget/1 (https://github.com/leanprover-community/mathlib4)"

/-- Make a GET request and return `(http-status, body)`. Status is `0` if curl
itself failed. We append the HTTP status to the body via `-w '\n%{http_code}'`
and recover it from the final line — that avoids juggling a temp file. -/
private def fetchUrl (url : String) : IO (Nat × String) := do
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

/-- Replace runs of whitespace by a single space and strip leading/trailing ws. -/
private def flattenWhitespace (s : String) : String :=
  let go : Char → (String × Bool) → (String × Bool) := fun c (acc, prevSpace) =>
    let isWs := c == ' ' || c == '\t' || c == '\n' || c == '\r'
    if isWs then
      if prevSpace || acc.isEmpty then (acc, true)
      else (acc.push ' ', true)
    else
      (acc.push c, false)
  let (out, _) := s.toList.foldl (fun st c => go c st) ("", false)
  out.trimAscii.toString

/-- Best-effort HTML→text. We treat `<x…>` as a tag only when `x` is a letter,
`/`, or `!`, so a literal `<` inside LaTeX (`0 < 1`) is preserved. -/
private def stripHtml (html : String) : String :=
  let chars := html.toList
  let rec go : List Char → Bool → String → String
    | [], _, acc => acc
    | '<' :: rest, false, acc =>
      match rest with
      | c :: _ =>
        if c.isAlpha || c == '/' || c == '!' then go rest true acc
        else go rest false (acc.push '<')
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

open Lean in
/-- Walk a path of object keys in a `Json` value, returning the leaf as a
string if every step succeeds and the leaf is a string. -/
private def jsonStrPath? (j : Json) (path : List String) : Option String :=
  let rec go (cur : Json) : List String → Option String
    | [] => cur.getStr?.toOption
    | k :: rest =>
      match cur.getObjVal? k with
      | .ok next => go next rest
      | .error _ => none
  go j path

/-! ### Wikidata -/

open Lean in
private def fetchWikidata (qid : String) : IO SnippetOutcome := do
  let url := s!"https://www.wikidata.org/w/api.php?action=wbgetentities&ids={qid}\
              &languages=en&props=labels%7Cdescriptions&format=json"
  let (status, body) ← fetchUrl url
  if status != 200 then return .error (.network s!"wikidata HTTP {status}")
  match Json.parse body with
  | .error e => return .error (.network s!"wikidata json: {e}")
  | .ok json =>
    match json.getObjVal? "error" with
    | .ok err =>
      let code := jsonStrPath? err ["code"] |>.getD ""
      let info := jsonStrPath? err ["info"] |>.getD code
      if code == "no-such-entity" then return .ok none
      else return .error (.network s!"wikidata {code}: {info}")
    | _ =>
      match json.getObjVal? "entities" with
      | .error _ => return .error (.network "wikidata: no `entities` field")
      | .ok entities =>
        match entities.getObjVal? qid with
        | .error _ => return .ok none
        | .ok ent =>
          match ent.getObjVal? "missing" with
          | .ok _ => return .ok none
          | _ =>
            let label := jsonStrPath? ent ["labels", "en", "value"] |>.getD ""
            let desc  := jsonStrPath? ent ["descriptions", "en", "value"] |>.getD ""
            return .ok (some { title := flattenWhitespace label
                               description := flattenWhitespace desc })

/-! ### Stacks / Kerodon (Gerby) -/

/-- The base URL for a Gerby-style database, or `none` for Wikidata. -/
private def gerbyBase? : Database → Option String
  | .stacks   => some "https://stacks.math.columbia.edu"
  | .kerodon  => some "https://kerodon.net"
  | .wikidata => none

/-- Return the substring of `s` after the first occurrence of `needle`,
or `none` if `needle` is absent. -/
private def afterFirst? (s needle : String) : Option String :=
  let parts := s.splitOn needle
  match parts with
  | _ :: rest@(_ :: _) => some (needle.intercalate rest)
  | _ => none

/-- Take everything up to (but not including) the first occurrence of `c`. -/
private def takeUntilChar (s : String) (c : Char) : String :=
  String.ofList (s.toList.takeWhile (· != c))

/-- Pull the environment type (`Lemma`, `Proposition`, …) and reference number
from the `/content/statement` HTML. Both Stacks and Kerodon wrap each tag in
`<article class="env-{TYPE}" id="{TAG}">` and lead with
`<a ...>Lemma <span data-tag="...">14.32.3</span>.</a>`. -/
private def parseGerbyTitle (html : String) : String :=
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

private def fetchGerby (db : Database) (tag : String) : IO SnippetOutcome := do
  let some base := gerbyBase? db | return .error (.network s!"{db.name}: no Gerby base")
  let url := s!"{base}/data/tag/{tag}/content/statement"
  let (status, body) ← fetchUrl url
  if status != 200 then return .error (.network s!"{db.name} HTTP {status}")
  -- Gerby returns HTTP 200 even for missing tags; detect via body text.
  if body.trimAscii.toString == "This tag does not exist." then return .ok none
  let title := parseGerbyTitle body
  let snippet := stripHtml body
  if title.isEmpty && snippet.isEmpty then
    return .error (.network s!"{db.name}: could not parse statement")
  return .ok (some { title, description := snippet })

/-- Fetch one snippet from the appropriate upstream database. -/
public def fetchSnippet (db : Database) (tag : String) : IO SnippetOutcome :=
  match db with
  | .wikidata => fetchWikidata tag
  | _ => fetchGerby db tag

end Mathlib.CrossRef
