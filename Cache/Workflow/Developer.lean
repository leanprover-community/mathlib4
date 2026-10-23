/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Cache.Workflow.Chain
public import Cache.Workflow.Notice
public import Cache.Workflow.Developer.Query

/-!
# The developer-cache workflow

The workflow of a fork checkout (the nightly-testing repository included),
and of a read on the canonical repository that names a chain, a scope, or
`--unsafe`. A read walks the trust-ordered chain `containers`: `master` from
the public cache, then the fork's per-commit namespace in `forks` from the
developer bucket (`containerBase` names the hosts). The per-commit scope of the
`forks` round, the `--unsafe` walk over cached fork commits and its summary,
the hint for missing files, and the non-default-scope notice all belong here.
CI uploads a fork build to `forks` under the commit's scope, with the marker
`query` probes to find a fork's cached commits
(`Cache.Workflow.Developer.Query`); `query` is a command of this workflow, and
answers for the canonical repository that it has no per-commit namespace.

The workflow owns the flags `--cache-from`, `--scope`, `--unsafe` and
`--unsafe-window` (`flags`) and the variables `MATHLIB_CACHE_FROM` and
`MATHLIB_CACHE_REPO_SCOPE`; `parseOptions` reads them into `Options`.
-/

public section

namespace Cache.Workflow.Developer

open Cache.Requests
open System (FilePath)

/-- The workflow's name in messages. -/
def name : String := "developer cache"

/--
The developer cache's read host: the bucket that holds the `forks` container,
read directly rather than through the cache resolver. The workflow reads its
other containers through the public endpoint (`publicCacheEndpoint`).
-/
def developerCacheEndpoint : String := "https://r2devcache.mathlib.org"

/-- The read base of each container in a developer read under the settings
`s`: `forks` on the developer cache's host, every other container on the
public endpoint, both under the read base rule (`readBase`). -/
def containerBase (s : Settings) (c : Container) : String :=
  readBase s (if c == .forks then developerCacheEndpoint else publicCacheEndpoint)

/-- `--unsafe`: the automatic walk over cached fork commits. -/
def unsafeFlag : Cli.Flag := .paramless
  (longName := "unsafe")
  (description := "Walk this branch's history and try the most recent cached fork commits \
    as scopes, most recent first, until the cache is satisfied, instead of pinning one \
    --scope. Trusts the artifacts of every commit it tries and prints a security notice. \
    Excludes --scope.")

/-- `--unsafe-window=N`: how many cached fork commits `--unsafe` tries. -/
def unsafeWindowFlag : Cli.Flag := {
  longName := "unsafe-window"
  description := s!"The number of cached fork commits --unsafe tries (default \
    {defaultUnsafeSHAWindow}). Implies --unsafe."
  type := Nat }

/-- The flags of the workflow. -/
def flags : Array Cli.Flag := #[ChainOptions.flag, Scope.flag, unsafeFlag, unsafeWindowFlag]

/-- The options of a developer read. -/
structure Options where
  /-- The chain options: `--cache-from`, `MATHLIB_CACHE_FROM`. -/
  chain : ChainOptions := {}
  /-- The per-commit scope: `--scope`, `MATHLIB_CACHE_REPO_SCOPE`. -/
  scope? : Option Scope := none
  /-- The `--unsafe` window: how many cached fork commits to try. -/
  unsafeWindow? : Option Nat := none
  deriving Inhabited

/--
Parse the workflow's options from the parsed command line `p` and the
settings `s`, with `--scope` refs resolved in the Mathlib checkout. Fails on a
flag of another workflow. `--unsafe` and `--scope` are mutually exclusive: `--unsafe`
walks several commit scopes, `--scope` pins one. `--unsafe-window=N` implies
`--unsafe` and needs a positive `N`; the parser has already rejected a
non-numeric one.
-/
def parseOptions (p : Cli.Parsed) (s : Settings := {}) : IO.CacheM Options := do
  checkForeignFlags name flags p
  let chain ← ChainOptions.parse p s
  let unsafeWindow? ← match p.flag? unsafeWindowFlag.longName with
    | some f =>
      let n := f.as! Nat
      if n == 0 then fail "--unsafe-window must be a positive integer"
      pure (some n)
    | none => pure (if p.hasFlag unsafeFlag.longName then some defaultUnsafeSHAWindow else none)
  if unsafeWindow?.isSome && p.hasFlag Scope.flag.longName then
    fail "--unsafe and --scope are mutually exclusive: --unsafe walks several commit \
      scopes automatically, while --scope pins exactly one."
  return { chain, scope? := ← Scope.parse p s, unsafeWindow? }

/--
The developer chain, most trusted first: `master` for the shared upstream
artifacts (the bulk of any fork's files), then `forks` for the fork's own
per-commit uploads. The layout is fixed per container (`Container.flatPath`),
so `master` is read flat whatever the repo is, and `forks` at
`/f/{repo}/{scope}/...`.
-/
def containers : List Container := [.master, .forks]

/-- The `--unsafe` summary: which fork commits supplied files, so the user
knows whose artifacts they ended up trusting. -/
def reportUnsafeScopes (result : DownloadResult) : IO Unit := do
  let byScope := result.served.filterMap fun (location, n) => location.sha?.map (·, n)
  if byScope.isEmpty then
    IO.eprintln "--unsafe: no fork scopes were needed; \
      all files were served by other locations."
  else
    IO.eprintln s!"--unsafe: cache served from {byScope.length} fork commit scope(s):"
    for (sha, n) in byScope do
      IO.eprintln s!"  {sha} → {n} file(s)"
    if result.missing > 0 then
      IO.eprintln s!"  {result.missing} file(s) still missing after all scopes."

/--
The `--unsafe` walk: the SHA scopes to try, most recent first, discovered by
`discoverUnsafeScopes` against the markers under `forksBase` over the history
of the Mathlib checkout, reported on stderr. Empty when no cached fork commit
is in range; the `forks` round then reads at the checked-out HEAD, as a plain
read does (`Chain.readLocations`).
-/
def unsafeScopes (forksBase repo : String) (window : Nat) : IO.CacheM (List String) := do
  let scopes ← discoverUnsafeScopes forksBase repo window
  if scopes.isEmpty then
    IO.eprintln s!"--unsafe: no cached fork commits found in range for {repo}; \
      reading the default cache only."
  else
    IO.eprintln s!"--unsafe: trying {scopes.length} cached fork commit scope(s) for \
      {repo} (most recent first):"
    for s in scopes do IO.eprintln s!"  {s}"
  return scopes

/--
Lines for the missing-files warning on a fork checkout whose HEAD has no
published fork cache: a previous CI build of this fork may hold the missing
files, so the message points at `cache query` and the SHA-scoped workflow.
Selected by `forkHintSHA?`.
-/
def missingFilesForkLines (repo sha : String) (missing : Nat) : List String := [
  "",
  s!"NOTE: {missing} file(s) were not found in any cache for fork {repo}.",
  s!"CI has not published a fork cache for HEAD ({sha}) — most likely it",
  "hasn't built this commit yet. The missing files will be built locally",
  "by `lake build`.",
  "",
  "To reuse a previous CI build from this fork instead, find a cached commit:",
  "    lake exe cache query",
  "",
  "then re-run with:",
  "    lake exe cache get --scope=<that-sha>",
  "",
  "Important: using another commit's scope means trusting the artifacts",
  "produced at that commit. `cache get` will print a security notice",
  "when you do.",
  "",
]

/--
When the missing-files warning should point at the fork workflow (`cache
query` / `--scope`), return the HEAD SHA it should mention; `none` means the
generic divergence warning applies (`missingFilesGenericLines`).

The fork hint fires only for a plain read on a fork checkout whose HEAD has
no published fork cache:
- not in `--unsafe` mode (that read already walked fork scopes and reported
  what they served)
- no scope set (`options.scope?`): the user has already picked a scope and
  the notice did the talking
- no `--cache-from` (`options.chain.cli?`): the user has taken explicit
  responsibility for the lookup chain
- the repo is a fork, not the canonical repo: the canonical repo doesn't build
  into the per-commit `forks` namespace this hint points at
- HEAD is not an ancestor of `master`: misses there are master-container lag
  (CI still building master), which no fork scope can serve
- the fork marker for HEAD under `forksBase` is absent; when it is present the
  HEAD scope was already read and came up short anyway, so pointing back at it
  would not help

Guards are ordered cheapest first; the marker probe (one HTTPS round-trip)
runs only when every local check passes.
-/
def forkHintSHA? (options : Options) (forksBase repo : String) :
    IO.CacheM (Option String) := do
  if options.unsafeWindow?.isSome then return none
  if options.scope?.isSome then return none
  if options.chain.cli?.isSome then return none
  if isCanonicalRepo repo then return none
  if (← headIsAncestorOfMaster) then return none
  let sha ← try getGitCommitHash catch _ => return none
  if (← probeForksForSHA forksBase repo sha) then return none
  return some sha

/--
The read. Prints the non-default-scope notice when the read is taken off the
default trust boundary, runs the `--unsafe` walk, downloads the chain
(`Chain.readLocations containers`), then reports what the read did. The
missing-files warning is keyed on the read's outcome: nothing when every file
arrived, the fork hint for reads that `forkHintSHA?` accepts, and the generic
divergence warning otherwise.
-/
def get (options : Options) (ctx : ReadContext) (req : ReadRequest) : IO.CacheM Unit := do
  Notice.emit {
    repoExplicit? := ctx.repoExplicit?, detectedRepo? := ctx.detectedRepo?,
    chain := options.chain, defaultChain := containers, scope? := options.scope?,
    unsafeWindow? := options.unsafeWindow? } ctx.repo
  let base := containerBase ctx.settings
  let scopes ← match options.unsafeWindow? with
    | some window => unsafeScopes (base .forks) ctx.repo window
    | none => pure []
  let locations ← Chain.readLocations containers base options.chain options.scope? ctx.repo
    scopes
  let result ← getFiles ctx.repo locations req.hashMap req.forceDownload req.forceDownload
    req.mode req.decompress
  if !scopes.isEmpty then reportUnsafeScopes result
  if result.missing > 0 then
    warnMissing <| match ← forkHintSHA? options (base .forks) ctx.repo with
      | some sha => missingFilesForkLines ctx.repo sha result.missing
      | none => missingFilesGenericLines result.missing

/--
Resolve the repo to use for a `cache query` invocation.

Precedence: the explicit `--repo=` flag (if passed) > the Mathlib checkout's
git remote > `MATHLIBREPO`. Defaulting to the git remote is intentional for
`query`: the typical user is asking "what's cached for *my* commits", not for
canonical mathlib's commits. Repo and commit lookups use the same checkout.

In a project that depends on Mathlib (`isMathlibRoot` is false), a `get`
does not read a fork's cache on the dependency checkout's remote alone
(`resolveRepo`), so `query` there requires an explicit `--repo=` and fails
with that guidance otherwise.
-/
def resolveQueryRepo (repoExplicit? : Option String) (isMathlibRoot : Bool) :
    IO.CacheM String := do
  match repoExplicit? with
  | some r => pure r
  | none =>
    unless isMathlibRoot do
      fail "`cache query` locates a mathlib fork's per-commit cache, and in a project \
        that depends on Mathlib the dependency checkout's remote does not select one. \
        Pass --repo=OWNER/REPO to name the fork to query."
    match ← getRemoteRepo (← read).mathlibDepPath with
    | some info => pure info.repo
    | none => pure MATHLIBREPO

/--
The `query` answer for a canonical repository: `query` probes the per-commit
markers of forks only, so it has nothing to query for `repo`. Without a `ref`
the answer is a note on stdout, exit status 0; with one it is an error, exit
status 1, in place of a misleading `not cached`.
-/
def noPerCommitNamespace (repo : String) (ref? : Option String) : IO UInt32 := do
  match ref? with
  | none =>
    IO.println s!"`cache query` locates a fork PR's per-commit cache. {repo} reads \
      its own cache container directly, so there is nothing to query for it."
    return 0
  | some _ =>
    IO.eprintln s!"{repo} caches by file hash, not per commit, so there is no per-commit \
      build to query."
    return 1

/-- `cache query [REF]` for `repo` under the settings `s`, and its exit
status: without a ref, the most recent cached commit of the fork on this
branch; with one, whether that commit is cached (0) or not (1). A canonical
repository has no per-commit namespace (`noPerCommitNamespace`). -/
def query (s : Settings) (repo : String) (ref? : Option String) : IO.CacheM UInt32 := do
  if isCanonicalRepo repo then
    noPerCommitNamespace repo ref?
  else match ref? with
    | none => cacheQuery (containerBase s .forks) repo (cap := 50); return 0
    | some ref => cacheQuerySingle (containerBase s .forks) repo (← resolveGitRef ref)

end Cache.Workflow.Developer
