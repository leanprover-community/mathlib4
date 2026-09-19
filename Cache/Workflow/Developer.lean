/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Workflow.Chain
import Cache.Workflow.Notice
import Cache.Workflow.Developer.Query

/-!
# The developer-cache workflow

The workflow of a fork checkout, and of any read that names a chain, a scope,
or `--unsafe`. A read walks the trust-ordered chain `containers`: `master`
from the public cache, the fork's per-commit namespace in `forks` from the
developer cache, then `legacy`. The per-commit scope of the `forks` round, the
`--unsafe` walk over cached fork commits, the uncached-HEAD hint, and the
non-default-scope notice all belong here. CI uploads a fork build to `forks`
under the commit's scope, with the marker `query` probes to find a fork's
cached commits (`Cache.Workflow.Developer.Query`); `query` is a command of
this workflow, and answers for the canonical repositories that they have no
per-commit namespace.

The workflow owns the chain-read flags `--cache-from`, `--scope`, `--unsafe`
and `--unsafe-window` (`flags`) and the variables `MATHLIB_CACHE_FROM` and
`MATHLIB_CACHE_REPO_SCOPE` (`envVariables`); `parseOptions` reads them into
`Options`.
-/

namespace Cache.Workflow.Developer

open Cache.Requests
open System (FilePath)

/-- The workflow's name in messages. -/
def name : String := "developer cache"

/-- The environment variables of the workflow. -/
def envVariables : List String := ["MATHLIB_CACHE_FROM", "MATHLIB_CACHE_REPO_SCOPE"]

/--
The default number of marked fork commits `cache get --unsafe` tries as
scopes: 1, the latest cached SHA. `--unsafe-window=N` overrides it.
-/
def defaultUnsafeWindow : Nat := 1

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
    {defaultUnsafeWindow}). Implies --unsafe."
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
Parse the workflow's options from the parsed command line `p`, with `--scope`
refs resolved in `cwd`. Rejects a flag of another workflow. `--unsafe` and
`--scope` are mutually exclusive: `--unsafe` walks several commit scopes,
`--scope` pins one. `--unsafe-window=N` implies `--unsafe` and needs a
positive `N`; the parser has already rejected a non-numeric one.
-/
def parseOptions (p : Cli.Parsed) (cwd : FilePath := ".") : IO Options := do
  rejectForeignFlags name flags p
  let chain ← ChainOptions.parse p
  let unsafeWindow? ← match p.flag? unsafeWindowFlag.longName with
    | some f =>
      let n := f.as! Nat
      if n == 0 then
        IO.eprintln "--unsafe-window must be a positive integer"
        IO.Process.exit 1
      pure (some n)
    | none => pure (if p.hasFlag unsafeFlag.longName then some defaultUnsafeWindow else none)
  if unsafeWindow?.isSome && p.hasFlag Scope.flag.longName then
    IO.eprintln "--unsafe and --scope are mutually exclusive: --unsafe walks several commit \
      scopes automatically, while --scope pins exactly one."
    IO.Process.exit 1
  return { chain, scope? := ← Scope.parse p cwd, unsafeWindow? }

/--
The developer chain, most trusted first: `master` for the shared upstream
artifacts (the bulk of any fork's files), `forks` for the fork's own
per-commit uploads, then `legacy` so older clients' artifacts stay reachable.
The layout is fixed per container (`Container.flatPath`), so `master` is read
flat whatever the repo is, and `forks` at `/f/{repo}/{scope}/...`.
-/
def containers : List Container := [.master, .forks, .legacy]

/--
If the user is on a commit that hasn't been cached for this fork (no marker
present at `forks/m/{repo}/{HEAD-sha}`), print an informational note
explaining the SHA-scoped behavior and pointing at `cache query`.

Fires only on a plain `cache get`:
- no scope set: the user picked a scope, and the non-default-scope warning
  covers it
- no chain override: the user took responsibility for the chain
- the repo is a fork: the canonical repos do not build into the per-commit
  `forks` namespace this note checks
- HEAD is not an ancestor of `master`. On a fork checkout at `master` (or an
  undiverged branch) the fork's SHA-scoped marker is absent by construction,
  and `master`, first in the chain, serves every file by hash. There is nothing
  fork-specific to build, so the note would be a false positive.

One HEAD probe per invocation. The message goes to stderr, apart from
`cache get`'s stdout output. The HEAD is that of the mathlib checkout at
`ctx.mathlibCwd`.
-/
def informIfHeadNotBuilt (options : Options) (ctx : ReadContext) : IO Unit := do
  if options.scope?.isSome then return
  if options.chain.chain?.isSome then return
  if isCanonicalRepo ctx.repo then return
  -- HEAD already on (an ancestor of) master: master CI builds these commits and
  -- the master container (first in the fork lookup chain) serves their artifacts
  -- by hash, so there is nothing fork-specific to build. The forks marker is
  -- structurally absent here, which would otherwise trigger a misleading note.
  if (← headIsAncestorOfMaster ctx.mathlibCwd) then return
  let sha ← try getGitCommitHash ctx.mathlibCwd catch _ => return
  let hasMarker ← probeContainerForSHA Container.forks ctx.repo sha
  if hasMarker then return
  let lines : List String := [
    "",
    s!"NOTE: no cache found for HEAD ({sha}) on fork {ctx.repo}.",
    "This commit hasn't been built by CI for this fork yet. You'll still",
    "get cache hits for files that match mathlib's master cache; only",
    "files unique to this PR will need to be rebuilt.",
    "",
    "To use a prior CI run from this fork, find a cached commit:",
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
  for line in lines do
    IO.eprintln line

/--
The `--unsafe` walk: the SHA scopes to try, most recent first, discovered by
`discoverUnsafeScopes` over the history of the checkout at `cwd`, reported on
stderr. Empty when no cached fork commit is in range; the read then falls back
to the plain chain.
-/
def unsafeScopes (repo : String) (window : Nat) (cwd : FilePath) : IO (List String) := do
  let scopes ← discoverUnsafeScopes repo window (cwd := cwd)
  if scopes.isEmpty then
    IO.eprintln s!"--unsafe: no cached fork commits found in range for {repo}; \
      reading the default cache only."
  else
    IO.eprintln s!"--unsafe: trying {scopes.length} cached fork commit scope(s) for \
      {repo} (most recent first):"
    for s in scopes do IO.eprintln s!"  {s}"
  return scopes

/--
The read. Prints the non-default-scope notice when the read is taken off the
default trust boundary, runs the `--unsafe` walk or the uncached-HEAD hint,
then downloads the chain rounds (`Chain.readRounds containers`).
-/
def get (options : Options) (ctx : ReadContext) (req : ReadRequest) : IO.CacheM Unit := do
  Notice.emit {
    repoExplicit? := ctx.repoExplicit?, detectedRepo? := ctx.detectedRepo?,
    chain := options.chain, defaultChain := containers, scope? := options.scope?,
    unsafeWindow? := options.unsafeWindow?, cwd := ctx.mathlibCwd } ctx.repo
  let scopes ← match options.unsafeWindow? with
    | some window => unsafeScopes ctx.repo window ctx.mathlibCwd
    | none =>
      informIfHeadNotBuilt options ctx
      pure []
  let rounds ← Chain.readRounds containers options.chain options.scope? ctx.mathlibCwd scopes
  getFiles rounds ctx.repo req.hashMap req.forceDownload req.forceDownload req.parallel
    req.decompress (reportScopes := !scopes.isEmpty)

/--
Resolve the repo `cache query` asks about.

Precedence: the explicit `--repo=` flag (if passed) > the cwd's git remote
> `MATHLIBREPO`. The git remote is the default because the typical user asks
what is cached for their own commits, not for canonical mathlib's.

In a project that depends on Mathlib (`isMathlibRoot` is false), the cwd is
that project's own checkout, whose remote and commits name no mathlib fork;
probing its markers would answer "not cached" for a namespace nothing writes.
`query` there requires an explicit `--repo=` and errors out with that guidance
otherwise.
-/
def resolveQueryRepo (repoExplicit? : Option String) (isMathlibRoot : Bool) : IO String := do
  match repoExplicit? with
  | some r => pure r
  | none =>
    unless isMathlibRoot do
      IO.eprintln "`cache query` locates a mathlib fork's per-commit cache, and this \
        project's own commits name none. Run it from a mathlib checkout, or pass \
        --repo=OWNER/REPO to name the fork to query."
      IO.Process.exit 1
    match ← getRemoteRepo "." with
    | some repo => pure repo
    | none => pure MATHLIBREPO

/--
The `query` answer for a canonical repository: `repo` caches by file hash, so
there is no per-commit build to find. Without a `ref` the answer is a note on
stdout; with one it is an error, exit 1, in place of a misleading
`not cached`.
-/
def noPerCommitNamespace (repo : String) (ref? : Option String) : IO Unit := do
  match ref? with
  | none =>
    IO.println s!"`cache query` locates a fork PR's per-commit cache. {repo} reads \
      its own cache container directly, so there is nothing to query for it."
  | some _ =>
    IO.eprintln s!"{repo} caches by file hash, not per commit, so there is no per-commit \
      build to query."
    (← IO.getStderr).flush
    IO.Process.exit 1

/-- `cache query [REF]` for `repo`: without a ref, the most recent cached
commit of the fork on this branch; with one, whether that commit is cached
(exit 0) or not (exit 1). A canonical repository has no per-commit namespace
(`noPerCommitNamespace`). -/
def query (repo : String) (ref? : Option String) : IO Unit := do
  if isCanonicalRepo repo then
    noPerCommitNamespace repo ref?
  else match ref? with
    | none => cacheQuery repo (cap := 50)
    | some ref => cacheQuerySingle repo (← resolveGitRef ref)

end Cache.Workflow.Developer
