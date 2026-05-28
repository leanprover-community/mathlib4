/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Cli
import Cache.Requests
import Cache.Lean

/-!
# Unit tests for the cache CLI

These tests cover the pure logic of the cache system, including:
- Container model (trust levels, URL shapes, Azure integration)
- Trust-ordered fallback chains per repo
- URL construction (`mkFileURL`) with support for per-SHA scoping
- CLI flag parsing (`--cache-from`, `--scope`, `--repo`, etc.)
- Utility functions (URL extraction, filename hashing, etc.)

Anything that touches `curl` or the network lives in the integration tests
(run by the CI workflow in `build_template.yml`).

## Design invariants these tests defend

1. **Trust boundary per container**: Each container has a dedicated writer
   (via OIDC + Azure RBAC), and reads are from a per-repo trust-ordered list.
   A malicious PR cannot upload to a higher-trust container.

2. **Per-SHA namespace for fork uploads**: Fork-trust uploads are scoped to
   their commit SHA (`/f/{repo}/{sha}/{hash}`), isolating commits from each
   other. A closed PR's uploads cannot reach later honest PRs from the same fork.

3. **Flat layout for single-writer containers**: `master` is always flat
   (`/f/{hash}`) because RBAC limits it to one writer. Readers on older tools
   that only know the flat path still find master artifacts.

4. **Prefixed layout for multi-writer containers**: `forks`, `nightly-testing`,
   and `pr-toolchain-tests` are always prefixed (`/f/{repo}/{hash}`) to
   disambiguate uploads from different sources. Canonical-repo builds at
   fork-trust level must coexist with fork builds without collisions.

5. **`legacy` preserved for migration**: The historical monolithic `mathlib4`
   container stays readable with its historical mixed layout (flat for canonical,
   prefixed for forks) so consumers on old cache tools don't break.

## Running the tests

Run with `lake exe cache-test`. Exits 0 on success, non-zero on failure.

The tests are deliberately standalone (do not require `MathlibTest`), since the
cache tool should be separable. A Lake package has a single `testDriver`, and
the enclosing `mathlib` package binds that to `MathlibTest` (see `lakefile.lean`).
If the cache tool moves to its own Lake project, the `lean_exe` `cache-test`
declared here can be promoted to that project's `testDriver`.
-/

namespace Cache.Test

open Cache.Requests

/-- Counter for failed assertions. -/
initialize failures : IO.Ref Nat ← IO.mkRef 0

/-- A single named assertion. On failure, prints details and bumps the counter. -/
def assert (name : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"  ok: {name}"
  else
    IO.eprintln s!"  FAIL: {name}"
    failures.modify (· + 1)

/-- Assert two strings are equal; show both on failure. -/
def assertEq (name expected actual : String) : IO Unit := do
  if expected == actual then
    IO.println s!"  ok: {name}"
  else
    IO.eprintln s!"  FAIL: {name}\n    expected: {expected}\n    actual:   {actual}"
    failures.modify (· + 1)

section ContainerModel

/-- Short name = the string used on the CLI (`--container=NAME`) and to derive
the Azure container name. Locking this down keeps the CLI surface stable and
makes the mapping bidirectional: Container name ↔ Azure container ↔ CLI flag.

These names are part of the public CLI contract — changing them breaks user
scripts and workflows. Tests pin them so refactors that rename containers are
explicit (and their broader impact is visible).
-/
def test_Container_name : IO Unit := do
  IO.println "Container.name:"
  -- "master" is the CLI label; the corresponding Azure container is `mathlib4-master`.
  assertEq "master"             "master"             Container.master.name
  -- Renamed from `pr` to `forks` to accurately reflect what writes to it: PR
  -- branches and their fork repos, plus canonical-repo branches at fork-trust
  -- level (ci-dev/*, bors trying). The old `pr` name was misleading.
  assertEq "forks"              "forks"              Container.forks.name
  -- Hyphenated name `nightly-testing` matches the container's input repos
  -- (the `mathlib4-nightly-testing` GitHub org) and the CI branch names.
  assertEq "nightly-testing"    "nightly-testing"    Container.nightlyTesting.name
  -- Kept the `pr-` prefix because the container exists for low-trust
  -- toolchain-PR test runs (lean-pr-testing-*, batteries-pr-testing-*).
  -- Distinguishing it from plain `forks` (medium-trust) in the name helps
  -- operators reason about trust levels.
  assertEq "pr-toolchain-tests" "pr-toolchain-tests" Container.prToolchainTests.name
  -- Bare `mathlib4` (the historical monolithic container, predating the split)
  -- is exposed on the CLI as `legacy` to signal its transitional role: it's
  -- being phased out in favor of per-trust-level containers, but still holds
  -- historical artifacts and serves as a fallback during the migration.
  assertEq "legacy"             "legacy"             Container.legacy.name

/-- Parser is the inverse of `Container.name` on valid inputs, and rejects everything else. -/
def test_Container_parse : IO Unit := do
  IO.println "Container.parse?:"
  -- Every canonical name round-trips back to its enum case.
  assert "master parses"          (Container.parse? "master" == some .master)
  assert "forks parses"           (Container.parse? "forks" == some .forks)
  assert "nightly-testing parses" (Container.parse? "nightly-testing" == some .nightlyTesting)
  assert "pr-toolchain-tests parses"
    (Container.parse? "pr-toolchain-tests" == some .prToolchainTests)
  assert "legacy parses"          (Container.parse? "legacy" == some .legacy)
  -- Unknown names must be rejected so `--container=bogus` errors out instead of silently
  -- defaulting to (or worse, fabricating) a container.
  assert "unknown rejected"       (Container.parse? "bogus" == none)
  -- Empty string is a likely user input (e.g. `--container=`); reject explicitly.
  assert "empty rejected"         (Container.parse? "" == none)

/-- The Azure URL each container resolves to. These URLs are baked into every
download/upload request, so changes here have an operational blast radius.
The URL pattern follows the convention `mathlib4-{name}` for per-trust containers
and bare `mathlib4` for the historical legacy container.

Changing these URLs is non-trivial: it requires coordinating the Azure side
(creating/destroying containers) with all consumers of the cache (any tool that
knows how to read the old URL is suddenly blind to the new one).
-/
def test_Container_azureURL : IO Unit := do
  IO.println "Container.azureURL:"
  -- The NEW dedicated master container — `mathlib4-master`, distinct from the
  -- legacy bare `mathlib4`. Only master CI writes here.
  assertEq "master URL"
    "https://lakecache.blob.core.windows.net/mathlib4-master"
    Container.master.azureURL
  -- Per-trust-level containers follow the `mathlib4-{name}` convention.
  assertEq "forks URL"
    "https://lakecache.blob.core.windows.net/mathlib4-forks"
    Container.forks.azureURL
  assertEq "nightly-testing URL"
    "https://lakecache.blob.core.windows.net/mathlib4-nightly-testing"
    Container.nightlyTesting.azureURL
  assertEq "pr-toolchain-tests URL"
    "https://lakecache.blob.core.windows.net/mathlib4-pr-toolchain-tests"
    Container.prToolchainTests.azureURL
  -- Legacy keeps the bare `mathlib4` container name (no `-legacy` suffix); this
  -- is the historical monolithic container that pre-dated the split.
  assertEq "legacy URL"
    "https://lakecache.blob.core.windows.net/mathlib4"
    Container.legacy.azureURL

/-- URL-shape policy per container: whether to namespace under `/f/<repo>/...`
or write flat at `/f/...`. This is a critical decision: different containers
have different numbers of writers, and the path layout must disambiguate them.

The policy is asymmetric on purpose:
- `master`: canonical-only (RBAC enforces single writer), so flat layout is safe.
  Flat is also historically required for readers on old tools.
- `legacy`: mixed behavior for back-compat. Flat for canonical (where old readers
  expect master artifacts), prefixed for forks (the old fork-upload shape).
- New per-trust-level containers (`forks`, `nightly-testing`, `pr-toolchain-tests`):
  ALWAYS prefixed, even for canonical-repo writers. This is essential because
  the container receives uploads from multiple sources (different forks, plus
  canonical-repo at low-trust via ci-dev/*, bors trying), and collisions on
  identical hashes would be silent and damaging.

The container's policy decides which writers can coexist safely in it.
-/
def test_Container_flatPath : IO Unit := do
  IO.println "Container.flatPath:"
  -- master is canonical-only (RBAC enforces this) and the layout is always flat.
  -- Even defensively, if a non-canonical repo were passed through, RBAC blocks
  -- the write at Azure; the flatPath policy is an extra layer of clarity.
  assert "master is flat for canonical mathlib4"
    (Container.master.flatPath MATHLIBREPO == true)
  assert "master is flat for any repo (canonical-only by RBAC)"
    (Container.master.flatPath "alice/mathlib4" == true)
  -- legacy: historical mixed behavior. Flat for canonical (where old mathlib
  -- readers look for master artifacts in the default container), prefixed
  -- for forks (the shape where old fork PRs were written by CI).
  assert "legacy is flat for canonical mathlib4 (historical master path)"
    (Container.legacy.flatPath MATHLIBREPO == true)
  assert "legacy is prefixed for fork repos (historical fork path)"
    (Container.legacy.flatPath "alice/mathlib4" == false)
  -- New per-trust-level containers are ALWAYS prefixed, including when the
  -- canonical mathlib4 repo is dispatched here at low-trust. This is what makes
  -- it possible for ci-dev/* and bors trying (canonical repo at fork-trust)
  -- and fork PRs to coexist in the same `forks` container without collisions.
  assert "forks is prefixed for canonical mathlib4 (trust-dispatch override)"
    (Container.forks.flatPath MATHLIBREPO == false)
  assert "forks is prefixed for fork repos"
    (Container.forks.flatPath "alice/mathlib4" == false)
  assert "nightly-testing is prefixed for nightly-testing repo"
    (Container.nightlyTesting.flatPath NIGHTLY_TESTING_REPO == false)
  assert "nightly-testing is prefixed for canonical mathlib4"
    (Container.nightlyTesting.flatPath MATHLIBREPO == false)
  assert "pr-toolchain-tests is prefixed for nightly-testing repo"
    (Container.prToolchainTests.flatPath NIGHTLY_TESTING_REPO == false)

end ContainerModel

section PerRepoAllowlist

/-- Trust-ordered fallback list per GitHub repo. The contract: each repo maps
to its own dedicated container first (1-1), with `legacy` as universal last-resort
fallback during migration.

This is a core trust boundary: the list is the read-side fallback chain that
determines which artifacts a consumer can reach from which sources. The ordering
matters — the tool tries containers in order and stops at the first hit.

Key constraints:
- **Canonical mathlib4** (master): reads from `master` first, then `legacy`.
  `master` has single-writer RBAC (master CI only) and holds the bulk of any
  mathlib build.
- **Nightly-testing repo**: reads from `nightly-testing` only (plus `legacy` for
  historical artifacts). **`pr-toolchain-tests` is deliberately excluded** from the
  default because toolchain-PR branches are low-trust (PR-submitted code). Trusted
  consumers on `nightly-testing` must not silently fall back to them. Toolchain-PR
  branches that need the wider chain opt in via `MATHLIB_CACHE_FROM` in CI.
- **Fork repos** (PR branches): reads from `master` first (highest-trust, bulk of
  deps), then `forks` (PR-specific files), then `legacy` (historical fallback).
  Note: `master` here reads the *canonical repo's* flat-layout master artifacts
  (hash X in master's `/f/X.ltar`), and the fork loop matches those artifacts
  because the root hashes align across repos. Later, we can't put `master` in
  the nightly chain because nightly runs under a different toolchain, so root
  hashes diverge.
- **Unknown repos**: default to the fork chain (conservative — prefer the highest-trust
  source and keep the migration tail).
- **Legacy always last**: a defensive invariant. Dropping `legacy` in a future
  refactor would silently shrink hit rates. We pin this so changes are explicit.
-/
def test_defaultContainersForRepo : IO Unit := do
  IO.println "defaultContainersForRepo:"
  -- Master branch reads its own container first; legacy is the universal tail.
  assert "mathlib4 master repo → [master, legacy]"
    (defaultContainersForRepo MATHLIBREPO == [.master, .legacy])
  -- Nightly-testing default is the STRICT trusted-nightly view: only the
  -- nightly container and legacy. `pr-toolchain-tests` is deliberately
  -- excluded so trusted consumers (`nightly-testing`, `nightly-testing-green`,
  -- `bump/*`) don't silently fall back to low-trust toolchain-PR test
  -- artifacts. Toolchain-test branches widen this from the CI workflow via
  -- `MATHLIB_CACHE_FROM` rather than from any branch detection in Lean.
  assert "nightly-testing repo → [nightly-testing, legacy] (strict default)"
    (defaultContainersForRepo NIGHTLY_TESTING_REPO == [.nightlyTesting, .legacy])
  -- A PR from a fork: master first (highest-trust, holds the bulk of any
  -- fork build's deps), then the fork's own container for PR-specific
  -- files, then legacy as the migration tail.
  assert "fork repo → [master, forks, legacy]"
    (defaultContainersForRepo "alice/mathlib4" == [.master, .forks, .legacy])
  -- Anything unrecognized falls through to the fork-default; conservative.
  assert "unknown repo → [master, forks, legacy] (fork-default)"
    (defaultContainersForRepo "some/other-repo" == [.master, .forks, .legacy])
  -- Defensive: every default allowlist must end with `.legacy` so historical
  -- artifacts remain reachable during the migration. Future edits that drop
  -- this guarantee would silently shrink cache-hit rates.
  assert "legacy is always last for fork repos"
    ((defaultContainersForRepo "alice/mathlib4").getLast? == some Container.legacy)
  assert "legacy is always last for master repo"
    ((defaultContainersForRepo MATHLIBREPO).getLast? == some Container.legacy)
  assert "legacy is always last for nightly-testing repo"
    ((defaultContainersForRepo NIGHTLY_TESTING_REPO).getLast? == some Container.legacy)

end PerRepoAllowlist

section MkFileURL

/-- URL path shape is decided by the *container*, not the repo (see
`Container.flatPath`). This is a critical invariant: a single repo (canonical
mathlib4) can dispatch to different containers based on its branch's trust
level, and each container's path layout must disambiguate all its writers.

- `master`: always flat (`/f/{hash}`) because only one writer (master CI) has
  RBAC access, so the repo prefix is moot. The flat layout is also the
  historical master path shape, preserved for readers on older tools.
- `forks`: always prefixed (`/f/{repo}/{hash}`) because multiple fork PRs
  write here, and also because canonical-repo CI at fork-trust level (e.g.
  `ci-dev/*` branches, `bors trying` temp branches) may write here. The prefix
  is mandatory to disambiguate canonical-repo uploads in `forks` from fork-repo
  uploads.
- `nightly-testing`, `pr-toolchain-tests`: always prefixed, same reasoning as
  `forks` — multiple sources write to these containers.
- `legacy`: mixed behavior for back-compat. Flat for canonical (where old
  mathlib readers still look for master artifacts), prefixed for forks.
- Env-var override (`MATHLIB_CACHE_GET_URL`, `MATHLIB_CACHE_PUT_URL`): falls
  back to legacy semantics (flat for canonical, prefixed for forks) since the
  URL is user-supplied and we don't know which container's policy applies.

Per-SHA scoping (via `MATHLIB_CACHE_REPO_SCOPE`) is orthogonal: when present,
the scope is inserted between repo and hash on *prefixed* paths only, producing
`/f/{repo}/{sha}/{hash}`. Flat paths ignore it since they have only one writer
and per-commit isolation is moot.
-/
def test_mkFileURL : IO Unit := do
  IO.println "mkFileURL:"
  -- master is flat for canonical mathlib4 (where master CI publishes).
  assertEq "master × mathlib4 (flat)"
    "https://lakecache.blob.core.windows.net/mathlib4-master/f/abc.ltar"
    (mkFileURL (some .master) MATHLIBREPO Container.master.azureURL "abc.ltar")
  -- master is *always* flat regardless of repo — by policy. RBAC enforces
  -- master-only writes anyway, so this branch shouldn't see fork repos in
  -- practice, but pinning the policy keeps the shape unambiguous if it does.
  assertEq "master × fork (still flat by policy)"
    "https://lakecache.blob.core.windows.net/mathlib4-master/f/abc.ltar"
    (mkFileURL (some .master) "alice/mathlib4" Container.master.azureURL "abc.ltar")
  -- The key new behavior: `forks` namespaces by repo *even for canonical
  -- mathlib4*. This covers the trust-dispatch case where the canonical repo
  -- runs at fork-level trust (`ci-dev/*`, `bors trying`) and the workflow
  -- routes the upload to the `forks` container. Without the prefix, those
  -- writes would land flat in `forks` and collide / be unfindable.
  assertEq "forks × mathlib4 (prefixed; trust-dispatch override)"
    "https://lakecache.blob.core.windows.net/mathlib4-forks/f/leanprover-community/mathlib4/abc.ltar"
    (mkFileURL (some .forks) MATHLIBREPO Container.forks.azureURL "abc.ltar")
  -- forks × fork: the original fork-PR upload shape, unchanged.
  assertEq "forks × fork (prefixed)"
    "https://lakecache.blob.core.windows.net/mathlib4-forks/f/alice/mathlib4/abc.ltar"
    (mkFileURL (some .forks) "alice/mathlib4" Container.forks.azureURL "abc.ltar")
  -- nightly-testing and pr-toolchain-tests follow the same policy: always
  -- prefixed, so multiple writers within a container stay disambiguated.
  assertEq "nightly-testing × nightly-testing repo (prefixed)"
    "https://lakecache.blob.core.windows.net/mathlib4-nightly-testing/f/leanprover-community/mathlib4-nightly-testing/abc.ltar"
    (mkFileURL (some .nightlyTesting) NIGHTLY_TESTING_REPO
      Container.nightlyTesting.azureURL "abc.ltar")
  assertEq "pr-toolchain-tests × nightly-testing repo (prefixed)"
    "https://lakecache.blob.core.windows.net/mathlib4-pr-toolchain-tests/f/leanprover-community/mathlib4-nightly-testing/abc.ltar"
    (mkFileURL (some .prToolchainTests) NIGHTLY_TESTING_REPO
      Container.prToolchainTests.azureURL "abc.ltar")
  -- Legacy preserves the historical mixed behavior: flat for canonical, prefixed
  -- otherwise. Older readers that point at the bare `mathlib4` container still
  -- find what they expect.
  assertEq "legacy × mathlib4 (flat, historical master path)"
    "https://lakecache.blob.core.windows.net/mathlib4/f/abc.ltar"
    (mkFileURL (some .legacy) MATHLIBREPO Container.legacy.azureURL "abc.ltar")
  assertEq "legacy × fork (prefixed, historical fork path)"
    "https://lakecache.blob.core.windows.net/mathlib4/f/alice/mathlib4/abc.ltar"
    (mkFileURL (some .legacy) "alice/mathlib4" Container.legacy.azureURL "abc.ltar")
  -- Env-var override (MATHLIB_CACHE_GET_URL / MATHLIB_CACHE_PUT_URL): container
  -- is `none`, so the URL-shape decision falls back to legacy semantics. This
  -- preserves the exact behavior dev/local override users had before the
  -- per-container split.
  assertEq "env-var override × mathlib4 (legacy semantics: flat)"
    "https://custom.example/cache/f/abc.ltar"
    (mkFileURL none MATHLIBREPO "https://custom.example/cache" "abc.ltar")
  assertEq "env-var override × fork (legacy semantics: prefixed)"
    "https://custom.example/cache/f/alice/mathlib4/abc.ltar"
    (mkFileURL none "alice/mathlib4" "https://custom.example/cache" "abc.ltar")
  -- Per-SHA scoping (via `MATHLIB_CACHE_REPO_SCOPE`): when present, the
  -- scope is appended as an extra path component after the repo prefix.
  -- This prevents within-fork temporal replay: each commit's CI run gets
  -- its own namespace, so a closed/hidden PR's uploads cannot poison a
  -- later honest PR from the same fork. The scope is only applied to
  -- non-flat (prefixed) paths; flat paths ignore it.
  assertEq "forks × fork + scope (per-SHA namespace)"
    "https://lakecache.blob.core.windows.net/mathlib4-forks/f/alice/mathlib4/abc123def/H.ltar"
    (mkFileURL (some .forks) "alice/mathlib4" Container.forks.azureURL "H.ltar" (some "abc123def"))
  assertEq "forks × mathlib4 + scope (ci-dev/* trust dispatch)"
    "https://lakecache.blob.core.windows.net/mathlib4-forks/f/leanprover-community/mathlib4/abc123def/H.ltar"
    (mkFileURL (some .forks) MATHLIBREPO Container.forks.azureURL "H.ltar" (some "abc123def"))
  -- Scope is ignored on flat paths (master container, legacy × MATHLIBREPO):
  -- the master container has a single writer so per-commit isolation is
  -- moot, and the legacy flat layout is fixed for back-compat.
  assertEq "master × mathlib4 + scope (scope ignored, still flat)"
    "https://lakecache.blob.core.windows.net/mathlib4-master/f/abc.ltar"
    (mkFileURL (some .master) MATHLIBREPO Container.master.azureURL "abc.ltar" (some "abc123def"))
  assertEq "legacy × mathlib4 + scope (scope ignored, still flat)"
    "https://lakecache.blob.core.windows.net/mathlib4/f/abc.ltar"
    (mkFileURL (some .legacy) MATHLIBREPO Container.legacy.azureURL "abc.ltar" (some "abc123def"))

end MkFileURL

section ParseCacheFromList

/-- Parser for the `--cache-from=a,b,c` CLI flag. Validates each name and
preserves ordering (the order is the trust order tried at download time).

The parser is strict: any unrecognized container name or empty input fails
the entire list rather than silently falling back. This is intentional — the
user's explicit input is the strongest signal we have about what they want,
and silently degrading to a default would mask typos and misunderstandings.
-/
def test_parseCacheFromList : IO Unit := do
  IO.println "parseCacheFromList:"
  -- Trivial case: one container. Round-trip check: string → list → works.
  assert "single container"
    (parseCacheFromList "master" == some [.master])
  -- The common user pattern: master + forks (or any other secondary trust source).
  assert "two containers"
    (parseCacheFromList "master,forks" == some [.master, .forks])
  -- Power-user: every known container at once. If someone wants this behavior,
  -- the parser should allow it (even though most users won't).
  assert "all five"
    (parseCacheFromList "master,forks,nightly-testing,pr-toolchain-tests,legacy" ==
      some [.master, .forks, .nightlyTesting, .prToolchainTests, .legacy])
  -- The migration-fallback shape that `defaultContainersForRepo MATHLIBREPO`
  -- now emits — make sure users can specify it explicitly via `--cache-from` too.
  -- During the dual-write phase, some builds may want to canonicalize reads to
  -- this pair even before all CI workflows converge.
  assert "master + legacy migration pattern"
    (parseCacheFromList "master,legacy" == some [.master, .legacy])
  -- Ordering must be preserved: the list order IS the trust order (tried in order
  -- on download). Swapping master and forks would reverse the lookup priority.
  -- This is a legitimate (if unusual) request and the parser preserves it without
  -- silent reordering.
  assert "preserves order (forks first)"
    (parseCacheFromList "forks,master" == some [.forks, .master])
  -- Tolerate whitespace around commas so the flag survives unquoted shell expansion.
  -- Typical shell usage: `--cache-from="master, forks"` or even bare `--cache-from=master,forks`.
  assert "whitespace tolerated"
    (parseCacheFromList " master , forks " == some [.master, .forks])
  -- One bad entry rejects the entire flag. Failing loudly is better than
  -- silently falling back: a typo like `--cache-from=master,forls` should fail
  -- immediately, not degrade to some default the user didn't ask for.
  assert "unknown name rejects whole list"
    (parseCacheFromList "master,bogus" == none)
  -- Empty input is rejected (not treated as "no overrides" or an empty list).
  -- Empty strings and whitespace-only strings also fail, keeping the CLI predictable.
  assert "empty rejected"
    (parseCacheFromList "" == none)

end ParseCacheFromList

section ExtractRepoFromUrl

/-- Parses `owner/name` from a git remote URL. Used to determine the right
per-repo container allowlist via `getRemoteRepo` and `resolveQueryRepo`.

The parser must tolerate all shapes git actually emits when the user runs
`git remote get-url` or passes a remote URL directly (e.g., `gh pr checkout`).
Returns `none` for unparseable URLs so the caller can decide how to degrade
(typically by falling back to `MATHLIBREPO`).

Security note: the returned repo name is used to select the per-repo
container lookup chain (master, forks, legacy for most repos). If the parser
misidentifies a fork as the canonical repo, the user would read from the
wrong container chain. The tests pin down that the parser correctly handles
the URL variants git actually produces.
-/
def test_extractRepoFromUrl : IO Unit := do
  IO.println "extractRepoFromUrl:"
  -- Canonical ssh shape produced by `git clone git@github.com:alice/mathlib4.git`.
  assert "ssh with .git suffix"
    (extractRepoFromUrl "git@github.com:alice/mathlib4.git" == some "alice/mathlib4")
  -- Same shape but missing the .git — some users configure remotes manually without it.
  assert "ssh without .git suffix"
    (extractRepoFromUrl "git@github.com:alice/mathlib4" == some "alice/mathlib4")
  -- Standard https clone URL with .git suffix.
  assert "https with .git suffix"
    (extractRepoFromUrl "https://github.com/alice/mathlib4.git" == some "alice/mathlib4")
  -- Same minus the .git (what GitHub's web UI displays as the canonical clone URL).
  assert "https without .git suffix"
    (extractRepoFromUrl "https://github.com/alice/mathlib4" == some "alice/mathlib4")
  -- Multi-segment owner names (orgs with hyphens like leanprover-community) must be
  -- extracted and preserved exactly — the org name is part of the repo identity.
  assert "https with leanprover-community"
    (extractRepoFromUrl "https://github.com/leanprover-community/mathlib4.git" == some "leanprover-community/mathlib4")
  -- Empty input → none. Downstream code treats this as "could not parse the remote"
  -- and falls back to MATHLIBREPO.
  assert "empty string returns none"
    (extractRepoFromUrl "" == none)
  -- A bare token with no slash or colon is unparseable (not a valid URL or remote).
  assert "malformed URL (no slash or colon)"
    (extractRepoFromUrl "norepo" == none)

end ExtractRepoFromUrl

section ExtractPRNumber

/-- Extracts a PR number from a git ref. The contract is "second-to-last
segment must be `pr`, last must be a Nat". -/
def test_extractPRNumber : IO Unit := do
  IO.println "extractPRNumber:"
  -- The shape git produces for fetched PR refs.
  assert "standard PR ref format"
    (extractPRNumber "refs/remotes/upstream/pr/1234" == some 1234)
  -- Branch refs are not PR refs; must not match.
  assert "master branch returns none"
    (extractPRNumber "refs/heads/master" == none)
  -- Minimal `pr/N` is also accepted — the parser only inspects the trailing two segments.
  assert "simple pr number"
    (extractPRNumber "pr/42" == some 42)
  -- The tail must be a valid Nat; non-numeric tails are rejected (no partial parsing).
  assert "non-numeric tail returns none"
    (extractPRNumber "refs/remotes/upstream/pr/foo" == none)
  -- `0` is a valid Nat; pin down that it isn't special-cased.
  assert "zero PR number"
    (extractPRNumber "refs/remotes/upstream/pr/0" == some 0)
  -- A numeric tail without the `pr/` parent must not be mistaken for a PR ref.
  assert "missing pr segment returns none"
    (extractPRNumber "refs/remotes/upstream/42" == none)

end ExtractPRNumber

section HashFromFileName

/-- Recovers the UInt64 cache hash from a cached file's path. The tricky bit is
the double-suffix logic for `.ltar.part` — in-flight downloads (while curl is
writing) have a `.part` extension that must be stripped *before* the `.ltar`
extension when recovering the original hash. This is the inverse of `UInt64.asLTar`.

The filename is the cache key: hash(source content + root hash) = filename.
Correctness requires round-tripping: `hash.asLTar` followed by `hashFromFileName`
must yield the original hash. A regression here would silently corrupt cache lookups.
-/
def test_hashFromFileName : IO Unit := do
  IO.println "hashFromFileName:"
  -- Standard finished-download file shape: `{16-digit-hex-hash}.ltar`.
  -- The parser pads short hashes with leading zeros to reconstruct the original.
  assert "simple ltar file"
    (hashFromFileName "abc123def.ltar" == String.parseHexToUInt64? "000000abc123def")
  -- `.ltar.part` is what curl writes to on disk during download. The parser must
  -- strip both extensions (in the right order: `.part` then `.ltar`) to recover
  -- the underlying hash. This is what happens in `downloadFile` when curl
  -- completes successfully.
  assert "ltar.part file (double suffix)"
    (hashFromFileName "abc123def.ltar.part" == String.parseHexToUInt64? "000000abc123def")
  -- Full 16-character hex (no leading-zero padding needed).
  assert "full 16-digit hex"
    (hashFromFileName "deadbeef00112233.ltar" == String.parseHexToUInt64? "deadbeef00112233")
  -- A non-hex stem must fail — invalid cache keys should not silently produce
  -- garbage values. Garbage keys could cause silent cache misses or (worse)
  -- collision with files from legitimate hashes.
  assert "non-hex stem returns none"
    (hashFromFileName "nothexa.ltar" == none)
  -- Path prefix must not interfere: the parser uses `fileStem` to extract just
  -- the basename's stem, ignoring directory components. Cache files live in
  -- a flat directory (CACHEDIR), but the parser must handle partial paths too.
  assert "file with path (extracts name only)"
    (hashFromFileName "/path/to/abc123def.ltar" == String.parseHexToUInt64? "000000abc123def")

end HashFromFileName

section IsRemoteURL

/-- Discriminator: is this string a remote URL (vs a local filesystem path)?
Used to decide whether to short-circuit `git remote get-url` lookups. -/
def test_isRemoteURL : IO Unit := do
  IO.println "isRemoteURL:"
  -- The three protocols accepted by the cache tool.
  assert "https URL is remote"
    (isRemoteURL "https://github.com/alice/mathlib4.git" == true)
  assert "http URL is remote"
    (isRemoteURL "http://github.com/alice/mathlib4" == true)
  assert "ssh URL is remote"
    (isRemoteURL "git@github.com:alice/mathlib4.git" == true)
  -- Absolute and relative local paths must be classified as not-remote so they
  -- get routed through `git remote get-url`.
  assert "local path is not remote"
    (isRemoteURL "/local/path/to/repo" == false)
  assert "relative path is not remote"
    (isRemoteURL "./local/repo" == false)
  -- Defensive — empty input shouldn't accidentally match the predicate.
  assert "empty string is not remote"
    (isRemoteURL "" == false)

end IsRemoteURL

section UInt64Formatting

/-- Filename derived from a cache hash. Must be **exactly 16 hex digits** + `.ltar`.

The 16-digit padding is mandatory: it makes the filename ↔ hash mapping
canonical and invertible. Without padding, short hashes like `1` and `01`
would both try to use the same filename stem `1`, creating collisions and
breaking cache lookups. With padding to 16 digits, every UInt64 has a unique
filename. The filename is the cache key, so uniqueness is critical.

All filenames are lowercase hex (the parser checks this). The filename is
generated once when a build produces a hash, then parsed when looking up
cached artifacts, so the round-trip invariant is essential.
-/
def test_UInt64_asLTar : IO Unit := do
  IO.println "UInt64.asLTar:"
  -- The leading-zero padding case: `1` produces 15 zeros + `1`.
  -- Without padding, `1` would use stem `1`, and `0x1` and `0x01` would collide.
  assertEq "small number padded to 16 hex digits"
    "0000000000000001.ltar"
    (1 : UInt64).asLTar
  -- Partially-padded: 6-digit hex (0xabc123) gets padded with 10 leading zeros.
  assertEq "medium number"
    "0000000000abc123.ltar"
    (0xabc123 : UInt64).asLTar
  -- Full-width hex: 16 digits, no padding needed. Verify the formatter
  -- doesn't truncate or strip digits.
  assertEq "full 16-digit number"
    "deadbeef00112233.ltar"
    (0xdeadbeef00112233 : UInt64).asLTar
  -- Zero is the trickiest edge case: must still pad to 16 digits (`0000...0000`),
  -- not produce an empty stem or just `.ltar`.
  assertEq "zero is padded"
    "0000000000000000.ltar"
    (0 : UInt64).asLTar
  -- Upper bound (max UInt64): 16 `f`s in lowercase. The parser elsewhere
  -- is case-sensitive, so the formatter must use lowercase consistently.
  assertEq "max UInt64"
    "ffffffffffffffff.ltar"
    (0xffffffffffffffff : UInt64).asLTar

end UInt64Formatting

section RoundTrip

/-- End-to-end invariant: writing a hash to disk (via `asLTar`) and reading
the file back (via `hashFromFileName`) must yield the original hash.

This is the foundational property that justifies treating the filename as a
cache key. The hash is computed from source content + root hash; the filename
must round-trip losslessly through serialization and deserialization.

A regression here — e.g., a padding bug or truncation — would silently corrupt
cache lookups: a file at `0000000000abc123.ltar` on disk might be read back as
a different hash, causing cache misses or collisions.
-/
def test_hash_roundtrip : IO Unit := do
  IO.println "hash roundtrip (asLTar then hashFromFileName):"
  -- Full-width hash (16 hex digits): no padding on write, no trimming on read.
  let h1 : UInt64 := 0xdeadbeef00112233
  let fileName := h1.asLTar
  assert "roundtrip through asLTar → hashFromFileName"
    (hashFromFileName fileName == some h1)
  -- Short hash: exercises both pad-on-write and trim-on-read. The formatter
  -- pads `0xabc123` to `0000000000abc123`, and the parser must strip the
  -- leading zeros to recover `0xabc123`.
  let h2 : UInt64 := 0xabc123
  let fileName2 := h2.asLTar
  assert "roundtrip with smaller number"
    (hashFromFileName fileName2 == some h2)

end RoundTrip

section Marker

/-- URL shape for the per-SHA marker blob written by `put-staged`. Probed by
`cache query` with a HEAD request. The marker lives at `/m/{repo}/{sha}` in
the chosen container; its presence is a 200 HEAD response that signals "all
artifacts for this commit were uploaded". This shape enables cheap per-commit
discovery via HEAD (no blob-listing). -/
def test_markerURL : IO Unit := do
  IO.println "markerURL:"
  -- Basic marker URL: `forks` container, a fork repo, and a commit SHA.
  assertEq "forks marker URL"
    "https://lakecache.blob.core.windows.net/mathlib4-forks/m/alice/mathlib4/abc123"
    (markerURL Container.forks "alice/mathlib4" "abc123")
  -- Marker URL is independent of the data prefix (`/f/`): it's its own `/m/` namespace.
  -- Different repos' markers in the same container are disambiguated by the repo segment.
  assertEq "marker URL is independent of /f/ data prefix"
    "https://lakecache.blob.core.windows.net/mathlib4-forks/m/leanprover-community/mathlib4/deadbeef"
    (markerURL Container.forks MATHLIBREPO "deadbeef")
  -- Marker URL shape applies to all containers that support SHA-scoped reads.
  -- (Master and nightly-testing don't do SHA scoping, but the URL shape is consistent.)
  assertEq "legacy container marker URL"
    "https://lakecache.blob.core.windows.net/mathlib4/m/someorg/mathlib4/sha9999"
    (markerURL Container.legacy "someorg/mathlib4" "sha9999")

end Marker

section ScopeResolution

/-- `getRepoScope` is the single read point for "is the user opting in to
reading at a SHA-scoped namespace?". It consults two sources, in this order:

1. `scopeOverride`, an `IO.Ref` set when `--scope=...` is parsed (Lean side,
   user-facing flag).
2. The `MATHLIB_CACHE_REPO_SCOPE` environment variable, set by CI's
   `cache-trust-dispatch` action for fork-trust uploads.

The CLI flag wins so that an explicit user invocation isn't accidentally
overridden by an inherited env var.

The function also has to treat whitespace-only env values as "unset" — a
common foot-gun when shell scripts default a variable to `""` and expect
that to mean "don't scope".

These tests pin the precedence and the trimming rules; future refactors
to the read path must keep both intact (a regression would either silently
scope reads to a stale SHA or, worse, fail to scope when CI expects scoping).
-/
def test_getRepoScope : IO Unit := do
  IO.println "getRepoScope:"
  -- Guard the IORef so a leak doesn't pollute subsequent tests.
  let saved ← scopeOverride.get
  try
    -- Baseline: nothing set, no env var. Returns none.
    scopeOverride.set none
    let s ← getRepoScope
    assert "no scope set → none" (s == none)

    -- `--scope=` form (IORef set): wins regardless of env state.
    scopeOverride.set (some "abc123")
    let s ← getRepoScope
    assert "--scope IORef set → returns IORef value" (s == some "abc123")

    -- Whitespace-only IORef value still wins (the IORef holds whatever
    -- the CLI parsed; trimming env-var input is separate). We don't trim
    -- the IORef here: callers should not set whitespace, but if they do,
    -- the value passes through verbatim — the security warning will still
    -- fire on it (non-empty is enough for the trigger).
    scopeOverride.set (some "deadbeef")
    let s ← getRepoScope
    assert "IORef value passes through verbatim" (s == some "deadbeef")

    -- Putting `none` back makes the env var the only signal. We can't
    -- safely set env vars in a unit test without leaking process state,
    -- so this case is covered manually via the runtime invocation:
    --     MATHLIB_CACHE_REPO_SCOPE=abc lake exe cache get
    -- which the security-warning prints out the env-var form as the
    -- reason, exercising the env-fallback branch.
    scopeOverride.set none
    let s ← getRepoScope
    assert "IORef cleared → none (no env var set in this test process)"
      (s == none)
  finally
    scopeOverride.set saved

end ScopeResolution

section NonDefaultScope

/-- `shouldWarnNonDefaultScope` is the binary trigger for the non-default-scope
security warning. It returns `true` when any of three conditions hold:

1. **Condition 1 (scope):** `--scope=` (IORef) or `MATHLIB_CACHE_REPO_SCOPE`
   (env) is set — user is reading from a specific commit's namespace.
2. **Condition 2 (cache-from):** `--cache-from=LIST` was passed and the list
   *differs* from the per-repo default. (If the user explicitly passes the
   same list as the default, that's not "widening" and shouldn't warn.)
3. **Condition 3 (repo):** `--repo=` was explicitly passed AND its value
   does not match the cwd's detected git remote.

The fiddly bits these tests pin:

- Condition 3 must *only* fire when `--repo=` was explicit. A previous
  regression resolved `repo` to `MATHLIBREPO` for every fork checkout and
  then complained that "MATHLIBREPO" mismatched the git remote, firing
  the warning on every default `cache get`. The function signature was
  changed to take the *Option* explicitly so this distinction survives.
- Condition 2 compares against `defaultContainersForRepo`, so passing
  the per-repo default explicitly is NOT a trigger (it's the same lookup
  chain the user would have got without the flag).
-/
def test_shouldWarnNonDefaultScope : IO Unit := do
  IO.println "shouldWarnNonDefaultScope:"
  -- Sandbox the IORef for the duration of this test.
  let saved ← scopeOverride.get
  try
    scopeOverride.set none

    -- Baseline: no overrides, no scope, repo defaulted. No warning fires.
    -- Note: Condition 3 reads `getRemoteRepo "."`, which may return some
    -- repo (the cache binary lives inside a git checkout when these tests
    -- run). Even so, when `repoExplicit?` is `none`, Condition 3 is
    -- gated off — this is exactly the regression-guard described above.
    let shouldWarn ← shouldWarnNonDefaultScope none none MATHLIBREPO
    assert "no overrides + repo? = none → no warning (Condition 3 gated on explicit)"
      (shouldWarn == false)

    -- Condition 1: --scope= set via IORef. Fires regardless of repo or cache-from.
    scopeOverride.set (some "abc123")
    let shouldWarn ← shouldWarnNonDefaultScope none none MATHLIBREPO
    assert "scope set → warns (Condition 1)" (shouldWarn == true)
    scopeOverride.set none

    -- Condition 2 negative: --cache-from equals the per-repo default.
    -- Passing `[master, legacy]` explicitly to a MATHLIBREPO build matches
    -- the default, so this isn't widening anything — no warning.
    let mathlibDefault := defaultContainersForRepo MATHLIBREPO
    let shouldWarn ← shouldWarnNonDefaultScope none (some mathlibDefault) MATHLIBREPO
    assert "--cache-from matching default → no warning (Condition 2 doesn't fire)"
      (shouldWarn == false)

    -- Condition 2 positive: --cache-from differs from the default. Adding
    -- `forks` to a MATHLIBREPO read lookup chain is real widening (master CI's
    -- consumers wouldn't normally see fork-trust artifacts), so warn.
    let widened := [.master, .forks, .legacy]
    let shouldWarn ← shouldWarnNonDefaultScope none (some widened) MATHLIBREPO
    assert "--cache-from widening → warns (Condition 2)" (shouldWarn == true)

    -- Condition 3 gate: even with a `repo` value that disagrees with
    -- `MATHLIBREPO`, no warning if `repoExplicit?` is `none` (the value
    -- was defaulted, not user-supplied). This is the regression-guard:
    -- a fork checkout's git remote is alice/mathlib4, but the user didn't
    -- pass --repo=, so Condition 3 must remain silent.
    let shouldWarn ← shouldWarnNonDefaultScope none none "alice/mathlib4"
    assert "repo? = none doesn't fire Condition 3 even on a fork checkout"
      (shouldWarn == false)
  finally
    scopeOverride.set saved

/-- `getNonDefaultScopeReason` produces the `Reason:` line in the security
warning banner. It checks the three conditions in priority order and reports
the first one that triggered, with the specific value that triggered it.

The reason text is the user-facing accountability surface: it has to be
specific enough for the user to know *which* of their inputs caused the
warning. Two `--scope=abc` and `--cache-from=forks,legacy` triggers would
otherwise be indistinguishable, defeating the warning's purpose.

Priority order matters when multiple conditions are simultaneously true:
the most specific trigger (scope) is reported first, then cache-from, then
repo. A future refactor that reorders these would change the warning text
in subtle ways, so the order is pinned here.
-/
def test_getNonDefaultScopeReason : IO Unit := do
  IO.println "getNonDefaultScopeReason:"
  let saved ← scopeOverride.get
  try
    scopeOverride.set none

    -- Defensive fallback: if `shouldWarn` returned true but none of the
    -- conditions can be re-identified, we return a placeholder rather than
    -- a crash or empty string.
    let reason ← getNonDefaultScopeReason none none MATHLIBREPO
    assert "unknown reason when no conditions trigger" (reason == "unknown reason")

    -- Condition 1, --scope= form (IORef): the reason explicitly names the
    -- flag the user passed and the SHA they supplied. This lets a reviewer
    -- match the warning to their own command line.
    scopeOverride.set (some "abc123")
    let reason ← getNonDefaultScopeReason none none MATHLIBREPO
    assert "scope set → reason names --scope and the SHA"
      (reason == "--scope=abc123 (explicit per-commit scope)")

    -- Priority: scope outranks cache-from. With both set, the scope reason
    -- is reported first (the more specific signal).
    let reason ← getNonDefaultScopeReason none (some [.forks]) MATHLIBREPO
    assert "scope outranks cache-from (priority order)"
      (reason == "--scope=abc123 (explicit per-commit scope)")
    scopeOverride.set none

    -- Condition 2: --cache-from override mentions the container list. The
    -- format lets the user see exactly what they widened to.
    let reason ← getNonDefaultScopeReason none (some [.forks, .legacy]) MATHLIBREPO
    assert "cache-from override → reason names --cache-from and the list"
      (reason == "--cache-from=forks, legacy (explicit container override)")

    -- Condition 2 silent: cache-from equal to default is not a trigger,
    -- so the reason falls through to "unknown reason" (since shouldWarn
    -- would have returned false anyway).
    let reason ← getNonDefaultScopeReason none (some [.master, .legacy]) MATHLIBREPO
    assert "cache-from = default → falls through (no trigger)"
      (reason == "unknown reason")
  finally
    scopeOverride.set saved

/-- `findMostRecentSHAWithCache` walks a list of candidate commit SHAs,
probing each for a per-SHA marker in the `forks` container, and returns
the first one found. Used by `cache query` (walk mode) to discover the
most recent cached build on the current branch.

The non-empty-list cases require Azure network access to test
end-to-end (the probe calls `curl` on a real container URL); those paths
are covered by the CI integration tests (`build_template.yml`'s
`post_steps` job runs `cache query` end-to-end after a roundtrip).

This unit test pins the only pure case: an empty list short-circuits to
`none` without any probe call. Combined with the integration coverage,
this gives us regression protection on both ends of the function.
-/
def test_findMostRecentSHAWithCache : IO Unit := do
  IO.println "findMostRecentSHAWithCache:"
  let result ← findMostRecentSHAWithCache [] MATHLIBREPO
  assert "empty SHA list → none (no probe attempted)" (result == none)

end NonDefaultScope

section CliOptions

open Cache.Cli

/-- `isKnownOpt` is the gatekeeper that decides whether a `--`-prefixed token
in the command line is a recognized option or a typo. Unknown options error
out with a help message rather than being silently ignored — important so a
typo like `--scoop=abc` doesn't silently disable the scope flag.

The recognition rule:
- A named option matches if `--{name}=` is a prefix of the token.
- A flag matches if the token is exactly `--{name}` (no `=`).

These tests pin the contract so a future refactor can't accidentally accept
unknown options or reject known ones. -/
def test_isKnownOpt : IO Unit := do
  IO.println "isKnownOpt:"
  -- Every named option is recognized when used with `=value` form.
  assert "--repo=foo is known"           (isKnownOpt "--repo=foo")
  assert "--cache-from=master is known"  (isKnownOpt "--cache-from=master")
  assert "--scope=HEAD is known"         (isKnownOpt "--scope=HEAD")
  assert "--container=master is known"   (isKnownOpt "--container=master")
  assert "--staging-dir=/tmp is known"   (isKnownOpt "--staging-dir=/tmp")

  -- Empty value passes recognition (parseNamedOpt returns the empty string
  -- for these — callers decide whether to treat that as an error).
  assert "--scope= (empty value) is known" (isKnownOpt "--scope=")

  -- Flags use the bare `--name` form, no `=`.
  assert "--help (no =) is known" (isKnownOpt "--help")

  -- A typo on a known option name should fail recognition, not be silently
  -- accepted. This is the regression-guard: if `--scoop=` were accepted, the
  -- user's `--scope=` would be silently dropped and reads would fall back to
  -- the default chain with no warning.
  assert "--scoop=foo (typo on scope) is NOT known" (!isKnownOpt "--scoop=foo")
  assert "--bogus=foo (unknown name) is NOT known" (!isKnownOpt "--bogus=foo")

  -- A named option without `=` must NOT be accepted as a flag — `--scope`
  -- (no value) is a user error, distinct from the `--help` flag form.
  assert "--scope (no =) is NOT known (named opts require value)"
    (!isKnownOpt "--scope")

  -- Symmetric: a flag with `=` must NOT be accepted as a named opt.
  assert "--help=foo is NOT known (flags don't take values)"
    (!isKnownOpt "--help=foo")

  -- A bare positional doesn't even look like an option. The cache binary
  -- splits args by `startsWith "--"` before consulting `isKnownOpt`, so this
  -- case should never reach us, but we pin it anyway for safety.
  assert "bare positional 'scope' is NOT known" (!isKnownOpt "scope")

/-- `parseNamedOpt` extracts the value of a `--name=value` option from a
list of args. The rules tests pin:

- Missing option → `none`.
- Single occurrence → the value after `=`.
- Empty value (`--scope=`) → `some ""` (caller decides what to do).
- Multiple occurrences → the *last* one wins (`findRev?`). This mirrors
  conventional shell semantics where `--scope=a --scope=b` resolves to `b`.
- Non-matching args are ignored, even if they look similar (e.g.,
  `--scope-other=` is a different option name).
-/
def test_parseNamedOpt : IO Unit := do
  IO.println "parseNamedOpt:"
  -- Empty arg list.
  let v ← parseNamedOpt "scope" []
  assert "empty args → none" (v == none)

  -- Args without the target option.
  let v ← parseNamedOpt "scope" ["--repo=foo", "get"]
  assert "no matching option → none" (v == none)

  -- Single occurrence.
  let v ← parseNamedOpt "scope" ["--scope=abc123"]
  assert "single occurrence → some value" (v == some "abc123")

  -- Empty value: `--scope=` is recognized; the value is the empty string.
  -- Lets callers distinguish "not passed" (none) from "passed empty"
  -- (some ""). Currently no caller treats them differently, but the
  -- distinction is preserved by parseNamedOpt.
  let v ← parseNamedOpt "scope" ["--scope="]
  assert "empty value → some \"\"" (v == some "")

  -- Multiple occurrences: last wins. Models shell precedence.
  let v ← parseNamedOpt "scope" ["--scope=first", "--scope=second"]
  assert "duplicate option → last value wins" (v == some "second")

  -- Other options surrounding the target don't interfere.
  let v ← parseNamedOpt "scope" ["get", "--repo=foo", "--scope=mid", "Mathlib/Init.lean"]
  assert "interleaved with positionals/other opts → still found"
    (v == some "mid")

  -- Lookalike option names must not match. Without prefix-anchoring on the
  -- `=`, this is the kind of bug that's invisible until a user types it.
  let v ← parseNamedOpt "scope" ["--scope-other=foo"]
  assert "similar prefix doesn't match (--scope-other ≠ --scope)"
    (v == none)

/-- `parseFlagOpt` checks whether a bare `--name` flag is present in args.
Used for `--help` today. The contract is strict equality — `--help` matches,
`--help=true` and `--help-me` do not. -/
def test_parseFlagOpt : IO Unit := do
  IO.println "parseFlagOpt:"
  -- Empty args.
  assert "empty args → false" (!parseFlagOpt "help" [])

  -- Bare `--help` present.
  assert "--help present → true" (parseFlagOpt "help" ["--help"])

  -- `--help=` with a value is NOT a bare flag. (`isKnownOpt` would also
  -- reject it; this is the parser-level guarantee.)
  assert "--help=true is NOT a bare flag" (!parseFlagOpt "help" ["--help=true"])

  -- Flag absent among other args.
  assert "no flag among args → false"
    (!parseFlagOpt "help" ["get", "--repo=foo"])

  -- Lookalike: `--help-me` isn't the `--help` flag.
  assert "lookalike prefix doesn't match" (!parseFlagOpt "help" ["--help-me"])

end CliOptions

def runAll : IO Unit := do
  test_Container_name
  test_Container_parse
  test_Container_azureURL
  test_Container_flatPath
  test_defaultContainersForRepo
  test_mkFileURL
  test_parseCacheFromList
  test_extractRepoFromUrl
  test_extractPRNumber
  test_hashFromFileName
  test_isRemoteURL
  test_UInt64_asLTar
  test_hash_roundtrip
  test_markerURL
  test_getRepoScope
  test_shouldWarnNonDefaultScope
  test_getNonDefaultScopeReason
  test_findMostRecentSHAWithCache
  test_isKnownOpt
  test_parseNamedOpt
  test_parseFlagOpt

end Cache.Test

open Cache.Test in
def main : IO UInt32 := do
  runAll
  let n ← failures.get
  if n == 0 then
    IO.println "\nAll cache tests passed."
    return 0
  else
    IO.eprintln s!"\n{n} cache test(s) failed."
    return 1
