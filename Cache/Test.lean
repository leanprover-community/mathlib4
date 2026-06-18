/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Cli
import Cache.Requests
import Cache.Marker
import Cache.Query
import Cache.Warning
import Cache.Lean

/-!
# Unit tests for the cache CLI

These tests cover the pure logic of the cache system, including:
- Container model (trust levels, URL shapes, Azure integration)
- Trust-ordered fallback chains per repo
- URL construction (`mkFileURL`) with support for per-SHA scoping
- CLI flag parsing (`--cache-from`, `--scope`, `--unsafe`, `--repo`, etc.)
- `--unsafe` download-round expansion (`expandDownloadRounds`) and the
  non-default-scope security warning it triggers
- Utility functions (URL extraction, filename hashing, etc.)

Anything that touches `curl` or the network is left to CI, which exercises the
`cache get`/`put` paths end-to-end on real containers.

## Invariants these tests defend

1. Trust boundary per container: each container has a dedicated writer (OIDC +
   Azure RBAC) and reads follow a per-repo trust-ordered list, so a PR cannot
   upload to a higher-trust container.
2. Per-SHA namespace for fork uploads: fork uploads land at `/f/{repo}/{sha}/{hash}`,
   so one commit's artifacts never serve another commit on the same fork.
3. Flat layout for single-writer containers: `master` reads and writes flat at
   `/f/{hash}`, the path older tools also use.
4. Prefixed layout for multi-writer containers: `forks`, `nightly-testing`, and
   `pr-toolchain-tests` namespace by repo so uploads from different sources don't
   collide.
5. `legacy` stays readable with its mixed layout (flat for the canonical repo,
   prefixed for forks) so older clients keep working.

## Running the tests

Run with `lake exe cache-test`. Exits 0 on success, non-zero on failure.

The tests stand alone (no dependency on `MathlibTest`). A Lake package has a
single `testDriver`, and the enclosing `mathlib` package binds that to
`MathlibTest` (see `lakefile.lean`); if the cache tool moves to its own Lake
project, the `cache-test` `lean_exe` here can become that project's `testDriver`.
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

/-- Run `action` with both stdout and stderr redirected to /dev/null. Restores
both on completion, including on exception. Apply this to every production code
call in tests so diagnostic prints never mix with test output, regardless of
whether the production code currently produces any. -/
private def withSuppressedOutput (action : IO α) : IO α := do
  let savedOut ← IO.getStdout
  let savedErr ← IO.getStderr
  let sink ← IO.FS.Handle.mk "/dev/null" IO.FS.Mode.append
  let sinkStream := IO.FS.Stream.ofHandle sink
  -- `IO.setStdout`/`IO.setStderr` return the previous stream; we already saved it,
  -- so discard the return value here.
  discard <| IO.setStdout sinkStream
  discard <| IO.setStderr sinkStream
  try
    let r ← action
    discard <| IO.setStdout savedOut
    discard <| IO.setStderr savedErr
    return r
  catch e =>
    discard <| IO.setStdout savedOut
    discard <| IO.setStderr savedErr
    throw e

section ContainerModel

/-- The short name is the string used on the CLI (`--container=NAME`) and to
derive the Azure container name. These names are part of the public CLI
contract, so they are pinned here: a rename must be a deliberate edit to this
test, not an accident. -/
def test_Container_name : IO Unit := do
  IO.println "Container.name:"
  assertEq "master"             "master"             Container.master.name
  assertEq "forks"              "forks"              Container.forks.name
  assertEq "nightly-testing"    "nightly-testing"    Container.nightlyTesting.name
  assertEq "pr-toolchain-tests" "pr-toolchain-tests" Container.prToolchainTests.name
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
  -- Matching is case-insensitive, so `--container=Master` canonicalizes too.
  assert "case-insensitive"       (Container.parse? "Master" == some .master)
  -- An unknown name returns `none` so `--container=bogus` errors out rather than
  -- defaulting to some container the user didn't ask for.
  assert "unknown rejected"       (Container.parse? "bogus" == none)
  assert "empty rejected"         (Container.parse? "" == none)

/-- The Azure URL each container resolves to: `mathlib4-{name}` for the
trust-level containers, bare `mathlib4` for `legacy`. These URLs go into every
request, and changing one means re-coordinating the Azure side with every
consumer, so they are pinned here. -/
def test_Container_azureURL : IO Unit := do
  IO.println "Container.azureURL:"
  assertEq "master URL"
    "https://lakecache.blob.core.windows.net/mathlib4-master"
    Container.master.azureURL
  assertEq "forks URL"
    "https://lakecache.blob.core.windows.net/mathlib4-forks"
    Container.forks.azureURL
  assertEq "nightly-testing URL"
    "https://lakecache.blob.core.windows.net/mathlib4-nightly-testing"
    Container.nightlyTesting.azureURL
  assertEq "pr-toolchain-tests URL"
    "https://lakecache.blob.core.windows.net/mathlib4-pr-toolchain-tests"
    Container.prToolchainTests.azureURL
  -- `legacy` is the bare `mathlib4` container, with no `-legacy` suffix.
  assertEq "legacy URL"
    "https://lakecache.blob.core.windows.net/mathlib4"
    Container.legacy.azureURL

/-- Whether a container lays files out flat (`/f/<hash>`) or namespaces them by
repo (`/f/<repo>/<hash>`). The layout is fixed per container so that all of a
container's writers stay on non-colliding paths:
- `master` is flat for every repo (one writer, no collisions possible).
- `forks`, `nightly-testing`, and `pr-toolchain-tests` are prefixed for every
  repo, including the canonical one, so fork-trust uploads from the canonical
  repo coexist with fork uploads.
- `legacy` is flat for the canonical repo and prefixed otherwise.
-/
def test_Container_flatPath : IO Unit := do
  IO.println "Container.flatPath:"
  assert "master is flat for the canonical repo"
    (Container.master.flatPath MATHLIBREPO == true)
  assert "master is flat for a fork repo too"
    (Container.master.flatPath "alice/mathlib4" == true)
  assert "legacy is flat for the canonical repo"
    (Container.legacy.flatPath MATHLIBREPO == true)
  assert "legacy is prefixed for a fork repo"
    (Container.legacy.flatPath "alice/mathlib4" == false)
  assert "forks is prefixed for the canonical repo"
    (Container.forks.flatPath MATHLIBREPO == false)
  assert "forks is prefixed for a fork repo"
    (Container.forks.flatPath "alice/mathlib4" == false)
  assert "nightly-testing is prefixed for the nightly-testing repo"
    (Container.nightlyTesting.flatPath NIGHTLY_TESTING_REPO == false)
  assert "nightly-testing is prefixed for the canonical repo"
    (Container.nightlyTesting.flatPath MATHLIBREPO == false)
  assert "pr-toolchain-tests is prefixed for the nightly-testing repo"
    (Container.prToolchainTests.flatPath NIGHTLY_TESTING_REPO == false)

end ContainerModel

section PerRepoAllowlist

/-- Trust-ordered read chain per GitHub repo: the tool tries containers in this
order and stops at the first hit, so both membership and ordering are part of
the trust boundary. Key points the tests pin:
- The nightly-testing chain excludes `pr-toolchain-tests`, so trusted-nightly
  consumers never fall back to low-trust toolchain-PR uploads (those branches
  opt into the wider chain via `MATHLIB_CACHE_FROM` in CI).
- The fork chain leads with `master` (shared upstream deps), then `forks`
  (PR-specific files); `master` is absent from the nightly chain because that
  repo's toolchain gives it a different root hash.
- Every chain ends with `legacy`, so older clients' artifacts stay reachable.
-/
def test_defaultContainersForRepo : IO Unit := do
  IO.println "defaultContainersForRepo:"
  assert "canonical repo → [master, legacy]"
    (defaultContainersForRepo MATHLIBREPO == [.master, .legacy])
  assert "nightly-testing repo → [nightly-testing, legacy], no pr-toolchain-tests"
    (defaultContainersForRepo NIGHTLY_TESTING_REPO == [.nightlyTesting, .legacy])
  assert "fork repo → [master, forks, legacy]"
    (defaultContainersForRepo "alice/mathlib4" == [.master, .forks, .legacy])
  assert "unknown repo falls back to the fork chain"
    (defaultContainersForRepo "some/other-repo" == [.master, .forks, .legacy])
  -- Every chain ends with `legacy`; dropping it would quietly shrink hit rates.
  assert "fork chain ends with legacy"
    ((defaultContainersForRepo "alice/mathlib4").getLast? == some .legacy)
  assert "canonical chain ends with legacy"
    ((defaultContainersForRepo MATHLIBREPO).getLast? == some .legacy)
  assert "nightly-testing chain ends with legacy"
    ((defaultContainersForRepo NIGHTLY_TESTING_REPO).getLast? == some .legacy)

end PerRepoAllowlist

section MkFileURL

/-- URL construction for a cache file. The path shape follows the container
(`Container.flatPath`), not the repo, so the same repo lands flat in `master`
and prefixed in `forks`. A `none` container is the user-supplied-URL case
(`MATHLIB_CACHE_GET_URL` / `_PUT_URL`), where the shape follows the repo alone.

A per-SHA scope (`MATHLIB_CACHE_REPO_SCOPE`) inserts `{sha}` between repo and
hash on prefixed paths only — `/f/{repo}/{sha}/{hash}` — keeping each commit's
fork uploads in their own namespace. Flat paths ignore the scope.
-/
def test_mkFileURL : IO Unit := do
  IO.println "mkFileURL:"
  assertEq "master is flat for the canonical repo"
    "https://lakecache.blob.core.windows.net/mathlib4-master/f/abc.ltar"
    (mkFileURL (some .master) MATHLIBREPO Container.master.azureURL "abc.ltar")
  assertEq "master is flat for a fork repo too"
    "https://lakecache.blob.core.windows.net/mathlib4-master/f/abc.ltar"
    (mkFileURL (some .master) "alice/mathlib4" Container.master.azureURL "abc.ltar")
  -- `forks` prefixes by repo even for the canonical repo, so its fork-trust
  -- uploads don't collide with fork uploads in the same container.
  assertEq "forks prefixes by repo for the canonical repo"
    "https://lakecache.blob.core.windows.net/mathlib4-forks/f/leanprover-community/mathlib4/abc.ltar"
    (mkFileURL (some .forks) MATHLIBREPO Container.forks.azureURL "abc.ltar")
  assertEq "forks prefixes by repo for a fork repo"
    "https://lakecache.blob.core.windows.net/mathlib4-forks/f/alice/mathlib4/abc.ltar"
    (mkFileURL (some .forks) "alice/mathlib4" Container.forks.azureURL "abc.ltar")
  assertEq "nightly-testing prefixes by repo"
    "https://lakecache.blob.core.windows.net/mathlib4-nightly-testing/f/leanprover-community/mathlib4-nightly-testing/abc.ltar"
    (mkFileURL (some .nightlyTesting) NIGHTLY_TESTING_REPO
      Container.nightlyTesting.azureURL "abc.ltar")
  assertEq "pr-toolchain-tests prefixes by repo"
    "https://lakecache.blob.core.windows.net/mathlib4-pr-toolchain-tests/f/leanprover-community/mathlib4-nightly-testing/abc.ltar"
    (mkFileURL (some .prToolchainTests) NIGHTLY_TESTING_REPO
      Container.prToolchainTests.azureURL "abc.ltar")
  assertEq "legacy is flat for the canonical repo"
    "https://lakecache.blob.core.windows.net/mathlib4/f/abc.ltar"
    (mkFileURL (some .legacy) MATHLIBREPO Container.legacy.azureURL "abc.ltar")
  assertEq "legacy prefixes by repo for a fork repo"
    "https://lakecache.blob.core.windows.net/mathlib4/f/alice/mathlib4/abc.ltar"
    (mkFileURL (some .legacy) "alice/mathlib4" Container.legacy.azureURL "abc.ltar")
  -- No container (user-supplied URL): the shape follows the repo — flat for the
  -- canonical repo, prefixed otherwise.
  assertEq "user URL is flat for the canonical repo"
    "https://custom.example/cache/f/abc.ltar"
    (mkFileURL none MATHLIBREPO "https://custom.example/cache" "abc.ltar")
  assertEq "user URL prefixes by repo for a fork repo"
    "https://custom.example/cache/f/alice/mathlib4/abc.ltar"
    (mkFileURL none "alice/mathlib4" "https://custom.example/cache" "abc.ltar")
  -- A scope adds a `{sha}` path segment on prefixed paths.
  assertEq "scope adds a SHA segment on a fork path"
    "https://lakecache.blob.core.windows.net/mathlib4-forks/f/alice/mathlib4/abc123def/H.ltar"
    (mkFileURL (some .forks) "alice/mathlib4" Container.forks.azureURL "H.ltar" (some "abc123def"))
  assertEq "scope adds a SHA segment on the canonical repo's forks path"
    "https://lakecache.blob.core.windows.net/mathlib4-forks/f/leanprover-community/mathlib4/abc123def/H.ltar"
    (mkFileURL (some .forks) MATHLIBREPO Container.forks.azureURL "H.ltar" (some "abc123def"))
  -- A scope is ignored on flat paths.
  assertEq "scope is ignored on a flat master path"
    "https://lakecache.blob.core.windows.net/mathlib4-master/f/abc.ltar"
    (mkFileURL (some .master) MATHLIBREPO Container.master.azureURL "abc.ltar" (some "abc123def"))
  assertEq "scope is ignored on a flat legacy path"
    "https://lakecache.blob.core.windows.net/mathlib4/f/abc.ltar"
    (mkFileURL (some .legacy) MATHLIBREPO Container.legacy.azureURL "abc.ltar" (some "abc123def"))
  -- The repo segment is lowercased, so a mixed-case GitHub owner resolves to the
  -- same path whether it reaches the cache from CI or a local remote URL.
  assertEq "fork repo is lowercased in the path"
    "https://lakecache.blob.core.windows.net/mathlib4-forks/f/alice/mathlib4/abc.ltar"
    (mkFileURL (some .forks) "Alice/Mathlib4" Container.forks.azureURL "abc.ltar")

end MkFileURL

section ParseCacheFromList

/-- Parser for `--cache-from=a,b,c`. List order is the trust order tried at
download time, so it is preserved exactly. The parser is strict: one bad name
or empty input fails the whole list rather than degrading to a default, so a
typo surfaces instead of silently changing where the cache is read. -/
def test_parseCacheFromList : IO Unit := do
  IO.println "parseCacheFromList:"
  assert "single container"
    (parseCacheFromList "master" == some [.master])
  assert "two containers"
    (parseCacheFromList "master,forks" == some [.master, .forks])
  assert "all five containers"
    (parseCacheFromList "master,forks,nightly-testing,pr-toolchain-tests,legacy" ==
      some [.master, .forks, .nightlyTesting, .prToolchainTests, .legacy])
  assert "master,legacy"
    (parseCacheFromList "master,legacy" == some [.master, .legacy])
  -- Order is preserved, not normalized: `forks,master` reverses the priority.
  assert "preserves the given order"
    (parseCacheFromList "forks,master" == some [.forks, .master])
  -- Whitespace around commas is tolerated, so the flag survives shell expansion.
  assert "whitespace around names is tolerated"
    (parseCacheFromList " master , forks " == some [.master, .forks])
  assert "one unknown name rejects the whole list"
    (parseCacheFromList "master,bogus" == none)
  assert "empty input is rejected"
    (parseCacheFromList "" == none)

end ParseCacheFromList

section ExtractRepoFromUrl

/-- Parses `owner/name` from a git remote URL. The result selects the per-repo
read chain, so misreading a fork as the canonical repo would read the wrong
chain; these cases cover every URL shape git emits via `git remote get-url` or a
direct remote (e.g. `gh pr checkout`). Unparseable input returns `none`, and the
caller falls back to `MATHLIBREPO`. -/
def test_extractRepoFromUrl : IO Unit := do
  IO.println "extractRepoFromUrl:"
  assert "ssh URL with .git suffix"
    (extractRepoFromUrl "git@github.com:alice/mathlib4.git" == some "alice/mathlib4")
  assert "ssh URL without .git suffix"
    (extractRepoFromUrl "git@github.com:alice/mathlib4" == some "alice/mathlib4")
  assert "https URL with .git suffix"
    (extractRepoFromUrl "https://github.com/alice/mathlib4.git" == some "alice/mathlib4")
  assert "https URL without .git suffix"
    (extractRepoFromUrl "https://github.com/alice/mathlib4" == some "alice/mathlib4")
  -- A hyphenated owner is part of the repo identity and must survive intact.
  assert "hyphenated owner is preserved"
    (extractRepoFromUrl "https://github.com/leanprover-community/mathlib4.git" == some "leanprover-community/mathlib4")
  assert "empty input returns none"
    (extractRepoFromUrl "" == none)
  assert "a token with no slash or colon returns none"
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

/-- Recovers the UInt64 cache hash from a cached file's path, the inverse of
`UInt64.asLTar`. The subtle case is `.ltar.part` — the suffix curl writes during
a download — where `.part` must be stripped before `.ltar`. A regression here
corrupts cache lookups, so both suffixes and a non-hex stem are covered. -/
def test_hashFromFileName : IO Unit := do
  IO.println "hashFromFileName:"
  assert "plain .ltar file"
    (hashFromFileName "abc123def.ltar" == String.parseHexToUInt64? "000000abc123def")
  assert "in-flight .ltar.part file strips both suffixes"
    (hashFromFileName "abc123def.ltar.part" == String.parseHexToUInt64? "000000abc123def")
  assert "full 16-digit hex stem"
    (hashFromFileName "deadbeef00112233.ltar" == String.parseHexToUInt64? "deadbeef00112233")
  -- A non-hex stem returns none rather than a garbage hash.
  assert "non-hex stem returns none"
    (hashFromFileName "nothexa.ltar" == none)
  -- Directory components are ignored; only the basename's stem is parsed.
  assert "leading path is ignored"
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

/-- Filename derived from a cache hash: exactly 16 lowercase hex digits plus
`.ltar`. The fixed width makes the hash ↔ filename mapping unique and
invertible — without it, `0x1` and `0x01` would share a stem and collide. -/
def test_UInt64_asLTar : IO Unit := do
  IO.println "UInt64.asLTar:"
  assertEq "small value is left-padded to 16 digits"
    "0000000000000001.ltar"
    (1 : UInt64).asLTar
  assertEq "mid-width value is left-padded"
    "0000000000abc123.ltar"
    (0xabc123 : UInt64).asLTar
  assertEq "full-width value is not truncated"
    "deadbeef00112233.ltar"
    (0xdeadbeef00112233 : UInt64).asLTar
  assertEq "zero is padded, not emptied"
    "0000000000000000.ltar"
    (0 : UInt64).asLTar
  -- Max value is 16 lowercase `f`s; the parser elsewhere is case-sensitive.
  assertEq "max value is lowercase hex"
    "ffffffffffffffff.ltar"
    (0xffffffffffffffff : UInt64).asLTar

end UInt64Formatting

section RoundTrip

/-- `asLTar` then `hashFromFileName` must return the original hash — the property
that lets the filename serve as the cache key. A padding or truncation bug would
read a file back as a different hash, causing misses or collisions. -/
def test_hash_roundtrip : IO Unit := do
  IO.println "hash roundtrip (asLTar then hashFromFileName):"
  let h1 : UInt64 := 0xdeadbeef00112233
  assert "full-width hash round-trips"
    (hashFromFileName h1.asLTar == some h1)
  -- A short hash exercises both pad-on-write and trim-on-read.
  let h2 : UInt64 := 0xabc123
  assert "padded hash round-trips"
    (hashFromFileName h2.asLTar == some h2)

end RoundTrip

section Marker

/-- URL shape for the per-SHA marker blob written by `put-staged`. Probed by
`cache query` with a HEAD request. The marker lives at `/m/{repo}/{sha}` in
the chosen container; its presence is a 200 HEAD response that signals "all
artifacts for this commit were uploaded". This shape enables cheap per-commit
discovery via HEAD (no blob-listing). -/
def test_markerURL : IO Unit := do
  IO.println "markerURL:"
  assertEq "forks marker URL"
    "https://lakecache.blob.core.windows.net/mathlib4-forks/m/alice/mathlib4/abc123"
    (markerURL .forks "alice/mathlib4" "abc123")
  -- The marker lives under `/m/`, its own namespace, and is keyed by repo.
  assertEq "marker is under /m/, keyed by repo"
    "https://lakecache.blob.core.windows.net/mathlib4-forks/m/leanprover-community/mathlib4/deadbeef"
    (markerURL .forks MATHLIBREPO "deadbeef")
  assertEq "marker URL respects the container base"
    "https://lakecache.blob.core.windows.net/mathlib4/m/someorg/mathlib4/sha9999"
    (markerURL .legacy "someorg/mathlib4" "sha9999")
  -- The repo segment is lowercased, so an upload and a probe for the same fork
  -- meet at one path regardless of how the owner name was capitalized.
  assertEq "marker repo is lowercased in the path"
    "https://lakecache.blob.core.windows.net/mathlib4-forks/m/alice/mathlib4/abc123"
    (markerURL .forks "Alice/Mathlib4" "abc123")

end Marker

section ScopeResolution

/-- `getRepoScope` answers "is the user reading from a SHA-scoped namespace?".
It reads the `--scope=` flag (the `scopeOverride` ref) first, then the
`MATHLIB_CACHE_REPO_SCOPE` env var, so an explicit flag is never overridden by
an inherited env var. The flag value is returned as given. The env-var branch
needs process state, so it is exercised by the CI integration tests rather than
here. -/
def test_getRepoScope : IO Unit := do
  IO.println "getRepoScope:"
  -- Guard the IORef so a leak doesn't pollute subsequent tests.
  let saved ← scopeOverride.get
  try
    scopeOverride.set none
    assert "no scope set returns none" ((← withSuppressedOutput getRepoScope) == none)

    scopeOverride.set (some "abc123")
    assert "the flag value is returned" ((← withSuppressedOutput getRepoScope) == some "abc123")

    -- The flag value is returned as-is, without trimming or normalization.
    scopeOverride.set (some "deadbeef")
    assert "the flag value is returned verbatim"
      ((← withSuppressedOutput getRepoScope) == some "deadbeef")

    scopeOverride.set none
    assert "clearing the flag returns none" ((← withSuppressedOutput getRepoScope) == none)
  finally
    scopeOverride.set saved

end ScopeResolution

section NonDefaultScope

/-- `shouldWarnNonDefaultScope` decides whether `cache get` prints the
non-default-scope security warning. It warns when any of three inputs takes the
reader off the repo's default trust boundary:

1. a scope is set (`--scope=` or `MATHLIB_CACHE_REPO_SCOPE`) and differs from
   the checked-out HEAD;
2. `--cache-from=LIST` differs from the repo's default chain (passing the
   default explicitly is not widening);
3. `--repo=` is given and differs from the detected git remote.

The behavior the tests pin most carefully: a plain `cache get` with no flags
never warns, even on a fork checkout whose remote isn't the canonical repo.
`detectedRepo?` is passed in (resolved once by `resolveRepo`), so the cases are
deterministic without needing a real checkout. -/
def test_shouldWarnNonDefaultScope : IO Unit := do
  IO.println "shouldWarnNonDefaultScope:"
  -- Sandbox the IORef for the duration of this test.
  let saved ← scopeOverride.get
  try
    scopeOverride.set none

    assert "plain get with no flags does not warn"
      (!(← withSuppressedOutput (shouldWarnNonDefaultScope none none none MATHLIBREPO)))

    scopeOverride.set (some "abc123")
    assert "a set scope warns"
      (← withSuppressedOutput (shouldWarnNonDefaultScope none none none MATHLIBREPO))
    scopeOverride.set none

    -- A scope equal to HEAD is trust-equivalent to no scope (CI's normal mode).
    -- Skipped when HEAD can't be resolved (not in a git checkout).
    let head? ← try some <$> withSuppressedOutput getGitCommitHash catch _ => pure none
    if let some head := head? then
      scopeOverride.set (some head)
      assert "a scope equal to HEAD does not warn"
        (!(← withSuppressedOutput (shouldWarnNonDefaultScope none none none MATHLIBREPO)))
      scopeOverride.set none

    -- --cache-from equal to the repo's default chain is not widening.
    let mathlibDefault := defaultContainersForRepo MATHLIBREPO
    assert "--cache-from equal to the default does not warn"
      (!(← withSuppressedOutput
          (shouldWarnNonDefaultScope none none (some mathlibDefault) MATHLIBREPO)))

    assert "--cache-from widening the chain warns"
      (← withSuppressedOutput
          (shouldWarnNonDefaultScope none none (some [.master, .forks, .legacy]) MATHLIBREPO))

    -- A fork checkout (remote ≠ resolved repo) stays silent without an explicit --repo.
    assert "a fork checkout without --repo does not warn"
      (!(← withSuppressedOutput
          (shouldWarnNonDefaultScope none (some "alice/mathlib4") none "alice/mathlib4")))

    assert "--repo differing from the remote warns"
      (← withSuppressedOutput
          (shouldWarnNonDefaultScope (some "bob/mathlib4") (some "alice/mathlib4") none "bob/mathlib4"))

    assert "--repo matching the remote does not warn"
      (!(← withSuppressedOutput
          (shouldWarnNonDefaultScope (some "alice/mathlib4") (some "alice/mathlib4") none
            "alice/mathlib4")))

    -- With no detectable remote there is nothing to compare --repo against.
    assert "--repo with no detectable remote does not warn"
      (!(← withSuppressedOutput
          (shouldWarnNonDefaultScope (some "bob/mathlib4") none none "bob/mathlib4")))

    -- `--unsafe` (any window) always warns; it walks several untrusted scopes.
    assert "--unsafe warns regardless of other inputs"
      (← withSuppressedOutput
          (shouldWarnNonDefaultScope none none none MATHLIBREPO (unsafeWindow? := some 5)))
    assert "no --unsafe (none window) does not warn on its own"
      (!(← withSuppressedOutput
          (shouldWarnNonDefaultScope none none none MATHLIBREPO (unsafeWindow? := none))))
  finally
    scopeOverride.set saved

/-- `getNonDefaultScopeReason` produces the `Reason:` line in the warning, naming
the specific input that triggered it so the user can match it to their command
line. When several inputs apply at once it reports the most specific first —
scope, then `--cache-from`, then `--repo` — and that order is pinned here. -/
def test_getNonDefaultScopeReason : IO Unit := do
  IO.println "getNonDefaultScopeReason:"
  let saved ← scopeOverride.get
  try
    scopeOverride.set none

    -- A placeholder rather than a crash if nothing matches.
    let reason ← withSuppressedOutput (getNonDefaultScopeReason none none none MATHLIBREPO)
    assert "no trigger yields a placeholder reason" (reason == "unknown reason")

    scopeOverride.set (some "abc123")
    let reason ← withSuppressedOutput (getNonDefaultScopeReason none none none MATHLIBREPO)
    assert "scope reason names the flag and SHA"
      (reason == "--scope=abc123 (explicit per-commit scope)")

    -- Scope outranks cache-from when both apply.
    let reason ← withSuppressedOutput (getNonDefaultScopeReason none none (some [.forks]) MATHLIBREPO)
    assert "scope is reported ahead of cache-from"
      (reason == "--scope=abc123 (explicit per-commit scope)")
    scopeOverride.set none

    -- A HEAD scope is exempt from condition 1, so a simultaneous cache-from
    -- trigger is reported instead of the scope.
    let head? ← try some <$> withSuppressedOutput getGitCommitHash catch _ => pure none
    if let some head := head? then
      scopeOverride.set (some head)
      let reason ←
        withSuppressedOutput (getNonDefaultScopeReason none none (some [.forks, .legacy]) MATHLIBREPO)
      assert "a HEAD scope yields the cache-from reason"
        (reason == "--cache-from=forks, legacy (explicit container override)")
      scopeOverride.set none

    let reason ←
      withSuppressedOutput (getNonDefaultScopeReason none none (some [.forks, .legacy]) MATHLIBREPO)
    assert "cache-from reason names the container list"
      (reason == "--cache-from=forks, legacy (explicit container override)")

    let reason ← withSuppressedOutput
      (getNonDefaultScopeReason (some "bob/mathlib4") (some "alice/mathlib4") none "bob/mathlib4")
    assert "repo reason names the override and the detected remote"
      (reason == "--repo=bob/mathlib4 (overrides detected git remote: alice/mathlib4)")

    -- --cache-from equal to the default is not a trigger, so no reason applies.
    let reason ←
      withSuppressedOutput (getNonDefaultScopeReason none none (some [.master, .legacy]) MATHLIBREPO)
    assert "cache-from equal to the default yields the placeholder"
      (reason == "unknown reason")

    -- `--unsafe` outranks every other trigger and names its window.
    scopeOverride.set (some "abc123")
    let reason ← withSuppressedOutput
      (getNonDefaultScopeReason (some "bob/mathlib4") (some "alice/mathlib4") (some [.forks])
        "bob/mathlib4" (unsafeWindow? := some 7))
    assert "unsafe reason names the window and outranks scope/cache-from/repo"
      (reason == "--unsafe (automatic walk over up to 7 fork commit(s); trusting whoever built them)")
    scopeOverride.set none
  finally
    scopeOverride.set saved

/-- `findMostRecentSHAWithCache` returns the first candidate SHA whose per-SHA
marker exists in the `forks` container, used by `cache query` to find the most
recent cached build on the branch. The non-empty cases hit the network (a marker
HEAD probe per SHA) and aren't unit-tested; here we pin that an empty list
returns `none` with no probe. -/
def test_findMostRecentSHAWithCache : IO Unit := do
  IO.println "findMostRecentSHAWithCache:"
  let result ← withSuppressedOutput (findMostRecentSHAWithCache [] MATHLIBREPO)
  assert "empty SHA list returns none without probing" (result == none)

/-- `findRecentSHAsWithCache` collects up to `limit` marked SHAs. The non-empty
cases hit the network (a marker HEAD probe per SHA); here we pin that an empty
candidate list returns `[]` for any limit, with no probe. -/
def test_findRecentSHAsWithCache : IO Unit := do
  IO.println "findRecentSHAsWithCache:"
  let result ← withSuppressedOutput (findRecentSHAsWithCache [] MATHLIBREPO 5)
  assert "empty SHA list returns [] without probing" (result == [])
  let result ← withSuppressedOutput (findRecentSHAsWithCache [] MATHLIBREPO 0)
  assert "limit 0 returns [] without probing" (result == [])

end NonDefaultScope

section GitFallback

/-- `getRemoteRepo` and `resolveRepo` must never throw, regardless of git's
availability or the state of the target path. This matters for `cache get`
invoked inside a Lake dependency update, where the Mathlib dependency may be a
plain archive without a `.git` directory.

Two distinct failure modes are tested:

* **Nonexistent path** — `IO.Process.output` throws before git even starts
  (the OS rejects the invalid cwd). The `try...catch` in `getRemoteRepo` must
  catch the exception and return `none`.

* **Non-git directory** — git runs successfully but the path is not a repo, so
  every git command exits non-zero. The existing exit-code checks already handle
  this path; the test pins that `none` is returned here too.

In both cases `resolveRepo` must fall back to `MATHLIBREPO`, giving the
master-only container chain (no `forks`) — exactly what a dependency build
should read from. -/
def test_getRemoteRepo_gitFallback : IO Unit := do
  IO.println "getRemoteRepo git fallback:"
  -- Case 1: nonexistent cwd causes IO.Process.output to throw.
  -- The try...catch in getRemoteRepo must intercept it and return none.
  let fakePath := "/tmp/surely-nonexistent-mathlib-cache-test-xyz-9999999"
  let r1 ← withSuppressedOutput (getRemoteRepo fakePath)
  assert "getRemoteRepo returns none when git throws (nonexistent cwd)" (r1 == none)

  -- Case 2: existing directory that is not a git repo (git returns exit 128).
  -- This exercises the exit-code fallback path that predates the try...catch.
  let r2 ← withSuppressedOutput (getRemoteRepo "/tmp")
  assert "getRemoteRepo returns none in a non-git directory" (r2 == none)

  -- resolveRepo propagates the fallback correctly:
  --   detected? = none, resolved = MATHLIBREPO → master-only chain.
  let (detected?, resolved) ← withSuppressedOutput (resolveRepo none fakePath)
  assert "resolveRepo detected? is none on git failure" (detected? == none)
  assert "resolveRepo falls back to MATHLIBREPO on git failure" (resolved == MATHLIBREPO)
  assert "fallback chain includes master"
    ((defaultContainersForRepo resolved).contains .master)
  assert "fallback chain excludes forks (no fork container for dependency builds)"
    (!(defaultContainersForRepo resolved).contains .forks)

/-- `headIsAncestorOfMaster` gates the uncached-fork-HEAD note: when HEAD is
already part of master's history, `master` (first in the fork lookup chain)
serves every file by hash, so the note would be a false positive and is
suppressed.

Like `getRemoteRepo`, this helper must never throw — it runs on the read path,
including inside dependency builds where the checkout may not be a git repo (or
may lack a local `master`). Both failure modes degrade to `false` (= "not an
ancestor", so the caller keeps its default behavior):

* **Nonexistent path** — `IO.Process.output` throws before git starts; the
  `try...catch` must intercept it.
* **Non-git directory** — git runs but exits non-zero; the `exitCode == 0`
  check returns `false`.

The positive topology cases (HEAD on master ⇒ `true`; diverged branch ⇒ `false`)
exercise real git history and are covered by the CI integration tests, matching
how the other git-walking helpers are tested. -/
def test_headIsAncestorOfMaster_gitFallback : IO Unit := do
  IO.println "headIsAncestorOfMaster git fallback:"
  let fakePath := "/tmp/surely-nonexistent-mathlib-cache-test-xyz-9999999"
  let r1 ← withSuppressedOutput (headIsAncestorOfMaster fakePath)
  assert "headIsAncestorOfMaster returns false when git throws (nonexistent cwd)"
    (r1 == false)
  let r2 ← withSuppressedOutput (headIsAncestorOfMaster "/tmp")
  assert "headIsAncestorOfMaster returns false in a non-git directory" (r2 == false)

end GitFallback

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
  assert "--unsafe-window=5 is known" (isKnownOpt "--unsafe-window=5")

  -- Empty value passes recognition (parseNamedOpt returns the empty string
  -- for these — callers decide whether to treat that as an error).
  assert "--scope= (empty value) is known" (isKnownOpt "--scope=")

  -- Flags use the bare `--name` form, no `=`.
  assert "--help (no =) is known" (isKnownOpt "--help")
  assert "--unsafe (no =) is known" (isKnownOpt "--unsafe")

  -- `--unsafe` is a flag, not a named option: the `=value` form is a user error.
  assert "--unsafe=5 is NOT known (flags don't take values)"
    (!isKnownOpt "--unsafe=5")

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

  -- `--scope=` is recognized with the empty string as its value, distinct from
  -- "not passed" (none).
  let v ← parseNamedOpt "scope" ["--scope="]
  assert "empty value → some \"\"" (v == some "")

  -- Multiple occurrences: last wins, matching shell precedence.
  let v ← parseNamedOpt "scope" ["--scope=first", "--scope=second"]
  assert "duplicate option → last value wins" (v == some "second")

  -- Surrounding positionals and other options don't interfere.
  let v ← parseNamedOpt "scope" ["get", "--repo=foo", "--scope=mid", "Mathlib/Init.lean"]
  assert "found among other args" (v == some "mid")

  -- A longer lookalike name must not match.
  let v ← parseNamedOpt "scope" ["--scope-other=foo"]
  assert "--scope-other does not match --scope" (v == none)

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

section CacheMissStatus

/-- `isCacheMissStatus` decides whether a read's HTTP status is a benign miss
(fall through to the next container) or a real transfer failure. `404` is always
a miss; `403` is a miss only for a container flagged `treatForbiddenAsMiss`
(currently `legacy`, whose reads start returning `403` once public access is
revoked ahead of retirement). This guards old clients — whose chain still lists
`legacy` — against per-file failures when the container is brought down. -/
def test_isCacheMissStatus : IO Unit := do
  IO.println "isCacheMissStatus:"
  -- 404 is a miss regardless of the flag.
  assert "404 is a miss (flag off)"        (isCacheMissStatus 404 false)
  assert "404 is a miss (flag on)"         (isCacheMissStatus 404 true)
  -- 403 is a miss only when the flag is set (i.e. for `legacy`).
  assert "403 is a failure when flag off"  (!isCacheMissStatus 403 false)
  assert "403 is a miss when flag on"      (isCacheMissStatus 403 true)
  -- Success and server errors are never misses; they must surface.
  assert "200 is not a miss"               (!isCacheMissStatus 200 true)
  assert "500 is not a miss"               (!isCacheMissStatus 500 true)
  assert "403-as-miss is scoped to 403"    (!isCacheMissStatus 401 true)

end CacheMissStatus

section AlreadyPresentStatus

/-- A non-overwrite `put` (`If-None-Match: *`) gets a 409 or 412 back for a blob
that already exists; both mean "present", not a failure. -/
def test_isAlreadyPresentStatus : IO Unit := do
  IO.println "isAlreadyPresentStatus:"
  -- 409/412 are the codes Azure returns for a blob that already exists.
  assert "409 is already-present" (isAlreadyPresentStatus 409)
  assert "412 is already-present" (isAlreadyPresentStatus 412)
  -- Successes, misses, and server errors are not.
  assert "201 is not already-present" (!isAlreadyPresentStatus 201)
  assert "404 is not already-present" (!isAlreadyPresentStatus 404)
  assert "500 is not already-present" (!isAlreadyPresentStatus 500)

end AlreadyPresentStatus

section UnsafeRounds

/-- `expandDownloadRounds` turns the trust-ordered container list into the
concrete download rounds to run, each tagged with the SHA scope to read at.

Without `--unsafe` (empty `unsafeScopes`) every round carries the single resolved
base scope; with no base scope, `headScope?` applies to the `forks` round only,
so a plain `cache get` reads the fork namespace of the checked-out commit while
the other containers' non-SHA-scoped layouts stay untouched. With `--unsafe` the
`forks` container — the only SHA-scoped container — fans out into one round per
discovered SHA (most recent first), while every other container reads unscoped
and the base scope is dropped. -/
def test_expandDownloadRounds : IO Unit := do
  IO.println "expandDownloadRounds:"
  let chain : List (Option Container × String) :=
    [(some .master, "U_m"), (some .forks, "U_f"), (some .legacy, "U_l")]

  -- No unsafe scopes: one round per container, each carrying the base scope.
  assert "no unsafe scopes, no base scope → scope none on every round"
    (expandDownloadRounds chain none [] ==
      [(some .master, "U_m", none), (some .forks, "U_f", none), (some .legacy, "U_l", none)])
  assert "no unsafe scopes, base scope → base scope on every round"
    (expandDownloadRounds chain (some "S") [] ==
      [(some .master, "U_m", some "S"), (some .forks, "U_f", some "S"),
       (some .legacy, "U_l", some "S")])

  -- With no base scope the forks round defaults to the HEAD scope; the other
  -- containers' layouts are not SHA-scoped, so it must not leak into them.
  assert "no base scope, head scope → forks at head, others unscoped"
    (expandDownloadRounds chain none [] (some "H") ==
      [(some .master, "U_m", none), (some .forks, "U_f", some "H"),
       (some .legacy, "U_l", none)])
  assert "explicit base scope wins over head scope"
    (expandDownloadRounds chain (some "S") [] (some "H") ==
      [(some .master, "U_m", some "S"), (some .forks, "U_f", some "S"),
       (some .legacy, "U_l", some "S")])
  assert "unsafe mode ignores head scope"
    (expandDownloadRounds chain none ["a"] (some "H") ==
      [(some .master, "U_m", none), (some .forks, "U_f", some "a"),
       (some .legacy, "U_l", none)])

  -- Unsafe scopes: only forks fans out, in order; others unscoped, base dropped.
  assert "unsafe scopes fan out forks (in order), others unscoped"
    (expandDownloadRounds chain (some "ignored") ["a", "b"] ==
      [(some .master, "U_m", none),
       (some .forks, "U_f", some "a"), (some .forks, "U_f", some "b"),
       (some .legacy, "U_l", none)])

  -- A chain without forks admits no SHA-scoped reads, so it is left unchanged.
  assert "no forks container → unsafe scopes have no effect"
    (expandDownloadRounds [(some .master, "U_m"), (some .legacy, "U_l")] none ["a", "b"] ==
      [(some .master, "U_m", none), (some .legacy, "U_l", none)])

end UnsafeRounds

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
  test_findRecentSHAsWithCache
  test_getRemoteRepo_gitFallback
  test_headIsAncestorOfMaster_gitFallback
  test_isKnownOpt
  test_parseNamedOpt
  test_parseFlagOpt
  test_isCacheMissStatus
  test_isAlreadyPresentStatus
  test_expandDownloadRounds

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
