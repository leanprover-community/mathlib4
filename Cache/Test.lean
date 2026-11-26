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
- Decompression-pipeline carry across download rounds (`DecompState`,
  `finalizeDecomp`, `monitorCurl`)
- Transfer classification (`classifyDownload`/`classifyUpload`): delivered,
  miss, skip, or failed, per HTTP status and curl exit code
- The two retry-flag tiers (`curlRetryArgs`)
- Utility functions (URL extraction, filename hashing, etc.)

Anything that touches the network is left to CI, which exercises the
`cache get`/`put` paths end-to-end on real containers. The unit tests spawn
two local processes, `curl --version` and one leantar run on a nonexistent
archive; neither makes a network request.

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
6. Multi-round downloads decompress every file they fetch: the decompression
   pipeline state is carried from each container round into the next and
   drained after the last one, so a fork-PR `get` leaves no downloaded file
   compressed on disk.

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
def assertTrue (name : String) (cond : Bool) : IO Unit := do
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

/-- Run `action` with both stdout and stderr redirected to the platform null
device. Restores both on completion, including on exception. Apply this to every
production code call in tests so diagnostic prints never mix with test output,
regardless of whether the production code currently produces any. -/
private def withSuppressedOutput (action : IO α) : IO α := do
  let savedOut ← IO.getStdout
  let savedErr ← IO.getStderr
  let sink ← IO.FS.Handle.mk Cache.IO.nullDevice IO.FS.Mode.append
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
  assertTrue "master parses"          (Container.parse? "master" == some .master)
  assertTrue "forks parses"           (Container.parse? "forks" == some .forks)
  assertTrue "nightly-testing parses" (Container.parse? "nightly-testing" == some .nightlyTesting)
  assertTrue "pr-toolchain-tests parses"
    (Container.parse? "pr-toolchain-tests" == some .prToolchainTests)
  assertTrue "legacy parses"          (Container.parse? "legacy" == some .legacy)
  -- Matching is case-insensitive, so `--container=Master` canonicalizes too.
  assertTrue "case-insensitive"       (Container.parse? "Master" == some .master)
  -- An unknown name returns `none` so `--container=bogus` errors out rather than
  -- defaulting to some container the user didn't ask for.
  assertTrue "unknown rejected"       (Container.parse? "bogus" == none)
  assertTrue "empty rejected"         (Container.parse? "" == none)

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

/-- A variable that names a read URL or a read chain arrives trimmed, and an
empty or whitespace-only value means unset. `MATHLIB_CACHE_BASE_URL`,
`MATHLIB_CACHE_GET_URL`, and `MATHLIB_CACHE_FROM` follow that rule. CI wires
them from a GitHub Actions `vars` lookup, which yields `""` for an undefined
variable, and such a value behaves as an absent one. The upload endpoint
`MATHLIB_CACHE_PUT_URL` keeps the opposite rule: an empty value there fails the
upload rather than divert it to the fallback container. -/
def test_envValueNormalization : IO Unit := do
  IO.println "nonEmptyEnvValue / normalizeBaseURL:"
  -- `<unset>` stands in for `none`, so a failure shows both sides as strings.
  let shown (value? : Option String) : String := value?.getD "<unset>"
  assertEq "absent value reads as unset" "<unset>" (shown (nonEmptyEnvValue none))
  assertEq "empty value reads as unset" "<unset>" (shown (nonEmptyEnvValue (some "")))
  assertEq "whitespace-only value reads as unset" "<unset>"
    (shown (nonEmptyEnvValue (some " \n")))
  assertEq "value is trimmed" "master,forks" (shown (nonEmptyEnvValue (some " master,forks\n")))
  assertEq "URL keeps its own path" "https://cache.example.org/mathlib4"
    (shown (normalizeBaseURL (some "https://cache.example.org/mathlib4")))
  assertEq "trailing slashes are stripped" "https://cache.example.org"
    (shown (normalizeBaseURL (some "https://cache.example.org///")))
  assertEq "a slash-only value reads as unset" "<unset>" (shown (normalizeBaseURL (some "/")))

/-- The read base follows `MATHLIB_CACHE_BASE_URL` when the variable is set
and falls back to the Azure account when it is not. `getBaseURLFrom` is pure,
so this test covers both branches; the environment-reading wrapper
(`getBaseURL`) adds no logic of its own. -/
def test_getBaseURLFrom : IO Unit := do
  IO.println "getBaseURLFrom:"
  assertEq "no override → the Azure account"
    defaultGetBaseURL (getBaseURLFrom none)
  assertEq "override → the given base"
    "https://cache.example.org" (getBaseURLFrom (some "https://cache.example.org"))
  -- A GitHub Actions `${{ vars.… }}` lookup yields "" while the variable is
  -- undefined, so an empty value must keep the default.
  assertEq "empty value counts as unset"
    defaultGetBaseURL (getBaseURLFrom (some ""))
  assertEq "whitespace-only value counts as unset"
    defaultGetBaseURL (getBaseURLFrom (some " \n"))
  assertEq "override is trimmed"
    "https://cache.example.org" (getBaseURLFrom (some "https://cache.example.org\n"))
  -- A base written with a trailing slash must not double the separator in
  -- `{base}/{container}/{key}`.
  assertEq "trailing slash is stripped"
    "https://cache.example.org" (getBaseURLFrom (some "https://cache.example.org/"))

/-- Read URLs follow `getBaseURL`: the same `/{container}` namespace as
`azureURL`, under whichever base `MATHLIB_CACHE_BASE_URL` selects. With no
override, reads address Azure directly and the two URL families coincide. -/
def test_Container_getURL : IO Unit := do
  IO.println "Container.getURL:"
  let base ← getBaseURL
  assertEq "master read URL" s!"{base}/mathlib4-master" (← Container.master.getURL)
  assertEq "forks read URL" s!"{base}/mathlib4-forks" (← Container.forks.getURL)
  assertEq "legacy read URL" s!"{base}/mathlib4" (← Container.legacy.getURL)
  -- The effective base drives this guard, so an empty variable reaches the
  -- assertions below: it means unset, and the Azure host answers for it.
  if base == defaultGetBaseURL then
    assertEq "default read URL matches azureURL"
      Container.master.azureURL (← Container.master.getURL)

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
  assertTrue "master is flat for the canonical repo"
    (Container.master.flatPath MATHLIBREPO == true)
  assertTrue "master is flat for a fork repo too"
    (Container.master.flatPath "alice/mathlib4" == true)
  assertTrue "legacy is flat for the canonical repo"
    (Container.legacy.flatPath MATHLIBREPO == true)
  assertTrue "legacy is prefixed for a fork repo"
    (Container.legacy.flatPath "alice/mathlib4" == false)
  assertTrue "forks is prefixed for the canonical repo"
    (Container.forks.flatPath MATHLIBREPO == false)
  assertTrue "forks is prefixed for a fork repo"
    (Container.forks.flatPath "alice/mathlib4" == false)
  assertTrue "nightly-testing is prefixed for the nightly-testing repo"
    (Container.nightlyTesting.flatPath NIGHTLY_TESTING_REPO == false)
  assertTrue "nightly-testing is prefixed for the canonical repo"
    (Container.nightlyTesting.flatPath MATHLIBREPO == false)
  assertTrue "pr-toolchain-tests is prefixed for the nightly-testing repo"
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
  assertTrue "canonical repo → [master, legacy]"
    (defaultContainersForRepo MATHLIBREPO == [.master, .legacy])
  assertTrue "nightly-testing repo → [nightly-testing, forks, legacy], no pr-toolchain-tests"
    (defaultContainersForRepo NIGHTLY_TESTING_REPO == [.nightlyTesting, .forks, .legacy])
  assertTrue "fork repo → [master, forks, legacy]"
    (defaultContainersForRepo "alice/mathlib4" == [.master, .forks, .legacy])
  assertTrue "unknown repo falls back to the fork chain"
    (defaultContainersForRepo "some/other-repo" == [.master, .forks, .legacy])
  -- Every chain ends with `legacy`; dropping it would quietly shrink hit rates.
  assertTrue "fork chain ends with legacy"
    ((defaultContainersForRepo "alice/mathlib4").getLast? == some .legacy)
  assertTrue "canonical chain ends with legacy"
    ((defaultContainersForRepo MATHLIBREPO).getLast? == some .legacy)
  assertTrue "nightly-testing chain ends with legacy"
    ((defaultContainersForRepo NIGHTLY_TESTING_REPO).getLast? == some .legacy)

/-- `effectiveGetURLs` pairs the lookup chain with read URLs in trust order.
This test covers the default chain and the `--cache-from` override. The
`MATHLIB_CACHE_GET_URL` and `MATHLIB_CACHE_FROM` branches need process state,
so the CI integration tests exercise them instead. -/
def test_effectiveGetURLs : IO Unit := do
  IO.println "effectiveGetURLs:"
  if (← getEnvNonEmpty "MATHLIB_CACHE_GET_URL").isSome ||
      (← getEnvNonEmpty "MATHLIB_CACHE_FROM").isSome then
    IO.println "  skipped: MATHLIB_CACHE_GET_URL or MATHLIB_CACHE_FROM is set"
    return
  let base ← getBaseURL
  assertTrue "default chain pairs each container with its read URL"
    ((← effectiveGetURLs MATHLIBREPO) ==
      [(some .master, s!"{base}/mathlib4-master"),
       (some .legacy, s!"{base}/mathlib4")])
  cacheFromOverride.set (some [.forks, .master])
  assertTrue "--cache-from override keeps its order"
    ((← effectiveGetURLs MATHLIBREPO) ==
      [(some .forks, s!"{base}/mathlib4-forks"),
       (some .master, s!"{base}/mathlib4-master")])
  cacheFromOverride.set none

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
  assertTrue "single container"
    (parseCacheFromList "master" == some [.master])
  assertTrue "two containers"
    (parseCacheFromList "master,forks" == some [.master, .forks])
  assertTrue "all five containers"
    (parseCacheFromList "master,forks,nightly-testing,pr-toolchain-tests,legacy" ==
      some [.master, .forks, .nightlyTesting, .prToolchainTests, .legacy])
  assertTrue "master,legacy"
    (parseCacheFromList "master,legacy" == some [.master, .legacy])
  -- Order is preserved, not normalized: `forks,master` reverses the priority.
  assertTrue "preserves the given order"
    (parseCacheFromList "forks,master" == some [.forks, .master])
  -- Whitespace around commas is tolerated, so the flag survives shell expansion.
  assertTrue "whitespace around names is tolerated"
    (parseCacheFromList " master , forks " == some [.master, .forks])
  assertTrue "one unknown name rejects the whole list"
    (parseCacheFromList "master,bogus" == none)
  assertTrue "empty input is rejected"
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
  assertTrue "ssh URL with .git suffix"
    (extractRepoFromUrl "git@github.com:alice/mathlib4.git" == some "alice/mathlib4")
  assertTrue "ssh URL without .git suffix"
    (extractRepoFromUrl "git@github.com:alice/mathlib4" == some "alice/mathlib4")
  assertTrue "https URL with .git suffix"
    (extractRepoFromUrl "https://github.com/alice/mathlib4.git" == some "alice/mathlib4")
  assertTrue "https URL without .git suffix"
    (extractRepoFromUrl "https://github.com/alice/mathlib4" == some "alice/mathlib4")
  -- A hyphenated owner is part of the repo identity and must survive intact.
  assertTrue "hyphenated owner is preserved"
    (extractRepoFromUrl "https://github.com/leanprover-community/mathlib4.git" == some "leanprover-community/mathlib4")
  assertTrue "empty input returns none"
    (extractRepoFromUrl "" == none)
  assertTrue "a token with no slash or colon returns none"
    (extractRepoFromUrl "norepo" == none)

end ExtractRepoFromUrl

section ExtractPRNumber

/-- Extracts a PR number from a git ref. The contract is "second-to-last
segment must be `pr`, last must be a Nat". -/
def test_extractPRNumber : IO Unit := do
  IO.println "extractPRNumber:"
  -- The shape git produces for fetched PR refs.
  assertTrue "standard PR ref format"
    (extractPRNumber "refs/remotes/upstream/pr/1234" == some 1234)
  -- Branch refs are not PR refs; must not match.
  assertTrue "master branch returns none"
    (extractPRNumber "refs/heads/master" == none)
  -- Minimal `pr/N` is also accepted — the parser only inspects the trailing two segments.
  assertTrue "simple pr number"
    (extractPRNumber "pr/42" == some 42)
  -- The tail must be a valid Nat; non-numeric tails are rejected (no partial parsing).
  assertTrue "non-numeric tail returns none"
    (extractPRNumber "refs/remotes/upstream/pr/foo" == none)
  -- `0` is a valid Nat; pin down that it isn't special-cased.
  assertTrue "zero PR number"
    (extractPRNumber "refs/remotes/upstream/pr/0" == some 0)
  -- A numeric tail without the `pr/` parent must not be mistaken for a PR ref.
  assertTrue "missing pr segment returns none"
    (extractPRNumber "refs/remotes/upstream/42" == none)

end ExtractPRNumber

section HashFromFileName

/-- Recovers the UInt64 cache hash from a cached file's path, the inverse of
`UInt64.asLTar`. The subtle cases are the in-flight suffixes curl writes during a
download: today's process-tagged `.ltar.<pid>.part` (see `IO.PARTSUFFIX`) and the
untagged `.ltar.part` a cache from before tagging may have left in the shared
directory. A regression here corrupts cache lookups, so every suffix and a
non-hex stem are covered. -/
def test_hashFromFileName : IO Unit := do
  IO.println "hashFromFileName:"
  assertTrue "plain .ltar file"
    (hashFromFileName "abc123def.ltar" == String.parseHexToUInt64? "000000abc123def")
  assertTrue "in-flight process-tagged .part file strips all three suffixes"
    (hashFromFileName "abc123def.ltar.31415.part" == String.parseHexToUInt64? "000000abc123def")
  assertTrue "legacy untagged .ltar.part file strips both suffixes"
    (hashFromFileName "abc123def.ltar.part" == String.parseHexToUInt64? "000000abc123def")
  assertTrue "the tag this process actually writes round-trips"
    (hashFromFileName ("abc123def.ltar" ++ IO.PARTSUFFIX) ==
      String.parseHexToUInt64? "000000abc123def")
  assertTrue "full 16-digit hex stem"
    (hashFromFileName "deadbeef00112233.ltar" == String.parseHexToUInt64? "deadbeef00112233")
  -- A non-hex stem returns none rather than a garbage hash.
  assertTrue "non-hex stem returns none"
    (hashFromFileName "nothexa.ltar" == none)
  assertTrue "non-hex stem returns none for a tagged part file too"
    (hashFromFileName "nothexa.ltar.31415.part" == none)
  -- Directory components are ignored; only the basename's stem is parsed.
  assertTrue "leading path is ignored"
    (hashFromFileName "/path/to/abc123def.ltar" == String.parseHexToUInt64? "000000abc123def")

end HashFromFileName

section TempFileNames

/-- Every temporary file `cache` writes into the shared `CACHEDIR` carries this process's
tag, so two runs in flight in one cache directory cannot write each other's curl
configuration or each other's partial downloads. The `.part` ending is load-bearing
beyond uniqueness: the download monitor keys both its rename-on-success and its
remove-on-error off it. -/
def test_tempFileNames : IO Unit := do
  IO.println "temporary file names:"
  assertTrue "the process tag is non-empty" (!IO.PROCTAG.isEmpty)
  assertTrue "the in-flight suffix still ends in .part" (IO.PARTSUFFIX.endsWith ".part")
  assertTrue "the in-flight suffix is tagged, not a bare .part" (IO.PARTSUFFIX != ".part")
  assertTrue "the in-flight suffix carries the tag" ((IO.PARTSUFFIX.splitOn IO.PROCTAG).length == 2)
  assertTrue "the curl config carries the tag"
    ((IO.CURLCFG.toString.splitOn IO.PROCTAG).length == 2)
  assertTrue "the curl config sits in the cache directory"
    (IO.CURLCFG.parent == some IO.CACHEDIR)
  -- The tag must not reintroduce a path separator or a shell/curl-config hazard.
  assertTrue "the tag is a bare identifier" (IO.PROCTAG.all fun c => c.isAlphanum)

end TempFileNames

section IsRemoteURL

/-- Discriminator: is this string a remote URL (vs a local filesystem path)?
Used to decide whether to short-circuit `git remote get-url` lookups. -/
def test_isRemoteURL : IO Unit := do
  IO.println "isRemoteURL:"
  -- The three protocols accepted by the cache tool.
  assertTrue "https URL is remote"
    (isRemoteURL "https://github.com/alice/mathlib4.git" == true)
  assertTrue "http URL is remote"
    (isRemoteURL "http://github.com/alice/mathlib4" == true)
  assertTrue "ssh URL is remote"
    (isRemoteURL "git@github.com:alice/mathlib4.git" == true)
  -- Absolute and relative local paths must be classified as not-remote so they
  -- get routed through `git remote get-url`.
  assertTrue "local path is not remote"
    (isRemoteURL "/local/path/to/repo" == false)
  assertTrue "relative path is not remote"
    (isRemoteURL "./local/repo" == false)
  -- Defensive — empty input shouldn't accidentally match the predicate.
  assertTrue "empty string is not remote"
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
  assertTrue "full-width hash round-trips"
    (hashFromFileName h1.asLTar == some h1)
  -- A short hash exercises both pad-on-write and trim-on-read.
  let h2 : UInt64 := 0xabc123
  assertTrue "padded hash round-trips"
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

/-- Marker probes read through the base URL; marker writes address Azure
directly (`markerURL`). The two URLs agree only under the default base. -/
def test_markerReadURL : IO Unit := do
  IO.println "markerReadURL:"
  let base ← getBaseURL
  assertEq "probe URL follows the read base"
    s!"{base}/mathlib4-forks/m/alice/mathlib4/abc123"
    (← markerReadURL .forks "alice/mathlib4" "abc123")
  assertEq "probe repo is lowercased in the path"
    s!"{base}/mathlib4-forks/m/alice/mathlib4/abc123"
    (← markerReadURL .forks "Alice/Mathlib4" "abc123")
  -- The effective base drives this guard, so an empty variable reaches the
  -- assertions below: it means unset, and the Azure host answers for it.
  if base == defaultGetBaseURL then
    assertEq "default probe URL matches the write URL"
      (markerURL .forks "alice/mathlib4" "abc123")
      (← markerReadURL .forks "alice/mathlib4" "abc123")

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
    assertTrue "no scope set returns none" ((← withSuppressedOutput getRepoScope) == none)

    scopeOverride.set (some "abc123")
    assertTrue "the flag value is returned" ((← withSuppressedOutput getRepoScope) == some "abc123")

    -- The flag value is returned as-is, without trimming or normalization.
    scopeOverride.set (some "deadbeef")
    assertTrue "the flag value is returned verbatim"
      ((← withSuppressedOutput getRepoScope) == some "deadbeef")

    scopeOverride.set none
    assertTrue "clearing the flag returns none" ((← withSuppressedOutput getRepoScope) == none)
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

    assertTrue "plain get with no flags does not warn"
      (!(← withSuppressedOutput (shouldWarnNonDefaultScope none none none MATHLIBREPO)))

    scopeOverride.set (some "abc123")
    assertTrue "a set scope warns"
      (← withSuppressedOutput (shouldWarnNonDefaultScope none none none MATHLIBREPO))
    scopeOverride.set none

    -- A scope equal to HEAD is trust-equivalent to no scope (CI's normal mode).
    -- Skipped when HEAD can't be resolved (not in a git checkout).
    let head? ← try some <$> withSuppressedOutput getGitCommitHash catch _ => pure none
    if let some head := head? then
      scopeOverride.set (some head)
      assertTrue "a scope equal to HEAD does not warn"
        (!(← withSuppressedOutput (shouldWarnNonDefaultScope none none none MATHLIBREPO)))
      scopeOverride.set none

    -- --cache-from equal to the repo's default chain is not widening.
    let mathlibDefault := defaultContainersForRepo MATHLIBREPO
    assertTrue "--cache-from equal to the default does not warn"
      (!(← withSuppressedOutput
          (shouldWarnNonDefaultScope none none (some mathlibDefault) MATHLIBREPO)))

    assertTrue "--cache-from widening the chain warns"
      (← withSuppressedOutput
          (shouldWarnNonDefaultScope none none (some [.master, .forks, .legacy]) MATHLIBREPO))

    -- A fork checkout (remote ≠ resolved repo) stays silent without an explicit --repo.
    assertTrue "a fork checkout without --repo does not warn"
      (!(← withSuppressedOutput
          (shouldWarnNonDefaultScope none (some "alice/mathlib4") none "alice/mathlib4")))

    assertTrue "--repo differing from the remote warns"
      (← withSuppressedOutput
          (shouldWarnNonDefaultScope (some "bob/mathlib4") (some "alice/mathlib4") none "bob/mathlib4"))

    assertTrue "--repo matching the remote does not warn"
      (!(← withSuppressedOutput
          (shouldWarnNonDefaultScope (some "alice/mathlib4") (some "alice/mathlib4") none
            "alice/mathlib4")))

    -- With no detectable remote there is nothing to compare --repo against.
    assertTrue "--repo with no detectable remote does not warn"
      (!(← withSuppressedOutput
          (shouldWarnNonDefaultScope (some "bob/mathlib4") none none "bob/mathlib4")))

    -- `--unsafe` (any window) always warns; it walks several untrusted scopes.
    assertTrue "--unsafe warns regardless of other inputs"
      (← withSuppressedOutput
          (shouldWarnNonDefaultScope none none none MATHLIBREPO (unsafeWindow? := some 5)))
    assertTrue "no --unsafe (none window) does not warn on its own"
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
    assertTrue "no trigger yields a placeholder reason" (reason == "unknown reason")

    scopeOverride.set (some "abc123")
    let reason ← withSuppressedOutput (getNonDefaultScopeReason none none none MATHLIBREPO)
    assertTrue "scope reason names the flag and SHA"
      (reason == "--scope=abc123 (explicit per-commit scope)")

    -- Scope outranks cache-from when both apply.
    let reason ← withSuppressedOutput (getNonDefaultScopeReason none none (some [.forks]) MATHLIBREPO)
    assertTrue "scope is reported ahead of cache-from"
      (reason == "--scope=abc123 (explicit per-commit scope)")
    scopeOverride.set none

    -- A HEAD scope is exempt from condition 1, so a simultaneous cache-from
    -- trigger is reported instead of the scope.
    let head? ← try some <$> withSuppressedOutput getGitCommitHash catch _ => pure none
    if let some head := head? then
      scopeOverride.set (some head)
      let reason ←
        withSuppressedOutput (getNonDefaultScopeReason none none (some [.forks, .legacy]) MATHLIBREPO)
      assertTrue "a HEAD scope yields the cache-from reason"
        (reason == "--cache-from=forks, legacy (explicit container override)")
      scopeOverride.set none

    let reason ←
      withSuppressedOutput (getNonDefaultScopeReason none none (some [.forks, .legacy]) MATHLIBREPO)
    assertTrue "cache-from reason names the container list"
      (reason == "--cache-from=forks, legacy (explicit container override)")

    let reason ← withSuppressedOutput
      (getNonDefaultScopeReason (some "bob/mathlib4") (some "alice/mathlib4") none "bob/mathlib4")
    assertTrue "repo reason names the override and the detected remote"
      (reason == "--repo=bob/mathlib4 (overrides detected git remote: alice/mathlib4)")

    -- --cache-from equal to the default is not a trigger, so no reason applies.
    let reason ←
      withSuppressedOutput (getNonDefaultScopeReason none none (some [.master, .legacy]) MATHLIBREPO)
    assertTrue "cache-from equal to the default yields the placeholder"
      (reason == "unknown reason")

    -- `--unsafe` outranks every other trigger and names its window.
    scopeOverride.set (some "abc123")
    let reason ← withSuppressedOutput
      (getNonDefaultScopeReason (some "bob/mathlib4") (some "alice/mathlib4") (some [.forks])
        "bob/mathlib4" (unsafeWindow? := some 7))
    assertTrue "unsafe reason names the window and outranks scope/cache-from/repo"
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
  assertTrue "empty SHA list returns none without probing" (result == none)

/-- `findRecentSHAsWithCache` collects up to `limit` marked SHAs. The non-empty
cases hit the network (a marker HEAD probe per SHA); here we pin that an empty
candidate list returns `[]` for any limit, with no probe. -/
def test_findRecentSHAsWithCache : IO Unit := do
  IO.println "findRecentSHAsWithCache:"
  let result ← withSuppressedOutput (findRecentSHAsWithCache [] MATHLIBREPO 5)
  assertTrue "empty SHA list returns [] without probing" (result == [])
  let result ← withSuppressedOutput (findRecentSHAsWithCache [] MATHLIBREPO 0)
  assertTrue "limit 0 returns [] without probing" (result == [])

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
  assertTrue "getRemoteRepo returns none when git throws (nonexistent cwd)" (r1 == none)

  -- Case 2: existing directory that is not a git repo (git returns exit 128).
  -- This exercises the exit-code fallback path that predates the try...catch.
  let r2 ← withSuppressedOutput (getRemoteRepo "/tmp")
  assertTrue "getRemoteRepo returns none in a non-git directory" (r2 == none)

  -- resolveRepo propagates the fallback correctly:
  --   detected? = none, resolved = MATHLIBREPO → master-only chain.
  let (detected?, resolved) ← withSuppressedOutput (resolveRepo none fakePath)
  assertTrue "resolveRepo detected? is none on git failure" (detected? == none)
  assertTrue "resolveRepo falls back to MATHLIBREPO on git failure" (resolved == MATHLIBREPO)
  assertTrue "fallback chain includes master"
    ((defaultContainersForRepo resolved).contains .master)
  assertTrue "fallback chain excludes forks (no fork container for dependency builds)"
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
  assertTrue "headIsAncestorOfMaster returns false when git throws (nonexistent cwd)"
    (r1 == false)
  let r2 ← withSuppressedOutput (headIsAncestorOfMaster "/tmp")
  assertTrue "headIsAncestorOfMaster returns false in a non-git directory" (r2 == false)

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
  assertTrue "--repo=foo is known"           (isKnownOpt "--repo=foo")
  assertTrue "--cache-from=master is known"  (isKnownOpt "--cache-from=master")
  assertTrue "--scope=HEAD is known"         (isKnownOpt "--scope=HEAD")
  assertTrue "--container=master is known"   (isKnownOpt "--container=master")
  assertTrue "--staging-dir=/tmp is known"   (isKnownOpt "--staging-dir=/tmp")
  assertTrue "--unsafe-window=5 is known" (isKnownOpt "--unsafe-window=5")

  -- Empty value passes recognition (parseNamedOpt returns the empty string
  -- for these — callers decide whether to treat that as an error).
  assertTrue "--scope= (empty value) is known" (isKnownOpt "--scope=")

  -- Flags use the bare `--name` form, no `=`.
  assertTrue "--help (no =) is known" (isKnownOpt "--help")
  assertTrue "--unsafe (no =) is known" (isKnownOpt "--unsafe")

  -- `--unsafe` is a flag, not a named option: the `=value` form is a user error.
  assertTrue "--unsafe=5 is NOT known (flags don't take values)"
    (!isKnownOpt "--unsafe=5")

  -- A typo on a known option name should fail recognition, not be silently
  -- accepted. This is the regression-guard: if `--scoop=` were accepted, the
  -- user's `--scope=` would be silently dropped and reads would fall back to
  -- the default chain with no warning.
  assertTrue "--scoop=foo (typo on scope) is NOT known" (!isKnownOpt "--scoop=foo")
  assertTrue "--bogus=foo (unknown name) is NOT known" (!isKnownOpt "--bogus=foo")

  -- A named option without `=` must NOT be accepted as a flag — `--scope`
  -- (no value) is a user error, distinct from the `--help` flag form.
  assertTrue "--scope (no =) is NOT known (named opts require value)"
    (!isKnownOpt "--scope")

  -- Symmetric: a flag with `=` must NOT be accepted as a named opt.
  assertTrue "--help=foo is NOT known (flags don't take values)"
    (!isKnownOpt "--help=foo")

  -- A bare positional doesn't even look like an option. The cache binary
  -- splits args by `startsWith "--"` before consulting `isKnownOpt`, so this
  -- case should never reach us, but we pin it anyway for safety.
  assertTrue "bare positional 'scope' is NOT known" (!isKnownOpt "scope")

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
  assertTrue "empty args → none" (v == none)

  -- Args without the target option.
  let v ← parseNamedOpt "scope" ["--repo=foo", "get"]
  assertTrue "no matching option → none" (v == none)

  -- Single occurrence.
  let v ← parseNamedOpt "scope" ["--scope=abc123"]
  assertTrue "single occurrence → some value" (v == some "abc123")

  -- `--scope=` is recognized with the empty string as its value, distinct from
  -- "not passed" (none).
  let v ← parseNamedOpt "scope" ["--scope="]
  assertTrue "empty value → some \"\"" (v == some "")

  -- Multiple occurrences: last wins, matching shell precedence.
  let v ← parseNamedOpt "scope" ["--scope=first", "--scope=second"]
  assertTrue "duplicate option → last value wins" (v == some "second")

  -- Surrounding positionals and other options don't interfere.
  let v ← parseNamedOpt "scope" ["get", "--repo=foo", "--scope=mid", "Mathlib/Init.lean"]
  assertTrue "found among other args" (v == some "mid")

  -- A longer lookalike name must not match.
  let v ← parseNamedOpt "scope" ["--scope-other=foo"]
  assertTrue "--scope-other does not match --scope" (v == none)

/-- `parseFlagOpt` checks whether a bare `--name` flag is present in args.
Used for `--help` today. The contract is strict equality — `--help` matches,
`--help=true` and `--help-me` do not. -/
def test_parseFlagOpt : IO Unit := do
  IO.println "parseFlagOpt:"
  -- Empty args.
  assertTrue "empty args → false" (!parseFlagOpt "help" [])

  -- Bare `--help` present.
  assertTrue "--help present → true" (parseFlagOpt "help" ["--help"])

  -- `--help=` with a value is NOT a bare flag. (`isKnownOpt` would also
  -- reject it; this is the parser-level guarantee.)
  assertTrue "--help=true is NOT a bare flag" (!parseFlagOpt "help" ["--help=true"])

  -- Flag absent among other args.
  assertTrue "no flag among args → false"
    (!parseFlagOpt "help" ["get", "--repo=foo"])

  -- Lookalike: `--help-me` isn't the `--help` flag.
  assertTrue "lookalike prefix doesn't match" (!parseFlagOpt "help" ["--help-me"])

end CliOptions

section ReadRedirects

/-- Reads follow redirects, so a read base can answer with the blob's current
location. This test pins the flag set, because each flag bounds what a redirect
may do: `--proto-redir =https` holds a transfer on an encrypted protocol, and
`--max-redirs` bounds the chain. The upload path builds its own `curl`
arguments and carries none of these flags. -/
def test_curlFollowRedirectArgs : IO Unit := do
  IO.println "curlFollowRedirectArgs:"
  assertEq "read redirect flags"
    "--location --proto-redir =https --max-redirs 5"
    (" ".intercalate curlFollowRedirectArgs.toList)

end ReadRedirects

section RetryFlags

/-- Only a path with a curl 7.71 floor may pass `--retry-all-errors`; an older
curl rejects the whole command. The legacy tier serves the serial download
path, so it must stay free of that flag. -/
def test_curlRetryArgs : IO Unit := do
  IO.println "curlRetryArgs:"
  assertEq "legacy tier" "--retry 5"
    (" ".intercalate (curlRetryArgs (supportLegacyCurl := true)).toList)
  assertEq "full tier" "--retry 5 --retry-all-errors"
    (" ".intercalate (curlRetryArgs (supportLegacyCurl := false)).toList)

end RetryFlags

section RunCmdErrors

/-- With `showArgsOnError := false` a failing command's error names only the
command: the argument list can carry a credential (the marker uploads pass
`--oauth2-bearer` and SAS-tokened URLs). The default keeps the argument list
in the message. -/
def test_runCmd_showArgsOnError : IO Unit := do
  IO.println "runCmd showArgsOnError:"
  let secret := "hunter2-credential"
  let hidden ← try
      discard <| IO.runCmd "curl" #["--not-a-curl-flag", secret] (showArgsOnError := false)
      pure "no failure"
    catch e => pure (toString e)
  assertTrue "the failure throws" (hidden != "no failure")
  assertTrue "the message hides the arguments" ((hidden.splitOn secret).length == 1)
  let shown ← try
      discard <| IO.runCmd "curl" #["--not-a-curl-flag", secret]
      pure "no failure"
    catch e => pure (toString e)
  assertTrue "the default shows the arguments" ((shown.splitOn secret).length == 2)

end RunCmdErrors

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
  assertTrue "404 is a miss (flag off)"        (isCacheMissStatus 404 false)
  assertTrue "404 is a miss (flag on)"         (isCacheMissStatus 404 true)
  -- 403 is a miss only when the flag is set (i.e. for `legacy`).
  assertTrue "403 is a failure when flag off"  (!isCacheMissStatus 403 false)
  assertTrue "403 is a miss when flag on"      (isCacheMissStatus 403 true)
  -- Success and server errors are never misses; they must surface.
  assertTrue "200 is not a miss"               (!isCacheMissStatus 200 true)
  assertTrue "500 is not a miss"               (!isCacheMissStatus 500 true)
  assertTrue "403-as-miss is scoped to 403"    (!isCacheMissStatus 401 true)
  -- A refused redirect (`--proto-redir`, `--max-redirs`) leaves its status
  -- here. A miss verdict would make it look like an empty cache and send the
  -- read silently down the container chain, so it counts as a failure.
  assertTrue "302 is not a miss"               (!isCacheMissStatus 302 true)

end CacheMissStatus

section AlreadyPresentStatus

/-- A non-overwrite `put` (`If-None-Match: *`) gets a 409 or 412 back for a blob
that already exists; both mean "present", not a failure. -/
def test_isAlreadyPresentStatus : IO Unit := do
  IO.println "isAlreadyPresentStatus:"
  -- 409/412 are the codes Azure returns for a blob that already exists.
  assertTrue "409 is already-present" (isAlreadyPresentStatus 409)
  assertTrue "412 is already-present" (isAlreadyPresentStatus 412)
  -- Successes, misses, and server errors are not.
  assertTrue "201 is not already-present" (!isAlreadyPresentStatus 201)
  assertTrue "404 is not already-present" (!isAlreadyPresentStatus 404)
  assertTrue "500 is not already-present" (!isAlreadyPresentStatus 500)

end AlreadyPresentStatus

section TransferClassification

/-- `classifyDownload` is the decision table shared by the parallel and serial
download paths. The clean-exit rows guard against renaming a truncated body: a
transport error that outlives the retries reports `http_code: 200` with a
nonzero `exitcode`. -/
def test_classifyDownload : IO Unit := do
  IO.println "classifyDownload:"
  -- A clean 200/201 delivers.
  assertTrue "200 + exit 0 delivers"
    (classifyDownload (some 200) 0 false matches .delivered)
  assertTrue "201 + exit 0 delivers"
    (classifyDownload (some 201) 0 false matches .delivered)
  -- A 200 with a nonzero exit code carries a truncated body.
  assertTrue "200 + exit 18 fails"
    (classifyDownload (some 200) 18 false matches .failed)
  assertTrue "201 + exit 18 fails"
    (classifyDownload (some 201) 18 false matches .failed)
  -- The status alone decides a miss.
  assertTrue "404 is a miss"
    (classifyDownload (some 404) 0 false matches .miss)
  assertTrue "404 + nonzero exit is still a miss"
    (classifyDownload (some 404) 18 false matches .miss)
  assertTrue "403 is a miss with treatForbiddenAsMiss"
    (classifyDownload (some 403) 0 true matches .miss)
  assertTrue "403 fails otherwise"
    (classifyDownload (some 403) 0 false matches .failed)
  assertTrue "409 fails on a read"
    (classifyDownload (some 409) 0 false matches .failed)
  -- No usable status is a failure (a connection error reports `000`).
  assertTrue "status 0 fails"
    (classifyDownload (some 0) 0 false matches .failed)
  assertTrue "no status fails"
    (classifyDownload none 0 false matches .failed)

/-- The put config discards every response body: stdout must carry only the
per-transfer JSON reports (`--write-out '%{json}'`) that `monitorCurl`
parses. -/
def test_mkPutConfigContent : IO Unit := do
  IO.println "mkPutConfigContent:"
  let cfg ← mkPutConfigContent (some .master) MATHLIBREPO "https://example.invalid"
    #["/tmp/00000000deadbeef.ltar"] (.azureSas "tok")
  assertTrue "uploads the file" ((cfg.splitOn "-T /tmp/00000000deadbeef.ltar").length == 2)
  assertTrue "discards the response body" ((cfg.splitOn s!"-o {IO.nullDevice}").length == 2)

/-- `classifyUpload`: a clean 200/201 delivers, a 409/412 skips for a
non-overwrite put, and every other answer — a 404 included — is a failure. -/
def test_classifyUpload : IO Unit := do
  IO.println "classifyUpload:"
  assertTrue "201 + exit 0 delivers"
    (classifyUpload (some 201) 0 false matches .delivered)
  assertTrue "201 + exit 18 fails"
    (classifyUpload (some 201) 18 false matches .failed)
  assertTrue "409 skips on a non-overwrite put"
    (classifyUpload (some 409) 0 true matches .skip)
  assertTrue "412 skips on a non-overwrite put"
    (classifyUpload (some 412) 0 true matches .skip)
  assertTrue "409 fails on an overwrite put"
    (classifyUpload (some 409) 0 false matches .failed)
  assertTrue "404 fails"
    (classifyUpload (some 404) 0 true matches .failed)
  assertTrue "no status fails"
    (classifyUpload none 0 true matches .failed)

end TransferClassification

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
  assertTrue "no unsafe scopes, no base scope → scope none on every round"
    (expandDownloadRounds chain none [] ==
      [(some .master, "U_m", none), (some .forks, "U_f", none), (some .legacy, "U_l", none)])
  assertTrue "no unsafe scopes, base scope → base scope on every round"
    (expandDownloadRounds chain (some "S") [] ==
      [(some .master, "U_m", some "S"), (some .forks, "U_f", some "S"),
       (some .legacy, "U_l", some "S")])

  -- With no base scope the forks round defaults to the HEAD scope; the other
  -- containers' layouts are not SHA-scoped, so it must not leak into them.
  assertTrue "no base scope, head scope → forks at head, others unscoped"
    (expandDownloadRounds chain none [] (some "H") ==
      [(some .master, "U_m", none), (some .forks, "U_f", some "H"),
       (some .legacy, "U_l", none)])
  assertTrue "explicit base scope wins over head scope"
    (expandDownloadRounds chain (some "S") [] (some "H") ==
      [(some .master, "U_m", some "S"), (some .forks, "U_f", some "S"),
       (some .legacy, "U_l", some "S")])
  assertTrue "unsafe mode ignores head scope"
    (expandDownloadRounds chain none ["a"] (some "H") ==
      [(some .master, "U_m", none), (some .forks, "U_f", some "a"),
       (some .legacy, "U_l", none)])

  -- Unsafe scopes: only forks fans out, in order; others unscoped, base dropped.
  assertTrue "unsafe scopes fan out forks (in order), others unscoped"
    (expandDownloadRounds chain (some "ignored") ["a", "b"] ==
      [(some .master, "U_m", none),
       (some .forks, "U_f", some "a"), (some .forks, "U_f", some "b"),
       (some .legacy, "U_l", none)])

  -- A chain without forks admits no SHA-scoped reads, so it is left unchanged.
  assertTrue "no forks container → unsafe scopes have no effect"
    (expandDownloadRounds [(some .master, "U_m"), (some .legacy, "U_l")] none ["a", "b"] ==
      [(some .master, "U_m", none), (some .legacy, "U_l", none)])

end UnsafeRounds

section DecompPipeline

/-- Shared `DecompConfig` for the pipeline tests. `hashToMod` is unused here;
`isMathlibRoot := true` makes `decompressBatch` treat pending paths as plain
entries, so `mathlibDepPath` is unused too. -/
private def testDecompConfig : DecompConfig :=
  { hashToMod := ∅, force := false, isMathlibRoot := true, mathlibDepPath := "." }

/-- `finalizeDecomp` drains the decompression pipeline after the last download
round: it harvests the in-flight leantar batch, then decompresses the pending
files. A pipeline dropped at a round boundary leaves downloaded files
compressed on disk, forcing a rebuild. This test pins the harvest/counter
logic and the pending-drain failure path; successful pending decompression
needs real archives and is covered by CI. -/
def test_finalizeDecomp : IO Unit := do
  IO.println "finalizeDecomp:"
  -- An empty pipeline passes the counters through unchanged.
  let (d, f) ← withSuppressedOutput <|
    finalizeDecomp { decompressed := 5, decompFailed := 2 } testDecompConfig
  assertTrue "empty pipeline passes counters through" (d == 5 && f == 2)

  -- A finished successful batch is harvested into the success counter.
  let okTask : Task (Except IO.Error Unit) := Task.pure (.ok ())
  let (d, f) ← withSuppressedOutput <| finalizeDecomp
    { currentTask := some okTask, lastBatchSize := 3, decompressed := 5 } testDecompConfig
  assertTrue "successful in-flight batch adds its size to decompressed" (d == 8 && f == 0)

  -- A failed batch is harvested into the failure counter, not the success one.
  let errTask : Task (Except IO.Error Unit) := Task.pure (.error (IO.userError "boom"))
  let (d, f) ← withSuppressedOutput <| finalizeDecomp
    { currentTask := some errTask, lastBatchSize := 4, decompressed := 5, decompFailed := 1 }
    testDecompConfig
  assertTrue "failed in-flight batch adds its size to decompFailed" (d == 5 && f == 5)

  -- Pending files are drained even with no in-flight task; a batch whose
  -- leantar invocation fails lands in the failure counter.
  let (d, f) ← withSuppressedOutput <| finalizeDecomp
    { pending := #[(System.FilePath.mk "cache-test-missing-dir/bogus.ltar", `Mathlib.Bogus)]
      decompressed := 5 } testDecompConfig
  assertTrue "failed pending drain adds its size to decompFailed" (d == 5 && f == 1)

/-- A download round returns its decompression pipeline state in
`TransferState.decomp` so `downloadFiles` can hand it to the next round and
the final drain. A round in which curl transfers nothing, e.g. a container
missing every requested file, must return the carried state intact; otherwise
a prior round's queued files would be lost at the round boundary.
`curl --version` drives `monitorCurl` through a real curl spawn with no
downloads and no network. This pins `monitorCurl`'s half of the carry; the
round loop's half is exercised by the CI integration tests. -/
def test_monitorCurl_carries_decomp_state : IO Unit := do
  IO.println "monitorCurl carries decompression state:"
  let okTask : Task (Except IO.Error Unit) := Task.pure (.ok ())
  let carried : DecompState := {
    pending := #[(System.FilePath.mk "some/file.ltar", `Mathlib.SomeModule)]
    currentTask := some okTask
    lastBatchSize := 7
    decompressed := 42
    decompFailed := 1 }
  let (s, served) ← withSuppressedOutput <|
    monitorCurl #["--version"] 1 "Downloaded" "speed_download"
      (classifyDownload · · false) (decompState := carried)
  assertTrue "no transfers → an empty served set" served.isEmpty
  assertTrue "pending files survive the round" (s.decomp.pending.size == 1)
  assertTrue "the in-flight task survives the round" s.decomp.currentTask.isSome
  assertTrue "the batch size survives the round" (s.decomp.lastBatchSize == 7)
  assertTrue "the decompressed counter survives the round" (s.decomp.decompressed == 42)
  assertTrue "the decompFailed counter survives the round" (s.decomp.decompFailed == 1)

end DecompPipeline

def runAll : IO Unit := do
  test_Container_name
  test_Container_parse
  test_Container_azureURL
  test_Container_getURL
  test_envValueNormalization
  test_getBaseURLFrom
  test_Container_flatPath
  test_defaultContainersForRepo
  test_effectiveGetURLs
  test_mkFileURL
  test_parseCacheFromList
  test_extractRepoFromUrl
  test_extractPRNumber
  test_hashFromFileName
  test_tempFileNames
  test_isRemoteURL
  test_UInt64_asLTar
  test_hash_roundtrip
  test_markerURL
  test_markerReadURL
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
  test_curlFollowRedirectArgs
  test_curlRetryArgs
  test_runCmd_showArgsOnError
  test_isCacheMissStatus
  test_isAlreadyPresentStatus
  test_classifyDownload
  test_classifyUpload
  test_mkPutConfigContent
  test_expandDownloadRounds
  test_finalizeDecomp
  test_monitorCurl_carries_decomp_state

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
