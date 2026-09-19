/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Commands
import Cache.Lean

/-!
# Unit tests for the cache CLI

These tests cover the pure logic of the cache system, including:
- Container model (trust levels, URL shapes, Azure integration)
- The public/developer cache split: container → service mapping, per-service
  read bases, the read options (`Scope`, `ChainOptions`), the workflow
  decision (`Workflow.forRead`), and the upload (`Upload`)
- The container-chain read the developer and nightly workflows share
  (`Chain.resolve`, `Chain.withURLs`, `Chain.rounds`) and the public-cache
  workflow's one URL (`Public.url`)
- The trust-ordered chains of the developer and nightly workflows
- URL construction (`mkFileURL`) with support for per-SHA scoping
- CLI flag parsing (`--cache-from`, `--scope`, `--unsafe`, `--repo`, etc.)
- `--unsafe` download-round expansion (`Chain.rounds`) and the
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
   Azure RBAC) and reads follow the workflow's trust-ordered chain, so a PR
   cannot upload to a higher-trust container.
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
open Cache.Workflow

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

/-- The short name is the string used on the CLI (in `--cache-from=LIST`) and to
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
  -- Matching is case-insensitive, so `--cache-from=Master` canonicalizes too.
  assertTrue "case-insensitive"       (Container.parse? "Master" == some .master)
  -- An unknown name returns `none` so `--cache-from=bogus` errors out rather than
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

/-- Each service resolves its own read base. The precedence is
`MATHLIB_CACHE_DEVELOPER_BASE_URL` (developer cache only) over
`MATHLIB_CACHE_BASE_URL` (both services) over the service's endpoint, and
`MATHLIB_CACHE_DEBUG_USE_LEGACY` sends both services' defaults to the Azure
account. `getBaseURLFrom` is pure, so this test covers every branch; the
environment-reading wrapper (`getBaseURL`) adds no logic of its own. -/
def test_getBaseURLFrom : IO Unit := do
  IO.println "getBaseURLFrom:"
  assertEq "no override → the public endpoint for the public service"
    "https://cache.mathlib.org" (getBaseURLFrom .published none none false)
  assertEq "no override → the developer cache endpoint for the developer cache"
    "https://devcache.mathlib.org" (getBaseURLFrom .developer none none false)
  assertEq "legacy → the storage account for the public service"
    "https://lakecache.blob.core.windows.net" (getBaseURLFrom .published none none true)
  assertEq "legacy → the storage account for the developer cache too"
    "https://lakecache.blob.core.windows.net" (getBaseURLFrom .developer none none true)
  -- The legacy base is the host the container URLs (`azureURL`) are built on.
  assertEq "the legacy base matches the container URLs"
    azureAccountURL (getBaseURLFrom .published none none true)
  assertEq "base override → the given base for the public service"
    "https://cache.example.org" (getBaseURLFrom .published (some "https://cache.example.org") none false)
  assertEq "base override alone covers the developer cache too"
    "https://cache.example.org" (getBaseURLFrom .developer (some "https://cache.example.org") none false)
  assertEq "developer-cache override wins for the developer cache"
    "https://int.example.org" (getBaseURLFrom .developer
      (some "https://cache.example.org") (some "https://int.example.org") false)
  assertEq "developer-cache override does not touch the public service"
    "https://cache.example.org" (getBaseURLFrom .published
      (some "https://cache.example.org") (some "https://int.example.org") false)
  assertEq "developer-cache override alone keeps the public default"
    publicCacheEndpoint (getBaseURLFrom .published none (some "https://int.example.org") false)
  assertEq "override wins over legacy"
    "https://cache.example.org" (getBaseURLFrom .published (some "https://cache.example.org") none true)
  assertEq "developer-cache override wins over legacy"
    "https://int.example.org" (getBaseURLFrom .developer none (some "https://int.example.org") true)
  -- A GitHub Actions `${{ vars.… }}` lookup yields "" while the variable is
  -- undefined, so an empty value must keep the default.
  assertEq "empty value counts as unset"
    publicCacheEndpoint (getBaseURLFrom .published (some "") none false)
  assertEq "empty developer-cache value counts as unset"
    developerCacheEndpoint (getBaseURLFrom .developer none (some "") false)
  assertEq "whitespace-only value counts as unset"
    publicCacheEndpoint (getBaseURLFrom .published (some " \n") none false)
  assertEq "override is trimmed"
    "https://cache.example.org" (getBaseURLFrom .published (some "https://cache.example.org\n") none false)
  -- A base written with a trailing slash must not double the separator in
  -- `{base}/{container}/{key}`.
  assertEq "trailing slash is stripped"
    "https://cache.example.org" (getBaseURLFrom .published (some "https://cache.example.org/") none false)

/-- The container → service mapping is the boundary between the public cache
and the developer cache: it decides which endpoint serves a container's reads
and which storage its writers target. A container joining or leaving the
developer cache must be a deliberate edit to this test. -/
def test_Container_service : IO Unit := do
  IO.println "Container.service:"
  assertTrue "master is public" (Container.master.service == .published)
  assertTrue "legacy is public" (Container.legacy.service == .published)
  assertTrue "forks is developer-cache" (Container.forks.service == .developer)
  assertTrue "nightly-testing is developer-cache" (Container.nightlyTesting.service == .developer)
  assertTrue "pr-toolchain-tests is developer-cache" (Container.prToolchainTests.service == .developer)
  assertEq "public service endpoint"
    "https://cache.mathlib.org" Service.published.endpoint
  assertEq "developer cache endpoint"
    "https://devcache.mathlib.org" Service.developer.endpoint

/-- Read URLs follow `getBaseURL` for the container's service: the same
`/{container}` namespace as `azureURL`, under whichever base the environment
selects for that service. Without a base-URL override, both positions of the
legacy switch are pinned: each service's endpoint by default, `azureURL` under
legacy. -/
def test_Container_getURL : IO Unit := do
  IO.println "Container.getURL:"
  let publicBase ← getBaseURL .published
  let developerBase ← getBaseURL .developer
  assertEq "master read URL" s!"{publicBase}/mathlib4-master" (← Container.master.getURL)
  assertEq "forks read URL" s!"{developerBase}/mathlib4-forks" (← Container.forks.getURL)
  assertEq "legacy read URL" s!"{publicBase}/mathlib4" (← Container.legacy.getURL)
  -- A base-URL override answers for both switch positions, so the pinned
  -- assertions run only without one.
  if (normalizeBaseURL (← IO.getEnv "MATHLIB_CACHE_BASE_URL")).isNone &&
      (normalizeBaseURL (← IO.getEnv "MATHLIB_CACHE_DEVELOPER_BASE_URL")).isNone then
    let ambient ← useLegacy.get
    useLegacy.set false
    assertEq "default read URL is on the public endpoint"
      s!"{publicCacheEndpoint}/mathlib4-master" (← Container.master.getURL)
    assertEq "default forks read URL is on the developer cache endpoint"
      s!"{developerCacheEndpoint}/mathlib4-forks" (← Container.forks.getURL)
    assertEq "default nightly-testing read URL is on the developer cache endpoint"
      s!"{developerCacheEndpoint}/mathlib4-nightly-testing" (← Container.nightlyTesting.getURL)
    useLegacy.set true
    assertEq "legacy read URL matches azureURL"
      Container.master.azureURL (← Container.master.getURL)
    assertEq "legacy forks read URL matches azureURL"
      Container.forks.azureURL (← Container.forks.getURL)
    useLegacy.set ambient

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

/-- The two chains the chain-reading workflows own. Key points the tests pin:
- The developer chain leads with `master`: the master-built deps make up the
  bulk of any fork's files, and only PR-specific files come from `forks`.
- The nightly chain omits `master` (that repo's toolchain gives it a different
  root hash) and `pr-toolchain-tests` (a poisoned toolchain-experiment upload
  must not reach a trusted nightly consumer); it includes `forks` for the PRs
  opened from that repo into mathlib4.
- Both chains end with `legacy`, so older clients' artifacts stay reachable.
-/
def test_workflowContainers : IO Unit := do
  IO.println "Developer.containers / Nightly.containers:"
  assertTrue "developer chain → [master, forks, legacy]"
    (Developer.containers == [.master, .forks, .legacy])
  assertTrue "nightly chain → [nightly-testing, forks, legacy]"
    (Nightly.containers == [.nightlyTesting, .forks, .legacy])
  assertTrue "nightly chain excludes pr-toolchain-tests"
    (!Nightly.containers.contains .prToolchainTests)
  assertTrue "nightly chain excludes master"
    (!Nightly.containers.contains .master)
  -- Every chain ends with `legacy`; dropping it would quietly shrink hit rates.
  assertTrue "developer chain ends with legacy"
    (Developer.containers.getLast? == some .legacy)
  assertTrue "nightly chain ends with legacy"
    (Nightly.containers.getLast? == some .legacy)

/-- `Workflow.forRead` is the boundary between the three read workflows. A
read on the canonical repo is public unless a chain, a scope, or `--unsafe`
names the container-chain read; a fork is always the developer workflow and
the nightly-testing repo always the nightly one. -/
def test_Workflow_decision : IO Unit := do
  IO.println "Workflow.forRepo / forRead:"
  assertTrue "canonical repo → public cache"
    (Workflow.forRepo MATHLIBREPO == .publicCache)
  assertTrue "a fork → developer"
    (Workflow.forRepo "alice/mathlib4" == .developer)
  assertTrue "an unknown repo → developer"
    (Workflow.forRepo "some/other-repo" == .developer)
  assertTrue "the nightly-testing repo → nightly"
    (Workflow.forRepo NIGHTLY_TESTING_REPO == .nightly)
  -- Reads: the repo, the flat endpoint, and whether a chain read was requested
  -- (a chain-read flag, `MATHLIB_CACHE_FROM`, or `MATHLIB_CACHE_REPO_SCOPE`).
  let flat := some "https://cache.example.org/my-prefix"
  assertTrue "canonical repo, no chain read → public cache"
    (Workflow.forRead MATHLIBREPO none false == .publicCache)
  assertTrue "a chain read on the canonical repo → developer"
    (Workflow.forRead MATHLIBREPO none true == .developer)
  assertTrue "a fork → developer, chain read or not"
    (Workflow.forRead "alice/mathlib4" none false == .developer &&
      Workflow.forRead "alice/mathlib4" none true == .developer)
  assertTrue "the nightly-testing repo → nightly, chain read or not"
    (Workflow.forRead NIGHTLY_TESTING_REPO none false == .nightly &&
      Workflow.forRead NIGHTLY_TESTING_REPO none true == .nightly)
  -- A flat endpoint is a public cache served elsewhere: public, whatever the repo.
  assertTrue "MATHLIB_CACHE_GET_URL → public cache for the canonical repo"
    (Workflow.forRead MATHLIBREPO flat false == .publicCache)
  assertTrue "MATHLIB_CACHE_GET_URL → public cache for a fork"
    (Workflow.forRead "alice/mathlib4" flat false == .publicCache)
  assertTrue "MATHLIB_CACHE_GET_URL → public cache for the nightly repo, even with a chain read"
    (Workflow.forRead NIGHTLY_TESTING_REPO flat true == .publicCache)

/-- `Upload.decide` is the decision of a `put`: the configuration, URL and
form, from `MATHLIB_CACHE_PUT_URL` and `--dev-cache` or from the well-known
container `--container` names (`Upload.config`), and the upload itself from
`--repo` and the scope (`Upload.form`). `Upload.dest` is the layout each
upload writes under the URL, the one the readers probe. -/
def test_Upload : IO Unit := do
  IO.println "Upload.decide / Upload.dest:"
  let scope : Scope := ⟨"abc123", .flag⟩
  let envScope : Scope := ⟨"abc123", .env⟩
  let url := "https://acct.example/mathlib4-forks"
  let decided (o : Upload.Options) : Option (Upload × String) := (Upload.decide o).toOption
  let fails (o : Upload.Options) : Bool := (Upload.decide o) matches .error _
  -- The URL variable and the flag.
  assertTrue "the URL alone → the flat upload under it"
    (decided { putURL? := some url } == some (.flat, url))
  assertTrue "a scope on the flat upload fails"
    (fails { putURL? := some url, scope? := some scope })
  assertTrue "a scope from the environment fails the flat upload too"
    (fails { putURL? := some url, scope? := some envScope })
  assertTrue "the flat upload ignores --repo"
    (decided { putURL? := some url, repo? := some "alice/mathlib4" } == some (.flat, url))
  assertTrue "--dev-cache with a repo and a scope → that fork's per-commit namespace"
    (decided { devCache := true, putURL? := some url, repo? := some "alice/mathlib4",
               scope? := some scope } == some (.devCache "alice/mathlib4" (some "abc123"), url))
  assertTrue "--dev-cache without a scope → the repo-namespaced layout, unscoped"
    (decided { devCache := true, putURL? := some url, repo? := some "a/b" } ==
      some (.devCache "a/b" none, url))
  assertTrue "--dev-cache without --repo is for the canonical repository"
    (decided { devCache := true, putURL? := some url, scope? := some scope } ==
      some (.devCache MATHLIBREPO (some "abc123"), url))
  assertTrue "no URL and no container fails" (fails {})
  -- The well-known containers: the URL and the form at once.
  assertTrue "master stands for the flat upload under its Azure base"
    ((Upload.configOf .master).toOption ==
      some { url := Container.master.azureURL, devCache := false })
  assertTrue "forks and the nightly containers stand for developer-cache uploads"
    ([Container.forks, .nightlyTesting, .prToolchainTests].all fun c =>
      (Upload.configOf c).toOption == some { url := c.azureURL, devCache := true })
  assertTrue "legacy is read-only" ((Upload.configOf .legacy) matches .error _)
  -- CI's lines, per trust class.
  assertTrue "master class: flat, --repo ignored"
    (decided { container? := some .master, repo? := some MATHLIBREPO } ==
      some (.flat, Container.master.azureURL))
  assertTrue "forks class: the per-commit namespace of the repo, the scope in the environment"
    (decided { container? := some .forks, repo? := some MATHLIBREPO, scope? := some envScope } ==
      some (.devCache MATHLIBREPO (some "abc123"), Container.forks.azureURL))
  assertTrue "nightly class: the repo-namespaced layout, unscoped"
    (decided { container? := some .nightlyTesting, repo? := some NIGHTLY_TESTING_REPO } ==
      some (.devCache NIGHTLY_TESTING_REPO none, Container.nightlyTesting.azureURL))
  assertTrue "toolchain class: the repo-namespaced layout, unscoped"
    (decided { container? := some .prToolchainTests, repo? := some NIGHTLY_TESTING_REPO } ==
      some (.devCache NIGHTLY_TESTING_REPO none, Container.prToolchainTests.azureURL))
  assertTrue "forks without a scope → unscoped repo layout"
    (decided { container? := some .forks, repo? := some "alice/mathlib4" } ==
      some (.devCache "alice/mathlib4" none, Container.forks.azureURL))
  assertTrue "a scope on a nightly container fails"
    (fails { container? := some .nightlyTesting, scope? := some envScope })
  assertTrue "a scope on master fails"
    (fails { container? := some .master, scope? := some scope })
  assertTrue "--dev-cache with master fails"
    (fails { devCache := true, container? := some .master })
  assertTrue "--dev-cache with forks agrees"
    (decided { devCache := true, container? := some .forks, scope? := some scope } ==
      some (.devCache MATHLIBREPO (some "abc123"), Container.forks.azureURL))
  assertTrue "--container=legacy fails" (fails { container? := some .legacy })
  assertTrue "MATHLIB_CACHE_PUT_URL overrides the container's URL and keeps its form"
    (decided { container? := some .forks, putURL? := some url, scope? := some scope } ==
      some (.devCache MATHLIBREPO (some "abc123"), url))
  assertTrue "MATHLIB_CACHE_PUT_URL overrides the master URL, flat"
    (decided { container? := some .master, putURL? := some url } == some (.flat, url))
  -- The layouts under the URL, against what the readers probe.
  assertTrue "the flat upload writes f/ under the URL"
    (Upload.flat.dest url ==
      { base := url, label := "flat", filesPrefix := "f", markerPrefix := "m" })
  let forkDest := (Upload.devCache "Alice/Mathlib4" (some "abc123")).dest url
  assertEq "a scoped developer-cache upload writes the fork's per-commit namespace, lowercased"
    "f/alice/mathlib4/abc123" forkDest.filesPrefix
  assertEq "its marker is under m/, keyed by repo"
    s!"{url}/m/alice/mathlib4/abc123" (forkDest.markerURL "abc123")
  assertEq "a scoped file lands where the forks round reads it"
    (mkFileURL (some .forks) "alice/mathlib4" url "x.ltar" (some "abc123"))
    (forkDest.fileURL "x.ltar")
  let nightlyURL := Container.nightlyTesting.azureURL
  let unscoped := (Upload.devCache NIGHTLY_TESTING_REPO none).dest nightlyURL
  assertEq "an unscoped developer-cache file lands where the nightly-testing round reads it"
    (mkFileURL (some .nightlyTesting) NIGHTLY_TESTING_REPO nightlyURL "x.ltar")
    (unscoped.fileURL "x.ltar")
  assertEq "a flat file lands where the master round reads it"
    (mkFileURL (some .master) MATHLIBREPO Container.master.azureURL "x.ltar")
    ((Upload.flat.dest Container.master.azureURL).fileURL "x.ltar")
  assertTrue "the scoped upload carries the scope, the others none"
    ((Upload.devCache "a/b" (some "s")).scope? == some "s" &&
      (Upload.devCache "a/b" none).scope? == none && Upload.flat.scope? == none)

/-- Downstream repo resolution honors only a canonical detection, so a fork
remote on the dependency checkout can never steer a downstream read into that
fork's artifacts; the nightly-testing repo passes through because its
artifacts exist nowhere else. -/
def test_resolveDownstreamRepo : IO Unit := do
  IO.println "resolveDownstreamRepo:"
  assertEq "no detection → canonical mathlib"
    MATHLIBREPO (resolveDownstreamRepo none)
  assertEq "canonical detection passes through"
    MATHLIBREPO (resolveDownstreamRepo (some MATHLIBREPO))
  assertEq "nightly-testing detection passes through"
    NIGHTLY_TESTING_REPO (resolveDownstreamRepo (some NIGHTLY_TESTING_REPO))
  assertEq "a fork detection is ignored"
    MATHLIBREPO (resolveDownstreamRepo (some "alice/mathlib4"))
  assertEq "an unrelated detection is ignored"
    MATHLIBREPO (resolveDownstreamRepo (some "some/other-repo"))

/-- Integration check of `resolveRepo` in a project that depends on Mathlib:
against a real git checkout whose `origin` is a fork, the probe still reports
the fork (`detectedRepo?`, which feeds the `--repo` warning), while the
resolved repo — what the read path uses — stays canonical. The same checkout
resolves to the fork on a mathlib checkout, and an explicit `--repo` wins in
both. Skipped when git is unavailable. -/
def test_resolveRepo_downstream : IO Unit := do
  IO.println "resolveRepo (downstream):"
  let dir ← IO.FS.createTempDir
  try
    let git (args : Array String) : IO Bool := do
      try
        let out ← IO.Process.output {cmd := "git", args, cwd := dir}
        pure (out.exitCode == 0)
      catch _ => pure false
    unless (← git #["init", "-q"]) do
      IO.println "  skipped: git unavailable"
      return
    discard <| git #["remote", "add", "origin", "https://github.com/alice/mathlib4.git"]
    let (detected?, resolved) ← withSuppressedOutput (resolveRepo none dir false)
    assertTrue "the probe still reports the fork remote"
      (detected? == some "alice/mathlib4")
    assertEq "the downstream resolution ignores the fork remote"
      MATHLIBREPO resolved
    let (_, rootResolved) ← withSuppressedOutput (resolveRepo none dir true)
    assertEq "a mathlib checkout honors the fork remote" "alice/mathlib4" rootResolved
    let (_, explicitResolved) ←
      withSuppressedOutput (resolveRepo (some "bob/mathlib4") dir false)
    assertEq "an explicit --repo wins downstream" "bob/mathlib4" explicitResolved
  finally
    IO.FS.removeDirAll dir

/-- The public-cache workflow reads one URL, and the chain-reading workflows
pair their chains with read URLs in trust order, each container under its own
service's read base. This test covers `Public.url`, `Chain.withURLs` on both
chains, and `Chain.resolve` under the chain options. -/
def test_readURLs : IO Unit := do
  IO.println "Public.url / Chain.withURLs / Chain.resolve:"
  let publicBase ← getBaseURL .published
  let developerBase ← getBaseURL .developer
  -- The public-cache workflow: the public namespace on the public base, or
  -- the flat endpoint the options name. On an endpoint the namespace is
  -- `mathlib4`; on the Azure account that container is the frozen legacy
  -- one, so the namespace is `mathlib4-master`.
  assertEq "the public cache URL is the public namespace on the public base"
    (publicCacheURL publicBase) (← Public.url none)
  assertEq "an endpoint serves the public cache at /mathlib4"
    "https://cache.mathlib.org/mathlib4" (publicCacheURL "https://cache.mathlib.org")
  assertEq "the Azure account serves the public cache at /mathlib4-master"
    s!"{azureAccountURL}/mathlib4-master" (publicCacheURL azureAccountURL)
  assertEq "MATHLIB_CACHE_GET_URL replaces the public cache URL"
    "https://cache.example.org/my-prefix"
    (← Public.url (some "https://cache.example.org/my-prefix"))
  -- The developer chain crosses to the developer base for its forks round.
  assertTrue "developer chain pairs each container with its service's read URL"
    ((← Chain.withURLs Developer.containers) ==
      [(.master, s!"{publicBase}/mathlib4-master"),
       (.forks, s!"{developerBase}/mathlib4-forks"),
       (.legacy, s!"{publicBase}/mathlib4")])
  assertTrue "nightly chain reads its containers from the developer base"
    ((← Chain.withURLs Nightly.containers) ==
      [(.nightlyTesting, s!"{developerBase}/mathlib4-nightly-testing"),
       (.forks, s!"{developerBase}/mathlib4-forks"),
       (.legacy, s!"{publicBase}/mathlib4")])
  -- `Chain.resolve`: the workflow's chain, or the options' chain in its order;
  -- `--cache-from` wins over `MATHLIB_CACHE_FROM`.
  assertTrue "no chain option → the workflow's default chain"
    (Chain.resolve Developer.containers {} == Developer.containers)
  assertTrue "--cache-from replaces the chain and keeps its order"
    (Chain.resolve Developer.containers { cli? := some [.forks, .master] } == [.forks, .master])
  assertTrue "MATHLIB_CACHE_FROM replaces the chain"
    (Chain.resolve Nightly.containers { env? := some [.prToolchainTests, .nightlyTesting] } ==
      [.prToolchainTests, .nightlyTesting])
  assertTrue "--cache-from wins over MATHLIB_CACHE_FROM"
    (Chain.resolve Developer.containers
      { cli? := some [.master], env? := some [.forks] } == [.master])
  assertTrue "the chain option applies to every workflow's chain"
    (Chain.resolve Nightly.containers { cli? := some [.forks, .master] } == [.forks, .master])

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
  assertTrue "an upload's curl config sits under the given directory"
    ((IO.curlConfigIn "staging").parent == some "staging")
  assertTrue "an upload's curl config carries the same tagged name"
    ((IO.curlConfigIn "staging").fileName == IO.CURLCFG.fileName)
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

/-- URL shape for the per-SHA marker blob a developer-cache `put` writes
(`StagedUploadDest.markerURL`, on `Upload.dest`) and `cache query` probes with
a HEAD request. The marker lives at `/m/{repo}/{sha}` under the URL; a 200
HEAD response signals that all artifacts for the commit were uploaded. -/
def test_markerURL : IO Unit := do
  IO.println "StagedUploadDest.markerURL:"
  let markerURL (url : String) : String :=
    ((Upload.devCache "alice/mathlib4" (some "abc123")).dest url).markerURL "abc123"
  assertEq "forks marker URL under the Azure forks container"
    "https://lakecache.blob.core.windows.net/mathlib4-forks/m/alice/mathlib4/abc123"
    (markerURL Container.forks.azureURL)
  assertEq "the marker write meets the marker probe's legacy URL"
    s!"{Container.forks.azureURL}/{markerPath "alice/mathlib4" "abc123"}"
    (markerURL Container.forks.azureURL)
  -- The marker lives under `/m/`, its own namespace, and is keyed by repo.
  assertEq "marker is under /m/, keyed by repo"
    "m/leanprover-community/mathlib4/deadbeef"
    (markerPath MATHLIBREPO "deadbeef")
  -- The marker follows the URL with the artifacts it marks.
  assertEq "marker URL follows the upload URL"
    "https://bucket.example.org/mirror/mathlib4-forks/m/alice/mathlib4/abc123"
    (markerURL "https://bucket.example.org/mirror/mathlib4-forks")
  -- The repo segment is lowercased, so an upload and a probe for the same fork
  -- meet at one path regardless of how the owner name was capitalized.
  assertEq "marker repo is lowercased in the path"
    "m/alice/mathlib4/abc123"
    (markerPath "Alice/Mathlib4" "abc123")

/-- Marker probes read through the container's read base; marker writes follow
the upload URL (`StagedUploadDest.markerURL`). Without a
base-URL override, both positions of the legacy switch are pinned: probes
address the container's service endpoint by default, and under legacy they
match the Azure write URL. -/
def test_markerReadURL : IO Unit := do
  IO.println "markerReadURL:"
  let base ← getBaseURL .developer
  assertEq "probe URL follows the developer read base"
    s!"{base}/mathlib4-forks/m/alice/mathlib4/abc123"
    (← markerReadURL .forks "alice/mathlib4" "abc123")
  assertEq "probe repo is lowercased in the path"
    s!"{base}/mathlib4-forks/m/alice/mathlib4/abc123"
    (← markerReadURL .forks "Alice/Mathlib4" "abc123")
  if (normalizeBaseURL (← IO.getEnv "MATHLIB_CACHE_BASE_URL")).isNone &&
      (normalizeBaseURL (← IO.getEnv "MATHLIB_CACHE_DEVELOPER_BASE_URL")).isNone then
    let ambient ← useLegacy.get
    useLegacy.set false
    assertEq "default probe URL is on the developer cache endpoint"
      s!"{developerCacheEndpoint}/mathlib4-forks/m/alice/mathlib4/abc123"
      (← markerReadURL .forks "alice/mathlib4" "abc123")
    useLegacy.set true
    assertEq "legacy probe URL matches the Azure write URL"
      s!"{Container.forks.azureURL}/{markerPath "alice/mathlib4" "abc123"}"
      (← markerReadURL .forks "alice/mathlib4" "abc123")
    useLegacy.set ambient

end Marker

section ScopeResolution

/-- `Scope.ofString` admits a hex SHA and rejects anything that could reach a
URL path or a file name unchecked; it keeps the source for the notice. -/
def test_Scope : IO Unit := do
  IO.println "Scope.ofString:"
  let flag ← Scope.ofString "abc123" .flag
  assertTrue "a hex SHA from the flag is kept verbatim with its source"
    (flag == ⟨"abc123", .flag⟩)
  let env ← Scope.ofString "DEADBEEF" .env
  assertTrue "a hex SHA from the environment keeps its source" (env == ⟨"DEADBEEF", .env⟩)
  let rejected ← try discard <| Scope.ofString "refs/heads/x" .flag; pure false catch _ => pure true
  assertTrue "a ref name is rejected" rejected
  let rejected ← try discard <| Scope.ofString "" .env; pure false catch _ => pure true
  assertTrue "an empty scope is rejected" rejected
  -- `Scope.parse` reads `--scope` from the parsed command line; a value git
  -- cannot resolve is taken literally. No commit has the all-zero SHA.
  let zeros := "0000000000000000000000000000000000000000"
  match Commands.cache.process ["get", s!"--scope={zeros}"] with
  | .ok (_, p) =>
    assertTrue "--scope with an unresolvable SHA is taken literally, from the flag"
      ((← withSuppressedOutput (Scope.parse p)) == some ⟨zeros, .flag⟩)
  | .error (_, msg) => assertTrue s!"get --scope parses ({msg})" false
  match Commands.cache.process ["get"] with
  | .ok (_, p) =>
    assertTrue "no --scope → the environment's scope"
      ((← withSuppressedOutput (Scope.parse p)) == (← Scope.ofEnv))
  | .error (_, msg) => assertTrue s!"get parses ({msg})" false

end ScopeResolution

section NonDefaultScope

/-- `Notice.applies` decides whether a chain read prints the non-default-scope
security warning. It warns when any of these takes the reader off the
workflow's default trust boundary:

1. a scope is set and differs from the checked-out HEAD;
2. `--cache-from=LIST` differs from the workflow's chain (passing the chain
   itself is not widening; `MATHLIB_CACHE_FROM`, CI's setting, is not a trigger);
3. `--repo=` is given and differs from the detected git remote, or names a
   non-canonical repo with no detectable remote to compare against;
4. `--unsafe` is set.

The behavior the tests pin most carefully: a plain `cache get` with no options
never warns, even on a fork checkout whose remote isn't the canonical repo.
`detectedRepo?` is passed in (resolved once by `resolveRepo`), so the cases are
deterministic without needing a real checkout. -/
def test_Notice_applies : IO Unit := do
  IO.println "Notice.applies:"
  let chain := Developer.containers
  let base : Notice.Read := { defaultChain := chain }
  let applies (r : Notice.Read) (detected? : Option String := none) : IO Bool :=
    withSuppressedOutput (Notice.applies { r with detectedRepo? := detected? })

  assertTrue "plain get with no options does not warn" (!(← applies base))
  assertTrue "a set scope warns" (← applies { base with scope? := some ⟨"abc123", .flag⟩ })
  assertTrue "a scope from the environment warns too"
    (← applies { base with scope? := some ⟨"abc123", .env⟩ })

  -- A scope equal to HEAD is trust-equivalent to no scope (CI's normal mode).
  -- Skipped when HEAD can't be resolved (not in a git checkout).
  let head? ← try some <$> withSuppressedOutput getGitCommitHash catch _ => pure none
  if let some head := head? then
    assertTrue "a scope equal to HEAD does not warn"
      (!(← applies { base with scope? := some ⟨head, .env⟩ }))

  -- --cache-from equal to the workflow's chain is not widening.
  assertTrue "--cache-from equal to the chain does not warn"
    (!(← applies { base with chain := { cli? := some chain } }))
  assertTrue "--cache-from widening the chain warns"
    (← applies { base with chain := { cli? := some [.master, .forks, .prToolchainTests, .legacy] } })
  assertTrue "--cache-from reordering the chain warns"
    (← applies { base with chain := { cli? := some [.forks, .master, .legacy] } })
  assertTrue "MATHLIB_CACHE_FROM is CI's setting and does not warn"
    (!(← applies { base with chain := { env? := some [.master] } }))

  -- A fork checkout (remote ≠ resolved repo) stays silent without an explicit --repo.
  assertTrue "a fork checkout without --repo does not warn"
    (!(← applies base (some "alice/mathlib4")))
  assertTrue "--repo differing from the remote warns"
    (← applies { base with repoExplicit? := some "bob/mathlib4" } (some "alice/mathlib4"))
  assertTrue "--repo matching the remote does not warn"
    (!(← applies { base with repoExplicit? := some "alice/mathlib4" } (some "alice/mathlib4")))

  -- With no detectable remote there is nothing to compare --repo against, so
  -- a non-canonical --repo warns on the flag alone (it reads that fork's
  -- container purely on the user's say-so), while a canonical one is the
  -- default trust boundary and stays silent.
  assertTrue "a non-canonical --repo with no detectable remote warns"
    (← applies { base with repoExplicit? := some "bob/mathlib4" })
  assertTrue "a canonical --repo with no detectable remote does not warn"
    (!(← applies { base with repoExplicit? := some MATHLIBREPO }))

  -- `--unsafe` (any window) always warns; it walks several untrusted scopes.
  assertTrue "--unsafe warns regardless of other inputs"
    (← applies { base with unsafeWindow? := some 5 })

/-- `Notice.reason` produces the `Reason:` line in the warning, naming the
specific option that triggered it so the user can match it to their command
line. When several apply at once it reports the most specific first —
`--unsafe`, then the scope (named by its source), then `--cache-from`, then
`--repo` — and that order is pinned here. -/
def test_Notice_reason : IO Unit := do
  IO.println "Notice.reason:"
  let chain := Developer.containers
  let base : Notice.Read := { defaultChain := chain }
  let reason (r : Notice.Read) (detected? : Option String := none) : IO String :=
    withSuppressedOutput (Notice.reason { r with detectedRepo? := detected? })
  let withScope : Notice.Read := { base with scope? := some ⟨"abc123", .flag⟩ }

  -- A placeholder rather than a crash if nothing matches.
  assertEq "no trigger yields a placeholder reason" "unknown reason" (← reason base)
  assertEq "a flag scope names the flag and SHA"
    "--scope=abc123 (explicit per-commit scope)" (← reason withScope)
  assertEq "an environment scope names the variable"
    "MATHLIB_CACHE_REPO_SCOPE=abc123 (explicit per-commit scope)"
    (← reason { base with scope? := some ⟨"abc123", .env⟩ })
  -- Scope outranks cache-from when both apply.
  assertEq "scope is reported ahead of cache-from"
    "--scope=abc123 (explicit per-commit scope)"
    (← reason { withScope with chain := { cli? := some [.forks] } })

  -- A HEAD scope is exempt from the scope condition, so a simultaneous
  -- cache-from trigger is reported instead of the scope.
  let head? ← try some <$> withSuppressedOutput getGitCommitHash catch _ => pure none
  if let some head := head? then
    assertEq "a HEAD scope yields the cache-from reason"
      "--cache-from=forks, legacy (explicit container override)"
      (← reason { base with scope? := some ⟨head, .env⟩, chain := { cli? := some [.forks, .legacy] } })

  assertEq "cache-from reason names the container list"
    "--cache-from=forks, legacy (explicit container override)"
    (← reason { base with chain := { cli? := some [.forks, .legacy] } })
  assertEq "repo reason names the override and the detected remote"
    "--repo=bob/mathlib4 (overrides detected git remote: alice/mathlib4)"
    (← reason { base with repoExplicit? := some "bob/mathlib4" } (some "alice/mathlib4"))
  assertEq "a non-canonical --repo with no remote says so"
    "--repo=bob/mathlib4 (no git remote to compare against; reads that fork's cache)"
    (← reason { base with repoExplicit? := some "bob/mathlib4" })
  -- --cache-from equal to the chain is not a trigger, so no reason applies.
  assertEq "cache-from equal to the chain yields the placeholder"
    "unknown reason" (← reason { base with chain := { cli? := some chain } })
  -- `--unsafe` outranks every other trigger and names its window.
  let everything : Notice.Read := { withScope with
    repoExplicit? := some "bob/mathlib4", chain := { cli? := some [.forks] },
    unsafeWindow? := some 7 }
  assertEq "unsafe reason names the window and outranks scope/cache-from/repo"
    "--unsafe (automatic walk over up to 7 fork commit(s); trusting whoever built them)"
    (← reason everything (some "alice/mathlib4"))

/-- `findMostRecentSHAWithCache` returns the first candidate SHA whose per-SHA
marker exists in the `forks` container, used by `cache query` to find the most
recent cached build on the branch. The non-empty cases hit the network (a marker
HEAD probe per SHA) and aren't unit-tested; here we pin that an empty list
returns `none` with no probe. -/
def test_findMostRecentSHAWithCache : IO Unit := do
  IO.println "findMostRecentSHAWithCache:"
  let result ← withSuppressedOutput (Developer.findMostRecentSHAWithCache [] MATHLIBREPO)
  assertTrue "empty SHA list returns none without probing" (result == none)

/-- `findRecentSHAsWithCache` collects up to `limit` marked SHAs. The non-empty
cases hit the network (a marker HEAD probe per SHA); here we pin that an empty
candidate list returns `[]` for any limit, with no probe. -/
def test_findRecentSHAsWithCache : IO Unit := do
  IO.println "findRecentSHAsWithCache:"
  let result ← withSuppressedOutput (Developer.findRecentSHAsWithCache [] MATHLIBREPO 5)
  assertTrue "empty SHA list returns [] without probing" (result == [])
  let result ← withSuppressedOutput (Developer.findRecentSHAsWithCache [] MATHLIBREPO 0)
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
  --   detected? = none, resolved = MATHLIBREPO → the public-cache workflow.
  let (detected?, resolved) ← withSuppressedOutput (resolveRepo none fakePath true)
  assertTrue "resolveRepo detected? is none on git failure" (detected? == none)
  assertTrue "resolveRepo falls back to MATHLIBREPO on git failure" (resolved == MATHLIBREPO)
  assertTrue "the fallback reads the public cache (no fork container for dependency builds)"
    (Workflow.forRead resolved none false == .publicCache)

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
  IO.println "Developer.headIsAncestorOfMaster git fallback:"
  let fakePath := "/tmp/surely-nonexistent-mathlib-cache-test-xyz-9999999"
  let r1 ← withSuppressedOutput (Developer.headIsAncestorOfMaster fakePath)
  assertTrue "Developer.headIsAncestorOfMaster returns false when git throws (nonexistent cwd)"
    (r1 == false)
  let r2 ← withSuppressedOutput (Developer.headIsAncestorOfMaster "/tmp")
  assertTrue "Developer.headIsAncestorOfMaster returns false in a non-git directory" (r2 == false)

end GitFallback

section CommandLine

/-- The command line is the tool's contract with CI and with users, parsed by
the `Cli` library: each command declares its flags, a `get` the flags of every
workflow and a `put` the upload flags, so the parser rejects a typo, a flag
the command does not take, a value of the wrong type, and a duplicate flag
before anything runs. `normalizeArgs` lets a flag precede the command, as CI
writes it. -/
def test_commandLine : IO Unit := do
  IO.println "command line:"
  let parses (args : List String) : Bool := (Commands.cache.process args) matches .ok _
  let errorOf (args : List String) : String :=
    match Commands.cache.process args with
    | .error (_, msg) => msg
    | .ok _ => ""
  -- Reads.
  assertTrue "get accepts the read flags of every workflow"
    (parses ["get", "--repo=alice/mathlib4", "--cache-from=master,forks", "--scope=HEAD",
      "--unsafe-window=3"])
  assertTrue "get accepts module arguments" (parses ["get", "Mathlib/Init.lean", "Mathlib.Data.+"])
  assertTrue "--unsafe is a flag without a value" (parses ["get", "--unsafe"])
  assertTrue "a typo on a flag is rejected" (!parses ["get", "--scoop=abc"])
  assertTrue "a value on --unsafe is rejected" (!parses ["get", "--unsafe=5"])
  assertTrue "--scope without a value is rejected" (!parses ["get", "--scope"])
  assertTrue "an unknown container in --cache-from is rejected"
    (!parses ["get", "--cache-from=master,bogus"])
  assertTrue "a non-numeric --unsafe-window is rejected" (!parses ["get", "--unsafe-window=many"])
  assertTrue "a duplicate flag is rejected" (!parses ["get", "--scope=a", "--scope=b"])
  assertTrue "an upload flag on get is rejected" (!parses ["get", "--dev-cache"])
  assertTrue "the unknown-flag error names the flag"
    ((errorOf ["get", "--scoop=abc"]).startsWith "Unknown flag `--scoop`")
  -- Writes.
  assertTrue "put-staged accepts the upload flags"
    (parses ["put-staged", "--staging-dir=/tmp", "--dev-cache", "--repo=alice/mathlib4",
      "--scope=abc", "--backend=s3"])
  assertTrue "put accepts the flat upload's flags alone" (parses ["put", "--backend=s3"])
  assertTrue "--unsafe on put is rejected" (!parses ["put", "--unsafe"])
  assertTrue "put accepts --container as the URL shortcut" (parses ["put", "--container=master"])
  assertTrue "an unknown container is rejected" (!parses ["put", "--container=bogus"])
  assertTrue "CI's upload lines parse"
    (parses ["put-staged", "--container=forks", "--staging-dir=/tmp", "--repo=alice/mathlib4"] &&
     parses ["put-staged", "--container=master", "--staging-dir=/tmp", "--repo=a/b"] &&
     parses ["put-staged", "--backend=s3", "--staging-dir=/tmp", "--repo=a/b"])
  assertTrue "put-staged requires --staging-dir" (!parses ["put-staged", "--dev-cache"])
  assertTrue "an unknown backend is rejected" (!parses ["put", "--backend=ftp"])
  assertTrue "stage requires --staging-dir" (!parses ["stage"])
  assertTrue "unstage accepts --staging-dir alone" (parses ["unstage!", "--staging-dir=/tmp"])
  -- Commands.
  assertTrue "query takes an optional ref"
    (parses ["query"] && parses ["query", "HEAD", "--repo=alice/mathlib4"])
  assertTrue "an unknown command is rejected" (!parses ["fetch"])
  assertTrue "pack takes no flags" (!parses ["pack", "--repo=alice/mathlib4"])
  -- A flag before the command.
  assertTrue "flags may precede the command"
    (Commands.normalizeArgs ["--repo=a/b", "get", "Archive"] == ["get", "--repo=a/b", "Archive"])
  assertTrue "flags alone stay in place" (Commands.normalizeArgs ["--help"] == ["--help"])
  -- The chain-read flags select the developer workflow on the canonical repo,
  -- and each workflow takes its own flags and no other's.
  match Commands.cache.process ["get", "--cache-from=forks,master", "--unsafe-window=2"] with
  | .ok (_, p) =>
    assertTrue "--cache-from requests a chain read" (Workflow.chainReadFlagged p)
    let options ← withSuppressedOutput (Developer.parseOptions p)
    assertTrue "the developer workflow reads --cache-from in order"
      (options.chain.cli? == some [.forks, .master])
    assertTrue "the developer workflow reads --unsafe-window" (options.unsafeWindow? == some 2)
    let foreignTo (own : Array Cli.Flag) : List String :=
      (foreignFlags own p).toList.map (·.flag.longName)
    assertTrue "no flag is foreign to the developer workflow"
      ((foreignTo Developer.flags).isEmpty)
    assertTrue "--unsafe-window is foreign to the nightly workflow"
      (foreignTo Nightly.flags == ["unsafe-window"])
    assertTrue "both flags are foreign to the public-cache workflow"
      (foreignTo Public.flags == ["cache-from", "unsafe-window"])
  | .error (_, msg) => assertTrue s!"the chain-read line parses ({msg})" false
  match Commands.cache.process ["get", "--repo=alice/mathlib4", "Mathlib.Init"] with
  | .ok (_, p) =>
    assertTrue "--repo alone requests no chain read" (!Workflow.chainReadFlagged p)
    assertTrue "--repo reads as the repo" (CommonFlag.repoOf p == some "alice/mathlib4")
    assertTrue "the module arguments are kept" (p.variableArgsAs! String == #["Mathlib.Init"])
  | .error (_, msg) => assertTrue s!"the plain line parses ({msg})" false
  match Commands.cache.process ["put-staged", "--staging-dir=/tmp/x", "--dev-cache",
      "--backend=s3"] with
  | .ok (_, p) =>
    assertTrue "the backend and the staging directory read typed, and --dev-cache is seen"
      (CommonFlag.backendOf p == .s3 && CommonFlag.stagingDirOf p == some "/tmp/x" &&
        p.hasFlag Upload.devCacheFlag.longName)
  | .error (_, msg) => assertTrue s!"the write line parses ({msg})" false

/-- A boolean environment variable is on for `1` and `true`, off for `0` and
`false`, and `ifUnset` for an absent or blank value.
`MATHLIB_CACHE_DEBUG_USE_LEGACY` reads this way with `ifUnset := false`.

`ifUnset` decides the unset case alone: a variable that defaults on still reads
`0` as off, and a value the parser cannot read warns and falls back to
`ifUnset`. -/
def test_parseEnvFlag : IO Unit := do
  IO.println "parseEnvFlag:"
  let shown (flag : Bool) : String := if flag then "on" else "off"
  -- The variable name only reaches the warning, so any name serves the rest.
  let parse (value? : Option String) (ifUnset : Bool) : IO String := do
    return shown (← withSuppressedOutput (parseEnvFlag "FLAG" value? ifUnset))
  assertEq "absent value takes ifUnset" "off" (← parse none false)
  assertEq "empty value takes ifUnset" "off" (← parse (some "") false)
  assertEq "whitespace-only value takes ifUnset" "off" (← parse (some " \n") false)
  assertEq "1 is on" "on" (← parse (some "1") false)
  assertEq "true is on" "on" (← parse (some "true") false)
  assertEq "case does not matter" "on" (← parse (some "TRUE") false)
  assertEq "surrounding space does not matter" "on" (← parse (some " true ") false)
  assertEq "0 is off" "off" (← parse (some "0") false)
  assertEq "false is off" "off" (← parse (some "false") false)
  assertEq "an unreadable value falls back to ifUnset" "off" (← parse (some "yes") false)
  assertEq "a number other than 0 or 1 is unreadable" "off" (← parse (some "2") false)
  -- A default-on variable: `ifUnset` moves the unset case and nothing else.
  assertEq "absent value takes an on default" "on" (← parse none true)
  assertEq "empty value takes an on default" "on" (← parse (some "") true)
  assertEq "0 is off against an on default" "off" (← parse (some "0") true)
  assertEq "false is off against an on default" "off" (← parse (some "false") true)
  assertEq "1 is on against an on default" "on" (← parse (some "1") true)
  assertEq "an unreadable value takes an on default" "on" (← parse (some "yes") true)
  -- The warning names the variable and the value it rejected, and it fires only
  -- for a value the parser cannot read.
  let (warning, _) ← IO.FS.withIsolatedStreams (parseEnvFlag "MY_FLAG" (some "yes") false)
  assertTrue "the warning names the variable and the value"
    ((warning.splitOn "MY_FLAG=yes").length == 2)
  let (quiet, _) ← IO.FS.withIsolatedStreams (parseEnvFlag "MY_FLAG" (some "0") false)
  assertEq "a readable value warns about nothing" "" quiet

end CommandLine

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
`--oauth2-bearer` or the S3 `--user` keypair). The default keeps the argument
list in the message. -/
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
  let dest : StagedUploadDest :=
    { base := "https://example.invalid"
      label := "master"
      filesPrefix := "mathlib4-master/f"
      markerPrefix := "mathlib4-master/m/leanprover-community/mathlib4" }
  let cfg := mkPutConfigContent dest #["/tmp/00000000deadbeef.ltar"]
  assertTrue "uploads the file" ((cfg.splitOn "-T /tmp/00000000deadbeef.ltar").length == 2)
  assertTrue "addresses {base}/{filesPrefix}/{name}"
    ((cfg.splitOn
      "url = https://example.invalid/mathlib4-master/f/00000000deadbeef.ltar").length == 2)
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

section UploadDestination

/-- `UploadBackend.parse?` accepts the known backend names, case-insensitively. -/
def test_uploadBackendParse : IO Unit := do
  IO.println "UploadBackend.parse?:"
  assertTrue "azure parses" (UploadBackend.parse? "azure" == some .azure)
  assertTrue "s3 parses, case-insensitively" (UploadBackend.parse? "S3" == some .s3)
  assertTrue "an unknown name is rejected" ((UploadBackend.parse? "gcs").isNone)

/-- `azureAuthFrom` resolves the azure backend's credential: the bearer
token. A missing bearer errors naming the fix. -/
def test_azureAuthFrom : IO Unit := do
  IO.println "azureAuthFrom:"
  assertTrue "bearer token" (azureAuthFrom (some "bear") matches .ok "bear")
  assertTrue "no bearer errors" (azureAuthFrom none matches .error _)

/-- `s3AuthFrom` resolves the s3 backend's credentials: the pair with its
optional session token. A half-set pair errors instead of resolving. -/
def test_s3AuthFrom : IO Unit := do
  IO.println "s3AuthFrom:"
  assertTrue "pair with a session token"
    (s3AuthFrom (some "AK") (some "SK") (some "ST")
      matches .ok ⟨"AK", "SK", some "ST"⟩)
  assertTrue "pair without a session token"
    (s3AuthFrom (some "AK") (some "SK") none matches .ok ⟨"AK", "SK", none⟩)
  assertTrue "key id without a secret errors"
    (s3AuthFrom (some "AK") none none matches .error _)
  assertTrue "secret without a key id errors"
    (s3AuthFrom none (some "SK") none matches .error _)
  assertTrue "a stray session token alone errors"
    (s3AuthFrom none none (some "ST") matches .error _)

/-- `s3RegionFrom` resolves the s3 backend's signing region. An unset region
errors, and so does a value that is not a region name. -/
def test_s3RegionFrom : IO Unit := do
  IO.println "s3RegionFrom:"
  assertTrue "a plain name" (s3RegionFrom (some "auto") matches .ok "auto")
  assertTrue "an AWS region" (s3RegionFrom (some "eu-west-1") matches .ok "eu-west-1")
  assertTrue "unset errors" (s3RegionFrom none matches .error _)
  assertTrue "a value with a colon errors" (s3RegionFrom (some "eu:west") matches .error _)

/-- `isValidScope` gates every scope before it reaches a URL path or a file
name (the fork namespace, the marker path, and the marker's local temp file):
hex SHAs pass; a value with path characters or ref syntax is rejected, and
`Scope.ofString` throws on it. -/
def test_isValidScope : IO Unit := do
  IO.println "isValidScope:"
  assertTrue "a full SHA passes"
    (isValidScope "5a3c7e9a2f8c1d6b4e0f9a2c3d4e5f6a7b8c9d0e")
  assertTrue "a short SHA passes" (isValidScope "deadbeef")
  assertTrue "uppercase hex passes" (isValidScope "DEADBEEF")
  assertTrue "empty is rejected" (!isValidScope "")
  assertTrue "a path separator is rejected" (!isValidScope "abc/def")
  assertTrue "an absolute path is rejected" (!isValidScope "/tmp/pwned")
  assertTrue "dot-dot is rejected" (!isValidScope "..")
  assertTrue "a ref name is rejected" (!isValidScope "HEAD")
  assertTrue "a branch name is rejected" (!isValidScope "nightly-testing")
  assertTrue "an overlong value is rejected" (!isValidScope (String.ofList (List.replicate 65 'a')))
  -- `Scope.ofString` enforces the guard for both scope sources.
  let threw ← try discard <| Scope.ofString "/tmp/pwned" .env; pure false catch _ => pure true
  assertTrue "Scope.ofString throws on a malformed scope" threw
  assertTrue "Scope.ofString passes a hex scope through"
    ((← Scope.ofString "deadbeef" .flag) == ⟨"deadbeef", .flag⟩)

/-- `fileDirPath` is the one path policy behind `mkFileURL` and every
upload tool: bare `f` for a flat container, repo-namespaced otherwise, with
the per-SHA scope appended when given, and the repo lowercased. -/
def test_fileDirPath : IO Unit := do
  IO.println "fileDirPath:"
  assertEq "flat container → bare f"
    "f" (fileDirPath (some .master) MATHLIBREPO (some "sha1"))
  assertEq "namespaced container → repo segment"
    "f/alice/mathlib4" (fileDirPath (some .forks) "alice/mathlib4" none)
  assertEq "scope appends the per-commit segment"
    "f/alice/mathlib4/sha1" (fileDirPath (some .forks) "alice/mathlib4" (some "sha1"))
  assertEq "no container follows the repo (flat for canonical)"
    "f" (fileDirPath none MATHLIBREPO (some "sha1"))
  assertEq "no container follows the repo (namespaced for a fork)"
    "f/alice/mathlib4/sha1" (fileDirPath none "alice/mathlib4" (some "sha1"))
  assertEq "the repo is lowercased"
    "f/alice/mathlib4" (fileDirPath (some .forks) "Alice/Mathlib4" none)

/-- The curl arguments an s3 upload signs each request with (`s3CurlArgs`),
and the `If-None-Match: *` guard the curl tool adds to a non-overwrite put on
every backend (`uploadPutArgs`). Pins the S3 shape: SigV4 in the given region,
the `UNSIGNED-PAYLOAD` hash that lets curl sign a `-T` upload, and the
session-token header for temporary credentials. The azure arguments spawn
`date`, so this covers S3 only. -/
def test_s3CurlArgs : IO Unit := do
  IO.println "s3CurlArgs:"
  let s3 := uploadPutArgs (s3CurlArgs ⟨"AK", "SK", some "ST"⟩ "auto") (overwrite := false)
  assertTrue "S3 signs with SigV4 in the given region"
    ((s3.toList.zip s3.toList.tail).contains ("--aws-sigv4", "aws:amz:auto:s3"))
  assertTrue "S3 carries the keypair as --user"
    ((s3.toList.zip s3.toList.tail).contains ("--user", "AK:SK"))
  assertTrue "S3 signs the upload as UNSIGNED-PAYLOAD"
    (s3.contains "x-amz-content-sha256: UNSIGNED-PAYLOAD")
  assertTrue "S3 sends the session token" (s3.contains "x-amz-security-token: ST")
  assertTrue "non-overwrite adds If-None-Match" (s3.contains "If-None-Match: *")
  assertTrue "S3 sends no Azure blob-type header"
    (!s3.contains "x-ms-blob-type: BlockBlob")
  let s3Static := uploadPutArgs (s3CurlArgs ⟨"AK", "SK", none⟩ "auto") (overwrite := true)
  assertTrue "a static keypair sends no session token"
    (s3Static.all (!·.startsWith "x-amz-security-token"))
  assertTrue "overwrite drops If-None-Match" (!s3Static.contains "If-None-Match: *")

/-- The transfer-tool policy for the s3 backend: rclone when available, curl
otherwise; MATHLIB_CACHE_PUT_FORCE_CURL selects curl regardless. The azure
backend has no policy to test: it always transfers with curl
(`azurePutStaged`). -/
def test_s3UploadToolFrom : IO Unit := do
  IO.println "s3UploadToolFrom:"
  assertTrue "rclone when available"
    (s3UploadToolFrom (forceCurl := false) (rcloneAvailable := true) == .rclone)
  assertTrue "curl without rclone"
    (s3UploadToolFrom (forceCurl := false) (rcloneAvailable := false) == .curl)
  assertTrue "the flag forces curl past an available rclone"
    (s3UploadToolFrom (forceCurl := true) (rcloneAvailable := true) == .curl)

/-- The endpoint/bucket split the rclone tool builds its remote from. -/
def test_s3EndpointSplit : IO Unit := do
  IO.println "s3EndpointSplit:"
  assertTrue "endpoint and bucket split"
    ((s3EndpointSplit "https://acct.r2.cloudflarestorage.com/devbucket").toOption ==
      some ("https://acct.r2.cloudflarestorage.com", "devbucket"))
  assertTrue "a deeper path stays with the bucket"
    ((s3EndpointSplit "https://host.example/bucket/prefix").toOption ==
      some ("https://host.example", "bucket/prefix"))
  assertTrue "a base without a bucket path errors"
    (s3EndpointSplit "https://host.example" matches .error _)
  assertTrue "a trailing slash errors rather than yield an empty segment"
    (s3EndpointSplit "https://host.example/bucket/" matches .error _)
  assertTrue "a non-URL errors"
    (s3EndpointSplit "host.example/bucket" matches .error _)

/-- The rclone invocations, pinned: the files copy is restricted to the
caller's `--files-from` list and skips existing objects (the curl tool's
`If-None-Match: *`); the marker copy overwrites freely, like the curl marker
put; and both remotes are the same `{prefix}/{name}` shape every other tool
addresses. -/
def test_rcloneArgs : IO Unit := do
  IO.println "rcloneArgs:"
  let dest := (Upload.devCache "alice/mathlib4" (some "abc1")).dest "https://acct.example/devbucket"
  let files := rcloneFilesArgs "devbucket" dest "staging" "tmp/files-from.txt"
    (overwrite := false)
  assertEq "files copy remote matches the destination contract"
    s!":s3:devbucket/{dest.filesPrefix}" files[2]!
  assertTrue "files copy is a copy" (files[0]! == "copy")
  assertTrue "files copy is restricted to the caller's file list"
    ((files.toList.zip files.toList.tail).contains ("--files-from", "tmp/files-from.txt"))
  assertTrue "a non-overwrite copy skips existing objects"
    (files.contains "--ignore-existing")
  assertTrue "an overwrite copy replaces existing objects"
    (!(rcloneFilesArgs "devbucket" dest "staging" "tmp/files-from.txt"
      (overwrite := true)).contains "--ignore-existing")
  assertTrue "files copy skips the bucket-creation probe"
    (files.contains "--s3-no-check-bucket")
  let marker := rcloneMarkerArgs "devbucket" dest "tmp/abc1" "abc1"
  assertEq "marker remote matches the marker path contract"
    s!":s3:devbucket/{markerPath "alice/mathlib4" "abc1"}" marker[2]!
  assertTrue "marker copy is a copyto" (marker[0]! == "copyto")
  assertTrue "marker copy overwrites freely"
    !(marker.contains "--ignore-existing")

/-- The child environment the rclone tool runs under: credentials and
endpoint set, a stale session token cleared when the credential has none,
and nothing else touched. -/
def test_rcloneEnv : IO Unit := do
  IO.println "rcloneEnv:"
  let env := rcloneEnv ⟨"AK", "SK", some "tok"⟩ "https://host.example" "Other" "auto"
  assertTrue "credentials and endpoint are set"
    (env.contains ("RCLONE_S3_ACCESS_KEY_ID", some "AK") &&
     env.contains ("RCLONE_S3_SECRET_ACCESS_KEY", some "SK") &&
     env.contains ("RCLONE_S3_ENDPOINT", some "https://host.example") &&
     env.contains ("RCLONE_S3_SESSION_TOKEN", some "tok"))
  assertTrue "config comes from the tool, not ambient credentials"
    (env.contains ("RCLONE_S3_ENV_AUTH", some "false"))
  assertTrue "the region is the one given"
    (env.contains ("RCLONE_S3_REGION", some "auto"))
  assertTrue "the provider is set (rclone refuses to run without one)"
    (env.contains ("RCLONE_S3_PROVIDER", some "Other"))
  let noSession := rcloneEnv ⟨"AK", "SK", none⟩ "https://host.example" "Other" "auto"
  assertTrue "a static keypair clears any ambient session token"
    (noSession.contains ("RCLONE_S3_SESSION_TOKEN", none))

/-- `putStagedViaRclone` end to end against a recording fake binary: the
files copy runs first with the child environment the caller assembled
(`rcloneEnv`), the marker copy follows with the SHA-named temp file, and a
marker failure warns without failing the put. -/
def test_putStagedViaRclone : IO Unit := do
  IO.println "putStagedViaRclone (fake binary):"
  if System.Platform.isWindows then
    IO.println "  (skipped on Windows)"
    return
  let dir ← IO.FS.createTempDir
  try
    let staging := dir / "staging"
    IO.FS.createDirAll staging
    IO.FS.writeFile (staging / "aa.ltar") "x"
    let fake := dir / "fake-rclone"
    IO.FS.writeFile fake <|
      "#!/bin/sh\n" ++
      s!"printf '%s\\n' \"$@\" > \"{dir}/args-$1\"\n" ++
      s!"env | grep '^RCLONE_S3_\\|^HOME=' | sort > \"{dir}/env-$1\"\n" ++
      -- The files-from list is a temp file the tool deletes after the run, so
      -- the fake preserves its content for the assertions below.
      "prev=''\n" ++
      "for a in \"$@\"; do\n" ++
      s!"  if [ \"$prev\" = --files-from ]; then cp \"$a\" \"{dir}/files-from-copy\"; fi\n" ++
      "  prev=\"$a\"\n" ++
      "done\n" ++
      "if [ \"$1\" = copyto ]; then exit 3; fi\n" ++
      "exit 0\n"
    discard <| IO.runCmd "chmod" #["+x", fake.toString]
    let dest := (Upload.devCache "alice/mathlib4" (some "abc1")).dest "https://acct.example/devbucket"
    withSuppressedOutput <| putStagedViaRclone dest
      (rcloneEnv ⟨"AK", "SK", some "tok"⟩ "https://acct.example" "Other" "auto")
      "devbucket" (some "abc1") staging
      #["aa.ltar"] (overwrite := false) (rclone := fake.toString)
    let copyArgs ← IO.FS.readFile (dir / "args-copy")
    assertTrue "files copy targets the staging dir"
      ((copyArgs.splitOn "\n").any (· == staging.toString))
    assertTrue "files copy addresses the resolved remote"
      ((copyArgs.splitOn "\n").any (· == s!":s3:devbucket/{dest.filesPrefix}"))
    assertEq "the files-from list holds exactly the caller's file names"
      "aa.ltar\n" (← IO.FS.readFile (dir / "files-from-copy"))
    let copyEnv ← IO.FS.readFile (dir / "env-copy")
    assertTrue "the credentials travel in the child environment"
      ((copyEnv.splitOn "\n").contains "RCLONE_S3_ACCESS_KEY_ID=AK" &&
       (copyEnv.splitOn "\n").contains "RCLONE_S3_SESSION_TOKEN=tok" &&
       (copyEnv.splitOn "\n").contains "RCLONE_S3_ENDPOINT=https://acct.example")
    -- The env parameter extends the parent environment (each pair sets or
    -- unsets one variable), so the child keeps HOME, PATH, and any RCLONE_*
    -- tuning of the caller. Pinned here so a runtime change cannot silently
    -- drop them from rclone's environment.
    assertTrue "the parent environment is inherited alongside the credentials"
      ((copyEnv.splitOn "\n").any (·.startsWith "HOME="))
    -- The fake exits 3 on `copyto`, so this pins the marker invocation shape
    -- and that a marker failure warns without failing the put.
    let markerArgs ← IO.FS.readFile (dir / "args-copyto")
    assertTrue "the marker temp file is named after the SHA"
      ((markerArgs.splitOn "\n").any (·.endsWith "/abc1"))
    assertTrue "the marker addresses the marker path"
      ((markerArgs.splitOn "\n").any
        (· == s!":s3:devbucket/{dest.markerPrefix}/abc1"))
  finally
    IO.FS.removeDirAll dir

end UploadDestination

section UnsafeRounds

/-- `Chain.rounds` expands a chain, paired with URLs, into download rounds.
Only a container with per-commit namespaces (`Container.perCommit`, that is
`forks`) reads at a scope: the explicit scope, else the caller's HEAD scope,
else one round per `--unsafe` SHA. Every other container reads unscoped. -/
def test_chainRounds : IO Unit := do
  IO.println "Chain.rounds:"
  let chain : List (Container × String) := [(.master, "U_m"), (.forks, "U_f"), (.legacy, "U_l")]
  let round (c : Container) (url : String) (scope? : Option String := none) : DownloadRound :=
    { container? := some c, url, scope? }

  assertTrue "forks is the only per-commit container"
    (Container.all.filter Container.perCommit == [.forks])

  -- No unsafe scopes: one round per container; only forks carries a scope.
  assertTrue "no scopes → one unscoped round per container"
    (Chain.rounds chain none [] ==
      [round .master "U_m", round .forks "U_f", round .legacy "U_l"])
  assertTrue "explicit scope reaches the forks round only"
    (Chain.rounds chain (some "S") [] ==
      [round .master "U_m", round .forks "U_f" (some "S"), round .legacy "U_l"])

  -- With no explicit scope the forks round defaults to the HEAD scope; the other
  -- containers' layouts are not SHA-scoped, so it must not leak into them.
  assertTrue "head scope → forks at head, others unscoped"
    (Chain.rounds chain none [] (some "H") ==
      [round .master "U_m", round .forks "U_f" (some "H"), round .legacy "U_l"])
  assertTrue "explicit scope wins over head scope"
    (Chain.rounds chain (some "S") [] (some "H") ==
      [round .master "U_m", round .forks "U_f" (some "S"), round .legacy "U_l"])
  assertTrue "unsafe mode ignores head scope"
    (Chain.rounds chain none ["a"] (some "H") ==
      [round .master "U_m", round .forks "U_f" (some "a"), round .legacy "U_l"])

  -- Unsafe scopes: only forks fans out, in order; others unscoped, base dropped.
  assertTrue "unsafe scopes fan out forks (in order), others unscoped"
    (Chain.rounds chain (some "ignored") ["a", "b"] ==
      [round .master "U_m", round .forks "U_f" (some "a"), round .forks "U_f" (some "b"),
       round .legacy "U_l"])

  -- The nightly containers are unscoped whatever the scope: a scoped path
  -- there is one no writer fills.
  assertTrue "nightly containers read unscoped under a scope"
    (Chain.rounds [(.nightlyTesting, "U_n"), (.prToolchainTests, "U_p")] (some "S") [] ==
      [round .nightlyTesting "U_n", round .prToolchainTests "U_p"])

  -- A chain without forks admits no SHA-scoped reads, so it is left unchanged.
  assertTrue "no forks container → unsafe scopes have no effect"
    (Chain.rounds [(.master, "U_m"), (.legacy, "U_l")] none ["a", "b"] ==
      [round .master "U_m", round .legacy "U_l"])

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
  test_Container_service
  test_Container_flatPath
  test_workflowContainers
  test_Workflow_decision
  test_Upload
  test_resolveDownstreamRepo
  test_resolveRepo_downstream
  test_readURLs
  test_mkFileURL
  test_parseCacheFromList
  test_extractRepoFromUrl
  test_hashFromFileName
  test_tempFileNames
  test_isRemoteURL
  test_UInt64_asLTar
  test_hash_roundtrip
  test_markerURL
  test_markerReadURL
  test_Scope
  test_Notice_applies
  test_Notice_reason
  test_findMostRecentSHAWithCache
  test_findRecentSHAsWithCache
  test_getRemoteRepo_gitFallback
  test_headIsAncestorOfMaster_gitFallback
  test_parseEnvFlag
  test_commandLine
  test_curlFollowRedirectArgs
  test_curlRetryArgs
  test_runCmd_showArgsOnError
  test_isCacheMissStatus
  test_isAlreadyPresentStatus
  test_classifyDownload
  test_classifyUpload
  test_mkPutConfigContent
  test_uploadBackendParse
  test_azureAuthFrom
  test_s3AuthFrom
  test_s3RegionFrom
  test_isValidScope
  test_fileDirPath
  test_s3CurlArgs
  test_s3UploadToolFrom
  test_s3EndpointSplit
  test_rcloneArgs
  test_rcloneEnv
  test_putStagedViaRclone
  test_chainRounds
  test_finalizeDecomp
  test_monitorCurl_carries_decomp_state

end Cache.Test

open Cache Cache.Test Cache.Requests in
def main : IO UInt32 := do
  -- Resolve the legacy switch the way the tool's `main` does, so the read-base
  -- assertions see the setting the environment names.
  useLegacy.set (← getEnvFlag "MATHLIB_CACHE_DEBUG_USE_LEGACY" (ifUnset := false))
  runAll
  let n ← failures.get
  if n == 0 then
    IO.println "\nAll cache tests passed."
    return 0
  else
    IO.eprintln s!"\n{n} cache test(s) failed."
    return 1
