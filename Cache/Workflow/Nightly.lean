/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Workflow.Chain
import Cache.Workflow.Notice

/-!
# The nightly workflow

The workflow of the nightly-testing repository, `NIGHTLY_TESTING_REPO`: its
checkouts, its CI, and a project whose Mathlib dependency is pinned to it.
That repository builds under a non-release toolchain, so its root hash differs
from master's and its artifacts exist only in the developer cache's
`nightly-testing` and `pr-toolchain-tests` containers, which its CI fills. A
read walks the chain `containers`. The nightly containers cache by file hash,
so `query` has nothing to find, and `--unsafe` is not an option of this
workflow.

The workflow's flags (`flags`) are the chain `--cache-from`, with
`MATHLIB_CACHE_FROM` (CI widens the chain per job), and the scope `--scope`,
with `MATHLIB_CACHE_REPO_SCOPE`, for the `forks` round: a PR from the
nightly-testing repository into mathlib4 builds with fork trust and uploads
there.
-/

namespace Cache.Workflow.Nightly

open Cache.Requests
open System (FilePath)

/-- The workflow's name in messages. -/
def name : String := "nightly"

/-- The flags of the workflow. -/
def flags : Array Cli.Flag := #[ChainOptions.flag, Scope.flag]

/-- The options of a nightly read. -/
structure Options where
  /-- The chain options: `--cache-from`, `MATHLIB_CACHE_FROM`. -/
  chain : ChainOptions := {}
  /-- The per-commit scope of the `forks` round: `--scope`,
  `MATHLIB_CACHE_REPO_SCOPE`. -/
  scope? : Option Scope := none
  deriving Inhabited

/-- Parse the workflow's options from the parsed command line `p`, with
`--scope` refs resolved in `cwd`. Rejects a flag of another workflow,
`--unsafe` included. -/
def parseOptions (p : Cli.Parsed) (cwd : FilePath := ".") : IO Options := do
  rejectForeignFlags name flags p
  return { chain := ← ChainOptions.parse p, scope? := ← Scope.parse p cwd }

/--
The nightly chain, most trusted first: `nightly-testing` for the repository's
own trusted builds, `forks` for the PRs opened from that repository into
mathlib4 (their CI uploads land there, in the per-commit namespace), then
`legacy`. `master` is absent: the nightly root hash differs, so a master probe
misses. `pr-toolchain-tests` is absent too, so the default chain keeps an
upload from an experimental toolchain branch away from a trusted nightly
consumer; CI widens the chain for those branches through `MATHLIB_CACHE_FROM`.
-/
def containers : List Container := [.nightlyTesting, .forks, .legacy]

/--
The read: the notice when the read is taken off the default trust boundary,
then the chain rounds (`Chain.readRounds containers`). A scope applies to the
`forks` round alone.
-/
def get (options : Options) (ctx : ReadContext) (req : ReadRequest) : IO.CacheM Unit := do
  Notice.emit {
    repoExplicit? := ctx.repoExplicit?, detectedRepo? := ctx.detectedRepo?,
    chain := options.chain, defaultChain := containers, scope? := options.scope?,
    cwd := ctx.mathlibCwd } ctx.repo
  let rounds ← Chain.readRounds containers options.chain options.scope? ctx.mathlibCwd
  getFiles rounds ctx.repo req.hashMap req.forceDownload req.forceDownload req.parallel
    req.decompress

end Cache.Workflow.Nightly
