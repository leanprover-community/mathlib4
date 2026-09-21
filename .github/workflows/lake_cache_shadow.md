# Lake cache shadow pipeline

`lake_cache_shadow.yml` exercises Lake's built-in artifact cache against the
live mathlib4 master branch. It runs beside the regular master CI and stays
independent of it. It writes to the isolated `mathlib4-master-shadow` scope,
which only this pipeline reads.

The pipeline caches mathlib and every git dependency in its manifest, under
one revision: the mathlib commit. mathlib goes to
`revisions/<SCOPE>/<mathlib-sha>.jsonl` and each dependency to
`revisions/<SCOPE>/<DEP>/<mathlib-sha>.jsonl`, where `<DEP>` is the dependency
and `<SCOPE>` is `mathlib4-master-shadow`. One mathlib commit therefore names
one complete set of packages. A dispatched run can set `cache_deps` to false,
which leaves the dependencies out of that run's mappings.

## Jobs

- `build_and_stage` builds mathlib and its dependencies, and stages the
  mappings of each package.
- `upload` pushes the staged files to the bucket. It records a manifest under
  `analysis/<toolchain-slug>/` and reports the carryover.
- `consume` fetches every package into a fresh checkout, builds against them,
  and verifies the result with `--rehash`.
- `downstream` builds a small project that requires mathlib, from mathlib's sha
  alone. It runs when the targets are `Mathlib` and the run caches
  dependencies.
- `report` posts a summary of the run to Zulip.

## Cache service configuration

Each job runs on its own runner and writes its own service definition, into
the file `LAKE_CONFIG` names:

    [[cache.service]]
    name = "shadow"
    type = "s3"
    artifactEndpoint = "https://<host>/cache/artifacts"
    revisionEndpoint = "https://<host>/cache/revisions"

A job that fetches writes the public read endpoints, as above. The upload job
writes the authenticated S3 endpoints, and `LAKE_CACHE_KEY` signs its requests.

## The revision

Every package uses the mathlib commit as its `--rev`, dependencies included. A
dependency's own revision leaves open which upstreams it was built against, and
a mathlib commit that bumps one dependency changes the correct mappings for
every dependency below it. The mathlib commit determines the whole set, through
its manifest.

Lake accepts this because `GitRepo.resolveRevision` returns a full SHA-1
unchanged, without looking it up, and `cache put-staged` loads no workspace and
resolves nothing. So a dependency's revision file lands under the mathlib
commit even though that commit belongs to another repository.

The revision reaches only the revision file's name. Artifacts are content
addressed under `artifacts/<SCOPE>/<DEP>/`, so a dependency whose content holds
steady overwrites its own artifacts instead of leaving a copy under every
commit.

## Push

Every run publishes every package. An export costs seconds once the artifacts
are in the local cache, and the run writes one revision file per package either
way. The pipeline therefore skips asking the bucket what it already holds.

1. `lake build <targets> -o .lake/outputs.jsonl` builds mathlib and every
   dependency, writes the artifacts into the local Lake cache, and records
   mathlib's own mappings. Lake tracks every target the build covers, whether
   it compiled that target or replayed it.
2. `lake build @<DEP> --package=<DEP> -o .lake/dep-outputs/<DEP>.jsonl`, once
   per dependency. `-o` records the mappings of the workspace root, and
   `--package` points it at a dependency instead, so the export runs in
   mathlib's own workspace and replays what step 1 produced. `@<DEP>` names the
   default targets of the dependency, which reach the modules mathlib leaves
   unimported.
3. `lake cache stage`, once per package, each into its own directory, because
   `cache stage` writes one `outputs.jsonl` per directory. The tree travels to
   the `upload` job as a GitHub artifact, because the build runs in a sandbox
   without the credentials.
4. `lake cache put-staged`, once per package, all with
   `--rev=<mathlib-sha>`. mathlib passes `--scope=<SCOPE>` and each dependency
   `--scope=<SCOPE>/<DEP>`. Lake PUTs the artifacts first and the revision file
   last.

A run whose staging tree exceeds 2 GB fails before the upload. The cap protects
the R2 free tier and the lifecycle budget.

## Pull

The `consume` job builds mathlib from the bucket alone. It sets
`LAKE_NO_CACHE`, so the bucket accounts for every replay.

1. `lake cache get --scope=<SCOPE> --rev=<mathlib-sha>`.
2. `lake cache get --package=<DEP> --scope=<SCOPE>/<DEP> --rev=<mathlib-sha>`,
   once per dependency.
3. `lake build <targets>` replays both.

The `downstream` job runs the same sequence for a small project that requires
mathlib. It holds mathlib's sha and its own manifest, and derives no scope or
qualifier of its own.

Every fetch passes `--rev`, so each one is a single exact request. A fetch
without `--rev` backtracks up to `--max-revs` commits, 100 by default, and
finds nothing here: a revision endpoint holds exactly one revision per
package.

## Storage layout

One bucket holds these keys:

    revisions/mathlib4-master-shadow/<mathlib-sha>.jsonl
    revisions/mathlib4-master-shadow/<DEP>/<mathlib-sha>.jsonl
    artifacts/mathlib4-master-shadow/<content-hash>.art
    artifacts/mathlib4-master-shadow/<DEP>/<content-hash>.art
    analysis/<toolchain-slug>/_latest.txt
    analysis/<toolchain-slug>/<mathlib-sha>.txt

`lake cache get --scope=<SCOPE> --rev=<REV>` reads
`<revisionEndpoint>/<SCOPE>/<REV>.jsonl`, which maps input hashes to artifacts,
and downloads the `<artifactEndpoint>/<SCOPE>/<content-hash>.art` files it
names. The workflow owns the `analysis/` prefix; Lake owns the other two.
`_latest.txt` holds the sha the next run warm starts from, and
`<mathlib-sha>.txt` holds its carryover baseline.

The revision keys carry the mathlib sha and the artifact keys leave it out. An
old commit therefore stays replayable for as long as its revision files live,
and the artifacts stay shared. Each commit owns one revision file per package,
so a lifecycle rule can evict a commit by age. A lifecycle rule can
expire an artifact by age instead: Lake re-uploads every artifact a run uses, so an object that
stops being written is an object no recent run references.

A toolchain bump is itself a mathlib commit, so it writes new revision keys and
leaves the previous toolchain's set in place. Its artifacts differ in content,
and therefore in key, and both generations coexist.

## The scope

Lake requires `--scope` or `--repo` on every put and get against a custom
endpoint. A pinned run passes `mathlib4-master-shadow` for mathlib and
`mathlib4-master-shadow/<DEP>` for a dependency, which Lake uses verbatim. The
prefix keeps this pipeline's artifacts apart from the rest of the bucket. The
package segment gives each package its own artifact namespace, which bounds
where a content hash is trusted.

An override run appends its toolchain slug, so it writes to
`mathlib4-master-shadow/<toolchain-slug>` and
`mathlib4-master-shadow/<toolchain-slug>/<DEP>`. An override run builds one
commit on a second toolchain, so the slug keeps the two lanes from writing each
other's revision files. It costs the override run nothing: the analysis chain
is already per toolchain, so an override run only ever warm starts from its own
lineage. "Toolchain override" below describes what a shared scope would do.

The scope carries no other qualifier. It needs no pin hash, because the
revision endpoint already names the commit that pins the whole set. A pinned
run needs no toolchain segment, because mathlib declares `fixedToolchain`, so
one commit means one build.

The scope is a plain string, not `--repo=<owner>/<name>`. A repo scope takes
exactly one `/`, which leaves no room for the pipeline's prefix, and Lake
appends the toolchain and the platform to it. `put-staged` loads no workspace,
so it cannot apply the `fixedToolchain` and `platformIndependent` nullification
that the consumer applies. Every job runs on Linux, so the scope carries no
platform segment.

## Hydration

Three optimizations decide how much a run compiles. None of them changes the
keys or the content that a run writes.

- The warm start. `lake cache get --service=shadow --scope=<SCOPE>
  --rev=<previous-sha>` seeds the local cache from the previous run on this
  toolchain, so the build compiles the churn since that run only.
  `analysis/<toolchain-slug>/_latest.txt` holds the previous sha.
- The dependency warm start, the same fetch per dependency with the previous
  sha. A dependency that this run bumps is absent from that set and misses at
  once, because the lookup is exact.
- The legacy cache, a bootstrap fallback. A run uses it only when the analysis
  chain holds no previous run, which is the first run on a toolchain. The legacy cache is keyed to the repo pin, so only a pinned run
  uses it.

## What a full cache hit requires

Three things are necessary. Without any one of them a fetch returns mappings
that do not match, and the modules rebuild.

- `LAKE_ARTIFACT_CACHE=true`, which lets the workspace write to Lake's artifact
  cache. mathlib leaves `enableArtifactCache` unset in its lakefile, and Lake
  reads the environment before the lakefile, so the pipeline sets the variable
  and leaves the checkout untouched. Every package in the workspace inherits
  it, dependencies included.
- The export of each dependency, with `--package`.
- The mathlib commit as the revision for every package, which pairs a
  dependency with the upstreams it was built against.

## Toolchain override

The `toolchain_override` input, or the `LAKE_SHADOW_TOOLCHAIN_OVERRIDE`
variable, changes the toolchain of the whole pipeline. `build_and_stage`
resolves it into its `toolchain` output, and the later jobs stamp that output
into their checkouts, so every job runs the same lake.

The lean of the override must behave like the repo pin. A Lake change,
cherry-picked onto the lineage of the pinned release as a pr-release, is a
valid example.

The analysis chain is per toolchain, under `analysis/<slug>/`. A pinned run and
an override run therefore warm start from their own lineage, and compare
against it. The first override run on a toolchain has no lineage to start
from, and costs one full source build of mathlib and its dependencies. A republished
pr-release tag costs the same.

The override is the one case that breaks "a commit determines its toolchain",
which is why its scope carries the slug. Two lanes that shared a scope would
write one commit's keys twice, and the later run would win. The other lineage's
next warm start would then fetch mappings that match nothing and build mathlib
from source. That build can exceed the job timeout, and the analysis pointer
only advances after a successful upload, so the lineage would keep reading the
same commit and keep failing. To compare two toolchains, dispatch both lanes
with the same explicit `mathlib_ref`.

## Dependency skip list

`DEP_SKIP` excludes dependencies from caching, separated by spaces. It is
empty: the pipeline caches all of them, proofwidgets included. proofwidgets
commits its npm output and the Lake traces that guard the npm steps, so a build
at a pinned revision skips npm entirely.

The warm start, the export, the upload and the fetch tolerate a per-dependency
failure. A miss, or a failed export, makes
that dependency build from source, and the consume health line reports it. A
toolchain older than v4.35.0-rc1 has no `build --package` and behaves the same
way. A dependency that sets `enableArtifactCache := false` in its own lakefile
overrides the environment: it exports mappings whose artifacts are absent from
the cache, which fails `lake cache stage`. Put such a dependency on the skip
list.

## Required repository configuration

Secrets:

- `LAKE_CACHE_KEY` — SigV4 credential for the cache bucket, as
  `<ACCESS_KEY_ID>:<SECRET_ACCESS_KEY>` (curl `--user`; region is `auto`).
- `ZULIP_API_KEY` — Zulip bot key for the `report` job.

Variables:

- `LAKE_CACHE_ARTIFACT_ENDPOINT` and `LAKE_CACHE_REVISION_ENDPOINT` — the
  authenticated S3 endpoints. The `upload` job PUTs to them. For example
  `https://<acct>.r2.cloudflarestorage.com/<bucket>/<prefix>/artifacts`.
- `LAKE_CACHE_ARTIFACT_ENDPOINT_PUBLIC` and
  `LAKE_CACHE_REVISION_ENDPOINT_PUBLIC` — the public read endpoints, for
  anonymous GETs. On R2 these use a different host than the S3 API endpoints.
  For example `https://pub-<hash>.r2.dev/<prefix>/artifacts`.
- `MATHLIB_CACHE_BASE_URL` — optional. The legacy cache reads it during the
  bootstrap fallback.
- `LAKE_SHADOW_TOOLCHAIN_OVERRIDE` — optional. It sets the toolchain override
  for every run. The dispatch input takes precedence. Leave it unset to run on
  the repo pin.
