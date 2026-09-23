# Lake cache shadow pipeline

`lake_cache_shadow.yml` exercises Lake's built-in artifact cache against the
live mathlib4 master branch. It runs beside the regular master CI and stays
independent of it, in a bucket that only this pipeline reads.

The pipeline caches mathlib and every git dependency in its manifest. Each
package has its own revision file, under the key that `lake cache get` derives
for it:

    revisions/<SCOPE>/<mathlib-sha>.jsonl
    revisions/<RESERVOIR>/pt/<platform>/tc/<toolchain>/<dep-rev>.jsonl

`<SCOPE>` is `mathlib4-master-shadow`. `<RESERVOIR>` is the dependency's
Reservoir identity, `<scope>/<name>` from the manifest, such as
`leanprover-community/batteries`. `<dep-rev>` is the dependency's own
revision, as mathlib's manifest pins it. A dispatched run can set `cache_deps`
to false, which leaves the dependencies out of that run's mappings.

## Jobs

- `build_and_stage` builds mathlib and its dependencies, and stages the
  mappings of each package.
- `upload` pushes the staged files to the bucket. It records a manifest under
  `analysis/<toolchain-slug>/` and reports the carryover.
- `consume` fetches every package into a fresh checkout, builds against them,
  and verifies the result with `--rehash`.
- `downstream` builds a small project that requires mathlib, and passes no
  revision to any fetch. It runs when the targets are `Mathlib` and the run
  caches dependencies.
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

## The key of a package

mathlib is the workspace root. It passes `--scope=<SCOPE>` and its own commit
as the revision. A dependency passes `--repo=<RESERVOIR>` and its own
revision. With a `--repo` scope, Lake adds the toolchain and the platform to
the revision path, and leaves the artifact path unqualified. The toolchain is
the one elan runs. The platform is `System.Platform.target`, and Lake leaves it
out for a package that declares `platformIndependent`. This is the key tuple
Reservoir uses, laid out on an S3 service.

A consumer therefore supplies no revision for a dependency. Lake reads it from
the dependency's checkout and walks back through its history, up to
`--max-revs` commits, to the nearest revision the bucket holds.

A dependency's revision does not fix its upstreams. aesop at one revision,
built under two mathlib commits that pin different batteries revisions,
produces two sets of mappings under one key, and the later upload replaces the
earlier one. Lake looks an entry up by its input hash, so a mapping for other
upstreams misses and the module rebuilds. It never replays a wrong output.

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
4. `lake cache put-staged`, once per package. mathlib passes
   `--scope=<SCOPE> --rev=<mathlib-sha>`. Each dependency passes
   `--repo=<RESERVOIR> --rev=<dep-rev> --toolchain=<toolchain>`, and
   `--platform=<platform>` unless it is platform independent. `put-staged`
   loads no workspace, so the build job records each dependency's platform
   setting with `lake reservoir-config`, which loads that one package. Lake
   PUTs the artifacts first and the revision file last.

A run whose staging tree exceeds 2 GB fails before the upload. The cap protects
the R2 free tier and the lifecycle budget.

## Pull

The `consume` job builds mathlib from the bucket alone. It sets
`LAKE_NO_CACHE`, so the bucket accounts for every replay.

1. `lake cache get --scope=<SCOPE> --rev=<mathlib-sha>`.
2. `lake cache get --package=<DEP> --repo=<RESERVOIR> --rev=<dep-rev>`, once per
   dependency.
3. `lake build <targets>` replays both.

`consume` passes each revision, so every fetch is one exact request and the job
tests what this run uploaded. The `downstream` job runs the same sequence for a
small project that requires mathlib, without `--rev`, as a real downstream
project would.

## Storage layout

One bucket holds these keys:

    revisions/<SCOPE>/<mathlib-sha>.jsonl
    revisions/<RESERVOIR>/pt/<platform>/tc/<toolchain>/<dep-rev>.jsonl
    artifacts/<SCOPE>/<content-hash>.art
    artifacts/<RESERVOIR>/<content-hash>.art
    analysis/<toolchain-slug>/_latest.txt
    analysis/<toolchain-slug>/<mathlib-sha>.txt

A revision file maps input hashes to artifacts, and `lake cache get` downloads
the artifacts it names from the same scope. The workflow owns the `analysis/`
prefix; Lake owns the other two. `_latest.txt` holds the sha the next run warm
starts from, and `<mathlib-sha>.txt` holds its carryover baseline.

The revision keys carry a revision and the artifact keys leave it out, so the
artifacts stay shared across revisions. A mathlib commit stays replayable for
as long as its revision files live. A dependency's revision file serves every
mathlib commit that pins that revision on that toolchain. A lifecycle rule can
evict a dependency's toolchain by deleting its `tc/<toolchain>/` prefix. A
lifecycle rule can expire an artifact by age: Lake re-uploads every artifact a
run uses, so an object that stops being written is an object no recent run
references.

## The scope

Lake requires `--scope` or `--repo` on every put and get against a custom
endpoint. mathlib's `<SCOPE>` is a plain string, which Lake uses verbatim.
mathlib declares `fixedToolchain`, so Lake adds no toolchain to its key, and
one commit means one build on the repo pin.

An override run appends its toolchain slug to mathlib's scope, so it writes to
`mathlib4-master-shadow/<toolchain-slug>`. An override run builds one commit on
a second toolchain, so the slug keeps the two lanes from writing each other's
revision files. It costs the override run nothing: the analysis chain is
already per toolchain, so an override run only ever warm starts from its own
lineage. A dependency needs no slug, because its key carries the toolchain.
"Toolchain override" below describes what a shared scope would do.

## Hydration

Two fetches decide how much a run compiles. Neither changes the keys or the
content that a run writes.

- The warm start. `lake cache get --service=shadow --scope=<SCOPE>
  --rev=<previous-sha>` seeds the local cache from the previous run on this
  toolchain, so the build compiles the churn since that run only.
  `analysis/<toolchain-slug>/_latest.txt` holds the previous sha.
- The dependency warm start, `lake cache get --package=<DEP>
  --repo=<RESERVOIR>` without `--rev`. A dependency that this run bumps starts
  from the nearest earlier revision the bucket holds.

The first run on a toolchain has no pointer to start from, and builds mathlib
and every dependency from source.

## What a full cache hit requires

Three things are necessary. Without any one of them a fetch returns mappings
that do not match, and the modules rebuild.

- `LAKE_ARTIFACT_CACHE=true`, which lets the workspace write to Lake's artifact
  cache. mathlib leaves `enableArtifactCache` unset in its lakefile, and Lake
  reads the environment before the lakefile, so the pipeline sets the variable
  and leaves the checkout untouched. Every package in the workspace inherits
  it, dependencies included.
- The export of each dependency, with `--package`.
- The same toolchain and platform strings on both sides of a dependency's key.
  The upload passes the resolved `lean-toolchain` and the platform the build
  job recorded; `lake cache get` derives them from elan and the host.

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
against it. A republished pr-release tag reads as a new toolchain, and costs
the same full source build as any first run.

The override is the one case that breaks "a commit determines its toolchain",
which is why mathlib's scope carries the slug. Two lanes that shared a scope would
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
way. A dependency without a scope in the manifest has no Reservoir identity,
and the pipeline does not cache it. A dependency that declares
`fixedToolchain` has no toolchain in the key `lake cache get` derives, and
misses the key the upload writes. A dependency that sets `enableArtifactCache := false` in its own lakefile
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
- `LAKE_SHADOW_TOOLCHAIN_OVERRIDE` — optional. It sets the toolchain override
  for every run. The dispatch input takes precedence. Leave it unset to run on
  the repo pin.
