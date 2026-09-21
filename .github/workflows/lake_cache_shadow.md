# Lake cache shadow pipeline

`lake_cache_shadow.yml` exercises Lake's built-in artifact cache against the
live mathlib4 master branch. It runs beside the regular master CI and stays
independent of it. It writes to an isolated `mathlib4-master-shadow` scope, so
no other consumer reads what it produces.

The pipeline caches mathlib and every git dependency in its manifest as one
unit. A run publishes a single revision file per mathlib commit, holding the
whole cone of artifacts that commit builds, and a consumer replays all of it
from that one file. `<DEP>` below is one dependency, and every put and get uses
one scope, `mathlib4-master-shadow`.

## Jobs

- `build_and_stage` builds mathlib and its dependencies with Lake's artifact
  cache, and stages one merged mappings file covering every package.
- `upload` pushes the staged files to the bucket with one `put-staged`. It
  records a manifest under `analysis/<toolchain-slug>/` and reports the
  carryover.
- `consume` fetches that file into a fresh checkout, registers it against each
  dependency, builds against it, and verifies the result with `--rehash`.
- `downstream` creates a small project that depends on mathlib and replays the
  same file, holding nothing but mathlib's sha.
- `report` posts a summary of the run to Zulip.

## Cache service configuration

Every `lake cache` call passes `--service=shadow`. Each job writes that service
definition itself, into the file `LAKE_CONFIG` names, because each job runs on
its own runner:

    [[cache.service]]
    name = "shadow"
    type = "s3"
    artifactEndpoint = "https://pub-<hash>.r2.dev/<prefix>/artifacts"
    revisionEndpoint = "https://pub-<hash>.r2.dev/<prefix>/revisions"

A job that fetches writes the public read endpoints, as above. The upload job
writes the authenticated S3 endpoints, and `LAKE_CACHE_KEY` signs its requests.
A services file is the supported way to configure a cache service, and Lake
deprecates the endpoint environment variables.

## Push

Every run publishes every package. A dependency costs seconds to export once
its artifacts are in the local cache, and the run writes one revision file
either way, so the pipeline does not ask the bucket what it already holds.

1. `lake build Mathlib -o .lake/dep-outputs/mathlib.jsonl` builds mathlib and
   every dependency, writes the artifacts into the local Lake cache, and
   records mathlib's own mappings. Lake tracks every target the build covers,
   whether it compiled it or replayed it.
2. `lake build @<DEP> --package=<DEP> -o .lake/dep-outputs/<DEP>.jsonl`, once
   per dependency. `-o` records the mappings of the workspace root, and
   `--package` points it at a dependency instead, so the export runs in
   mathlib's own workspace and replays what step 1 produced. `@<DEP>` names
   the default targets of the dependency, which reach the modules mathlib
   does not import.
3. Merge. Lake builds the map in pieces and offers no way to combine them:
   `-o` writes exactly one package's mappings, and `cache stage` copies one
   mappings file over the staging directory's `outputs.jsonl`, so staging
   twice accumulates the artifacts but keeps only the second map. The
   workflow merges on the file format instead: a mappings file is a schema
   version line followed by one flat input-hash-keyed entry per target, with
   no per-package partition, so keeping one header and concatenating the
   entries yields a valid map. Lake skips a repeated schema line with a
   warning and takes the last of a repeated entry, so this is about not
   shipping a file that warns on every load, not about correctness. It is
   the one place the pipeline reads the mappings format. A `-o` that covered
   the whole workspace, or a `cache stage` that took several mappings files,
   would remove the need for it.
4. `lake cache stage .lake/outputs.jsonl lake-cache-staging` copies the map and
   every artifact it names into one flat directory. The tree travels to the
   `upload` job as a GitHub artifact, because the build runs in a sandbox
   without the credentials.
5. `lake cache put-staged lake-cache-staging --service=shadow --scope=<SCOPE>
   --rev=<mathlib-sha>`. Lake PUTs the artifacts first and the revision file
   last, so a reader never sees a map whose artifacts are missing.

## Pull

The `consume` job builds mathlib from the bucket alone. It sets
`LAKE_NO_CACHE`, so the bucket accounts for every replay.

1. `lake cache get --service=shadow --scope=<SCOPE> --rev=<mathlib-sha>`. The
   revision file maps every input hash in the workspace, so this one fetch
   downloads every artifact the replay needs, mathlib's and its dependencies'.
   Lake saves the file at
   `$LAKE_CACHE_DIR/revisions/mathlib/<mathlib-sha>.jsonl`.
2. `lake cache add <that file> --package=<DEP> --service=shadow
   --scope=<SCOPE>`, once per dependency. Lake resolves an input hash under
   the owning package's local scope, and step 1 registered the map under the
   root's only. This step is offline: the artifacts are already on disk.
   `--service` and `--scope` record where they came from, so one that goes
   missing is re-fetched rather than rebuilt.
3. `lake build Mathlib` replays the whole cone.

The `downstream` job runs the same two steps for a small project that requires
mathlib, with `--package=mathlib` on the fetch. It derives no scope of its own
beyond the toolchain slug, which it reads off its own `lean-toolchain`. A real
downstream project holds mathlib's sha and nothing else, and that is all the
bucket asks for.

## What a warm run adds

Three optimizations decide how much a run compiles. None of them changes the
keys or the content that a run writes.

- The warm start. `lake cache get --service=shadow --scope=<SCOPE>
  --rev=<previous-sha>` seeds the local cache from the previous run on this
  toolchain, so step 1 compiles the churn since that run only.
  `analysis/<toolchain-slug>/_latest.txt` holds the previous sha.
- The dependency half of the warm start. The fetch above already downloaded
  every dependency artifact, so this is a `lake cache add` per dependency
  against the previous run's file, which lets step 1 replay them instead of
  compiling them.
- The legacy cache, for a cold analysis chain only, where no previous run
  exists to warm start from.

The `--rev` arguments are an optimization too. Without them Lake searches back
through the ancestors of the checkout's HEAD.

## Storage layout

One bucket holds these keys:

    revisions/mathlib4-master-shadow/<mathlib-sha>.jsonl
    artifacts/mathlib4-master-shadow/<content-hash>.art
    analysis/<toolchain-slug>/_latest.txt
    analysis/<toolchain-slug>/<mathlib-sha>.txt

`lake cache get --scope=<SCOPE> --rev=<REV>` reads
`revisions/<SCOPE>/<REV>.jsonl`, which maps input hashes to artifacts, and
downloads the `artifacts/<SCOPE>/<content-hash>.art` files it names. Lake does
not know the `analysis/` prefix; the workflow owns it. `_latest.txt` holds the
sha the next run warm starts from, and `<mathlib-sha>.txt` holds its carryover
baseline.

One revision file per mathlib commit is the whole cone for that commit, so an
old commit stays replayable for as long as its file and artifacts live. The
artifacts are content-addressed under a constant scope, so a run that rebuilds
unchanged bytes overwrites them rather than adding a copy.

## The scope

Lake requires `--scope` or `--repo` on every put and get against a custom
endpoint; there is no unscoped form. The pipeline passes the one string
`mathlib4-master-shadow` to `--scope`, which Lake uses verbatim, to keep this
experiment's artifacts apart from the rest of the bucket.

`--repo=<owner>/<name>` would make Lake append the toolchain and the platform
itself, but a repo scope takes exactly one `/` and has no room for the
experiment prefix; `put-staged` also loads no workspace, so it could not apply
the same `fixedToolchain` and `platformIndependent` nullification the consumer
applies, and the two sides could disagree on the path. Every job runs on Linux,
so the scope carries no platform segment.

Nothing in the bucket is keyed by a dependency's own revision. A dependency is
reachable through the mathlib commit that pins it, which is what a consumer of
this cache has.

The scope carries no toolchain segment either, because mathlib declares
`fixedToolchain` and one commit therefore means one build. The
`toolchain_override` input breaks that declaration: it runs one commit on a
second toolchain, and both runs write `revisions/mathlib4-master-shadow/<that
commit>.jsonl`. The later run wins, and the other lineage's next warm start
fetches mappings that match nothing and rebuilds from source. Master moves
between runs, so two lineages rarely land on one commit, but an override run
given an explicit `mathlib_ref` can. Adding a toolchain segment to the scope
fixes it and orphans everything already in the bucket, so it wants its own
change.

## What a full cache hit requires

Three things are necessary. Without any one of them a fetch returns mappings
that do not match, and the modules rebuild.

- The lakefile patch, which lets the workspace write to Lake's artifact cache
  at all. mathlib does not set `enableArtifactCache` itself yet, so the
  pipeline injects it. Every dependency inherits the setting from the root.
- The export of each dependency, with `--package`.
- The `lake cache add` per dependency on the consumer, which is what makes the
  merged map resolvable under each package's own local scope.

Everything in "What a warm run adds" is speed. A run without those parts writes
the same keys with the same content, and takes longer.

## Hydration and the legacy cache

A pinned run hydrates from the shadow scope. The root package warm starts from
the previous run on the toolchain's analysis chain, and each dependency warm
starts from its own scope. The incremental build then compiles the churn since
that run.

The legacy cache is a bootstrap fallback. A run uses it only when the analysis
chain holds no previous run, which happens on a fresh toolchain generation on
the repo pin. An override run never uses it, because the legacy cache is keyed
to the repo pin.

## Toolchain override

The `toolchain_override` input, or the `LAKE_SHADOW_TOOLCHAIN_OVERRIDE`
variable, changes the toolchain of the whole pipeline. `build_and_stage`
resolves it into its `toolchain` output, and the later jobs stamp that output
into their checkouts, so every job runs the same lake.

The lean of the override must behave like the repo pin. A Lake change,
cherry-picked onto the lineage of the pinned release as a pr-release, is a
valid example. Input hashes cover the toolchain, so all runs share one artifact
scope safely.

The analysis chain is per toolchain, under `analysis/<slug>/`. A pinned run and
an override run therefore warm start from their own lineage, and compare
against it.

The first run on a toolchain misses the legacy cache and every prior root
artifact, and costs one full source build of the root package. A republished
pr-release tag costs the same. Dependencies already in the shadow scope for
that toolchain still replay.

## Dependency skip list

`DEP_SKIP` excludes dependencies from caching, separated by spaces. It is
empty: the pipeline caches all of them, proofwidgets included. proofwidgets
commits its npm output and the Lake traces that guard the npm steps, so a build
at a pinned revision never calls npm.

Every per-dependency step tolerates failure. A miss, or a failed export, makes
that dependency build from source, and the consume health line reports it. A
toolchain older than v4.35.0-rc1 has no `build --package` and behaves the same
way. A dependency that sets `enableArtifactCache := false` in its own lakefile
would export mappings whose artifacts are not in the cache, which fails
`lake cache stage`; put it on the skip list.

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
  anonymous GETs. On R2 these are a different host than the S3 API endpoints.
  For example `https://pub-<hash>.r2.dev/<prefix>/artifacts`.
- `LAKE_SHADOW_TOOLCHAIN_OVERRIDE` — optional. It sets the toolchain override
  for every run. The dispatch input takes precedence. Leave it unset to run on
  the repo pin.
