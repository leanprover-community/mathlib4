# Lake cache shadow pipeline

`lake_cache_shadow.yml` exercises Lake's built-in artifact cache against the
live mathlib4 master branch. It runs beside the regular master CI and stays
independent of it. It writes to an isolated `mathlib4-master-shadow` scope, so
no other consumer reads what it produces.

The pipeline caches mathlib and every git dependency in its manifest. mathlib
goes to `revisions/<SCOPE>/<mathlib-sha>.jsonl`, and the dependencies go under
that same commit, at `revisions/by-sha/<mathlib-sha>/<SCOPE>/<DEP>/<R-DEP>.jsonl`,
where `<DEP>` is the dependency, `<R-DEP>` is its revision from the manifest and
`<SCOPE>` is `mathlib4-master-shadow`. A mathlib commit therefore names one
complete, self-consistent set of packages.

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

Each job writes its own service definitions, into the file `LAKE_CONFIG` names,
because each job runs on its own runner. There are two, and they differ only in
where they look for a revision file:

    [[cache.service]]
    name = "shadow"
    type = "s3"
    artifactEndpoint = "https://<host>/cache/artifacts"
    revisionEndpoint = "https://<host>/cache/revisions"

    [[cache.service]]
    name = "shadow-deps"
    type = "s3"
    artifactEndpoint = "https://<host>/cache/artifacts"
    revisionEndpoint = "https://<host>/cache/revisions/by-sha/<mathlib-sha>"

A job that fetches writes the public read endpoints, as above. The upload job
writes the authenticated S3 endpoints, and `LAKE_CACHE_KEY` signs its requests.

The two endpoints are what make the dependency keys exact. A dependency's
revision does not say which upstreams it was built against, and a run of
mathlib that bumps one dependency changes the correct mappings for every
dependency downstream of it. The mathlib commit does determine the whole set,
through its manifest, so it qualifies the revision endpoint. It does not
qualify the artifact endpoint, so a dependency whose content did not change
overwrites its own artifacts instead of leaving a copy under every commit.

`build_and_stage` also writes a `shadow-deps-prev` service, pointing at the
previous run's commit, which is what its dependency warm start reads.

## Push

Every run publishes every package. A dependency costs seconds to export once
its artifacts are in the local cache, and the run writes one revision file per
package either way, so the pipeline does not ask the bucket what it already
holds.

1. `lake build Mathlib -o .lake/outputs.jsonl` builds mathlib and every
   dependency, writes the artifacts into the local Lake cache, and records
   mathlib's own mappings. Lake tracks every target the build covers, whether
   it compiled it or replayed it.
2. `lake build @<DEP> --package=<DEP> -o .lake/dep-outputs/<DEP>.jsonl`, once
   per dependency. `-o` records the mappings of the workspace root, and
   `--package` points it at a dependency instead, so the export runs in
   mathlib's own workspace and replays what step 1 produced. `@<DEP>` names
   the default targets of the dependency, which reach the modules mathlib
   does not import.
3. `lake cache stage`, once per package, each into its own directory, because
   `cache stage` writes one `outputs.jsonl` per directory. The tree travels to
   the `upload` job as a GitHub artifact, because the build runs in a sandbox
   without the credentials.
4. `lake cache put-staged`, once per package. mathlib goes to
   `--service=shadow --scope=<SCOPE> --rev=<mathlib-sha>`, and each dependency
   to `--service=shadow-deps --scope=<SCOPE>/<DEP> --rev=<R-DEP>`. Lake PUTs
   the artifacts first and the revision file last.

## Pull

The `consume` job builds mathlib from the bucket alone. It sets
`LAKE_NO_CACHE`, so the bucket accounts for every replay.

1. `lake cache get --service=shadow --scope=<SCOPE> --rev=<mathlib-sha>`.
2. `lake cache get --service=shadow-deps --package=<DEP> --scope=<SCOPE>/<DEP>
   --rev=<R-DEP>`, once per dependency, with the revisions from mathlib's
   manifest.
3. `lake build Mathlib` replays both.

The `downstream` job runs the same sequence for a small project that requires
mathlib. It holds mathlib's sha and its own manifest, and derives no scope or
qualifier of its own.

Every fetch passes `--rev`, so each is one exact request. Without `--rev` Lake
lists the package's own HEAD and up to `--max-revs` ancestors, default 100, and
probes them in order until one has a published map. That walk cannot help here:
one mathlib commit pins one revision of each dependency, so its revision
endpoint holds exactly one revision per package and the other 99 requests would
find nothing.

## What a warm run adds

Three optimizations decide how much a run compiles. None of them changes the
keys or the content that a run writes.

- The warm start. `lake cache get --service=shadow --scope=<SCOPE>
  --rev=<previous-sha>` seeds the local cache from the previous run on this
  toolchain, so step 1 compiles the churn since that run only.
  `analysis/<toolchain-slug>/_latest.txt` holds the previous sha.
- The dependency warm start, `--service=shadow-deps-prev` for each dependency,
  which reads the previous run's published set. A dependency this run bumps is
  not in it and misses at once, because the lookup is exact.
- The legacy cache, for a cold analysis chain only, where no previous run
  exists to warm start from.

## Storage layout

One bucket holds these keys:

    revisions/mathlib4-master-shadow/<mathlib-sha>.jsonl
    revisions/by-sha/<mathlib-sha>/mathlib4-master-shadow/<DEP>/<R-DEP>.jsonl
    artifacts/mathlib4-master-shadow/<content-hash>.art
    artifacts/mathlib4-master-shadow/<DEP>/<content-hash>.art
    analysis/<toolchain-slug>/_latest.txt
    analysis/<toolchain-slug>/<mathlib-sha>.txt

`lake cache get --scope=<SCOPE> --rev=<REV>` reads
`<revisionEndpoint>/<SCOPE>/<REV>.jsonl`, which maps input hashes to artifacts,
and downloads the `<artifactEndpoint>/<SCOPE>/<content-hash>.art` files it
names. Lake does not know the `analysis/` prefix; the workflow owns it.
`_latest.txt` holds the sha the next run warm starts from, and
`<mathlib-sha>.txt` holds its carryover baseline.

The revision keys carry the mathlib sha and the artifact keys do not, so an old
commit stays replayable for as long as its revision files live, while the
artifacts stay shared. A toolchain bump is itself a mathlib commit, so it writes
new revision keys and leaves the previous toolchain's set in place; its
artifacts differ in content and therefore in key, and both coexist.

## The scope

Lake requires `--scope` or `--repo` on every put and get against a custom
endpoint; there is no unscoped form. The pipeline passes
`mathlib4-master-shadow` for mathlib and `mathlib4-master-shadow/<DEP>` for a
dependency, which Lake uses verbatim. The prefix keeps this experiment apart
from the rest of the bucket, and the package segment gives each package its own
artifact namespace, which is where a content hash is trusted.

The scope carries no other qualifier. It needs no pin hash, because the
revision endpoint already names the commit that pins the whole set. It needs no
toolchain segment, because mathlib declares `fixedToolchain` and one commit
therefore means one build.

`--repo=<owner>/<name>` would make Lake append the toolchain and the platform
itself, but a repo scope takes exactly one `/` and has no room for the
experiment prefix; `put-staged` also loads no workspace, so it could not apply
the same `fixedToolchain` and `platformIndependent` nullification the consumer
applies, and the two sides could disagree on the path. Every job runs on Linux,
so the scope carries no platform segment.

The `toolchain_override` input is the one case that breaks "a commit determines
its toolchain": it runs one commit on a second toolchain, and both runs write
that commit's keys. The later run wins, and the other lineage's next warm start
fetches mappings that match nothing and rebuilds from source. Master moves
between runs, so two lineages rarely land on one commit, but an override run
given an explicit `mathlib_ref` can. Adding a toolchain segment fixes it and
orphans everything already in the bucket, so it wants its own change.

## What a full cache hit requires

Three things are necessary. Without any one of them a fetch returns mappings
that do not match, and the modules rebuild.

- `LAKE_ARTIFACT_CACHE=true`, which lets the workspace write to Lake's
  artifact cache at all. mathlib does not set `enableArtifactCache` in its
  lakefile, and Lake reads the environment before the lakefile, so the
  pipeline sets the variable and leaves the checkout untouched. Every package
  in the workspace inherits it, dependencies included.
- The export of each dependency, with `--package`.
- The `by-sha` revision endpoint, which is what pairs a dependency's revision
  with the upstreams it was built against.

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
overrides the environment, so it would export mappings whose artifacts are not
in the cache, which fails `lake cache stage`; put it on the skip list.

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
