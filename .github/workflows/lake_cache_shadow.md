# Lake cache shadow pipeline

`lake_cache_shadow.yml` exercises Lake's built-in artifact cache against the
live mathlib4 master branch. It runs beside the regular master CI and stays
independent of it. It writes to the isolated `mathlib4-master-shadow` scope,
which only this pipeline reads.

The pipeline caches mathlib and every git dependency in its manifest. mathlib
goes to `revisions/<SCOPE>/<mathlib-sha>.jsonl`, and each dependency goes under
that same commit, at
`revisions/by-sha/<mathlib-sha>/<SCOPE>/<DEP>/<R-DEP>.jsonl`. `<DEP>` is the
dependency, `<R-DEP>` is its revision from the manifest, and `<SCOPE>` is
`mathlib4-master-shadow`. One mathlib commit therefore names one complete set
of packages.

## Jobs

- `build_and_stage` builds mathlib and its dependencies, and stages the
  mappings of each package.
- `upload` pushes the staged files to the bucket. It records a manifest under
  `analysis/<toolchain-slug>/` and reports the carryover.
- `consume` fetches every package into a fresh checkout, builds against them,
  and verifies the result with `--rehash`.
- `downstream` builds a small project that requires mathlib, from mathlib's sha
  alone.
- `report` posts a summary of the run to Zulip.

## Cache service configuration

Each job runs on its own runner and writes its own service definitions, into
the file `LAKE_CONFIG` names. The two services share an artifact endpoint and
differ in where they look for a revision file:

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
`build_and_stage` writes a third service, `shadow-deps-prev`, which points at
the previous run's commit and serves its dependency warm start.

The split makes the dependency keys exact. A dependency's revision leaves open
which upstreams it was built against, and a mathlib commit that bumps one
dependency changes the correct mappings for every dependency below it. The
mathlib commit determines the whole set, through its manifest, so it qualifies
the revision endpoint. It leaves the artifact endpoint alone, so a dependency
whose content holds steady overwrites its own artifacts instead of leaving a
copy under every commit.

## Push

Every run publishes every package. An export costs seconds once the artifacts
are in the local cache, and the run writes one revision file per package either
way. The pipeline therefore skips asking the bucket what it already holds.

1. `lake build Mathlib -o .lake/outputs.jsonl` builds mathlib and every
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

Every fetch passes `--rev`, so each one is a single exact request. Without
`--rev`, Lake lists the package's own HEAD and up to `--max-revs` ancestors,
default 100, then probes them in order until one has a published map. That walk
finds nothing here: one mathlib commit pins one revision of each dependency, so
its revision endpoint holds exactly one revision per package.

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
names. The workflow owns the `analysis/` prefix; Lake reads the other two.
`_latest.txt` holds the sha the next run warm starts from, and
`<mathlib-sha>.txt` holds its carryover baseline.

The revision keys carry the mathlib sha and the artifact keys leave it out. An
old commit therefore stays replayable for as long as its revision files live,
and the artifacts stay shared. `revisions/by-sha/<mathlib-sha>/` is one prefix
per commit, so a lifecycle rule can evict a commit as a unit. An artifact expires
by age instead: Lake re-uploads every artifact a run uses, so an object that
stops being written is an object no recent run references.

A toolchain bump is itself a mathlib commit, so it writes new revision keys and
leaves the previous toolchain's set in place. Its artifacts differ in content,
and therefore in key, and both generations coexist.

## The scope

Lake requires `--scope` or `--repo` on every put and get against a custom
endpoint. The pipeline passes `mathlib4-master-shadow` for mathlib and
`mathlib4-master-shadow/<DEP>` for a dependency, which Lake uses verbatim. The
prefix keeps this pipeline's artifacts apart from the rest of the bucket. The
package segment gives each package its own artifact namespace, which bounds
where a content hash is trusted.

The scope carries no other qualifier. It needs no pin hash, because the
revision endpoint already names the commit that pins the whole set. It needs no
toolchain segment, because mathlib declares `fixedToolchain`, so one commit
means one build.

`--repo=<owner>/<name>` would make Lake append the toolchain and the platform
itself. A repo scope takes exactly one `/`, which leaves no room for the
pipeline's prefix. `put-staged` also loads no workspace, so it could not apply
the `fixedToolchain` and `platformIndependent` nullification that the consumer
applies, and the two sides could disagree on the path. Every job runs on Linux,
so the scope carries no platform segment.

## Hydration

Three optimizations decide how much a run compiles. None of them changes the
keys or the content that a run writes.

- The warm start. `lake cache get --service=shadow --scope=<SCOPE>
  --rev=<previous-sha>` seeds the local cache from the previous run on this
  toolchain, so the build compiles the churn since that run only.
  `analysis/<toolchain-slug>/_latest.txt` holds the previous sha.
- The dependency warm start, `--service=shadow-deps-prev` per dependency, which
  reads the previous run's published set. A dependency that this run bumps is
  absent from that set and misses at once, because the lookup is exact.
- The legacy cache, a bootstrap fallback. A run uses it only when the analysis
  chain holds no previous run, which happens on a fresh toolchain generation of
  the repo pin. The legacy cache is keyed to the repo pin, so only a pinned run
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
- The `by-sha` revision endpoint, which pairs a dependency's revision with the
  upstreams it was built against.

Everything under "Hydration" is speed. A run without those parts writes the
same keys with the same content, and takes longer.

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
against it. The first run on a toolchain has no lineage to start from, and
costs one full source build of mathlib and its dependencies. A republished
pr-release tag costs the same.

The override is also the one case that breaks "a commit determines its
toolchain". It runs one commit on a second toolchain, and both runs write that
commit's keys. The later run wins, and the other lineage's next warm start
fetches mappings that match nothing and rebuilds from source. Master moves
between runs, so two lineages rarely land on one commit, but an override run
given an explicit `mathlib_ref` can. A toolchain segment on the scope fixes
this and orphans everything already in the bucket, so it belongs in a change of
its own.

## Dependency skip list

`DEP_SKIP` excludes dependencies from caching, separated by spaces. It is
empty: the pipeline caches all of them, proofwidgets included. proofwidgets
commits its npm output and the Lake traces that guard the npm steps, so a build
at a pinned revision skips npm entirely.

Every per-dependency step tolerates failure. A miss, or a failed export, makes
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
- `LAKE_SHADOW_TOOLCHAIN_OVERRIDE` — optional. It sets the toolchain override
  for every run. The dispatch input takes precedence. Leave it unset to run on
  the repo pin.
