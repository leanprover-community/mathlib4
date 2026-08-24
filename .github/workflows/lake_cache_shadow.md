# Lake cache shadow pipeline

`lake_cache_shadow.yml` exercises Lake's built-in artifact cache against the
live mathlib4 master branch. It runs beside the regular master CI and stays
independent of it. It writes to an isolated `mathlib4-master-shadow` scope, so
no other consumer reads what it produces.

The pipeline caches the root package, mathlib, and every git dependency in
mathlib's manifest. In the examples below, `<DEP>` is one dependency, `<R-DEP>`
is its revision from the manifest, and `<S-DEP>` is its scope,
`mathlib4-master-shadow/deps/<toolchain-slug>/<pin-hash>/<DEP>`. A rendered
scope reads
`mathlib4-master-shadow/deps/leanprover-lean4-v4.34.0-rc2/2d10dd67/batteries`.

## Jobs

- `build_and_stage` builds mathlib and its dependencies with Lake's artifact
  cache. It stages the outputs of the root package, and the mappings of each
  dependency the bucket does not hold.
- `upload` pushes the staged files to the bucket, once for the root scope and
  then once per dependency scope. It records a manifest under
  `analysis/<toolchain-slug>/` and reports the carryover.
- `consume` fetches the root and dependency outputs into a fresh checkout,
  builds against them, and verifies the result with `--rehash`.
- `downstream` creates a small project that depends on mathlib, fetches
  mathlib and every transitive dependency from the bucket, and requires zero
  Mathlib rebuilds.
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

## Push, from a clean cache

Lake's `-o` records the mappings of the workspace root only, so step 3 loads
each dependency as its own root. Step 1 runs once, and steps 2 to 5 run once
per dependency.

1. `lake build Mathlib` builds mathlib and every dependency from source, and
   writes the artifacts into the local Lake cache.
2. Write `<DEP>-overrides.json`. A `jq` filter reads mathlib's
   `lake-manifest.json`, drops the entry for `<DEP>` itself, and rewrites each
   remaining package as a path entry into this checkout. It keeps the `name`,
   `scope`, `configFile` and `inherited` fields, sets `type` to `path`, and
   sets `dir` to `.lake/packages/<name>`. For aesop it renders:

       {"version": "1.2.0",
        "packages": [
          {"name": "batteries", "scope": "leanprover-community",
           "configFile": "lakefile.toml", "inherited": false, "type": "path",
           "dir": "<checkout>/.lake/packages/batteries"},
          ... one entry per other package ...
        ]}

   The file pins the dependencies of `<DEP>` to mathlib's. Without it Lake uses
   the manifest of `<DEP>`, and the mappings never match this workspace's input
   hashes.
3. Export: `lake -d .lake/packages/<DEP> build
   --packages=.lake/dep-plan/<DEP>-overrides.json -o
   .lake/dep-outputs/<DEP>.jsonl`. This load replays instead of compiling,
   because step 1 filled the local cache.
4. Stage: `lake cache stage .lake/dep-outputs/<DEP>.jsonl
   lake-cache-staging/deps/<DEP>`. Each dependency needs its own directory,
   because `cache stage` writes one `outputs.jsonl` per directory. The staging
   tree travels to the `upload` job as a GitHub artifact, because the build
   runs in a sandbox without the credentials.
5. Upload: `lake cache put-staged lake-cache-staging/deps/<DEP>
   --service=shadow --scope=<S-DEP> --rev=<R-DEP>`. Lake PUTs the artifacts
   first and the revision file last.

## Pull

The `consume` job builds mathlib from the bucket alone. It sets
`LAKE_NO_CACHE`, so the bucket accounts for every replay.

1. `lake cache get --service=shadow --scope=mathlib4-master-shadow
   --rev=<mathlib-sha>`.
2. `lake cache get --service=shadow --package=<DEP> --scope=<S-DEP>
   --rev=<R-DEP>`, once per dependency, with the revisions from mathlib's
   manifest.
3. `lake build Mathlib` replays both.

The `downstream` job runs the same pull for a small project that requires
mathlib. In that project mathlib is a dependency, so it comes from the root
scope under its sha. That job derives the scope qualifiers itself, because a
real downstream project has no access to mathlib's CI outputs.

## What a warm run adds

Four optimizations decide how much a run compiles and uploads. None of them
changes the keys or the content that a run writes.

- The probe. Before the build, `curl -fsS -o /dev/null
  "$REVISION_ENDPOINT/<S-DEP>/<R-DEP>.jsonl"` asks whether the bucket already
  holds this dependency. If it does, steps 2 to 5 skip it. A revision, a
  toolchain and a pin set determine the content, so a dependency uploads once.
  Later runs skip it, until a manifest bump or a toolchain bump changes the
  scope.
- The root warm start. `lake cache get --service=shadow
  --scope=mathlib4-master-shadow --rev=<previous-sha>` seeds the local cache
  from the previous run on this toolchain, so step 1 compiles the churn since
  that run only. `analysis/<toolchain-slug>/_latest.txt` holds the previous
  sha.
- The dependency warm start. `lake cache get --service=shadow --package=<DEP>
  --scope=<S-DEP> --rev=<R-DEP>` for each dependency the probe found, so step 1
  replays it instead of compiling it.
- The legacy cache, for a cold analysis chain only, where no previous run
  exists to warm start from.

The `--rev` arguments are an optimization too. Without them Lake searches back
through the ancestors of the checkout's HEAD.

## Storage layout

One bucket holds these keys:

    revisions/mathlib4-master-shadow/<mathlib-sha>.jsonl
    artifacts/mathlib4-master-shadow/<content-hash>.art
    revisions/<S-DEP>/<R-DEP>.jsonl
    artifacts/<S-DEP>/<content-hash>.art
    analysis/leanprover-lean4-v4.34.0-rc2/_latest.txt
    analysis/leanprover-lean4-v4.34.0-rc2/<mathlib-sha>.txt

`lake cache get --scope=<SCOPE> --rev=<REV>` reads
`revisions/<SCOPE>/<REV>.jsonl`, which maps input hashes to artifacts, and
downloads the `artifacts/<SCOPE>/<content-hash>.art` files it names. Lake does
not know the `analysis/` prefix; the workflow owns it. `_latest.txt` holds the
sha the next run warm starts from, and `<mathlib-sha>.txt` holds its carryover
baseline.

## Scope qualifiers

Lake requires `--scope` or `--repo` on every put and get against a custom
endpoint; there is no unscoped form. A scope also bounds where a content hash
is trusted, because Lake does not use cryptographically secure hashes and
prefixes uploads to avoid clashes. Each package therefore gets its own
namespace for its artifacts and its revision files, and the root scope stays
for mathlib alone. `--repo=<owner>/<package>` would give a scope of that shape,
and Lake would add the toolchain and the platform to it. It has no place for
the pin hash, so the pipeline passes the whole string to `--scope`, which Lake
uses verbatim.

Two qualifiers extend a dependency scope, because the revision alone is not
exact.

- The toolchain slug separates the toolchains that build one long-lived
  revision. It is the toolchain with each character outside `A-Za-z0-9._-`
  replaced by `-`.
- The pin hash separates the manifest generations. The input hashes of a
  dependency cover the artifacts of its upstreams, so a bump of batteries alone
  changes the correct mappings for aesop but not the revision of aesop. The
  hash is 8 hex characters over the sorted `<name> <rev>` git entries of
  mathlib's manifest.

`build_and_stage` derives both and publishes them as job outputs. The `upload`
and `consume` jobs read them from there.

## What a full cache hit requires

Four things are necessary. Without any one of them a fetch returns mappings
that do not match, and the modules rebuild.

- The lakefile patch, which lets the workspace write to Lake's artifact cache
  at all. mathlib does not set `enableArtifactCache` itself yet, so the
  pipeline injects it.
- The export build of each dependency, with its `--packages` overrides.
- The two scope qualifiers.
- One `lake cache get`, `stage` and `put-staged` call per package. Lake has no
  workspace-wide form of these against a custom endpoint.

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
toolchain older than v4.34.0-rc2 has no `cache get --package` and behaves the
same way.

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
