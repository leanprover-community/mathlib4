# Lake cache shadow pipeline

`lake_cache_shadow.yml` exercises Lake's built-in artifact cache against the
live mathlib4 master branch. It runs beside the regular master CI and stays
independent of it, in a bucket that only this pipeline reads.

The pipeline caches mathlib and every git dependency in its manifest. Each
package has one revision file per mathlib commit:

    revisions/<SCOPE>/<mathlib-sha>.jsonl
    revisions/<DEP_SCOPE>/<name>/<mathlib-sha>.jsonl

`<SCOPE>` is `mathlib4-master-shadow`, with a toolchain suffix for override
runs. `<DEP_SCOPE>` is `mathlib4-master-shadow/deps/<toolchain-slug>`.
`<name>` is the dependency's package name in mathlib's manifest. A dispatched
run can set `cache_deps` to false to omit dependency caches.

## Jobs

- `build_and_stage` builds mathlib and its dependencies, and stages the
  mappings of each package.
- `upload` pushes the staged files to the bucket. It records a manifest under
  `analysis/<toolchain-slug>/` and reports the carryover.
- `consume` fetches every package into a fresh checkout, builds against them,
  and verifies the result with `--rehash`.
- `downstream` builds a small project that requires mathlib. It fetches every
  package at the mathlib SHA in its resolved manifest. It runs when the targets
  are `Mathlib` and the run caches dependencies.
- `report` posts a summary of the run to Zulip.

## Cache service configuration

Each job writes its own service definition into the file `LAKE_CONFIG` names:

    [[cache.service]]
    name = "shadow"
    type = "s3"
    artifactEndpoint = "https://<host>/cache/artifacts"
    revisionEndpoint = "https://<host>/cache/revisions"

A job that fetches uses the public read endpoints. The upload job uses the
S3 endpoints, and `LAKE_CACHE_KEY` signs its requests.

## The key of a package

mathlib passes `--scope=<SCOPE> --rev=<mathlib-sha>`. Each dependency passes
`--scope=<DEP_SCOPE>/<name> --rev=<mathlib-sha>`. Lake uses these plain scopes
verbatim. The workflow supplies the toolchain in `<DEP_SCOPE>` explicitly.
All jobs use the Linux runner platform.

The mathlib SHA fixes the complete dependency pin set. A dependency's own
revision fixes only its source: its upstream dependencies can change between
mathlib commits. For example, two mathlib commits can pin the same aesop
revision and different batteries revisions. The two aesop manifests then use
different mathlib SHAs, so both sets of mappings remain available.

Every pull supplies the full mathlib SHA, including pulls for dependencies.
Lake accepts a full SHA as the cache revision even when that commit belongs
to another repository. A downstream consumer reads this SHA from the mathlib
entry in its own `lake-manifest.json` and fetches all packages at that SHA.
The consumer must use mathlib's dependency pins to replay the complete cache.

## Push

Each run attempts to publish every selected package. Each export runs in mathlib's
workspace, so its mappings use the same upstream pins as the root build.

1. `lake build <targets> -o .lake/outputs.jsonl` builds the targets, writes
   artifacts into the local Lake cache, and records mathlib's mappings.
   Lake records both compiled targets and targets that replay cached outputs.
2. `lake build @<DEP> --package=<DEP> -o .lake/dep-outputs/<DEP>.jsonl` exports
   each dependency's mappings. `@<DEP>` selects its default targets, including
   modules that mathlib does not import.
3. `lake cache stage` copies each package into its own staging directory.
   The tree travels to the upload job as a GitHub artifact. The build sandbox
   has no upload credentials.
4. `lake cache put-staged` uploads each package. mathlib passes
   `--scope=<SCOPE> --rev=<mathlib-sha>`. Each dependency passes
   `--scope=<DEP_SCOPE>/<name> --rev=<mathlib-sha>`.
   Lake uploads the artifacts first and the revision file last.

A run whose staging tree exceeds 2 GB fails before the upload. The cap protects
the R2 free tier and the lifecycle budget.

## Pull

The `consume` job sets `LAKE_NO_CACHE` and builds from the shadow bucket:

1. `lake cache get --scope=<SCOPE> --rev=<mathlib-sha>` fetches mathlib.
2. `lake cache get --package=<DEP> --scope=<DEP_SCOPE>/<name>
   --rev=<mathlib-sha>` fetches each dependency.
3. `lake build <targets>` replays both.

The `downstream` job uses the same commands with `--package=mathlib` on the
root fetch. It reads the mathlib SHA from its resolved manifest. Every package
therefore comes from the same snapshot that the build job published.

The provenance checks count compiled modules, including modules that emit
warnings. A root module rebuild fails the job. Dependency rebuilds appear in
the report, including dependencies on the skip list.

## Storage layout

One bucket holds these keys:

    revisions/<SCOPE>/<mathlib-sha>.jsonl
    revisions/<DEP_SCOPE>/<name>/<mathlib-sha>.jsonl
    artifacts/<SCOPE>/<content-hash>.art
    artifacts/<DEP_SCOPE>/<name>/<content-hash>.art
    analysis/<toolchain-slug>/_latest.txt
    analysis/<toolchain-slug>/<mathlib-sha>.txt

A revision file maps input hashes to artifacts. `lake cache get` downloads the
artifacts from the same scope. The workflow owns the `analysis/` prefix; Lake
owns the other two. `_latest.txt` holds the SHA for the next warm start.
`<mathlib-sha>.txt` holds the carryover baseline.

Artifact keys omit the revision, so snapshots share identical content. A new
mathlib commit writes new revision files and retains the older mappings.
Historical snapshots remain replayable while their manifests and artifacts
remain in the bucket. A rerun at the same SHA and toolchain replaces that
snapshot's manifests; use the same targets to preserve its coverage.

A lifecycle rule can expire artifacts by age. Lake uploads every artifact a
run uses, which refreshes those objects. Retention must cover both manifests
and their referenced artifacts for the required historical window.

## Hydration

Both warm starts use `analysis/<toolchain-slug>/_latest.txt` as the previous
mathlib SHA:

- The root fetch uses `--scope=<SCOPE> --rev=<previous-sha>`.
- Each dependency fetch uses `--package=<DEP> --scope=<DEP_SCOPE>/<name>
  --rev=<previous-sha>`.

Lake replays outputs whose input hashes match the current workspace. The
build compiles changed modules and dependencies that the previous snapshot
lacks. A failed warm start also falls back to a source build.
The first run on a toolchain has no pointer and builds from source.

## What a full cache hit requires

- `LAKE_ARTIFACT_CACHE=true` enables cache writes in the build workspace.
  mathlib leaves `enableArtifactCache` unset, so its dependencies inherit the
  environment setting unless their own configuration overrides it.
- Each selected dependency exports its mappings with `--package`.
- Push and pull use the same mathlib SHA, effective toolchain, and platform.
  The mathlib SHA fixes the source and dependency pins. The workflow uses
  Linux runners for every job and carries the resolved scopes between jobs.

## Toolchain override

The `toolchain_override` input, or the `LAKE_SHADOW_TOOLCHAIN_OVERRIDE`
variable, changes the toolchain of the whole pipeline. The input takes
precedence. The build job resolves the toolchain, and the later jobs stamp
that value into their checkouts.

The override must compile the selected mathlib source. A Lake change applied
to the pinned Lean release is one example.

The analysis chain is per toolchain, under `analysis/<toolchain-slug>/`.
The slug replaces characters outside `A-Za-z0-9._-` with `-`.
Dependencies always use this slug in their scope. An override run also appends
it to mathlib's root scope: `mathlib4-master-shadow/<toolchain-slug>`.
This separates snapshots of one mathlib commit on different toolchains.
To compare two toolchains, dispatch both runs with the same `mathlib_ref`.

A republished toolchain tag keeps the same scope but can change input hashes.
Use a distinct toolchain name when both binary versions must remain replayable.

## Dependency skip list

`DEP_SKIP` excludes dependencies from caching, separated by spaces. It is
empty: the pipeline caches all git dependencies, proofwidgets included.
proofwidgets commits its npm output and the Lake traces that guard the npm
steps, so a build at a pinned revision skips npm.

Warm-start failures cause source builds in the build job. Export, upload,
and fetch failures can cause dependency rebuilds in consume. The consume
report records those rebuilds. A toolchain without `lake build --package`
cannot export dependency mappings and reports the same fallback.

A dependency that sets `enableArtifactCache := false` overrides the
environment. Its exported mappings can refer to artifacts absent from the
local cache, which fails `lake cache stage`. Put such a dependency on the
skip list.

## Required repository configuration

Secrets:

- `LAKE_CACHE_KEY` — SigV4 credential for the cache bucket, as
  `<ACCESS_KEY_ID>:<SECRET_ACCESS_KEY>` (curl `--user`; region is `auto`).
- `ZULIP_API_KEY` — Zulip bot key for the `report` job.

Variables:

- `LAKE_CACHE_ARTIFACT_ENDPOINT` and `LAKE_CACHE_REVISION_ENDPOINT` — the
  authenticated S3 endpoints. The upload job uses them. For example,
  `https://<acct>.r2.cloudflarestorage.com/<bucket>/<prefix>/artifacts`.
- `LAKE_CACHE_ARTIFACT_ENDPOINT_PUBLIC` and
  `LAKE_CACHE_REVISION_ENDPOINT_PUBLIC` — the public read endpoints for
  anonymous GETs. On R2 these use a different host than the S3 API endpoints.
  For example, `https://pub-<hash>.r2.dev/<prefix>/artifacts`.
- `LAKE_SHADOW_TOOLCHAIN_OVERRIDE` — optional. It sets the toolchain override
  for every run. The dispatch input takes precedence. Leave it unset to run on
  the repo pin.
