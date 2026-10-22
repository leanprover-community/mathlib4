# Lake cache shadow pipeline

`lake_cache_shadow.yml` exercises Lake's built-in artifact cache against the
live mathlib4 master branch. It runs beside the regular master CI and stays
independent of it, in a bucket that only this pipeline reads.

The pipeline caches mathlib and every git dependency in its manifest. Each
package publishes under its own revision:

    revisions/mathlib4-master-shadow/<name>/<toolchain-slug>/<rev>.jsonl

`<name>` is the package name, `mathlib` for mathlib itself. `<rev>` is the
package's own commit: mathlib's commit for mathlib, and the commit that
mathlib's manifest pins for a dependency. A dispatched run can set
`cache_deps` to false to omit dependency caches.

## Jobs

- `build_and_stage` builds mathlib and its dependencies, and stages the
  mappings of each package.
- `upload` pushes the staged files to the bucket. It records a manifest under
  `analysis/<toolchain-slug>/` and reports the carryover.
- `consume` fetches every package into a fresh checkout, builds against them,
  and verifies the result with `--rehash`.
- `downstream` builds a small project that requires mathlib. It passes no
  revision to any fetch; Lake reads each one from the package's checkout. It
  runs when the targets are `Mathlib` and the run caches dependencies.
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

Every package passes `--scope=mathlib4-master-shadow/<name>/<toolchain-slug>`
and its own commit as `--rev`. Lake uses the scope verbatim. All jobs use the
Linux runner platform.

The toolchain slug is the resolved `lean-toolchain` with each character outside
`A-Za-z0-9._-` replaced by `-`, for example `leanprover-lean4-v4.36.0-rc1`. A
package's revision can survive a toolchain bump. LeanSearchClient kept one
revision through 12 of mathlib's toolchain bumps. The slug keeps each
toolchain's build of that revision in its own revision file.

A dependency's revision fixes its source but not its upstream packages.
mathlib's manifest decides those for the whole workspace. Two mathlib commits
can pin the same aesop revision with different batteries revisions. Both write
`aesop/<toolchain-slug>/<aesop-rev>.jsonl`, and the later upload replaces the
earlier one. A consumer of the older commit then rebuilds the aesop modules
that import the changed batteries modules. Lake matches each entry by its input
hash, so a replaced entry causes a rebuild, never a wrong replay. Of mathlib's
dependencies, only aesop (on batteries) and importGraph (on Cli) have an
upstream in the set.

A consumer passes no revision. `lake cache get` reads it from the package's
checkout, and walks back through the package's history to the nearest revision
the bucket holds.

## Push

Each run attempts to publish every selected package. Each export runs in mathlib's
workspace, so its mappings use the same upstream pins as the root build.

1. `lake build <targets> -o .lake/outputs.jsonl` builds the targets, writes
   artifacts into the local Lake cache, and records mathlib's mappings.
   Lake records both compiled targets and targets that replay cached outputs.
2. `lake build <modules> --package=<DEP> -o .lake/dep-outputs/<DEP>.jsonl` exports
   each dependency's mappings. `<modules>` are the dependency's default modules,
   from `lake query @<DEP>:defaultModules`, including modules that mathlib does
   not import. Building them as modules links no executable, so the mappings
   hold Lean module archives only.
3. `lake cache stage` copies each package into its own staging directory.
   The tree travels to the upload job as a GitHub artifact. The build sandbox
   has no upload credentials.
4. `lake cache put-staged` uploads each package with
   `--scope=mathlib4-master-shadow/<name>/<toolchain-slug>` and its own commit
   as `--rev`. Lake uploads the artifacts first and the revision file last.

A run whose staging tree exceeds 2 GB fails before the upload. The cap protects
the R2 free tier and the lifecycle budget.

## Pull

The `consume` job sets `LAKE_NO_CACHE` and builds from the shadow bucket:

1. `lake cache get --scope=mathlib4-master-shadow/mathlib/<toolchain-slug>
   --rev=<mathlib-sha>` fetches mathlib.
2. `lake cache get --package=<DEP>
   --scope=mathlib4-master-shadow/<DEP>/<toolchain-slug> --rev=<dep-rev>`
   fetches each dependency at the revision that the manifest pins.
3. `lake build <targets>` replays both.

`consume` passes each revision, so every fetch is one exact request and the job
tests what this run uploaded. The `downstream` job runs the same fetches
without `--rev`. It derives the toolchain slug from its own `lean-toolchain`.

The provenance checks count compiled modules, including modules that emit
warnings. A root module rebuild fails the job. Dependency rebuilds appear in
the report, including dependencies on the skip list.

## Storage layout

One bucket holds these keys:

    revisions/mathlib4-master-shadow/<name>/<toolchain-slug>/<rev>.jsonl
    artifacts/mathlib4-master-shadow/<name>/<toolchain-slug>/<content-hash>.art
    analysis/<toolchain-slug>/_latest.txt
    analysis/<toolchain-slug>/<mathlib-sha>.txt

A revision file maps input hashes to artifacts. `lake cache get` downloads the
artifacts from the same scope. The workflow owns the `analysis/` prefix; Lake
owns the other two. `_latest.txt` holds the SHA for the next warm start.
`<mathlib-sha>.txt` holds the carryover baseline.

Artifact keys omit the revision, so the revisions of one package on one
toolchain share identical content. A dependency's revision file serves every
mathlib commit that pins that revision on that toolchain. Deleting a
`<toolchain-slug>/` prefix retires one toolchain for a package. A rerun at the
same revision and toolchain replaces that revision file; use the same targets
to preserve its coverage.

A lifecycle rule can expire artifacts by age. Lake uploads every artifact a
run uses, which refreshes those objects. Retention must cover both manifests
and their referenced artifacts for the required historical window.

## Hydration

Two fetches decide how much a run compiles. Neither changes the keys or the
content that a run writes.

- The root warm start, `lake cache get --rev=<previous-sha>` on mathlib's
  scope. `analysis/<toolchain-slug>/_latest.txt` holds the previous mathlib
  commit.
- The dependency warm start, `lake cache get --package=<DEP>` without `--rev`.
  Lake walks back through the dependency's history, so a dependency that this
  run bumps starts from its previous pin.

Lake replays outputs whose input hashes match the current workspace. The build
compiles changed modules and dependencies that the bucket lacks. A failed warm
start also falls back to a source build. The first run on a toolchain builds
from source.

## What a full cache hit requires

- `LAKE_ARTIFACT_CACHE=true` enables cache writes in the build workspace.
  mathlib leaves `enableArtifactCache` unset, so its dependencies inherit the
  environment setting unless their own configuration overrides it.
- Each selected dependency exports its mappings with `--package`.
- Push and pull use the same revisions and toolchain slug. The workflow uses
  Linux runners for every job.

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
