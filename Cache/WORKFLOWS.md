# The cache workflows

`lake exe cache get` runs one of three workflows: the public-cache workflow,
the developer-cache workflow, and the nightly workflow. Before it reads, the
command chooses the workflow from the repository the checkout names and from
the flags, and prints the workflow it runs. Each workflow has its own module
under `Cache/Workflow/`, its own flags, and its own code path. The workflows
share the transfers, the repository detection, and the container chain.

Only `get` chooses a workflow. An upload writes the container that
`--container` names, and the local commands take no workflow.

The [README](./README.md) says which workflow a typical user gets. This
document describes the three workflows in full. The trust model behind them is
in [`SECURITY.md`](./SECURITY.md); the upload commands are in
[`CI.md`](./CI.md).

## The public cache and the developer cache

| Container            | Holds                                   | Written by                         |
|----------------------|-----------------------------------------|------------------------------------|
| `master`             | the master-built artifacts              | master-trust CI only               |
| `forks`              | fork PR builds, per commit              | fork PR CI                         |
| `nightly-testing`    | the nightly-testing repository's builds | nightly CI                         |
| `pr-toolchain-tests` | toolchain experiments                   | toolchain CI                       |

The public cache is the `master` container: the master-built artifacts that
anyone may consume. The developer cache is the `forks` container. On R2 it
has its own bucket, apart from the public cache.

Each workflow names the host it reads each container from, so each workflow
can change its hosts on its own:

| Workflow        | Container and host                                                      |
|-----------------|-------------------------------------------------------------------------|
| public cache    | `master` on `https://cache.mathlib.org`                                 |
| developer cache | `master` on `https://cache.mathlib.org`, `forks` on `https://r2devcache.mathlib.org` |
| nightly         | `nightly-testing` and `forks` on `https://cache.mathlib.org`            |

`https://cache.mathlib.org` is the cache resolver: it serves every container
and resolves each one to its current storage. `https://r2devcache.mathlib.org`
is the developer bucket, which the developer workflow reads directly.
`MATHLIB_CACHE_BASE_URL` and `MATHLIB_CACHE_DEBUG_USE_LEGACY` replace every
host of this table (see [Environment variables](#environment-variables)).

Only the `forks` container has per-commit namespaces:
a fork upload lands under the commit it was built from, and a read of `forks`
addresses one commit's namespace.

## Which workflow runs

The repository is the checkout's git remote, or `--repo=OWNER/REPO`. In a
project that depends on Mathlib, only a canonical detection counts: a fork
remote on the dependency checkout resolves to `leanprover-community/mathlib4`,
and the tool says so. An explicit `--repo=` names the fork to read, for example
in a project that builds against a fork commit. A dependency pinned to the
nightly-testing repository, or to one of its `nightly-testing-*` tags, names
that repository.

A read (`get`, `get!`, `get-`) takes:

- the public-cache workflow when `MATHLIB_CACHE_GET_URL` is set, whatever the
  repository;
- the public-cache workflow on `leanprover-community/mathlib4`, unless a
  chain-read flag (`--cache-from`, `--scope`, `--unsafe`, `--unsafe-window`)
  or variable (`MATHLIB_CACHE_FROM`, `MATHLIB_CACHE_REPO_SCOPE`) is present,
  which selects the developer-cache workflow;
- the nightly workflow on the nightly-testing repository;
- the developer-cache workflow on any other repository, that is, a fork.

The chain-read flags and variables are a fixed list in `Cache/Workflow.lean`
(`chainReadFlags`, `chainReadVariables`). A flag that a workflow adds does not
move a read to another workflow.

`query` is a developer-cache command: on a fork it finds the commits CI has
cached; on the canonical and nightly-testing repositories it answers that
there is no per-commit namespace to query.

Each workflow accepts its own flags and rejects the flags of another workflow:

| Workflow        | Flags                                                    |
|-----------------|----------------------------------------------------------|
| public cache    | none                                                     |
| developer cache | `--cache-from`, `--scope`, `--unsafe`, `--unsafe-window` |
| nightly         | `--cache-from`, `--scope`                                |

`--repo` is common to the workflows. `lake exe cache <command> --help` lists
the flags of a command.

## The public-cache workflow

The workflow of a checkout of `leanprover-community/mathlib4`, of a project
that depends on Mathlib, and of any reader with `MATHLIB_CACHE_GET_URL` set.

`get` fetches `https://cache.mathlib.org/mathlib4-master/f/{hash}.ltar` for
each file it needs, or `{url}/f/{hash}.ltar` from the flat endpoint that
`MATHLIB_CACHE_GET_URL` names. It uses no container chain, no per-commit
scope, and no marker probe, and it prints no security notice. The resolver also
serves the artifacts of the retired `mathlib4` container behind that
namespace, so the tool needs no fallback of its own. The `master` container
holds the artifacts CI built from `master`, so a checkout at a master commit,
or a project pinned to one, finds every file.

The workflow has no flags of its own. A set `MATHLIB_CACHE_FROM` or
`MATHLIB_CACHE_REPO_SCOPE` fails the read, because the workflow has no chain
and no per-commit namespace for them to address.

## The developer-cache workflow

The workflow of a fork checkout, and of a read on the canonical repository
with a chain, a scope, or `--unsafe`.

`get` walks the trust-ordered chain `master`, `forks`. `master`, read from
the public cache, serves the bulk of any fork's files by hash. `forks`, read
from the developer bucket, serves the files the fork's own CI built. By
default the `forks` round reads the fork's namespace for the checked-out
commit, which CI fills when it builds a PR at that commit. `--scope=REF` reads
another commit's namespace, `--unsafe` finds cached commits automatically, and
`--cache-from=LIST` replaces the chain.

CI uploads a fork build to the `forks` container under the commit's scope,
with the marker that `query` probes. `query` finds the fork's cached commits.

### Trust-ordered containers

The cache is split across multiple containers, logical namespaces in the URL
contract `/{container}/{key}`. Container names accepted by `--cache-from=LIST`:
`master`, `forks`, `nightly-testing`, `pr-toolchain-tests`.

The developer-cache and nightly workflows resolve a file by trying a default
chain of containers in order:

| Workflow        | Container order tried        |
|-----------------|------------------------------|
| developer cache | `master`, `forks`            |
| nightly         | `nightly-testing`, `forks`   |

Each container is read from the host its workflow names (see the table
above). Only the `forks` round reads at a scope; the other containers are read
unscoped. The public-cache workflow has no chain.

Override the read chain with `--cache-from=LIST`. On the canonical repository
the flag selects the developer-cache workflow. A chain that differs from the
workflow's own prints the
[security warning](#security-warning-non-default-scope).

```bash
# Read only from the master container
lake exe cache get --cache-from=master

# Read master first, then forks
lake exe cache get --cache-from=master,forks
```

### Finding Cached Commits with `query`

For branches with per-commit SHA scoping (e.g., fork PRs), you can use
`lake exe cache query` to discover which recent commits on your branch have
cached entries. This is useful when your current branch has diverged from
upstream and you want to avoid waiting for CI to build everything.

```bash
# Find the most recent cached commit on the current branch
lake exe cache query

# Example output (on a fork checkout; the canonical repos have no
# per-commit namespace and `query` says so instead):
# Most recent cached commit on this branch for fork alice/mathlib4: 5a3c7e9a...
#
# To use this cache, run:
#   lake exe cache get --scope=5a3c7e9a...
```

The `query` command walks your git log backwards from `HEAD`, stopping at the
merge base with `master` or a hard cap of 50 commits (whichever comes first),
and probes each commit for a completed SHA-scoped upload in the `forks`
container. That signal is written by `cache put` only after a successful
upload, so its presence is a reliable "this commit was cached" signal. `query`
prints the SHA to stdout (and does not auto-apply it) — you manually copy the
result into your `cache get` command if desired.

### Boolean probe on a single commit

`lake exe cache query <REF>` checks a specific commit and exits with 0 (cached)
or 1 (not cached). The ref can be `HEAD`, a branch name, a tag, or a SHA — anything
`git rev-parse` accepts.

```bash
# Is the current checkout's HEAD cached?
lake exe cache query HEAD && echo "yes" || echo "no"

# Is a specific SHA cached?
lake exe cache query 5a3c7e9a2f8c1d6b4e0f9a2c3d4e5f6a7b8c9d0e
# prints "cached: 5a3c7e9a..." (exit 0) or "not cached: 5a3c7e9a..." (exit 1)
```

By default `query` (both modes) targets the cwd's git remote — pass `--repo=`
to override. In a project that depends on Mathlib, `query` asks for `--repo=`,
because the project's own commits name no mathlib fork.

### Unsafe automatic scope walk

`cache get --unsafe` folds the `query` discovery into the download itself: rather
than asking you to copy one SHA into `--scope=`, it walks your branch history
(`HEAD` back to the merge base with `master`) for commits that have a cached fork
build and reads the `forks` container at their scope. By
default it uses just the single most recent such commit; `--unsafe-window=N`
widens this to the `N` most recent, tried newest first with files fetched in one
round dropped from the next.

```bash
lake exe cache get --unsafe             # use the most recent cached fork commit
lake exe cache get --unsafe-window=10   # try the 10 most recent (implies --unsafe)
```

The trust-ordered container chain is unchanged: `master` is still tried first and
serves the bulk of every fork's files by hash; only the `forks` round is expanded
into one round per discovered SHA. If no cached fork commit is found in range,
`--unsafe` falls back to a plain read, which reads the `forks` namespace of the
checked-out commit.

`--unsafe` trusts the artifacts of *every* commit it tries, so it always prints
the [non-default-scope security notice](#security-warning-non-default-scope). It
is mutually exclusive with `--scope=` (which pins exactly one commit). The
nightly workflow rejects it.

### Missing files

When some files are in no container of the chain, `cache get` prints a
warning to stderr. In the developer-cache workflow the warning also points at
`cache query`, which finds an earlier cached commit of the branch, and says
that reading it trusts the artifacts built at that commit.

## The nightly workflow

The workflow of the nightly-testing repository: its checkouts, its CI, and a
project whose Mathlib dependency is pinned to it. That repository builds under
a non-release toolchain, so its root hash differs from master's and its
artifacts exist only in the nightly containers.

`get` walks the chain `nightly-testing`, `forks`, through the cache resolver.
`master` is absent because the nightly root hash differs, so a master probe
misses. `forks` is present because a PR from the nightly-testing repository
into mathlib4 builds with fork trust and uploads there; a scope applies to
that round alone. `pr-toolchain-tests` is absent, so an upload from an
experimental toolchain branch cannot reach a trusted nightly consumer. CI
widens the chain for those branches with `MATHLIB_CACHE_FROM`.

CI uploads the repository's builds to `nightly-testing` or
`pr-toolchain-tests`, unscoped. The workflow accepts `--cache-from` and
`--scope`, and rejects `--unsafe`. `query` probes the markers of forks only,
so on the nightly-testing repository it answers that there is nothing to
query.

## Security Warning: Non-Default Scope

When a chain read (the developer-cache and nightly workflows) reads cache
artifacts at a non-default scope, the cache tool prints a security warning to
stderr. This happens when:

1. **`--unsafe` is passed** — you are letting the tool walk history and trust the
   artifacts of whichever recent fork commit(s) it finds cached.
2. **`--scope=` is passed** — you are reading from a specific commit's
   namespace instead of the workflow's default trust chain.
3. **`--cache-from` widens the read chain** — you are explicitly telling the tool
   to trust containers beyond the workflow's chain.
4. **`--repo` overrides the detected git remote** — you are reading cache for a
   different repository than your cwd's git remote, or naming a fork when no git
   remote is detected.

Example warning:

```
=================================================================
SECURITY: reading cache at a non-default scope
=================================================================
You are reading cache artifacts at a scope outside the default trust
boundary for this repo. The cache cannot verify the contents of these
artifacts; you are choosing to trust whoever uploaded them.

Repository: leanprover-community/mathlib4
Reason: --scope=5a3c7e9a2f8c1d6b4e0f9a2c3d4e5f6a7b8c9d0e (explicit per-commit scope)
=================================================================
```

This warning is always printed — it cannot be suppressed with `--quiet`. The
warning is purely informational; it does not prompt for confirmation (so it
doesn't interfere with CI).

## Environment variables

| Variable                   | Effect on the workflow                                                            |
|----------------------------|-----------------------------------------------------------------------------------|
| `MATHLIB_CACHE_GET_URL`    | Selects the public-cache workflow and replaces its URL (see [Operating an external cache](README.md#operating-an-external-cache)). |
| `MATHLIB_CACHE_FROM`       | The chain of a chain read, as `--cache-from`, which takes precedence. On the canonical repository a set value selects the developer-cache workflow. Set by CI (see [`CI.md`](./CI.md)). |
| `MATHLIB_CACHE_REPO_SCOPE` | The per-commit scope, as `--scope`, which takes precedence. On the canonical repository a set value selects the developer-cache workflow. Set by CI. |
| `MATHLIB_CACHE_BASE_URL`   | Replaces the host of every container of every workflow: a host that mirrors the whole `/{container}/{key}` namespace. |
| `MATHLIB_CACHE_DEBUG_USE_LEGACY` | Reads every container from the Azure storage account (see [Troubleshooting](README.md#troubleshooting)). |

An empty value means unset.
