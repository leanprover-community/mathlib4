# The cache workflows

`lake exe cache get` runs one of three workflows: the public-cache workflow,
the developer-cache workflow, and the nightly workflow. The command chooses
the workflow before it reads, from the repository the checkout names and the
flags, and prints the workflow it runs. Each workflow has its own module under
`Cache/Workflow/`, its own flags, and its own code path. The workflows share
the transfers, the repository detection, and the container chain below them.
`get` is the one command whose behavior depends on the checkout and the
environment; an upload is chosen by its `--dev-cache` flag, and the local
commands depend on neither.

The [README](./README.md) says which workflow a typical user gets. This
document describes the three workflows in full. The trust model behind them is
in [`SECURITY.md`](./SECURITY.md); the upload commands are in
[`CI.md`](./CI.md).

## The public cache and the developer cache

The cache is two services, each with its own storage and read endpoint:

| Service   | Containers                                       | Read endpoint                  | Written by                           |
|-----------|--------------------------------------------------|--------------------------------|--------------------------------------|
| public    | `master`, `legacy`                               | `https://cache.mathlib.org`    | master-trust CI only                 |
| developer | `forks`, `nightly-testing`, `pr-toolchain-tests` | `https://devcache.mathlib.org` | fork PR CI, nightly CI, toolchain CI |

The public cache holds the master-built artifacts that anyone may consume.
The developer cache holds the work-in-progress artifacts: fork PR builds, the
nightly-testing repository, and toolchain experiments. The storage split keeps
a work-in-progress writer away from the artifacts the public consumes; the
endpoint split lets each side be re-pointed, cached, and retired on its own.

The containers are logical namespaces in the URL contract
`/{container}/{key}`. Only the `forks` container has per-commit namespaces:
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
  developer-cache flag (`--cache-from`, `--scope`, `--unsafe`,
  `--unsafe-window`) or variable (`MATHLIB_CACHE_FROM`,
  `MATHLIB_CACHE_REPO_SCOPE`) is present, which selects the developer-cache
  workflow;
- the nightly workflow on the nightly-testing repository;
- the developer-cache workflow on any other repository, that is, a fork.

An upload (`put`, `put!`, `put-staged`) has two forms, chosen by the flag
`--dev-cache` rather than by the checkout. The flat upload writes
`{url}/f/{hash}.ltar` under `MATHLIB_CACHE_PUT_URL`, the layout of `master`.
The developer-cache upload writes the repo-namespaced layout of the developer
cache's containers, `{url}/f/{repo}/`, for `--repo`, and with a scope
(`--scope`, `MATHLIB_CACHE_REPO_SCOPE`) the fork's per-commit namespace
`{url}/f/{repo}/{sha}/` and its marker. `--container=NAME` stands for both:
that container's Azure base as the URL, and its form; the variable overrides
the URL. The upload commands are internal to mathlib CI; see
[`CI.md`](./CI.md).

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

`get` fetches `https://cache.mathlib.org/mathlib4/f/{hash}.ltar` for each file
it needs (or `{url}/f/{hash}.ltar` from the flat endpoint the variable names),
and nothing else: no container chain, no per-commit scope, no marker probe,
no security notice. The public endpoint serves the `legacy` artifacts behind
that namespace, so the tool needs no fallback of its own. The cache holds the
artifacts CI built from `master`, so a checkout at a master commit, or a
project pinned to one, finds every file.

CI publishes the master builds this workflow reads into the `master`
container. The workflow has no flags of its own, and a set `MATHLIB_CACHE_FROM`
or `MATHLIB_CACHE_REPO_SCOPE` fails the read, because the workflow has no
chain and no per-commit namespace for them to address.

## The developer-cache workflow

The workflow of a fork checkout, and of a read on the canonical repository
with a chain, a scope, or `--unsafe`.

`get` walks the trust-ordered chain `master`, `forks`, `legacy`: `master` from
the public cache serves the bulk of any fork's files by hash, `forks` from the
developer cache serves the files the fork's own CI built, and `legacy` keeps
older artifacts reachable. The `forks` round reads the fork's namespace for
the checked-out commit by default, which CI fills when it builds a PR at that
commit. `--scope=REF` reads another commit's namespace, `--unsafe` finds one
automatically, and `--cache-from=LIST` replaces the chain.

CI uploads a fork build to the `forks` container under the commit's scope,
with the marker that `query` probes. `query` finds the fork's cached commits.

### Trust-ordered containers

The developer-cache and nightly workflows resolve a file by trying their
chain of containers in order:

| Workflow        | Container order tried                |
|-----------------|--------------------------------------|
| developer cache | `master`, `forks`, `legacy`          |
| nightly         | `nightly-testing`, `forks`, `legacy` |

Each container is read from its service's endpoint, so the developer chain
reads `master` and `legacy` from the public cache and `forks` from the
developer cache. Only the `forks` round reads at a scope; the other containers
are read unscoped. The public-cache workflow has no chain.

`--cache-from=LIST` replaces the chain with a trust-ordered, comma-separated
list of containers. Container names: `master`, `forks`, `nightly-testing`,
`pr-toolchain-tests`, `legacy`. On the canonical repository the flag selects
the developer-cache workflow. A chain that differs from the workflow's own
prints the [security notice](#security-notice-non-default-scope).

```bash
# Read only from the master container
lake exe cache get --cache-from=master

# Read master first, then forks
lake exe cache get --cache-from=master,forks
```

### Finding cached commits with `query`

For branches with per-commit SHA scoping (fork PRs), `lake exe cache query`
discovers which recent commits on the branch have cached entries. This is
useful when the branch has diverged from upstream and you want to avoid
waiting for CI to build everything.

```bash
# Find the most recent cached commit on the current branch
lake exe cache query

# Example output (on a fork checkout; the canonical repositories have no
# per-commit namespace and `query` says so instead):
# Most recent cached commit on this branch for fork alice/mathlib4: 5a3c7e9a...
#
# To use this cache, run:
#   lake exe cache get --scope=5a3c7e9a...
```

The `query` command walks the git log backwards from `HEAD`, stopping at the
merge base with `master` or a hard cap of 50 commits (whichever comes first),
and probes each commit for a completed SHA-scoped upload in the `forks`
container. That signal is written by `cache put` only after a successful
upload, so its presence is a reliable "this commit was cached" signal. `query`
prints the SHA to stdout and does not apply it; you copy the result into your
`cache get --scope=` command if desired.

By default `query` targets the cwd's git remote; `--repo=` overrides it. In a
project that depends on Mathlib, `query` asks for `--repo=`, because the
project's own commits name no mathlib fork.

### Boolean probe on a single commit

`lake exe cache query <REF>` checks a specific commit and exits with 0 (cached)
or 1 (not cached). The ref can be `HEAD`, a branch name, a tag, or a SHA,
anything `git rev-parse` accepts.

```bash
# Is the current checkout's HEAD cached?
lake exe cache query HEAD && echo "yes" || echo "no"

# Is a specific SHA cached?
lake exe cache query 5a3c7e9a2f8c1d6b4e0f9a2c3d4e5f6a7b8c9d0e
# prints "cached: 5a3c7e9a..." (exit 0) or "not cached: 5a3c7e9a..." (exit 1)
```

### Unsafe automatic scope walk

`cache get --unsafe` folds the `query` discovery into the download itself:
rather than asking you to copy one SHA into `--scope=`, it walks your branch
history (`HEAD` back to the merge base with `master`) for commits that have a
cached fork build and reads the `forks` container at their scope. By default
it uses just the single most recent such commit; `--unsafe-window=N` widens
this to the `N` most recent, tried newest first with files fetched in one
round dropped from the next.

```bash
lake exe cache get --unsafe             # use the most recent cached fork commit
lake exe cache get --unsafe-window=10   # try the 10 most recent (implies --unsafe)
```

The trust-ordered container chain is unchanged: `master` is still tried first
and serves the bulk of every fork's files by hash; only the `forks` round is
expanded into one round per discovered SHA. If no cached fork commit is found
in range, `--unsafe` falls back to a plain unscoped read.

`--unsafe` trusts the artifacts of *every* commit it tries, so it always prints
the [security notice](#security-notice-non-default-scope). It is mutually
exclusive with `--scope=`, which pins exactly one commit. The nightly workflow
rejects it.

### Heads-up note from `cache get`

When you run `cache get` on a fork checkout and HEAD has not been built and
cached at fork-trust level, the tool prints a stderr note pointing you at
`cache query`, and warns that picking a different commit means trusting its
artifacts. The note costs one HTTP HEAD per `cache get` invocation. It fires
only on a plain `cache get`: no `--scope=`, no `--cache-from`, and a HEAD that
is not already part of `master`, whose artifacts the `master` round serves.

## The nightly workflow

The workflow of the nightly-testing repository: its checkouts, its CI, and a
project whose Mathlib dependency is pinned to it. That repository builds under
a non-release toolchain, so its root hash differs from master's and its
artifacts exist only in the developer cache.

`get` walks the chain `nightly-testing`, `forks`, `legacy`. `master` is absent
because the nightly root hash differs, so a master probe misses. `forks` is
present because a PR from the nightly-testing repository into mathlib4 builds
with fork trust and uploads there; a scope applies to that round alone.
`pr-toolchain-tests` is absent, so an upload from an experimental toolchain
branch stays away from a trusted nightly consumer; CI widens the chain for
those branches with `MATHLIB_CACHE_FROM`.

CI uploads the repository's builds to `nightly-testing` or
`pr-toolchain-tests`, unscoped. The workflow accepts `--cache-from` and
`--scope`, and rejects `--unsafe`. The nightly containers cache by file hash,
so `query` has nothing to find and says so.

## Security notice: non-default scope

When a chain read (the developer-cache and nightly workflows) is taken off the
workflow's default trust boundary, the tool prints a security notice to
stderr. This happens when:

1. **`--unsafe` is passed**: you are letting the tool walk history and trust the
   artifacts of whichever recent fork commits it finds cached.
2. **`--scope=` names a commit other than HEAD**: you are reading from a
   specific commit's namespace instead of the one for the commit you have.
3. **`--cache-from` changes the read chain**: you are telling the tool to
   read containers beyond the workflow's chain, or in another order.
4. **`--repo` overrides the detected git remote**: you are reading the cache
   of a repository other than your checkout's.

Example notice:

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

The notice is informational: it prints and the read continues, so it does not
interfere with CI. `MATHLIB_CACHE_FROM` and a `MATHLIB_CACHE_REPO_SCOPE` equal
to HEAD, CI's own settings, do not trigger it.

## Environment variables

| Variable                   | Effect on the workflow                                                            |
|----------------------------|-----------------------------------------------------------------------------------|
| `MATHLIB_CACHE_GET_URL`    | Selects the public-cache workflow and replaces its URL (see [Operating an external cache](README.md#operating-an-external-cache)). |
| `MATHLIB_CACHE_FROM`       | The chain of a chain read, as `--cache-from`, which takes precedence. On the canonical repository a set value selects the developer-cache workflow. Set by CI (see [`CI.md`](./CI.md)). |
| `MATHLIB_CACHE_REPO_SCOPE` | The per-commit scope, as `--scope`, which takes precedence. On the canonical repository a set value selects the developer-cache workflow. Set by CI. |
| `MATHLIB_CACHE_DEBUG_USE_LEGACY` | Reads both caches from the Azure storage account (see [Troubleshooting](README.md#troubleshooting)). |

An empty value means unset.
