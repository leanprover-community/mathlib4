# Miscellaneous scripts for working on mathlib

This directory contains miscellaneous scripts that are useful for working on or with mathlib.
When adding a new script, please make sure to document it here, so other readers have a chance
to learn about it as well!


## Current scripts and their purpose

**Installation scripts**
- `install_debian.sh`, `install_macos.sh`
  Installation scripts referenced from the leanprover community install pages.
  https://leanprover-community.github.io/install/debian.html
  https://leanprover-community.github.io/install/macos.html
  If these web pages are deprecated or removed, we should remove these scripts.

**Repository analysis and reporting**
- `user_activity_report.py`
  Generates a comprehensive report of all users with repository access and their last commit activity.
  Shows username, age of last commit, and access level, sorted by commit recency (most recent first).

  **Features:**
  - Fetches repository collaborators and organization members via GitHub API
  - Intelligent caching: user lists (24h TTL) and commit data (6h TTL) for performance
  - Access level filtering: `--admin` (admin users only), `--write` (write+ access)
  - Single user analysis: `--user USERNAME` for debugging specific users
  - Result limiting: `--limit N` for testing with smaller datasets
  - Inactive user cleanup: `--remove N` generates (but doesn't execute) gh commands
    to remove write access from non-admin users inactive for more than N days
  - Fallback to contributors API if collaborators access is restricted (`--contributors-only`)

  **Caching:** Results cached in `scripts/users_cache.json` and `scripts/commits_cache.json`
  (automatically added to .gitignore). Cache saved after each commit lookup to prevent data loss.

  **Requirements:** `gh` (GitHub CLI) installed and authenticated (`gh auth login`).

**Tools for manual maintenance**
- `fix_unused.py`
  Bulk processing of unused variable warnings, replacing them with `_`.
- `add_deprecations.sh` is a text-based script that automatically adds deprecation statements.
  It assumes that the only difference between master and the current status of the PR consists
  of renames. More precisely, any change on a line that contains a declaration name
  and is not a rename, will likely confuse the script.
- `create_deprecated_modules.lean` defines the `#create_deprecated_modules` command that
  automatically generates the `deprecated_module` entries, gathering information from `git`.
  The expectation is that this will be expanded to a fully automated process that happens in CI.
- `migrate_to_fork.py`
  Helps contributors migrate from having direct write access to the main repository
  to using a fork-based workflow. This comprehensive script automates the entire migration process:
  * Validates the current branch (prevents migration of system branches like master, nightly-testing)
  * Checks GitHub CLI installation/authentication with OS-specific installation instructions
  * Creates or syncs a fork of mathlib4 automatically
  * Sets up git remotes correctly (`upstream` for leanprover-community/mathlib4, `origin` for user's fork)
  * Detects already-completed migration steps and skips them for efficiency
  * Migrates the current branch to the fork with proper upstream tracking
  * Intelligently handles existing PRs (migrates main repo PRs to fork-based PRs, detects existing fork PRs)
  * Uses fast delete/re-add approach for remote operations to avoid slow branch tracking updates
  * Provides comprehensive status reporting and next steps guidance
  Run with `python3 scripts/migrate_to_fork.py` (interactive) or `python3 scripts/migrate_to_fork.py -y` (auto-accept).
  Requires GitHub CLI (`gh`) installed and authenticated. Safe to run multiple times.
- `githelper.py`
  The subcommand `githelper.py fix` helps contributors fix their git repository setup
  by step-by-step converting it from its current state to a well-defined target state.
  The target state mostly matches the state after of a freshly cloned fork (`gh repo clone <fork>`)
  and looks like this:

  - The remote `upstream` points to `leanprover-community/mathlib4`
  - The remote `origin` points to the contributor's own fork
  - The `gh` default repo points to `leanprover-community/mathlib4`
  - `master`s remote is `upstream` but its pushRemote is `origin`

  Other subcommands to automate git-related actions may be added in the future.

**Analyzing Mathlib's import structure**
- `unused_in_pole.sh` (followed by an optional `<target>`, defaulting to `Mathlib`)
  calls `lake exe pole --loc --to <target>` to compute the longest
  pole to a given target module, and then feeds this into
  `lake exe unused` to analyze transitively unused imports.
  Generates `unused.md` containing a markdown table showing the unused imports,
  and suggests `lake exe graph` commands to visualize the largest "rectangles" of unused imports.

**CI workflow**
- `lake-build-with-retry.sh`
  Runs `lake build` on a target until `lake build --no-build` succeeds. Used in the main build workflows.
- `mk_all.lean`
  run via `lake exe mk_all`, regenerates the import-only files
  `Mathlib.lean`, `Mathlib/Tactic.lean`, `Archive.lean` and `Counterexamples.lean`
- `lint-style.lean`, `lint-style.py`, `print-style-errors.sh`
  style linters, written in Python and Lean. Run via `lake exe lint-style`.
  Medium-term, the latter two scripts should be rewritten and incorporated in `lint-style.lean`.
- `lint-bib.sh`
  normalize the BibTeX file `docs/references.bib` using `bibtool`.
- `yaml_check.py`, `check-yaml.lean`
  Sanity checks for `undergrad.yaml`, `overview.yaml`, `100.yaml` and `1000.yaml`.
- `lean-pr-testing-comments.sh`
  Generate comments and labels on a Lean or Batteries PR after CI has finished on a
  `*-pr-testing-NNNN` branch.
- `update_nolints_CI.sh`
  Update the `nolints.json` file to remove unneeded entries. Automatically run once a week.
- `assign_reviewers.py` is used to automatically assign a reviewer to each stale github PR on the review queue.
  This script downloads a .json file with proposed assignments and makes the
  corresponding github API calls.
- `bench_summary.lean`
  Convert data retrieved from the speed center into a shorter, more accessible format,
  and post a comment with this summary on github.
- `declarations_diff.sh`
  Attempts to find which declarations have been removed and which have been added in the current PR
  with respect to `master`, and posts a comment on github with the result.
- `autolabel.lean` is the Lean script in charge of automatically adding a `t-`label on eligible PRs.
  Autolabelling is inferred by which directories the current PR modifies.

**Managing nightly-testing and bump branches**
- `create-adaptation-pr.sh` implements some of the steps in the workflow described at
  https://leanprover-community.github.io/contribute/tags_and_branches.html#mathlib-nightly-and-bump-branches
  Specifically, it will:
  - merge `master` into `bump/v4.x.y`
  - create a new branch from `bump/v4.x.y`, called `bump/nightly-YYYY-MM-DD`
  - merge `nightly-testing` into the new branch
  - open a PR to merge the new branch back into `bump/v4.x.y`
  - announce the PR on zulip
  - finally, merge the new branch back into `nightly-testing`, if conflict resolution was required.

  If there are merge conflicts, it pauses and asks for help from the human driver.
- `merge-lean-testing-pr.sh` takes a PR number `NNNN` as argument,
  and attempts to merge the branch `lean-pr-testing-NNNN` into `master`.
  It will resolve conflicts in `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json`.
  If there are more conflicts, it will bail.

**Managing downstream repos**
- `downstream_repos.yml` contains basic information about significant downstream repositories.
- `downstream-tags.py` is a script to check whether a given tag exists on the downstream
  repositories listed in `downstream_repos.yml`.
- `downstream_dashboard.py` inspects the CI infrastructure of each repository in
  `downstream_repos.yml` and makes actionable suggestions for improvement or automation.

**Managing and tracking technical debt**
- `technical-debt-metrics.sh`
  Prints information on certain kind of technical debt in Mathlib.
  This output is automatically posted to zulip once a week.
- `long_file_report.sh`
  Prints the list of the 10 longest Lean files in `Mathlib`.
  This output is automatically posted to zulip once a week.

**Mathlib tactics**
- `polyrith_sage.py`, `polyrith_sage_helper.py` are required for `polyrith`
  to communication with the Sage server.

**Data files with linter exceptions**
- `nolints.json` contains exceptions for all `env_linter`s in mathlib.
  For permanent and deliberate exceptions, add a `@[nolint lintername]` in the .lean file instead.
- `nolints_prime_decls.txt` contains temporary exceptions for the `docPrime` linter

Both of these files should tend to zero over time;
please do not add new entries to these files. PRs removing (the need for) entries are welcome.

**API surrounding CI**
- `parse_lake_manifest_changes.py` compares two versions of `lake-manifest.json` to report
  dependency changes in Zulip notifications. Used by the `update_dependencies_zulip.yml` workflow
  to show which dependencies were updated, added, or removed, with links to GitHub diffs.
- `update_PR_comment.sh` is a script that edits an existing message (or creates a new one).
  It is used by the `PR_summary` workflow to maintain an up-to-date report with a searchable history.
- `get_tlabel.sh` extracts the `t-`label that a PR has (assuming that there is exactly one).
  It is used by the `maintainer_merge` family of workflows to dispatch `maintainer merge` requests
  to the appropriate topic on zulip.
- `count-trans-deps.py`, `import-graph-report.py` and `import_trans_difference.sh` produce various
  summaries of changes in transitive imports that the `PR_summary` message incorporates.
- `zulip_emoji_reactions.py` is called
  * every time a `bors d`, `bors merge` or `bors r` comment is added to a PR,
  * whenever bors merges a PR,
  * whenever a PR is closed or reopened
  * whenever a PR is labelled or unlabelled with `awaiting-author` or `maintainer-merge`
  It looks through all zulip posts containing a reference to the relevant PR
  and will post or update an emoji reaction corresponding to the current PR state to the message.
  This reaction is ✌️ (`:peace_sign:`) for delegated, `:bors:` for PRs sent to bors,
  `:merge` for merged PRs, ✍️ (`:writing:`) for PRs awaiting-author,
  🔨 (`:hammer:`) for maintainer-merged PRs and `:closed-pr:` for closed PRs.
  PRs which were migrated to a fork (as indicated by the `migrated-to-fork` label)
  additionally receive a reaction ... (`skip_forward`).
  Two of these are custom emojis configured on zulip.
- `late_importers.sh` is the main script used by the `latest_import.yml` action: it formats
  the `linter.minImports` output, summarizing the data in a table.  See the module docs of
  `late_importers.sh` for further details.
- `maintainer_merge_message.sh` contains a shell script that produces the Zulip message for a
  `maintainer merge`/`maintainer delegate` comment.

**Docker images**
- `docker_build.sh` builds the `lean4`, `gitpod4`, and `gitpod4-blueprint` Docker images.
  These are used by some CI workflows, as well as places such as Gitpod.
- `docker_push.sh` first runs `docker_build.sh`, and then pushes the images to Docker Hub,
  appropriately tagged with the date on which the images were built.
  This should be re-run after breaking changes to `elan`, so that CI and Gitpod have access to
  updated versions of `elan`.
