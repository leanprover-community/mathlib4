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

**Tool for manual maintenance**
- `fix_unused.py`
  Bulk processing of unused variable warnings, replacing them with `_`.
- `add_deprecations.sh` is a text-based script that automatically adds deprecation statements.
  It assumes that the only difference between master and the current status of the PR consists
  of renames. More precisely, any change on a line that contains a declaration name
  and is not a rename, will likely confuse the script.

**Analyzing Mathlib's import structure**
- `unused_in_pole.sh` (followed by an optional `<target>`, defaulting to `Mathlib`)
  calls `lake exe pole --loc --to <target>` to compute the longest
  pole to a given target module, and then feeds this into
  `lake exe unused` to analyze transitively unused imports.
  Generates `unused.md` containing a markdown table showing the unused imports,
  and suggests `lake exe graph` commands to visualize the largest "rectangles" of unused imports.

**CI workflow**
- `mk_all.lean`
  run via `lake exe mk_all`, regenerates the import-only files
  `Mathlib.lean`, `Mathlib/Tactic.lean`, `Archive.lean` and `Counterexamples.lean`
- `lint-style.lean`, `lint-style.py`, `print-style-errors.sh`
  style linters, written in Python and Lean. Run via `lake exe lint-style`.
  Medium-term, the latter two scripts should be rewritten and incorporated in `lint-style.lean`.
- `lint-bib.sh`
  normalize the BibTeX file `docs/references.bib` using `bibtool`.
- `yaml_check.py`, `check-yaml.lean`
  Sanity checks for `undergrad.yaml`, `overview.yaml`, and `100.yaml`.
- `lean-pr-testing-comments.sh`
  Generate comments and labels on a Lean or Batteries PR after CI has finished on a
  `*-pr-testing-NNNN` branch.
- `update_nolints_CI.sh`
  Update the `nolints.json` file to remove unneeded entries. Automatically run once a week.
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

**Managing and tracking technical debt**
- `technical-debt-metrics.sh`
  Prints information on certain kind of technical debt in Mathlib.
  This output is automatically posted to zulip once a week.
- `init_creation.sh`
  makes sure that every file in Mathlib transitively imports `Mathlib.init`
  This may be removed soon, and replaced by a different mechanism.

**Mathlib tactics**
- `polyrith_sage.py`, `polyrith_sage_helper.py` are required for `polyrith`
  to communication with the Sage server.

**Data files with linter exceptions**
- `nolints.json` contains exceptions for all `env_linter`s in mathlib.
  For permanent and deliberate exceptions, add a `@[nolint lintername]` in the .lean file instead.
- `no_lints_prime_decls.txt`
  contains temporary exceptions for the `docPrime` linter

Both of these files should tend to zero over time;
please do not add new entries to these files. PRs removing (the need for) entries are welcome.

**API surrounding CI**
- `update_PR_comment.sh` is a script that edits an existing message (or creates a new one).
  It is used by the `PR_summary` workflow to maintain an up-to-date report with a searchable history.
- `get_tlabel.sh` extracts the `t-`label that a PR has (assuming that there is exactly one).
  It is used by the `maintainer_merge` family of workflows to dispatch `maintainer merge` requests
  to the appropriate topic on zulip.
- `count-trans-deps.py`, `import-graph-report.py` and `import_trans_difference.sh` produce various
  summaries of changes in transitive imports that the `PR_summary` message incorporates.
