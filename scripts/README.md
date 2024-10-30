## Miscellaneous scripts for working on mathlib

This directory contains miscellaneous scripts that are useful for working on or with mathlib.
When adding a new script, please make sure to document it here, so other readers have a chance
to learn about it as well!

**Current scripts and their purpose.**
TODO: add real content for all these entries!

Installation scripts
- `install_debian.sh`, `install_macos.sh`
  Install scripts referenced from the leanprover community install pages.
  https://leanprover-community.github.io/install/debian.html
  https://leanprover-community.github.io/install/macos.html
  If these web pages are deprecated or removed, we should remove these scripts.

CI workflow
- `mk_all.lean`
  run via `lake exe mk_all`, regenerates `Mathlib.lean`
- `lint-style.py` and `lint-style.lean`, `print-style-errors.sh`
  style linters, written in Python and Lean.
- `lint-bib.sh`
  normalize the BibTeX file `docs/references.bib` using `bibtool`.
- `yaml_check.py`, `check-yaml.lean`
  Sanity checks for `undergrad.yaml`, `overview.yaml`, and `100.yaml`.
- `lean-pr-testing-comments.sh`
  Generate comments and labels on a Lean or Batteries PR after CI has finished on a
  `*-pr-testing-NNNN` branch.
- `update_nolints_CI.sh` (maintenance, runs once a week)
- `bench_summary.lean`
  Convert data retrieved from the speed-center into a shorter, more accessible format,
  and post a comment with this summary on github.
- `declarations_diff.sh`
  Attempts to find which declarations have been removed and which have been added in the current PR
  with respect to `master`, and posts a comment on github with the result.

Managing nightly-testing and bump branches
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

Managing and tracking technical debt
- `technical-debt-metrics.sh`
- `init_creation.sh` (supposed to be run manually; might be removed soon?)

Mathlib tactics
- `polyrith_sage.py`, `polyrith_sage_helper.py` are required for `polyrith`
  to communication with the Sage server.

Data files with exclusions for style linters: all of these should tend to zero over time
- `nolints.json`: TODO document!
- `no_lints_prime_decls.txt`: TODO document this

Tool for manual maintenance
- `fix_unused.py`
  Bulk processing of unused variable warnings, replacing them with `_`.

Other / uncategorized
- `autolabel.lean`, `get_tlabel.sh`
- `count-trans-deps.py`
- `import_trans_difference.sh`
- `update_PR_comment.sh`
- `import-graph-report.py`
