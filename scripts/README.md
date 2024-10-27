## Miscellaneous scripts for working on mathlib

This directory contains miscellaneous scripts that are useful for working on or with mathlib.
When adding a new script, please make sure to document it here, so other readers have a chance
to learn about it as well!

**Current scripts and their purpose.**
TODO: add real content for all these entries!

Part of mathlib
- `polyrith_sage.py`, `polyrith_sage_helper.py`

Part of CI workflow
- `mk_all.lean`
- `lint-style.py` and `lint-style.lean`, `print-style-errors.sh`
- `lint-bib.sh`
- `yaml_check.py`, `check-yaml.lean`

Managing and tracking technical debt
- `update_nolints_CI.sh` (maintenance, runs once a week)
- `technical-debt-metrics.sh`
- `init_creation.sh` (supposed to be run manually; might be removed soon?)

- `create-adaptation-pr.sh`, `lean-pr-testing-comments.sh`

- `bench_summary.lean`, `autolabel.lean`, `get_tlabel.sh`

- `install_debian.sh`, `install_macos.sh`

- `declarations_diff.sh`, `count-trans-deps.py`, `import_trans_difference.sh`, `update_PR_comment.sh`;
`import-graph-report.py`


Data files with exclusions for style linters: all of these should tend to zero over time
- `nolints.json`: TODO document!
- `no_lints_prime_decls.txt`: TODO document this

Other
- `fix_unused.py`
