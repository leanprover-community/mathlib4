# Public-import refactor progress

## Current state

- The working tree changes `public import` to `import` for modules initially selected as containing
  none of `def`, `abbrev`, `irreducible_def`, or `instance`.
- Directories `Mathlib/Tactic/` and `Mathlib/Util/` were restored, as requested.
- The build exposed public-API and tactic-syntax dependencies.  Required original re-export edges
  have been restored iteratively; no new imports were introduced.
- Current diff: 3,057 insertions and 3,057 deletions in 2,115 files. `git diff --check` passes.

## Validation status

`lake build` was stopped by the user while still running. It had reached target 8,336 of 8,677.
At that point the current log at `/tmp/public-import-removal-build.log` contained 25 failures.
Those diagnostics must be treated as incomplete, because the build had not finished.

## Resume procedure

1. Run the full build and wait for it to finish:

   ```bash
   lake build > /tmp/public-import-removal-build.log 2>&1
   ```

2. Extract every failed target, then inspect each target and the modules it `public import`s for
   changed import lines. Restore only those original lines from `import X` to `public import X`.
   This preserves the existing public-import graph instead of adding a new direct dependency.

3. Repeat until `lake build` succeeds. Useful diagnostics:

   ```bash
   rg '^✖ \[' /tmp/public-import-removal-build.log
   rg 'consider adding `public(?: meta)? import' /tmp/public-import-removal-build.log
   git diff --check
   ```

## Important caveat

The initial syntactic criterion is not sufficient to decide whether an import may be private.
For example, a module defining only a class, notation, syntax, or theorem can still be needed by
a public declaration in an importing module. Lean's build diagnostics are the authority for the
remaining required public re-exports.
