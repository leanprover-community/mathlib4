/-
This is the `Linter`s file: it only imports files defining linters and is
intended to be imported fairly early in `Mathlib`.

This file is ignored by `Shake`:
* it is in `ignoreAll`, meaning that all its imports are considered necessary;
* it is in `ignoreImport`, meaning that where it is imported, it is considered necessary.
-/

import Mathlib.Tactic.Lint
