/-
This is the `Linter`s file: it imports files defining linters.
All syntax linters enabled by default are imported in `Mathlib.Init`;
this file contains all other linters.

This file is ignored by `shake`:
* it is in `ignoreAll`, meaning that all its imports are considered necessary;
* it is in `ignoreImport`, meaning that where it is imported, it is considered necessary.
-/

import Mathlib.Tactic.Linter.HaveLetLinter
import Mathlib.Tactic.Linter.MinImports
import Mathlib.Tactic.Linter.TextBased
