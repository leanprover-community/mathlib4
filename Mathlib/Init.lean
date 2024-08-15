/-
This is the root file in Mathlib: it is imported by virtually *all* Mathlib files.

For this reason, the imports of this files are carefully curated.
Any modification involving a change in the imports of this file should be discussed beforehand.

Here are some general guidelines:
* no bucket imports (e.g. `Batteries`/`Lean`/etc);
* every import needs to have a comment explaining why the import is there;
* strong preference for avoiding files that themselves have imports beyond `Lean`, and
  any exception to this rule should by accompanied by a comment explaining the transitive imports.
-/

-- All these linters are meant to run on all of mathlib, are active by default,
-- and have no imports beyond `Lean`.
import Mathlib.Tactic.Linter.OldObtain
import Mathlib.Tactic.Linter.RefineLinter
-- xxx: this file imports Batteries.Lean.HashSet; is this acceptable?
import Mathlib.Tactic.Linter.HashCommandLinter
import Mathlib.Tactic.Linter.GlobalAttributeIn
-- xxx: this file imports Batteries.Data.String.Matcher and Batteries.Tactic.Lint; acceptable?
import Mathlib.Tactic.Linter.Lint
-- xxx: this files imports Batterires.Tactic.Unreachable; is this acceptable?
import Mathlib.Tactic.Linter.UnusedTactic
import Mathlib.Tactic.Linter.Style
