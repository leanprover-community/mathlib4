/-
See the module docstring below for guidelines on this file's imports.

These are all syntax linters defined in Mathlib which are active in Mathlib by default.
Syntax linters need to be imported to take effect, hence we would like them to be imported
as early as possible.
All these linters have no bulk imports; any import outside of `Lean` is explained below.

**Not** imported in this file are
- the text-based linters in `Linters/TextBased.lean`, as they can be imported later
- the `minImports` linter, as that is still disabled by default.
It *does* check a useful global coherence property, so perhaps changing this default at some
point can be useful. `mathlib` might need a fair amount of fixes for this to become viable, though.
-- XXX: the `haveLet` linter could also be imported here...

-/

import Mathlib.Tactic.Linter.HashCommandLinter
import Mathlib.Tactic.Linter.GlobalAttributeIn
-- This file imports Batteries.Tactic.Lint, where the `env_linter` attribute is defined.
import Mathlib.Tactic.Linter.Lint
import Mathlib.Tactic.Linter.OldObtain
import Mathlib.Tactic.Linter.RefineLinter
import Mathlib.Tactic.Linter.UnusedTactic
import Mathlib.Tactic.Linter.Style

/-!
This is the root file in Mathlib: it is imported by virtually *all* Mathlib files.

For this reason, the imports of this files are carefully curated.
Any modification involving a change in the imports of this file should be discussed beforehand.

Here are some general guidelines:
* no bucket imports (e.g. `Batteries`/`Lean`/etc);
* every import needs to have a comment explaining why the import is there;
* strong preference for avoiding files that themselves have imports beyond `Lean`, and
  any exception to this rule should by accompanied by a comment explaining the transitive imports.
-/
