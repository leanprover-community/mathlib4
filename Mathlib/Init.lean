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

-- These are all syntax linters defined in Mathlib which are active in Mathlib by default.
-- Syntax linters need to be imported to take effect, hence we would like them to be imported
-- as early as possible.
-- All these linters have no bulk imports; any import outside of `Lean` is explained below.

-- This linter checks for surprising syntax in Lean, and is active by default.
import Mathlib.Tactic.Linter.GlobalAttributeIn
-- This linter warns about unused tactics: occasionally, a new tactic needs to be excluded
-- using #allow_unused_tactic (as in `#allow_unused_tactic Lean.Parser.Tactic.done`),
-- but other that this, a warning usually indicates code that ought to be fixed.
-- This linter is also active by default.
import Mathlib.Tactic.Linter.UnusedTactic

-- The hash command linter warns about #commands in the source file which emit no message
-- (except for manual exceptions): these are usually meant for debugging.
-- This linter is on by default in Mathlib.
import Mathlib.Tactic.Linter.HashCommandLinter

-- The following linters are "restriction lints": they warn about a particular idiom,
-- where there are better alternatives. As this is somewhat subjective,
-- they are only enabled in mathlib (and the Archive and Counterexamples).
import Mathlib.Tactic.Linter.AdmitLinter
import Mathlib.Tactic.Linter.OldObtain
import Mathlib.Tactic.Linter.RefineLinter



-- uncat!

-- uncat!


-- All these linters are meant to run on all of mathlib,
-- are syntax linters active by default (no need to be imported as early as possible),
-- and have no imports beyond `Lean` unless noted below.



-- This file imports Batteries.Tactic.Lint, where the `env_linter` attribute is defined.
import Mathlib.Tactic.Linter.Lint


import Mathlib.Tactic.Linter.Style
