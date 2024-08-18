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

-- The `structureInType` and `dupNamespace` linters check for two features which are useful
-- when designing a large library. They are enabled by default since their warnings usually
-- indicate code that ought to be fixed.
--
-- This file imports Batteries.Tactic.Lint, where the `env_linter` attribute is defined.
-- The environment linter *could* be split out, if desired.
import Mathlib.Tactic.Linter.Lint

-- This linter warns about unused tactics: occasionally, a new tactic needs to be excluded
-- using #allow_unused_tactic (as in `#allow_unused_tactic Lean.Parser.Tactic.done`),
-- but other that this, a warning usually indicates code that ought to be fixed.
-- This linter is also active by default.
import Mathlib.Tactic.Linter.UnusedTactic

-- The `haveLet` linter warns on `have`s introducing hypotheses whose type is not Prop:
-- `have` will erase access to this data, which can be confusing.
-- By default, this linter only warnings on noisy declarations (i.e., in-progress proofs).
-- As that setting could be useful to outside projects, it is enabled by default.
import Mathlib.Tactic.Linter.HaveLetLinter

-- The following linters are "restriction lints": they warn about a particular idiom,
-- where there are better alternatives. As this is somewhat subjective,
-- they are only enabled in mathlib (and the Archive and Counterexamples).
import Mathlib.Tactic.Linter.AdmitLinter
import Mathlib.Tactic.Linter.OldObtain
import Mathlib.Tactic.Linter.RefineLinter

-- The hash command linter warns about #commands in the source file which emit no message
-- (except for manual exceptions): these are usually meant for debugging.
-- This linter is on by default in Mathlib.
import Mathlib.Tactic.Linter.HashCommandLinter

-- This file defines several linters about code style and formatting.
-- Other projects might find these useful, but these opinions are inherently subjective:
-- this is why they are disabled by default, but enabled in mathlib.
import Mathlib.Tactic.Linter.Style
