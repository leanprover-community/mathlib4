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
-- The `deprecatedNoSince` linter ensures all deprecation tags come with dates.
-- This convention is used beyond mathlib; this linter need not be... hmm.
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

/-
## OUTLOOK: future linters, their state and where to place them

The `longFile` checks for long files: this rewrites a text-based style linter as a syntax linter.
It will be enabled in all of mathlib, but disabled by default. Developed in #15610.

The `moduleDocstring` linter checks if every file has a module docstring: this is currently
blocked on some implementation questions. (There is a text-based Python linter enforcing this
check now.) While this is useful for downstream projects, the linter is enabled only on mathlib
and disabled by default.

The `assertNotExists` style linter verifies that `assert_not_exists` declarations appear
at the *beginning* of every file: this is a stylistic choice, hence this linter is only enabled in
mathlib.
Its sibling verifies that every declaration in an `assert_not_exists` command eventually exists:
this *should* be enabled globally (unless its performance is prohibitive). Development of both
is still in progress.

The `confusingVariables` linter warns about a certain bug in the handling of `variable`s
which can lead to confusing error messages. This is advised against in the Lean core documentation;
perhaps this linter would be useful to have globally.
Its implementation (in #15400) is still in progress; currently, the linter has both false positives
and false negatives.

The `decidableEq` and `finiteFintype` linters are environment linters, so need not be imported
in this file. They mostly work, but have about 50 false positives in mathlib. They are under
development in PR #xxx.
The `openClassicalLinter` is a syntax linter, so should be imported here. It is not fully certain
if that linter will land; it is implemented in #15454. About 200 instances in mathlib still need
to be fixed.
Both of these linters will be enabled in mathlib, but might be disabled globally. That can
(and will) still be decided later.

The `multigoal` linter warns if multiple goals are present without being appropropriately focused.
This is purely a style question, but might be a useful setting outside of mathlib.
It is disabled by default, but enabled in mathlib (and we recommend other projects enable it).
Under review in #12339; current waiting for its author to address review comments.

There is a converse linter, ensuring proofs are not *unnecessarily* focused; this is in progress
in #12414. It depends on the above linter, and will require a fair amount of tweaks to mathlib
(which are probably best automated).

The `flexible` linter generalises the check for non-terminal simps. It is quite useful,
but also flags about 200 instances in mathlib where there is no obvious and nice fix.
Therefore, it is disabled by default in mathlib. It need not be imported here.
It is developed at #11821; PR #13813 annotates all current exceptions.
(But in Tactic.Basic instead? Tactic.Common? Not at all?)

The `terminalRefine` linter checks for proofs ending in `refine` (which could be `exact`).
Automatically replacing this can lead to a slow-down, which is why this linter is disabled
by default (even in mathlib). Developed in #11890.

The `pedantic` linter checks for expressions whose formatting does not match how they are
pretty-printed. Occasionally, its suggestions are bogus, but often, they are useful.
the linter is under development at 15535 and will be disabled by default.

The `papercut` linter (developed in #13999) warns on certain features of Lean which can be
confusing to newcomers, such as natural number subtraction. It will be disabled by default;
downstream projects (such as those focused on teaching) can enable it individually.

The checkAsSorry linter will land off by default (also in mathlib, if at all):
its purpose is to help ensuring that a project compiles under the `debug.checkAsSorry` option.
The `repeatedTypeclass` linter is still an experiment (in #14731); probably, it will start out
by being mathlib-specific. Its reports can be useful, but also slightly awkward to fix.



**Not** imported in this file are
- all linters in `Linters/TextBased.lean`, as these are text-based, so can be imported later

- the `minImports` linter, as that is still disabled by default.
It *does* check a useful global coherence property, so perhaps changing this default at some
point can be useful. `mathlib` might need a fair amount of fixes for this to become viable, though.

-/
