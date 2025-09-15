import Lean.Linter.Sets -- for the definition of linter sets
import Mathlib.Tactic.Linter.CommandStart
import Mathlib.Tactic.Linter.DeprecatedSyntaxLinter
import Mathlib.Tactic.Linter.DirectoryDependency
import Mathlib.Tactic.Linter.DocPrime
import Mathlib.Tactic.Linter.DocString
import Mathlib.Tactic.Linter.GlobalAttributeIn
import Mathlib.Tactic.Linter.HashCommandLinter
import Mathlib.Tactic.Linter.Header
-- This linter is disabled by default, but downstream projects may want to enable it:
-- to facilitate this, we import the linter here.
import Mathlib.Tactic.Linter.FlexibleLinter
-- This file imports Batteries.Tactic.Lint, where the `env_linter` attribute is defined.
import Mathlib.Tactic.Linter.Lint
import Mathlib.Tactic.Linter.Multigoal
import Mathlib.Tactic.Linter.OldObtain
-- The following import contains the environment extension for the unused tactic linter.
import Mathlib.Tactic.Linter.UnusedTacticExtension
import Mathlib.Tactic.Linter.UnusedTactic
import Mathlib.Tactic.Linter.Style
-- This import makes the `#min_imports` command available globally.
import Mathlib.Tactic.MinImports
import Mathlib.Tactic.TacticAnalysis.Declarations

/-!
This is the root file in Mathlib: it is imported by virtually *all* Mathlib files.
For this reason, the imports of this file are carefully curated.
Any modification involving a change in the imports of this file should be discussed beforehand.

Here are some general guidelines:
* no bucket imports (e.g. `Batteries`/`Lean`/etc);
* every import needs to have a comment explaining why the import is there;
* strong preference for avoiding files that themselves have imports beyond `Lean`, and
  any exception to this rule should be accompanied by a comment explaining the transitive imports.

A linter verifies that every file in Mathlib imports `Mathlib.Init`
(perhaps indirectly) --- except for the imports in this file, of course.

## Linters

All syntax linters defined in Mathlib which are active by default are imported here.
Syntax linters need to be imported to take effect, hence we would like them to be imported
as early as possible.

All linters imported here have no bulk imports;
**Not** imported in this file are
- the text-based linters in `Linters/TextBased.lean`, as they can be imported later
- the `haveLet` linter, as it is currently disabled by default due to crashes
- the `ppRoundTrip` linter, which is currently disabled (as this is not mature enough)
- the `minImports` linter, as that linter is disabled by default (and has an informational function;
  it is useful for debugging, but not as a permanently enabled lint)
- the `upstreamableDecls` linter, as it is also mostly informational

-/

/-- Define a linter set of all mathlib syntax linters which are enabled by default.

Projects depending on mathlib can use `set_option linter.allMathlibLinters true` to enable
all these linters, or add the `weak.linter.mathlibStandardSet` option to their lakefile.
-/
register_linter_set linter.mathlibStandardSet :=
  linter.allScriptsDocumented
  linter.checkInitImports
  linter.hashCommand
  linter.oldObtain
  linter.style.cases
  linter.style.refine
  linter.style.commandStart
  linter.style.cdot
  linter.style.docString
  linter.style.dollarSyntax
  linter.style.lambdaSyntax
  linter.style.header
  linter.style.longLine
  linter.style.longFile
  linter.style.multiGoal
  linter.style.nativeDecide
  linter.style.openClassical
  linter.style.missingEnd
  linter.style.setOption
  linter.style.show
  linter.style.maxHeartbeats
  -- The `docPrime` linter is disabled: https://github.com/leanprover-community/mathlib4/issues/20560

/-- Define a set of linters that are used in the `nightly-testing` branch
to catch any regressions.
-/
register_linter_set linter.nightlyRegressionSet :=
  linter.tacticAnalysis.linarithToGrind
  linter.tacticAnalysis.omegaToGrind
  linter.tacticAnalysis.ringToGrind

-- Check that all linter options mentioned in the mathlib standard linter set exist.
open Lean Elab.Command Linter Mathlib.Linter Mathlib.Linter.Style

run_cmd liftTermElabM do
  let DefinedInScripts : Array Name :=
    #[`linter.checkInitImports, `linter.allScriptsDocumented]
  let env ← getEnv
  let ls := linterSetsExt.getEntries env
  let some (_, mlLinters) := ls.find? (·.1 == ``linter.mathlibStandardSet) |
    throwError m!"'linter.mathlibStandardSet' is not defined."
  for mll in mlLinters do
    let [(mlRes, _)] ← realizeGlobalName mll |
      if !DefinedInScripts.contains mll then
        throwError "Unknown option '{mll}'!"
    let some cinfo := env.find? mlRes | throwError "{mlRes}: this code should be unreachable."
    if !cinfo.type.isAppOf ``Lean.Option then
      throwError "{.ofConstName mlRes} is not an option, it is a{indentD cinfo.type}"
