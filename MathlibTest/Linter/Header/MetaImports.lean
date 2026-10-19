module

public meta import Lean.Elab.Command
import all Mathlib.Tactic.Linter.Header

/-! Tests for the development-tool meta-import policy. -/

open Lean Elab Command Mathlib.Linter

-- Parse source headers without loading their modules. This also tests that comments, whitespace,
-- and import modifiers are handled by Lean's parser rather than by line-based matching.
run_meta do
  let cases := #[
    ("import ImportGraph", true),
    ("module\nimport ImportGraph.Tools", true),
    ("module\npublic import ImportGraph.Tools", true),
    ("module\nimport all ImportGraph.Tools", true),
    ("module\npublic import all LeanSearchClient", true),
    ("module\npublic /- comment -/ import\n LeanSearchClient.Basic", true),
    ("module\nmeta import ImportGraph.Tools", false),
    ("module\npublic meta import ImportGraph.Tools", false),
    ("module\nmeta import all LeanSearchClient", false),
    ("module\npublic meta import all LeanSearchClient.Basic", false),
    ("module\nimport ImportGraphExtra", false),
    ("module\nimport Other.ImportGraph", false),
    ("module\nimport Mathlib.Tactic.Basic", false),
    ("module\n/- import ImportGraph -/\n-- import LeanSearchClient\n", false)]
  for (source, expected) in cases do
    let imports := (← parseImports' source "test header").imports
    unless imports.any isNonMetaToolImport == expected do
      throwError "Unexpected meta-import check result for {source}"

/-- Check synthetic imports using the same diagnostics as the header linter. -/
private meta def testMetaImports : CommandElabM Unit := do
  let bad ← `(Parser.Module.import| public import $(mkIdent `ImportGraph.Tools))
  let good ← `(Parser.Module.import| public meta import $(mkIdent `LeanSearchClient))
  let header ← `(Parser.Module.header| module $bad:import $good:import)
  metaImportsCheck (headerToImportRefs header)

/--
warning: `ImportGraph.Tools` is a development-tool dependency and must be imported using `meta import`.

Note: This linter can be disabled with `set_option linter.metaImports false`
-/
#guard_msgs in
run_cmd testMetaImports

#guard_msgs in
set_option linter.metaImports false in
run_cmd testMetaImports
