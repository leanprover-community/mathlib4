/-
Copyright (c) 2024 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Mathlib.Command.SyntaxRules.Elab

/-! # `syntax_rules_header`

Instead of manually attaching `@[syntax_rules_header_impl]` to each implementation, we can actually
use a syntax rules command to do so. E.g., to implement `foo_rules : id`, we might write

```lean
syntax (name := fooRulesStx) "foo_rules" ":" ident : syntaxRulesHeader

syntax_rules_header
| `(fooRulesStx|foo_rules : $id:ident) => do
  ...
  return (data : SyntaxRulesData)
```
-/

open Lean Elab

/-- Define an implementation for a syntax rules command. TODO: docs -/
syntax (name := syntaxRulesHeaderCmd) "syntax_rules_header" : syntaxRulesHeader

/-- Bootstrap `@[syntax_rules_header_impl]` to `syntax_rules_header` syntax so that we never have
to use `@[syntax_rules_header_impl]` when defining syntax rules commands directly. -/
@[syntax_rules_header_impl syntaxRulesHeaderCmd]
def syntaxRulesHeaderImpl : ToSyntaxRulesData
  | `(syntaxRulesHeaderCmd|syntax_rules_header) => return {
      type := ``ToSyntaxRulesData
      attrName := `syntax_rules_header_impl
      termOfAlts := fun alts => `(term|fun $alts:matchAlt*)
      fallbackTerm := `(term|throwUnsupportedSyntax)
      cmdName := "syntax_rules_header"
      auxDefName := `syntaxRulesHeaderImpl
    }
  | _ => throwUnsupportedSyntax
