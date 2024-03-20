/-
Copyright (c) 2024 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Mathlib.Command.SyntaxRules.Elab

/-! # `syntax_rules_header`

Instead of manually attaching `@[syntax_rules_header_impl]` to each implementation, we can actually use a `syntax_rules`-based command to do so. E.g., to implement `foo_rules : id`, we might write

```lean
syntax (name := fooRulesStx) "foo_rules" ":" ident : syntaxRulesHeader

syntax_rules_header
| `(fooRulesStx|foo_rules : $id:ident) => do
  ...
  return (data : SyntaxRuleData)
```
-/

open Lean Elab

syntax (name := syntaxRulesHeaderCmd) "syntax_rules_header" : syntaxRulesHeader

@[syntax_rules_header_impl syntaxRulesHeaderCmd]
def syntaxRulesHeaderImpl : ToSyntaxRuleData
  | `(syntaxRulesHeaderCmd|syntax_rules_header) => return {
      type := ``ToSyntaxRuleData
      attrName := `syntax_rules_header_impl
      termOfAlts := fun alts => `(term|fun $alts:matchAlt*)
      cmdName := "syntax_rules_header"
      auxDefName := `syntaxRulesHeaderImpl
    }
  | _ => throwUnsupportedSyntax
