/-
Copyright (c) 2024 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Mathlib.Command.SyntaxRules.Attr
import Mathlib.Command.SyntaxRules.Elab
import Mathlib.Command.SyntaxRules.Header
import Mathlib.Command.SyntaxRules.Util

--TODO: does this module doc belong here?


/-!

# `syntax_rules`

`syntax_rules` is an *internal* command used to implement commands of the form
```lean
foo_rules : bar
| `(node|stx₁) => ...
| `(node|stx₂) => ...
```

This is implemented via
* an (extensible) syntax category `syntaxRulesHeader` for custom headers like `foo_rules : bar`
* syntax `syntax_rules (header := $header) (kind := $kind?)`, where `$header:syntaxRulesHeader` is
  the user-facing syntax (e.g. `foo_rules : bar`)
* a macro from `syntaxRulesHeader matchAlts` to this internal `syntax_rules` syntax
* an attribute ``@[syntax_rules_header fooRulesHeader]`` on definitions
  ``fooRulesImpl : TSyntax `fooRulesHeader → CommandElabM SyntaxRuleData`` which lets us elaborate
  in a `$header`-dependent way
* a structure `SyntaxRuleData` which contains all data necessary for implementing the command,
  including, crucially, the name of an attribute `foo_rule` which `syntax_rules` attaches to
  definitions constructed from the match alts with the syntax nodekind as a parameter (e.g.
  `@[foo_rule tacticMyTacNode]`)

TODO: explain the other fields of `SyntaxRuleData`; give example implementation; clarify *when*
these definitions are used

-/
