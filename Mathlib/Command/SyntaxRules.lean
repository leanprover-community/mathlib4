/-
Copyright (c) 2024 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Mathlib.Command.SyntaxRules.Attr
import Mathlib.Command.SyntaxRules.Elab
import Mathlib.Command.SyntaxRules.Header
import Mathlib.Command.SyntaxRules.Util

/-!

# Syntax rules

This file provides an API for implementing commands of the form
```lean
foo_rules : bar
| `(node|stx₁) => ...
| `(node|stx₂) => ...
```
which, like `macro_rules` and `elab_rules`, allow the user to supply match alts on syntax
quotations to some end. The rules supplied to `foo_rules` are stored in an environment extension;
what this environment extension is actually used for is entirely arbitrary.

## Usage

The core of any `foo_rules` command is a `KeyedDeclsAttribute` used to tag declarations while
keying them by some `Name`. Usually this name is a `SyntaxNodeKind` (but can in principle be any
`Name`). (This is how `macro_rules` and `elab_rules` work as well.)

To create your own `foo_rules` command, you must do two things:

1. Register the desired header syntax in the `syntaxRulesHeader` syntax category: for example,
  `syntax (name := fooRulesStx) "foo_rules" (":" ident)? : syntaxRulesHeader`
2. Supply an instance of `SyntaxRulesData` for a given header syntax via `syntax_rules_header`.
  This will contain all of the data needed to apply the command, such as which attribute to use,
  what the type of the tagged declaration should be, etc. (See below.)

To supply such an instance, match on the header syntax:

```lean
syntax_rules_header
| `(syntaxRulesHeader|foo_rules)       => return (data1 : SyntaxRulesData)
| `(syntaxRulesHeader|foo_rules : $id) => return (data2 : SyntaxRulesData)
```
Note that we match on the syntax of the *header* of the command, and do *not* include the match
alts. The match alts are taken care of by the `SyntaxRules` infrastructure.

Note also that different header syntax can affect the implementation as desired. In the above,
since the `: ident` part of the header syntax was optional, we're able to implement `foo_rules` and
`foo_rules : $id` differently.

After this, macros defined around `syntaxRulesHeader` allow users to invoke `foo_rules`. E.g.

```lean
foo_rules : abc
| `(node|bar) => ...
| `(node|baz) => ...
...
```

Every invocation of `foo_rules` creates an auxiliary declaration tagged by a chosen attribute. For
example, the above might (depending on the specifics of the implementation provided in
`SyntaxRulesData`) produce a declaration like

```lean
@[foo_impl_attr node]
def aux.fooRules.1234 : FooType := fun
  | `(node|bar) => ...
  | `(node|baz) => ...
```

This declaration can then be returned when evaluating ``fooImplAttr.getValues env `node`` in
other code.

For example, you might be building a related tactic that takes some user-supplied
argument, e.g. `foo_tac term`, and during `foo_tac` you want to traverse the syntax of `term` and
at each node apply all of the `foo_rules` that the user had supplied earlier. Or you might be
building a command, or a widget, or anything else—as long as it can access the environment your
attribute's extension lives in, you can make use of the attribute (and the new decls) however you
wish.

Note that the declarations don't need to be of the above form (
``fun | `(node|bar) => ... | `(node|baz) => ...``); the match alts can be passed to anything that
takes match alts, such as a `match` clause.

### `SyntaxRulesData`

So, what is actually necessary to define an implementation of some `foo_rules` command? The fields
of `SyntaxRulesData` are sufficient. Recall that this information is used to turn a user-facing
command invocation like
```
foo_rules : id
| `(node|barStx) => barVal
| `(node|bazStx) => bazVal
```
into a tagged declaration like

```lean
@[foo_impl_attr node]
def aux.fooRules.1234 : FooType := fun
  | `(node|barStx) => barVal
  | `(node|bazStx) => bazStx
```

* `type : Name`: the name of the type of the declaration. In the example above, this is `FooType`.
  For technical reasons, this needs to be a name, not a `Sort`. Using an `abbrev` is typical, and
  by default, if `type` is an `abbrev`, it will be unfolded. (To prevent this behavior, use
  `unfoldAbbrev := false`.) (Note: this could be generalized to term syntax instead of a `Name`.)
* ```termOfAlts : Array (TSyntax ``Term.matchAlt) → CommandElabM Term```: this forms the body of
  the declaration from the `matchAlts` supplied to `foo_rules` (after some preprocessing to split
  out different node types). To produce the body in the example, we'd use
  ``termOfAlts := fun alts => `(term|fun alts:matchAlts*)``. The result (e.g.
  `fun alts:matchAlts*`, in this case) is elaborated with type `type`. Note that using `match`
  instead of `fun` (or anything else that accepts `matchAlts`) as appropriate is perfectly fine.
* `attrName : Name`: the name of the attribute, here `` `foo_impl_attr ``. This will be
  syntactically inserted into `@[]` followed by the key. This should likely by a
  `KeyedDeclsAttribute`, but can in principle be any attribute.
* ``mkAttr : Option ((attr node : Name) → CommandElabM (TSyntax `attr)) := none``: If this is
  `none` (as it is by default), we simply pass the `SyntaxNodeKind` as a parameter to the
  attribute, e.g. `@[foo_impl_attr node]`. Sometimes, however, we want to e.g. key by other names
  (for example, by a name pair consisting of the syntax node plus some category name supplied in
  the header syntax), or pass extra parameters to the attribute. In that case, we will use the
  value of `← mkAttr attrName node` as the attribute syntax. (Any `attrKind` such as `local` is
  handled automatically, and need not be considered here.)
* `cmdName : String`: this simply specifies how to refer to the command in error messages (e.g.
  `"foo_rules"`)
* `auxDefName : Name`: this is simply included in the name of the auxiliary declaration, and has no
  other impact. It's simply helpful to see if you have to debug and encounter one of these
  declarations later on. Here it might be simply `fooRules`.
* `unfoldTypeAbbrev := true`: determines whether to unfold `type` once if it is an `abbrev`.

## Implementation

This is implemented via

* an (extensible) syntax category `syntaxRulesHeader` for custom headers like `foo_rules : bar`
* syntax `syntax_rules (header := $header) (kind := $kind?)`, where `$header:syntaxRulesHeader` is
  the user-facing syntax (e.g. `foo_rules : bar`)
* a macro from `syntaxRulesHeader matchAlts` to this internal `syntax_rules` syntax
* an attribute ``@[syntax_rules_header_impl fooRulesHeader]`` on definitions
  ``fooRulesImpl : TSyntax `fooRulesHeader → CommandElabM SyntaxRuleData`` which lets us elaborate
  in a `$header`-dependent way
* a convenient bootstrapped wrapper `syntax_rules_header` for the attribute
  `syntax_rules_header_impl` so that we can use syntax rules to implement behavior for the headers
  of syntax rules
* a structure `SyntaxRuleData` which contains all data necessary for implementing the command,
  including, crucially, the name of an attribute `foo_impl_attr` which `syntax_rules` attaches to
  definitions constructed from the match alts with the syntax nodekind as a parameter (e.g.
  `@[foo_impl_attr tacticMyTacNode]`)

-/
