/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Tactic.Translate.Core

/-!
# The `@[to_differentiable]` attribute.

The `@[to_differentiable]` attribute is used to translate declarations about continuous
differentiability to counterparts about mere differentiability.
See the docstrings of `to_differentiable` for more information.

## TODO
This is just a prototype: this also needs to translate n in hypotheses, including instance ones!
-/

public meta section

namespace Mathlib.Tactic.ToDifferentiable
open Lean Elab Translate

/-- The attribute `to_differentiable` can be used to automatically transport thoerems
about continuous differentiability to counterparts about mere differentiability.

TODO: this is just copy-pasted and needs updating!
To use this attribute, just write:

```
@[to_differentiable]
theorem mul_comm' {α} [CommSemigroup α] (x y : α) : x * y = y * x := mul_comm x y
```

This code will generate a theorem named `add_comm'`. It is also
possible to manually specify the name of the new declaration:

```
@[to_differentiable add_foo]
theorem foo := sorry
```

An existing documentation string will _not_ be automatically used, so if the theorem or definition
has a doc string, a doc string for the additive version should be passed explicitly to
`to_differentiable`.

```
/-- Multiplication is commutative -/
@[to_differentiable /-- Addition is commutative -/]
theorem mul_comm' {α} [CommSemigroup α] (x y : α) : x * y = y * x := CommSemigroup.mul_comm
```

The transport tries to do the right thing in most cases using several
heuristics described below.  However, in some cases it fails, and
requires manual intervention.

Use the `(reorder := ...)` syntax to reorder the arguments in the generated additive declaration.
This is specified using cycle notation. For example `(reorder := α β, 5 6)` swaps the arguments
`α` and `β` with each other and the fifth and the sixth argument and `(reorder := 3 4 5)` will move
the fifth argument before the third argument. This is mostly useful to translate declarations using
`Pow` to those using `SMul`.

Use the `to_differentiable existing` syntax to use an existing additive declaration, instead of
automatically generating it. This attempts to autogenerate the `(reorder := ...)` argument.

Use the `(attr := ...)` syntax to apply attributes to both the multiplicative and the additive
version:

```
@[to_differentiable (attr := simp)] lemma mul_one' {G : Type*} [Group G] (x : G) : x * 1 = x := mul_one x
```

The `(rename := ...)` syntax can be used for specifying the argument names of the generated
declaration, overriding the automatic translation of names. For example, `(rename := x → a, y ↔ z)`
will translate `lemma mul_foo (x y z : α) ...` to `lemma add_foo (a z y : α) ...`.

## Implementation notes

TODO: this is just copy-pasted and needs updating!
The transport process generally works by taking all the names of
identifiers appearing in the name, type, and body of a declaration and
creating a new declaration by mapping those names to additive versions
using a simple string-based dictionary and also using all declarations
that have previously been labeled with `to_differentiable`. The dictionary is `ToAdditive.nameDict`
and can be found in the `Tactic.ToAdditive.GuessName` file. If you introduce a new name which
should be translated by `to_differentiable` you should add the translation to this dictionary.

In the `mul_comm'` example above, `to_differentiable` maps:
* `mul_comm'` to `add_comm'`,
* `CommSemigroup` to `AddCommSemigroup`,
* `x * y` to `x + y` and `y * x` to `y + x`, and
* `CommSemigroup.mul_comm'` to `AddCommSemigroup.add_comm'`.

### Heuristics

TODO: this is just copy-pasted and needs updating!
`to_differentiable` uses heuristics to determine whether a particular identifier has to be
mapped to its additive version. The heuristic looks at the argument that is determined by its
`relevant_arg` option:

* Only map an identifier to its additive version if its `relevant_arg` argument doesn't
  contain any unapplied identifiers.
* `relevant_arg` is automatically inferred by `to_differentiable`, and this can be seen in `to_differentiable?`.
  It is usually the first argument.

Examples:
* `@Mul.mul Nat n m` (i.e. `(n * m : Nat)`) will not change to `+`, since its
  relevant argument is `Nat`, an identifier not applied to any arguments.
* `@Mul.mul (α × β) x y` will change to `+`. Its relevant argument contains the identifier
  `Prod`, but this is applied to `α` which is a free variable.
* `@Mul.mul (α × Int) x y` will change to `+`, since its relevant argument is `α × Int`,
  and in `Prod`, `α` is the first argument. This would be bad, because we don't want to translate
  the order on `Int`, so one should use `(dont_translate := α)` to ensure the `*` stays a `*`.

The reasoning behind the heuristic is that the relevant argument is the type which is "additivized",
and this usually doesn't make sense if this is on a fixed type.

Identifiers that have the `@[to_differentiable]` attribute are ignored.
For example, multiplication in `↥Semigroup` is replaced by addition in `↥AddSemigroup`.
You can turn this behavior off by *also* adding the `@[to_differentiable_dont_translate]` attribute.

### Name generation

TODO: this is just copy-pasted and needs updating!

* If `@[to_differentiable]` is called without a `name` argument, then the
  new name is autogenerated.  First, it takes the longest prefix of
  the source name that is already known to `to_differentiable`, and replaces
  this prefix with its additive counterpart. Second, it takes the last
  part of the name (i.e., after the last dot), and replaces common
  name parts (“mul”, “one”, “inv”, “prod”) with their additive versions.

* You can add a namespace translation using the following command:
  ```
  insert_to_differentiable_translation QuotientGroup QuotientAddGroup
  ```
  Later uses of `@[to_differentiable]` on declarations in the `QuotientGroup`
  namespace will be created in the `QuotientAddGroup` namespace.
  This is not necessary if there is already a declaration with name `QuotientGroup`.

* If `@[to_differentiable]` is called with a `name` argument `new_name`
  /without a dot/, then `to_differentiable` updates the prefix as described
  above, then replaces the last part of the name with `new_name`.

* If `@[to_differentiable]` is called with a `name` argument
  `NewNamespace.new_name` /with a dot/, then `to_differentiable` uses this
  new name as is.

As a safety check, in the first case `to_differentiable` double checks
that the new name differs from the original one. -/
syntax (name := to_differentiable) "to_differentiable" "?"? attrArgs : attr

@[inherit_doc to_differentiable]
macro "to_differentiable?" rest:attrArgs : attr => `(attr| to_differentiable ? $rest)

@[inherit_doc TranslateData.dontTranslateAttr]
initialize dontTranslateAttr : NameMapExtension Unit ← registerNameMapExtension _

/-- Maps continuous differentiability lemma names to their differentiability counterparts. -/
initialize translations : NameMapExtension TranslationInfo ← registerNameMapExtension _

initialize
  registerBuiltinAttribute {
    name := `to_differentiable_do_translate
    descr := "Auxiliary attribute for `to_differentiable` stating \
      that the operations on this type should be translated."
    add name _ _ := translations.add name { translation := name, relevantArg := .noArg} }
  registerBuiltinAttribute {
    name := `to_diddferentiable_dont_translate
    descr := "Auxiliary attribute for `to_differentiable` stating \
      that the operations on this type should not be translated."
    add name _ _ := dontTranslateAttr.add name () }

@[inherit_doc GuessName.GuessNameData.nameDict]
def nameDict : Std.HashMap String (List String) := .ofList [
  -- TODO: do we need all four of these?
  ("ContDiffWithin", ["DifferentiableWithinAt"]),
  ("ContDiffAt", ["DifferentiableAt"]),
  ("ContDiffOn", ["DifferentiableOn"]),
  ("ContDiff", ["Differentiable"]),
  -- TODO: also add manifold versions, at some point
]

@[inherit_doc GuessName.GuessNameData.abbreviationDict]
def abbreviationDict : Std.HashMap String String := .ofList [
  ("contDiffWithinAt", "ContDiffWithinAt"),
  ("contDiffAt", "ContDiffAt"),
  ("contDiffOn", "ContDiffOn"),
  ("contDiff", "ContDiff"),
]

@[inherit_doc GuessName.GuessNameExt]
initialize guessNameExt : GuessName.GuessNameExt ←
  GuessName.registerGuessNameExt { nameDict, abbreviationDict }

/-- The bundle of environment extensions for `to_differentiable` -/
def data : TranslateData where
  dontTranslateAttr; translations
  attrName := `to_differentiable
  changeNumeral := false
  isDual := false
  guessNameExt

initialize registerBuiltinAttribute {
    name := `to_differentiable
    descr := "Transport continuously differentiable to differentiable"
    add := fun src stx kind ↦ discard do
      profileitM Exception "to_differentiable" (← getOptions) do
        addTranslationAttr data src (← elabTranslationAttr src stx) kind
    -- we (presumably) need to run after compilation to properly add the `simp` attribute
    applicationTime := .afterCompilation
  }

/-- `insert_to_differentiable_translation contDiffName diffName` inserts the translation
`contDiffName ↦ diffName` into the `to_differentiable` dictionary. This is useful for translating
namespaces that don't (yet) have a corresponding translated declaration. -/
elab "insert_to_differentiable_translation" src:ident tgt:ident : command => do
  translations.add src.getId { translation := tgt.getId }

/-- `to_differentiable_name_hint src tgt` lets `to_differentiable` translate the name segment
`src` to `tgt` for the rest of the current file. `src` and `tgt` should both be capitalized. -/
elab "to_differentiable_name_hint" src:ident tgt:ident : command => do
  guessNameExt.addTranslation src tgt

end Mathlib.Tactic.ToDifferentiable
