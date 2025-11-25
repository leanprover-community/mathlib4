/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov, Floris van Doorn, Jon Eugster, Bryan Gin-ge Chen,
Jovan Gerbscheid
-/
module

public meta import Mathlib.Tactic.Translate.Core

/-!
# The `@[to_additive]` attribute.

The `@[to_additive]` attribute is used to translate multiplicative declarations to their
additive equivalent. See the docstrings of `to_additive` for more information.
-/

public meta section

namespace Mathlib.Tactic.ToAdditive
open Lean Elab Translate

@[inherit_doc TranslateData.ignoreArgsAttr]
syntax (name := to_additive_ignore_args) "to_additive_ignore_args" (ppSpace num)* : attr

@[inherit_doc relevantArgOption]
syntax (name := to_additive_relevant_arg) "to_additive_relevant_arg " num : attr

@[inherit_doc TranslateData.dontTranslateAttr]
syntax (name := to_additive_dont_translate) "to_additive_dont_translate" : attr

/-- The attribute `to_additive` can be used to automatically transport theorems
and definitions (but not inductive types and structures) from a multiplicative
theory to an additive theory.

To use this attribute, just write:

```
@[to_additive]
theorem mul_comm' {α} [CommSemigroup α] (x y : α) : x * y = y * x := mul_comm x y
```

This code will generate a theorem named `add_comm'`. It is also
possible to manually specify the name of the new declaration:

```
@[to_additive add_foo]
theorem foo := sorry
```

An existing documentation string will _not_ be automatically used, so if the theorem or definition
has a doc string, a doc string for the additive version should be passed explicitly to
`to_additive`.

```
/-- Multiplication is commutative -/
@[to_additive /-- Addition is commutative -/]
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

Use the `to_additive existing` syntax to use an existing additive declaration, instead of
automatically generating it. This attempts to autogenerate the `(reorder := ...)` argument.

Use the `(attr := ...)` syntax to apply attributes to both the multiplicative and the additive
version:

```
@[to_additive (attr := simp)] lemma mul_one' {G : Type*} [Group G] (x : G) : x * 1 = x := mul_one x
```

For `simps` this also ensures that some generated lemmas are added to the additive dictionary.
`@[to_additive (attr := to_additive)]` is a special case, where the `to_additive`
attribute is added to the generated lemma only, to additivize it again.
This is useful for lemmas about `Pow` to generate both lemmas about `SMul` and `VAdd`. Example:
```
@[to_additive (attr := to_additive VAdd_lemma, simp) SMul_lemma]
lemma Pow_lemma ... :=
```
In the above example, the `simp` is added to all 3 lemmas. All other options to `to_additive`
(like the generated name or `(reorder := ...)`) are not passed down,
and can be given manually to each individual `to_additive` call.

## Implementation notes

The transport process generally works by taking all the names of
identifiers appearing in the name, type, and body of a declaration and
creating a new declaration by mapping those names to additive versions
using a simple string-based dictionary and also using all declarations
that have previously been labeled with `to_additive`. The dictionary is `ToAdditive.nameDict`
and can be found in the `Tactic.ToAdditive.GuessName` file. If you introduce a new name which
should be translated by `to_additive` you should add the translation to this dictionary.

In the `mul_comm'` example above, `to_additive` maps:
* `mul_comm'` to `add_comm'`,
* `CommSemigroup` to `AddCommSemigroup`,
* `x * y` to `x + y` and `y * x` to `y + x`, and
* `CommSemigroup.mul_comm'` to `AddCommSemigroup.add_comm'`.

### Heuristics

`to_additive` uses heuristics to determine whether a particular identifier has to be
mapped to its additive version. The basic heuristic is

* Only map an identifier to its additive version if its first argument doesn't
  contain any unapplied identifiers.

Examples:
* `@Mul.mul Nat n m` (i.e. `(n * m : Nat)`) will not change to `+`, since its
  first argument is `Nat`, an identifier not applied to any arguments.
* `@Mul.mul (α × β) x y` will change to `+`. It's first argument contains only the identifier
  `Prod`, but this is applied to arguments, `α` and `β`.
* `@Mul.mul (α × Int) x y` will not change to `+`, since its first argument contains `Int`.

The reasoning behind the heuristic is that the first argument is the type which is "additivized",
and this usually doesn't make sense if this is on a fixed type.

There are some exceptions to this heuristic:

* Identifiers that have the `@[to_additive]` attribute are ignored.
  For example, multiplication in `↥Semigroup` is replaced by addition in `↥AddSemigroup`.
  You can turn this behavior off by *also* adding the `@[to_additive_dont_translate]` attribute.
* If an identifier `d` has attribute `@[to_additive (relevant_arg := α)]` then the argument
  `α` is checked for a fixed type, instead of checking the first argument.
  `@[to_additive]` will automatically add the attribute `(relevant_arg := α)` to a
  declaration when the first argument has no multiplicative type-class, but argument `α` does.
* If an identifier has attribute `@[to_additive_ignore_args n1 n2 ...]` then all the arguments in
  positions `n1`, `n2`, ... will not be checked for unapplied identifiers (start counting from 1).
  For example, `ContMDiffMap` has attribute `@[to_additive_ignore_args 21]`, which means
  that its 21st argument `(n : WithTop ℕ)` can contain `ℕ`
  (usually in the form `Top.top ℕ ...`) and still be additivized.
  So `@Mul.mul (C^∞⟮I, N; I', G⟯) _ f g` will be additivized.

### Troubleshooting

If `@[to_additive]` fails because the additive declaration raises a type mismatch, there are
various things you can try.
The first thing to do is to figure out what `@[to_additive]` did wrong by looking at the type
mismatch error.

* Option 1: The most common case is that it didn't additivize a declaration that should be
  additivized. This happened because the heuristic applied, and the first argument contains a
  fixed type, like `ℕ` or `ℝ`. However, the heuristic misfires on some other declarations.
  Solutions:
  * First figure out what the fixed type is in the first argument of the declaration that didn't
    get additivized. Note that this fixed type can occur in implicit arguments. If manually finding
    it is hard, you can run `set_option trace.to_additive_detail true` and search the output for the
    fragment "contains the fixed type" to find what the fixed type is.
  * If the fixed type has an additive counterpart (like `↥Semigroup`), give it the `@[to_additive]`
    attribute.
  * If the fixed type has nothing to do with algebraic operations (like `TopCat`), add the attribute
    `@[to_additive self]` to the fixed type `Foo`.
  * If the fixed type occurs inside the `k`-th argument of a declaration `d`, and the
    `k`-th argument is not connected to the multiplicative structure on `d`, consider adding
    attribute `[to_additive_ignore_args k]` to `d`.
    Example: `ContMDiffMap` ignores the argument `(n : WithTop ℕ)`
  * If none of the arguments have a multiplicative structure, then the heuristic should not apply at
    all. This can be achieved with the option `(relevant_arg := _)`.
* Option 2: It additivized a declaration `d` that should remain multiplicative. Solution:
  * Make sure the first argument of `d` is a type with a multiplicative structure. If not, can you
    reorder the (implicit) arguments of `d` so that the first argument becomes a type with a
    multiplicative structure (and not some indexing type)?
    The reason is that `@[to_additive]` doesn't additivize declarations if their first argument
    contains fixed types like `ℕ` or `ℝ`. See section Heuristics.
    If the first argument is not the argument with a multiplicative type-class, `@[to_additive]`
    should have automatically added the attribute `(relevant_arg := ...)` to the declaration.
    You can test this by running the following (where `d` is the full name of the declaration):
    ```
      open Lean in run_cmd logInfo m!"{ToAdditive.relevantArgAttr.find? (← getEnv) `d}"
    ```
    The expected output is `n` where the `n`-th (0-indexed) argument of `d` is a type (family)
    with a multiplicative structure on it. `none` means `0`.
    If you get a different output (or a failure), you could add the attribute
    `@[to_additive (relevant_arg := n)]` manually, where `n` is an (1-indexed) argument with a
    multiplicative structure.
* Option 3: Arguments / universe levels are incorrectly ordered in the additive version.
  This likely only happens when the multiplicative declaration involves `pow`/`^`. Solutions:
  * Ensure that the order of arguments of all relevant declarations are the same for the
    multiplicative and additive version. This might mean that arguments have an "unnatural" order
    (e.g. `Monoid.npow n x` corresponds to `x ^ n`, but it is convenient that `Monoid.npow` has this
    argument order, since it matches `AddMonoid.nsmul n x`.
  * If this is not possible, add `(reorder := ...)` argument to `to_additive`.

If neither of these solutions work, and `to_additive` is unable to automatically generate the
additive version of a declaration, manually write and prove the additive version.
Often the proof of a lemma/theorem can just be the multiplicative version of the lemma applied to
`multiplicative G`.
Afterwards, apply the attribute manually:

```
attribute [to_additive foo_add_bar] foo_bar
```

This will allow future uses of `to_additive` to recognize that
`foo_bar` should be replaced with `foo_add_bar`.

### Handling of hidden definitions

Before transporting the “main” declaration `src`, `to_additive` first
scans its type and value for names starting with `src`, and transports
them. This includes auxiliary definitions like `src._match_1`

In addition to transporting the “main” declaration, `to_additive` transports
its equational lemmas and tags them as equational lemmas for the new declaration.

### Structure fields and constructors

If `src` is a structure, then the additive version has to be already written manually.
In this case `to_additive` adds all structure fields to its mapping.

### Name generation

* If `@[to_additive]` is called without a `name` argument, then the
  new name is autogenerated.  First, it takes the longest prefix of
  the source name that is already known to `to_additive`, and replaces
  this prefix with its additive counterpart. Second, it takes the last
  part of the name (i.e., after the last dot), and replaces common
  name parts (“mul”, “one”, “inv”, “prod”) with their additive versions.

* You can add a namespace translation using the following command:
  ```
  insert_to_additive_translation QuotientGroup QuotientAddGroup
  ```
  Later uses of `@[to_additive]` on declarations in the `QuotientGroup`
  namespace will be created in the `QuotientAddGroup` namespace.
  This is not necessary if there is already a declaration with name `QuotientGroup`.

* If `@[to_additive]` is called with a `name` argument `new_name`
  /without a dot/, then `to_additive` updates the prefix as described
  above, then replaces the last part of the name with `new_name`.

* If `@[to_additive]` is called with a `name` argument
  `NewNamespace.new_name` /with a dot/, then `to_additive` uses this
  new name as is.

As a safety check, in the first case `to_additive` double checks
that the new name differs from the original one. -/
syntax (name := to_additive) "to_additive" "?"? attrArgs : attr

@[inherit_doc to_additive]
macro "to_additive?" rest:attrArgs : attr => `(attr| to_additive ? $rest)


@[inherit_doc to_additive_ignore_args]
initialize ignoreArgsAttr : NameMapExtension (List Nat) ←
  registerNameMapAttribute {
    name := `to_additive_ignore_args
    descr :=
      "Auxiliary attribute for `to_additive` stating that certain arguments are not additivized."
    add := fun _ stx ↦ do
        let ids ← match stx with
          | `(attr| to_additive_ignore_args $[$ids:num]*) => pure <| ids.map (·.1.isNatLit?.get!)
          | _ => throwUnsupportedSyntax
        return ids.toList }

@[inherit_doc TranslateData.argInfoAttr]
initialize argInfoAttr : NameMapExtension ArgInfo ← registerNameMapExtension _

@[inherit_doc to_additive_dont_translate]
initialize dontTranslateAttr : NameMapExtension Unit ←
  registerNameMapAttribute {
    name := `to_additive_dont_translate
    descr := "Auxiliary attribute for `to_additive` stating \
      that the operations on this type should not be translated."
    add := fun
    | _, `(attr| to_additive_dont_translate) => return
    | _, _ => throwUnsupportedSyntax }

/-- Maps multiplicative names to their additive counterparts. -/
initialize translations : NameMapExtension Name ← registerNameMapExtension _

@[inherit_doc GuessName.GuessNameData.nameDict]
def nameDict : Std.HashMap String (List String) := .ofList [
  ("one", ["Zero"]),
  ("mul", ["Add"]),
  ("smul", ["VAdd"]),
  ("inv", ["Neg"]),
  ("div", ["Sub"]),
  ("prod", ["Sum"]),
  ("hmul", ["HAdd"]),
  ("hsmul", ["HVAdd"]),
  ("hdiv", ["HSub"]),
  ("hpow", ["HSMul"]),
  ("finprod", ["Finsum"]),
  ("tprod", ["TSum"]),
  ("pow", ["NSMul"]),
  ("npow", ["NSMul"]),
  ("zpow", ["ZSMul"]),
  ("mabs", ["Abs"]),
  ("monoid", ["Add", "Monoid"]),
  ("submonoid", ["Add", "Submonoid"]),
  ("group", ["Add", "Group"]),
  ("subgroup", ["Add", "Subgroup"]),
  ("semigroup", ["Add", "Semigroup"]),
  ("magma", ["Add", "Magma"]),
  ("haar", ["Add", "Haar"]),
  ("prehaar", ["Add", "Prehaar"]),
  ("unit", ["Add", "Unit"]),
  ("units", ["Add", "Units"]),
  ("cyclic", ["Add", "Cyclic"]),
  ("semigrp", ["Add", "Semigrp"]),
  ("grp", ["Add", "Grp"]),
  ("commute", ["Add", "Commute"]),
  ("semiconj", ["Add", "Semiconj"]),
  ("rootable", ["Divisible"]),
  ("zpowers", ["ZMultiples"]),
  ("powers", ["Multiples"]),
  ("multipliable", ["Summable"]),
  ("gpfree", ["APFree"]),
  ("quantale", ["Add", "Quantale"]),
  ("square", ["Even"]),
  ("mconv", ["Conv"]),
  ("irreducible", ["Add", "Irreducible"]),
  ("mlconvolution", ["LConvolution"])]

@[inherit_doc GuessName.GuessNameData.abbreviationDict]
def abbreviationDict : Std.HashMap String String := .ofList [
  ("isCancelAdd", "IsCancelAdd"),
  ("isLeftCancelAdd", "IsLeftCancelAdd"),
  ("isRightCancelAdd", "IsRightCancelAdd"),
  ("cancelAdd", "AddCancel"),
  ("leftCancelAdd", "AddLeftCancel"),
  ("rightCancelAdd", "AddRightCancel"),
  ("cancelCommAdd", "AddCancelComm"),
  ("commAdd", "AddComm"),
  ("zero_le", "Nonneg"),
  ("zeroLE", "Nonneg"),
  ("zero_lt", "Pos"),
  ("zeroLT", "Pos"),
  ("lezero", "Nonpos"),
  ("le_zero", "Nonpos"),
  ("ltzero", "Neg"),
  ("lt_zero", "Neg"),
  ("addSingle", "Single"),
  ("add_single", "Single"),
  ("addSupport", "Support"),
  ("add_support", "Support"),
  ("addTSupport", "TSupport"),
  ("add_tsupport", "TSupport"),
  ("addIndicator", "Indicator"),
  ("add_indicator", "Indicator"),
  ("isEven", "Even"),
  -- "Regular" is well-used in mathlib with various meanings (e.g. in
  -- measure theory) and a direct translation
  -- "regular" --> "addRegular" in `nameDict` above seems error-prone.
  ("isRegular", "IsAddRegular"),
  ("isLeftRegular", "IsAddLeftRegular"),
  ("isRightRegular", "IsAddRightRegular"),
  ("hasFundamentalDomain", "HasAddFundamentalDomain"),
  ("quotientMeasure", "AddQuotientMeasure"),
  ("negFun", "InvFun"),
  ("uniqueProds", "UniqueSums"),
  ("orderOf", "AddOrderOf"),
  ("zeroLePart", "PosPart"),
  ("leZeroPart", "NegPart"),
  ("isScalarTower", "VAddAssocClass"),
  ("isOfFinOrder", "IsOfFinAddOrder"),
  ("isCentralScalar", "IsCentralVAdd"),
  ("function_addSemiconj", "Function_semiconj"),
  ("function_addCommute", "Function_commute"),
  ("divisionAddMonoid", "SubtractionMonoid"),
  ("subNegZeroAddMonoid", "SubNegZeroMonoid"),
  ("modularCharacter", "AddModularCharacter")]

/-- The bundle of environment extensions for `to_additive` -/
def data : TranslateData where
  ignoreArgsAttr; argInfoAttr; dontTranslateAttr; translations
  attrName := `to_additive
  changeNumeral := true
  isDual := false
  guessNameData := { nameDict, abbreviationDict }

initialize registerBuiltinAttribute {
    name := `to_additive
    descr := "Transport multiplicative to additive"
    add := fun src stx kind ↦ discard do
      addTranslationAttr data src (← elabTranslationAttr src stx) kind
    -- we (presumably) need to run after compilation to properly add the `simp` attribute
    applicationTime := .afterCompilation
  }

/-- `insert_to_additive_translation mulName addName` inserts the translation `mulName ↦ addName`
into the `to_additive` dictionary. This is useful for translating namespaces that don't (yet)
have a corresponding translated declaration. -/
elab "insert_to_additive_translation" src:ident tgt:ident : command => do
  translations.add src.getId tgt.getId

end Mathlib.Tactic.ToAdditive
