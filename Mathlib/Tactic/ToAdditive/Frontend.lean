/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov, Floris van Doorn, Jon Eugster, Bryan Gin-ge Chen,
Jovan Gerbscheid
-/
import Batteries.Tactic.Trans
import Lean.Compiler.NoncomputableAttr
import Lean.Elab.Tactic.Ext
import Lean.Meta.Tactic.Rfl
import Lean.Meta.Tactic.Symm
import Lean.Meta.Tactic.TryThis
import Mathlib.Data.Array.Defs
import Mathlib.Data.Nat.Notation
import Mathlib.Lean.Expr.ReplaceRec
import Mathlib.Lean.Meta.Simp
import Mathlib.Lean.Name
import Mathlib.Tactic.Eqns -- just to copy the attribute
import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.ToAdditive.GuessName

/-!
# The `@[to_additive]` attribute.

Implementation of the `to_additive` attribute.
See the docstring of `ToAdditive.to_additive` for more information
-/

open Lean Meta Elab Command Std

namespace ToAdditive

/-- An attribute that tells `@[to_additive]` that certain arguments of this definition are not
involved when using `@[to_additive]`.
This helps the heuristic of `@[to_additive]` by also transforming definitions if `ℕ` or another
fixed type occurs as one of these arguments. -/
syntax (name := to_additive_ignore_args) "to_additive_ignore_args" (ppSpace num)* : attr

/-- This attribute is deprecated. Use `to_additive (relevant_arg := ...)` instead. -/
syntax (name := to_additive_relevant_arg) "to_additive_relevant_arg " num : attr

/-- An attribute that stores all the declarations that deal with numeric literals on variable types.

Numeral literals occur in expressions without type information, so in order to decide whether `1`
needs to be changed to `0`, the context around the numeral is relevant.
Most numerals will be in an `OfNat.ofNat` application, though tactics can add numeral literals
inside arbitrary functions. By default we assume that we do not change numerals, unless it is
in a function application with the `to_additive_change_numeral` attribute.

`@[to_additive_change_numeral n₁ ...]` should be added to all functions that take one or more
numerals as argument that should be changed if `additiveTest` succeeds on the first argument,
i.e. when the numeral is only translated if the first argument is a variable
(or consists of variables).
The arguments `n₁ ...` are the positions of the numeral arguments (starting counting from 1). -/
syntax (name := to_additive_change_numeral) "to_additive_change_numeral" (ppSpace num)* : attr

/-- The `to_additive_dont_translate` attribute, used to specify types that should be translated by
`to_additive`, but its operations should remain multiplicative.

Usage notes:
* Apply this together with the `to_additive` attribute.
* The name generation of `to_additive` is not aware that the operations on this type should not be
  translated, so you generally have to specify the name itself, if the name should remain
  multiplicative.
-/
syntax (name := to_additive_dont_translate) "to_additive_dont_translate" : attr

/-- `(attr := ...)` applies the given attributes to both the original and the
translated declaration. -/
syntax toAdditiveAttrOption := &"attr" " := " Parser.Term.attrInstance,*
/--
`(reorder := ...)` reorders the arguments/hypotheses in the generated declaration.
It uses cycle notation. For example `(reorder := 1 2, 5 6)` swaps the first two
arguments with each other and the fifth and the sixth argument and `(reorder := 3 4 5)` will move
the fifth argument before the third argument. This is used in `to_dual` to swap the arguments in
`≤`, `<` and `⟶`. It is also used in `to_additive` to translate from `^` to `•`.
-/
syntax toAdditiveReorderOption := &"reorder" " := " (num+),+
/--
the `relevant_arg := ...` option tells which argument is a type where this declaration uses the
multiplicative structure. This is inferred automatically using the function `findMultiplicativeArg`,
but it can also be overwritten using this syntax.

If there are multiple arguments with a multiplicative structure, we typically tag the first one.
If this argument contains a fixed type, this declaration will not be additivized.
See the Heuristics section of the `to_additive` doc-string for more details.

If a declaration is not tagged, it is presumed that the first argument is relevant.

To indicate that there is no relevant argument, set it to a number that is out of bounds,
i.e. larger than the number of arguments, e.g. `(relevant_arg := 100)`.

Implementation note: we only allow exactly 1 relevant argument, even though some declarations
(like `Prod.instGroup`) have multiple arguments with a multiplicative structure on it.
The reason is that whether we additivize a declaration is an all-or-nothing decision, and
we will not be able to additivize declarations that (e.g.) talk about multiplication on `ℕ × α`
anyway.
-/
syntax toAdditiveRelevantOption := &"relevant_arg" " := " num
/--
`dont_translate := ...` takes a list of type variables (separated by spaces) that should not be
considered for translation. For example in
```
lemma foo {α β : Type} [Group α] [Group β] (a : α) (b : β) : a * a⁻¹ = 1 ↔ b * b⁻¹ = 1
```
we can choose to only additivize `α` by writing `to_additive (dont_translate := β)`.
-/
syntax toAdditiveDontTranslateOption := &"dont_translate" " := " ident+
syntax toAdditiveOption := "(" toAdditiveAttrOption <|> toAdditiveReorderOption <|>
  toAdditiveRelevantOption <|> toAdditiveDontTranslateOption ")"
/-- A hint for where to find the tranlated declaration (`existing` or `self`) -/
syntax toAdditiveNameHint := (ppSpace (&"existing" <|> &"self"))?
syntax toAdditiveRest :=
  toAdditiveNameHint (ppSpace toAdditiveOption)* (ppSpace ident)? (ppSpace (str <|> docComment))?

-- We omit a doc-string on these syntaxes to instead show the `to_additive` or `to_dual` doc-string
attribute [nolint docBlame] toAdditiveRest toAdditiveOption

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

Use the `to_additive existing` syntax to use an existing additive declaration, instead of
automatically generating it.

Use the `(reorder := ...)` syntax to reorder the arguments in the generated additive declaration.
This is specified using cycle notation. For example `(reorder := 1 2, 5 6)` swaps the first two
arguments with each other and the fifth and the sixth argument and `(reorder := 3 4 5)` will move
the fifth argument before the third argument. This is mostly useful to translate declarations using
`Pow` to those using `SMul`.

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
* If an identifier `d` has attribute `@[to_additive (relevant_arg := n)]` then the argument
  in position `n` is checked for a fixed type, instead of checking the first argument.
  `@[to_additive]` will automatically add the attribute `(relevant_arg := n)` to a
  declaration when the first argument has no multiplicative type-class, but argument `n` does.
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
    all. This can be achieved by setting `relevant_arg` out of bounds, e.g. `(relevant_arg := 100)`.
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

* [todo] Namespaces can be transformed using `map_namespace`. For example:
  ```
  run_cmd to_additive.map_namespace `QuotientGroup `QuotientAddGroup
  ```

  Later uses of `to_additive` on declarations in the `QuotientGroup`
  namespace will be created in the `QuotientAddGroup` namespaces.

* If `@[to_additive]` is called with a `name` argument `new_name`
  /without a dot/, then `to_additive` updates the prefix as described
  above, then replaces the last part of the name with `new_name`.

* If `@[to_additive]` is called with a `name` argument
  `NewNamespace.new_name` /with a dot/, then `to_additive` uses this
  new name as is.

As a safety check, in the first case `to_additive` double checks
that the new name differs from the original one. -/
syntax (name := to_additive) "to_additive" "?"? toAdditiveRest : attr

@[inherit_doc to_additive]
macro "to_additive?" rest:toAdditiveRest : attr => `(attr| to_additive ? $rest)

initialize registerTraceClass `to_additive
initialize registerTraceClass `to_additive_detail

/-- Linter, mostly used by `@[to_additive]`, that checks that the source declaration doesn't have
certain attributes -/
register_option linter.existingAttributeWarning : Bool := {
  defValue := true
  descr := "Linter, mostly used by `@[to_additive]`, that checks that the source declaration \
    doesn't have certain attributes" }

/-- Linter to check that the `to_additive` attribute is not given manually -/
register_option linter.toAdditiveGenerateName : Bool := {
  defValue := true
  descr := "Linter used by `@[to_additive]` that checks if `@[to_additive]` automatically \
    generates the user-given name" }

/-- Linter to check whether the user correctly specified that the additive declaration already
exists -/
register_option linter.toAdditiveExisting : Bool := {
  defValue := true
  descr := "Linter used by `@[to_additive]` that checks whether the user correctly specified that
    the additive declaration already exists" }

/-- Linter to check that the `relevant_arg` attribute is not given manually -/
register_option linter.toAdditiveRelevantArg : Bool := {
  defValue := true
  descr := "Linter to check that the `relevant_arg` attribute is not given manually." }

@[inherit_doc to_additive_change_numeral]
initialize changeNumeralAttr : NameMapExtension (List Nat) ←
  registerNameMapAttribute {
    name := `to_additive_change_numeral
    descr :=
      "Auxiliary attribute for `to_additive` that stores functions that have numerals as argument."
    add := fun
    | _, `(attr| to_additive_change_numeral $[$arg]*) =>
      pure <| arg.map (·.1.isNatLit?.get!.pred) |>.toList
    | _, _ => throwUnsupportedSyntax }

/-- `BundledExts` is a structure that holds all environment extensions related to a
`to_additive`-like attribute. This allows us to use the `to_additive` machinery for other
attributes, such as `to_dual`. -/
structure BundledExts : Type where
  ignoreArgsAttr : NameMapExtension (List Nat)
  /-- `reorderAttr` stores the declarations that need their arguments reordered when tranlating.
  This is speicified using the `(reorder := ...)` syntax. -/
  reorderAttr : NameMapExtension (List <| List Nat)
  relevantArgAttr : NameMapExtension Nat
  dontTranslateAttr : NameMapExtension Unit
  /-- `translations` stores all of the constants that have been tagged with this attribute,
  and maps them to their translation. -/
  translations : NameMapExtension Name
  /-- The name of the attribute, for example `to_additive` or `to_dual`. -/
  attrName : Name
  /-- If `changeNumeral := true`, then try to translate the number `1` to `0`. -/
  changeNumeral : Bool
  /-- When `isDual := true`, every translation `A → B` will also give a translation `B → A`. -/
  isDual : Bool
  /-- `guessName` tries to guess how a lemma name should be translated. -/
  guessName : String → String
attribute [inherit_doc to_additive_ignore_args] BundledExts.ignoreArgsAttr
attribute [inherit_doc to_additive_relevant_arg] BundledExts.relevantArgAttr
attribute [inherit_doc to_additive_dont_translate] BundledExts.dontTranslateAttr

/-- Get the multiplicative → additive translation for the given name. -/
def findTranslation? (env : Environment) (b : BundledExts) : Name → Option Name :=
  (b.translations.getState env).find?

/-- Get the multiplicative → additive translation for the given name,
falling back to translating a prefix of the name if the full name can't be translated.
This allows translating automatically generated declarations such as `IsRegular.casesOn`. -/
def findPrefixTranslation (env : Environment) (nm : Name) (b : BundledExts) : Name :=
  nm.mapPrefix (findTranslation? env b)

/-- Add a (multiplicative → additive) name translation to the translations map. -/
def insertTranslation (b : BundledExts) (src tgt : Name) (failIfExists := true) : CoreM Unit := do
  if let some tgt' := findTranslation? (← getEnv) b src then
    if failIfExists then
      throwError "The translation {src} ↦ {tgt'} already exists"
    else
      trace[to_additive] "The translation {src} ↦ {tgt'} already exists"
      return
  modifyEnv (b.translations.addEntry · (src, tgt))
  trace[to_additive] "Added translation {src} ↦ {tgt}"
  if b.isDual && src != tgt then
    if let some src' := findTranslation? (← getEnv) b tgt then
      if failIfExists then
        throwError "The translation {tgt} ↦ {src'} already exists"
      else
        trace[to_additive] "The translation {tgt} ↦ {src'} already exists"
        return
    modifyEnv (b.translations.addEntry · (tgt, src))
    trace[to_additive] "Also added translation {tgt} ↦ {src}"

/-- `ArgInfo` stores information about how a constant should be translated. -/
structure ArgInfo where
  /-- The arguments that should be reordered by `to_additive`, using cycle notation. -/
  reorder : List (List Nat) := []
  /-- The argument used to determine whether this constant should be translated. -/
  relevantArg : Nat := 0

/-- Add a name translation to the translations map and add the `argInfo` information to `src`. -/
def insertTranslationAndInfo (b : BundledExts) (src tgt : Name) (argInfo : ArgInfo)
    (failIfExists := true) : CoreM Unit := do
  insertTranslation b src tgt failIfExists
  if argInfo.reorder != [] then
    trace[to_additive] "@[to_additive] will reorder the arguments of {tgt} by {argInfo.reorder}."
    b.reorderAttr.add src argInfo.reorder
  if argInfo.relevantArg != 0 then
    trace[to_additive_detail] "Setting relevant_arg for {src} to be {argInfo.relevantArg}."
    b.relevantArgAttr.add src argInfo.relevantArg

/-- `Config` is the type of the arguments that can be provided to `to_additive`. -/
structure Config : Type where
  /-- View the trace of the to_additive procedure.
  Equivalent to `set_option trace.to_additive true`. -/
  trace : Bool := false
  /-- The name of the target (the additive declaration). -/
  tgt : Name := Name.anonymous
  /-- An optional doc string. -/
  doc : Option String := none
  /-- If `allowAutoName` is `false` (default) then
  `@[to_additive]` will check whether the given name can be auto-generated. -/
  allowAutoName : Bool := false
  /-- The arguments that should be reordered by `to_additive`, using cycle notation. -/
  reorder : List (List Nat) := []
  /-- The argument used to determine whether this constant should be translated. -/
  relevantArg? : Option Nat := none
  /-- The attributes which we want to give to both the multiplicative and additive versions.
  For `simps` this will also add generated lemmas to the translation dictionary. -/
  attrs : Array Syntax := #[]
  /-- A list of type variables that should not be translated by `to_additive`. -/
  dontTranslate : List Ident := []
  /-- The `Syntax` element corresponding to the original multiplicative declaration
  (or the `to_additive` attribute if it is added later),
  which we need for adding definition ranges. -/
  ref : Syntax
  /-- An optional flag stating that the additive declaration already exists.
  If this flag is wrong about whether the additive declaration exists, `to_additive` will
  raise a linter error.
  Note: the linter will never raise an error for inductive types and structures. -/
  existing : Bool := false
  /-- An optional flag stating that the target of the translation is the target itself.
  This can be used to reorder arguments, such as in
  `attribute [to_dual self (reorder := 3 4)] LE.le`.
  It can also be used to give a hint to `additiveTest`, such as in
  `attribute [to_additive self] Unit`.
  If `self := true`, we should also have `existing := true`. -/
  self : Bool := false
  deriving Repr

-- See https://github.com/leanprover/lean4/issues/10295
attribute [nolint unusedArguments] instReprConfig.repr

/-- Eta expands `e` at most `n` times. -/
def etaExpandN (n : Nat) (e : Expr) : MetaM Expr := do
  forallBoundedTelescope (← inferType e) (some n) fun xs _ ↦ mkLambdaFVars xs (mkAppN e xs)

/-- `e.expand` eta-expands all expressions that have as head a constant `n` in `reorder`.
They are expanded until they are applied to one more argument than the maximum in `reorder.find n`.
It also expands all kernel projections that have as head a constant `n` in `reorder`. -/
def expand (b : BundledExts) (e : Expr) : MetaM Expr := do
  let env ← getEnv
  let reorderFn : Name → List (List ℕ) := fun nm ↦ (b.reorderAttr.find? env nm |>.getD [])
  let e₂ ← Lean.Meta.transform (input := e) (skipConstInApp := true)
    (post := fun e => return .done e) fun e ↦
    e.withApp fun f args ↦ do
    match f with
    | .proj n i s =>
      let some info := getStructureInfo? (← getEnv) n | return .continue -- e.g. if `n` is `Exists`
      let some projName := info.getProjFn? i | unreachable!
      -- if `projName` is explicitly tagged with `@[to_additive]`,
      -- replace `f` with the application `projName s` and then visit `projName s args` again.
      if findTranslation? env b projName |>.isNone then
        return .continue
      return .visit <| (← whnfD (← inferType s)).withApp fun sf sargs ↦
        mkAppN (mkApp (mkAppN (.const projName sf.constLevels!) sargs) s) args
    | .const c _ =>
      let reorder := reorderFn c
      if reorder.isEmpty then
        -- no need to expand if nothing needs reordering
        return .continue
      let needed_n := reorder.flatten.foldr Nat.max 0 + 1
      if needed_n ≤ args.size then
        return .continue
      else
        -- in this case, we need to reorder arguments that are not yet
        -- applied, so first η-expand the function.
        let e' ← etaExpandN (needed_n - args.size) e
        trace[to_additive_detail] "expanded {e} to {e'}"
        return .continue e'
    | _ => return .continue
  if e != e₂ then
    trace[to_additive_detail] "expand:\nBefore: {e}\nAfter: {e₂}"
  return e₂

/-- Implementation function for `additiveTest`.
Failure means that in that subexpression there is no constant that blocks `e` from being translated.
We cache previous applications of the function, using an expression cache using ptr equality
to avoid visiting the same subexpression many times. Note that we only need to cache the
expressions without taking the value of `inApp` into account, since `inApp` only matters when
the expression is a constant. However, for this reason we have to make sure that we never
cache constant expressions, so that's why the `if`s in the implementation are in this order.

Note that this function is still called many times by `applyReplacementFun`
and we're not remembering the cache between these calls. -/
unsafe def additiveTestUnsafe (env : Environment) (b : BundledExts) (e : Expr)
    (dontTranslate : Array FVarId) : Option (Name ⊕ FVarId) :=
  let rec visit (e : Expr) (inApp := false) : OptionT (StateM (PtrSet Expr)) (Name ⊕ FVarId) := do
    if e.isConst then
      if (b.dontTranslateAttr.find? env e.constName).isNone &&
        (inApp || (findTranslation? env b e.constName).isSome) then
        failure
      else
        return .inl e.constName
    if (← get).contains e then
      failure
    modify fun s => s.insert e
    match e with
    | x@(.app e a)       =>
        visit e true <|> do
          -- make sure that we don't treat `(fun x => α) (n + 1)` as a type that depends on `Nat`
          guard !x.isConstantApplication
          if let some n := e.getAppFn.constName? then
            if let some l := b.ignoreArgsAttr.find? env n then
              if e.getAppNumArgs + 1 ∈ l then
                failure
          visit a
    | .lam _ _ t _       => visit t
    | .forallE _ _ t _   => visit t
    | .letE _ _ e body _ => visit e <|> visit body
    | .mdata _ b         => visit b
    | .proj _ _ b        => visit b
    | .fvar fvarId       => if dontTranslate.contains fvarId then return .inr fvarId else failure
    | _                  => failure
  Id.run <| (visit e).run' mkPtrSet

/-- `additiveTest e` tests whether the expression `e` contains a constant
`nm` that is not applied to any arguments, and such that `translations.find?[nm] = none`.
This is used in `@[to_additive]` for deciding which subexpressions to transform: we only transform
constants if `additiveTest` applied to their relevant argument returns `true`.
This means we will replace expression applied to e.g. `α` or `α × β`, but not when applied to
e.g. `ℕ` or `ℝ × α`.
We ignore all arguments specified by the `ignore` `NameMap`. -/
def additiveTest (env : Environment) (b : BundledExts) (e : Expr)
    (dontTranslate : Array FVarId := #[]) : Option (Name ⊕ FVarId) :=
  unsafe additiveTestUnsafe env b e dontTranslate

/-- Swap the first two elements of a list -/
def _root_.List.swapFirstTwo {α : Type _} : List α → List α
  | []      => []
  | [x]     => [x]
  | x::y::l => y::x::l

/-- Change the numeral `nat_lit 1` to the numeral `nat_lit 0`.
Leave all other expressions unchanged. -/
def changeNumeral : Expr → Expr
  | .lit (.natVal 1) => mkRawNatLit 0
  | e                => e

/--
`applyReplacementFun e` replaces the expression `e` with its additive counterpart.
It translates each identifier (inductive type, defined function etc) in an expression, unless
* The identifier occurs in an application with first argument `arg`; and
* `test arg` is false.
However, if `f` is in the dictionary `relevant`, then the argument `relevant.find f`
is tested, instead of the first argument.

It will also reorder arguments of certain functions, using `reorderFn`:
e.g. `g x₁ x₂ x₃ ... xₙ` becomes `g x₂ x₁ x₃ ... xₙ` if `reorderFn g = some [1]`.
-/
def applyReplacementFun (b : BundledExts) (e : Expr) (dontTranslate : Array FVarId := #[]) :
    MetaM Expr := do
  let e' := aux (← getEnv) (← getBoolOption `trace.to_additive_detail) (← expand b e)
  -- Make sure any new reserved names in the expr are realized; this needs to be done outside of
  -- `aux` as it is monadic.
  e'.forEach fun
    | .const n .. => do
      if !(← hasConst (skipRealize := false) n) && isReservedName (← getEnv) n then
        executeReservedNameAction n
    | _ => pure ()
  return e'
where /-- Implementation of `applyReplacementFun`. -/
  aux (env : Environment) (trace : Bool) : Expr → Expr :=
  let reorderFn : Name → List (List ℕ) := fun nm ↦ (b.reorderAttr.find? env nm |>.getD [])
  let relevantArg : Name → ℕ := fun nm ↦ (b.relevantArgAttr.find? env nm).getD 0
  Lean.Expr.replaceRec fun r e ↦ Id.run do
    if trace then
      dbg_trace s!"replacing at {e}"
    match e with
    | .const n₀ ls₀ => do
      let n₁ := findPrefixTranslation env n₀ b
      let ls₁ : List Level := if 0 ∈ (reorderFn n₀).flatten then ls₀.swapFirstTwo else ls₀
      if trace then
        if n₀ != n₁ then
          dbg_trace s!"changing {n₀} to {n₁}"
        if 0 ∈ (reorderFn n₀).flatten then
          dbg_trace s!"reordering the universe variables from {ls₀} to {ls₁}"
      return some <| .const n₁ ls₁
    | .app g x => do
      let mut gf := g.getAppFn
      if gf.isBVar && x.isLit then
        if trace then
          dbg_trace s!"applyReplacementFun: Variables applied to numerals are not changed {g.app x}"
        return some <| g.app x
      let mut gAllArgs := e.getAppArgs
      let some nm := gf.constName? | return mkAppN (← r gf) (← gAllArgs.mapM r)
      -- e = `(nm y₁ .. yₙ x)
      /- Test if the head should not be replaced. -/
      let relevantArgId := relevantArg nm
      if h : relevantArgId < gAllArgs.size then
        if let some fxd := additiveTest env b gAllArgs[relevantArgId] dontTranslate then
          if trace then
            match fxd with
            | .inl fxd => dbg_trace s!"The application of {nm} contains the fixed type \
              {fxd}, so it is not changed."
            | .inr _ => dbg_trace s!"The application of {nm} contains a fixed \
              variable so it is not changed."
        else
          gf ← r gf
          /- Test if arguments should be reordered. -/
          let reorder := reorderFn nm
          if !reorder.isEmpty then
            gAllArgs := gAllArgs.permute! reorder
            if trace then
              dbg_trace s!"reordering the arguments of {nm} using the cyclic permutations {reorder}"
      else
        gf ← r gf
      /- Do not replace numerals in specific types. -/
      if let some changedArgNrs := changeNumeralAttr.find? env nm then
        let firstArg := gAllArgs[0]!
        if additiveTest env b firstArg dontTranslate |>.isNone then
          if trace then
            dbg_trace s!"applyReplacementFun: We change the numerals in this expression. \
              However, we will still recurse into all the non-numeral arguments."
          -- In this case, we still update all arguments of `g` that are not numerals,
          -- since all other arguments can contain subexpressions like
          -- `(fun x ↦ ℕ) (1 : G)`, and we have to update the `(1 : G)` to `(0 : G)`
          gAllArgs := gAllArgs.mapIdx fun argNr arg ↦
            if changedArgNrs.contains argNr then
              changeNumeral arg
            else
              arg
      return mkAppN gf (← gAllArgs.mapM r)
    | .proj n₀ idx e => do
      let n₁ := findPrefixTranslation env n₀ b
      if trace then
        dbg_trace s!"applyReplacementFun: in projection {e}.{idx} of type {n₀}, \
          replace type with {n₁}"
      return some <| .proj n₁ idx <| ← r e
    | _ => return none

/-- Rename binder names in pi type. -/
def renameBinderNames (b : BundledExts) (src : Expr) : Expr :=
  src.mapForallBinderNames fun
    | .str p s => .str p (b.guessName s)
    | n => n

/-- Reorder pi-binders. See doc of `reorderAttr` for the interpretation of the argument -/
def reorderForall (reorder : List (List Nat)) (src : Expr) : MetaM Expr := do
  if let some maxReorder := reorder.flatten.max? then
    forallBoundedTelescope src (some (maxReorder + 1)) fun xs e => do
      if xs.size = maxReorder + 1 then
        mkForallFVars (xs.permute! reorder) e
      else
        throwError "the permutation\n{reorder}\nprovided by the `(reorder := ...)` option is \
          out of bounds, the type{indentExpr src}\nhas only {xs.size} arguments"
  else
    return src

/-- Reorder lambda-binders. See doc of `reorderAttr` for the interpretation of the argument -/
def reorderLambda (reorder : List (List Nat)) (src : Expr) : MetaM Expr := do
  if let some maxReorder := reorder.flatten.max? then
    let maxReorder := maxReorder + 1
    lambdaBoundedTelescope src maxReorder fun xs e => do
      if xs.size = maxReorder then
        mkLambdaFVars (xs.permute! reorder) e
      else
        -- we don't have to consider the case where the given permutation is out of bounds,
        -- since `reorderForall` applied to the type would already have failed in that case.
        forallBoundedTelescope (← inferType e) (maxReorder - xs.size) fun ys _ => do
          mkLambdaFVars ((xs ++ ys).permute! reorder) (mkAppN e ys)
  else
    return src

/-- Run `applyReplacementFun` on an expression `∀ x₁ .. xₙ, e`,
making sure not to translate type-classes on `xᵢ` if `i` is in `dontTranslate`. -/
def applyReplacementForall (b : BundledExts) (dontTranslate : List Nat) (e : Expr) :
    MetaM Expr := do
  if let some maxDont := dontTranslate.max? then
    forallBoundedTelescope e (some (maxDont + 1)) fun xs e => do
      let xs := xs.map (·.fvarId!)
      let dontTranslate := dontTranslate.filterMap (xs[·]?) |>.toArray
      let mut e ← applyReplacementFun b e dontTranslate
      for x in xs.reverse do
        let decl ← x.getDecl
        let xType ← applyReplacementFun b decl.type dontTranslate
        e := .forallE decl.userName xType (e.abstract #[.fvar x]) decl.binderInfo
      return e
  else
    applyReplacementFun b e #[]

/-- Run `applyReplacementFun` on an expression `fun x₁ .. xₙ ↦ e`,
making sure not to translate type-classes on `xᵢ` if `i` is in `dontTranslate`. -/
def applyReplacementLambda (b : BundledExts) (dontTranslate : List Nat) (e : Expr) :
    MetaM Expr := do
  if let some maxDont := dontTranslate.max? then
    lambdaBoundedTelescope e (maxDont + 1) fun xs e => do
      let xs := xs.map (·.fvarId!)
      let dontTranslate := dontTranslate.filterMap (xs[·]?) |>.toArray
      let mut e ← applyReplacementFun b e dontTranslate
      for x in xs.reverse do
        let decl ← x.getDecl
        let xType ← applyReplacementFun b decl.type dontTranslate
        e := .lam decl.userName xType (e.abstract #[.fvar x]) decl.binderInfo
      return e
  else
    applyReplacementFun b e #[]

/-- Unfold auxlemmas in the type and value. -/
def declUnfoldAuxLemmas (decl : ConstantInfo) : MetaM ConstantInfo := do
  let mut decl := decl
  decl := decl.updateType <| ← unfoldAuxLemmas decl.type
  if let some v := decl.value? then
    trace[to_additive] "value before unfold:{indentExpr v}"
    decl := decl.updateValue <| ← unfoldAuxLemmas v
    trace[to_additive] "value after unfold:{indentExpr decl.value!}"
  else if let .opaqueInfo info := decl then -- not covered by `value?`
    decl := .opaqueInfo { info with value := ← unfoldAuxLemmas info.value }
  return decl

/--
Given a list of variable local identifiers that shouldn't be translated,
determine the arguments that shouldn't be translated.

TODO: Currently, this function doesn't deduce any `dont_translate` types from `type`.
In the future we would like that the presence of `MonoidAlgebra k G` will automatically
flag `k` as a type to not be translated.
-/
def getDontTranslates (given : List Ident) (type : Expr) : MetaM (List Nat) := do
  forallTelescope type fun xs _ => do
    given.mapM fun id => withRef id.raw <| do
      let fvarId ← getFVarFromUserName id.getId
      return (xs.idxOf? fvarId).get!

/-- Run applyReplacementFun on the given `srcDecl` to make a new declaration with name `tgt` -/
def updateDecl (b : BundledExts) (tgt : Name) (srcDecl : ConstantInfo)
    (reorder : List (List Nat)) (dont : List Ident) : MetaM ConstantInfo := do
  let mut decl := srcDecl.updateName tgt
  if 0 ∈ reorder.flatten then
    decl := decl.updateLevelParams decl.levelParams.swapFirstTwo
  let dont ← getDontTranslates dont srcDecl.type
  decl := decl.updateType <| ← reorderForall reorder <| ← applyReplacementForall b dont <|
    renameBinderNames b decl.type
  if let some v := decl.value? then
    decl := decl.updateValue <| ← reorderLambda reorder <| ← applyReplacementLambda b dont v
  else if let .opaqueInfo info := decl then -- not covered by `value?`
    decl := .opaqueInfo { info with
      value := ← reorderLambda reorder <| ← applyReplacementLambda b dont info.value }
  return decl

/-- Abstracts the nested proofs in the value of `decl` if it is a def. -/
def declAbstractNestedProofs (decl : ConstantInfo) : MetaM ConstantInfo := do
  if decl matches .defnInfo _ then
    return decl.updateValue <| ← withDeclNameForAuxNaming decl.name do
      Meta.abstractNestedProofs decl.value!
  else
    return decl

/-- Find the target name of `pre` and all created auxiliary declarations. -/
def findTargetName (env : Environment) (b : BundledExts) (src pre tgt_pre : Name) : CoreM Name :=
  /- This covers auxiliary declarations like `match_i` and `proof_i`. -/
  if let some post := pre.isPrefixOf? src then
    return tgt_pre ++ post
  /- This covers equation lemmas (for other declarations). -/
  else if let some post := privateToUserName? src then
    match findTranslation? env b post.getPrefix with
    -- this is an equation lemma for a declaration without `to_additive`. We will skip this.
    | none => return src
    -- this is an equation lemma for a declaration with `to_additive`. We will additivize this.
    -- Note: if this errors we could do this instead by calling `getEqnsFor?`
    | some addName => return src.updatePrefix <| mkPrivateName env addName
  else if src.hasMacroScopes then
    mkFreshUserName src.eraseMacroScopes
  else
    throwError "internal @[{b.attrName}] error."

/-- Returns a `NameSet` of all auxiliary constants in `e` that might have been generated
when adding `pre` to the environment.
Examples include `pre.match_5` and
`_private.Mathlib.MyFile.someOtherNamespace.someOtherDeclaration._eq_2`.
The last two examples may or may not have been generated by this declaration.
The last example may or may not be the equation lemma of a declaration with the `@[to_additive]`
attribute. We will only translate it if it has the `@[to_additive]` attribute.

Note that this function would return `proof_nnn` aux lemmas if
we hadn't unfolded them in `declUnfoldAuxLemmas`.
-/
def findAuxDecls (e : Expr) (pre : Name) : NameSet :=
  e.foldConsts ∅ fun n l ↦
    if n.getPrefix == pre || isPrivateName n || n.hasMacroScopes then
      l.insert n
    else
      l

/-- Transform the declaration `src` and all declarations `pre._proof_i` occurring in `src`
using the transforms dictionary.

`replace_all`, `trace`, `ignore` and `reorder` are configuration options.

`pre` is the declaration that got the `@[to_additive]` attribute and `tgt_pre` is the target of this
declaration. -/
partial def transformDeclAux (b : BundledExts) (cfg : Config) (pre tgt_pre : Name) :
    Name → CoreM Unit := fun src ↦ do
  let env ← getEnv
  trace[to_additive_detail] "visiting {src}"
  -- if we have already translated this declaration, we do nothing.
  if (findTranslation? env b src).isSome && src != pre then
      return
  -- if this declaration is not `pre` and not an internal declaration, we return an error,
  -- since we should have already translated this declaration.
  if src != pre && !src.isInternalDetail then
    throwError "The declaration {pre} depends on the declaration {src} which is in the namespace \
      {pre}, but does not have the `@[{b.attrName}]` attribute. This is not supported.\n\
      Workaround: move {src} to a different namespace."
  -- we find the additive name of `src`
  let tgt ← findTargetName env b src pre tgt_pre
  -- we skip if we already transformed this declaration before.
  if env.contains tgt then
    if tgt == src then
      -- Note: this can happen for equation lemmas of declarations without `@[to_additive]`.
      trace[to_additive_detail] "Auxiliary declaration {src} will be translated to itself."
    else
      trace[to_additive_detail] "Already visited {tgt} as translation of {src}."
    return
  let srcDecl ← getConstInfo src
  -- we first unfold all auxlemmas, since they are not always able to be additivized on their own
  let srcDecl ← MetaM.run' do declUnfoldAuxLemmas srcDecl
  -- we then transform all auxiliary declarations generated when elaborating `pre`
  for n in findAuxDecls srcDecl.type pre do
    transformDeclAux b cfg pre tgt_pre n
  if let some value := srcDecl.value? then
    for n in findAuxDecls value pre do
      transformDeclAux b cfg pre tgt_pre n
  if let .opaqueInfo {value, ..} := srcDecl then
    for n in findAuxDecls value pre do
      transformDeclAux b cfg pre tgt_pre n
  -- if the auxiliary declaration doesn't have prefix `pre`, then we have to add this declaration
  -- to the translation dictionary, since otherwise we cannot find the additive name.
  if !pre.isPrefixOf src then
    insertTranslation b src tgt
  -- now transform the source declaration
  let trgDecl : ConstantInfo ← MetaM.run' <|
    if src == pre then
      updateDecl b tgt srcDecl cfg.reorder cfg.dontTranslate
    else
      updateDecl b tgt srcDecl [] []
  let value ← match trgDecl with
    | .thmInfo { value, .. } | .defnInfo { value, .. } | .opaqueInfo { value, .. } => pure value
    | _ => throwError "Expected {tgt} to have a value."
  trace[to_additive] "generating\n{tgt} : {trgDecl.type} :=\n  {value}"
  try
    -- make sure that the type is correct,
    -- and emit a more helpful error message if it fails
    MetaM.run' <| check value
  catch
    | Exception.error _ msg => throwError "@[{b.attrName}] failed. \
      The translated value is not type correct. For help, see the docstring \
      of `to_additive.attr`, section `Troubleshooting`. \
      Failed to add declaration\n{tgt}:\n{msg}"
    | _ => panic! "unreachable"
  -- "Refold" all the aux lemmas that we unfolded.
  let trgDecl ← MetaM.run' <| declAbstractNestedProofs trgDecl
  /- If `src` is explicitly marked as `noncomputable`, then add the new decl as a declaration but
  do not compile it, and mark is as noncomputable. Otherwise, only log errors in compiling if `src`
  has executable code.

  Note that `noncomputable section` does not explicitly mark noncomputable definitions as
  `noncomputable`, but simply abstains from logging compilation errors.

  This is not a perfect solution, as ideally `to_additive` *should* complain when `src` should
  produce executable code but fails to do so (e.g. outside of `noncomputable section`). However,
  the `messages` and `infoState` are reset before this runs, so we cannot check for compilation
  errors on `src`. The scope set by `noncomputable` section lives in the `CommandElabM` state
  (which is inaccessible here), so we cannot test for `noncomputable section` directly. See [Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/to_additive.20and.20noncomputable/with/310541981). -/
  if isNoncomputable env src then
    addDecl trgDecl.toDeclaration!
    setEnv <| addNoncomputable (← getEnv) tgt
  else
    addAndCompile trgDecl.toDeclaration! (logCompileErrors := (IR.findEnvDecl env src).isSome)
  if let .defnDecl { hints := .abbrev, .. } := trgDecl.toDeclaration! then
    if (← getReducibilityStatus src) == .reducible then
      setReducibilityStatus tgt .reducible
    if Compiler.getInlineAttribute? (← getEnv) src == some .inline then
      MetaM.run' <| Meta.setInlineAttribute tgt
  -- now add declaration ranges so jump-to-definition works
  -- note: we currently also do this for auxiliary declarations, while they are not normally
  -- generated for those. We could change that.
  addDeclarationRangesFromSyntax tgt (← getRef) cfg.ref
  if isProtected (← getEnv) src then
    setEnv <| addProtected (← getEnv) tgt
  if defeqAttr.hasTag (← getEnv) src then
    defeqAttr.setTag tgt
  if let some matcherInfo ← getMatcherInfo? src then
    /-
    Use `Match.addMatcherInfo tgt matcherInfo`
    once https://github.com/leanprover/lean4/pull/5068 is in
    -/
    modifyEnv fun env => Match.Extension.addMatcherInfo env tgt matcherInfo
  -- necessary so that e.g. match equations can be generated for `tgt`
  enableRealizationsForConst tgt

/-- Copy the instance attribute in a `to_additive`

[todo] it seems not to work when the `to_additive` is added as an attribute later. -/
def copyInstanceAttribute (src tgt : Name) : CoreM Unit := do
  if let some prio ← getInstancePriority? src then
    let attr_kind := (← getInstanceAttrKind? src).getD .global
    trace[to_additive_detail] "Making {tgt} an instance with priority {prio}."
    addInstance tgt attr_kind prio |>.run'

/-- Warn the user when the multiplicative declaration has an attribute. -/
def warnAttrCore (stx : Syntax) (f : Environment → Name → Bool)
    (thisAttr attrName src tgt : Name) : CoreM Unit := do
  if f (← getEnv) src then
    Linter.logLintIf linter.existingAttributeWarning stx <|
      m!"The source declaration {src} was given attribute {attrName} before calling @[{thisAttr}]. \
         The preferred method is to use `@[{thisAttr} (attr := {attrName})]` to apply the \
         attribute to both {src} and the target declaration {tgt}." ++
      if thisAttr == `to_additive then
        m!"\nSpecial case: If this declaration was generated by @[to_additive] \
          itself, you can use @[to_additive (attr := to_additive, {attrName})] on the original \
          declaration."
      else ""

/-- Warn the user when the multiplicative declaration has a simple scoped attribute. -/
def warnAttr {α β : Type} [Inhabited β] (stx : Syntax) (attr : SimpleScopedEnvExtension α β)
    (f : β → Name → Bool) (thisAttr attrName src tgt : Name) : CoreM Unit :=
  warnAttrCore stx (f <| attr.getState ·) thisAttr attrName src tgt

/-- Warn the user when the multiplicative declaration has a parametric attribute. -/
def warnParametricAttr {β : Type} [Inhabited β] (stx : Syntax) (attr : ParametricAttribute β)
    (thisAttr attrName src tgt : Name) : CoreM Unit :=
  warnAttrCore stx (attr.getParam? · · |>.isSome) thisAttr attrName src tgt

/-- `additivizeLemmas names argInfo desc t` runs `t` on all elements of `names`
and adds translations between the generated lemmas (the output of `t`).
`names` must be non-empty. -/
def additivizeLemmas {m : Type → Type} [Monad m] [MonadError m] [MonadLiftT CoreM m]
    (b : BundledExts) (names : Array Name) (argInfo : ArgInfo) (desc : String)
    (t : Name → m (Array Name)) : m Unit := do
  let auxLemmas ← names.mapM t
  let nLemmas := auxLemmas[0]!.size
  for (nm, lemmas) in names.zip auxLemmas do
    unless lemmas.size == nLemmas do
      throwError "{names[0]!} and {nm} do not generate the same number of {desc}."
  for (srcLemmas, tgtLemmas) in auxLemmas.zip <| auxLemmas.eraseIdx! 0 do
    for (srcLemma, tgtLemma) in srcLemmas.zip tgtLemmas do
      insertTranslationAndInfo b srcLemma tgtLemma argInfo

/--
Find the argument of `nm` that appears in the first multiplicative (type-class) argument.
Returns 1 if there are no types with a multiplicative class as arguments.
E.g. `Prod.instGroup` returns 1, and `Pi.instOne` returns 2.
Note: we only consider the relevant argument (`(relevant_arg := ...)`) of each type-class.
E.g. `[Pow A N]` is a multiplicative type-class on `A`, not on `N`.
-/
def findMultiplicativeArg (b : BundledExts) (nm : Name) : MetaM Nat := do
  forallTelescopeReducing (← getConstInfo nm).type fun xs ty ↦ do
    let env ← getEnv
    -- check if `tgt` has a multiplicative type argument, and if so,
    -- find the index of a type from `xs` appearing in there
    let multArg? (tgt : Expr) : Option Nat := do
      let c ← tgt.getAppFn.constName?
      guard (findTranslation? env b c).isSome
      let relevantArg := (b.relevantArgAttr.find? env c).getD 0
      let arg ← tgt.getArg? relevantArg
      xs.findIdx? (arg.containsFVar ·.fvarId!)
    -- run the above check on all hypotheses and on the conclusion
    let arg ← OptionT.run <| xs.firstM fun x ↦ OptionT.mk do
        forallTelescope (← inferType x) fun _ys tgt ↦ return multArg? tgt
    let arg := arg <|> multArg? ty
    trace[to_additive_detail] "findMultiplicativeArg: {arg}"
    return arg.getD 0

/-- Return the provided target name or autogenerate one if one was not provided. -/
def targetName (b : BundledExts) (cfg : Config) (src : Name) : CoreM Name := do
  if cfg.self then
    if cfg.tgt != .anonymous then
      logWarning m!"`{b.attrName} self` ignores the provided name {cfg.tgt}"
    return src
  let .str pre s := src | throwError "{b.attrName}: can't transport {src}"
  trace[to_additive_detail] "The name {s} splits as {s.splitCase}"
  let tgt_auto := b.guessName s
  let depth := cfg.tgt.getNumParts
  let pre := findPrefixTranslation (← getEnv) pre b
  let (pre1, pre2) := pre.splitAt (depth - 1)
  let res := if cfg.tgt == .anonymous then pre.str tgt_auto else pre1 ++ cfg.tgt
  if res == src then
    throwError "{b.attrName}: the generated translated name equals the original name '{src}'.\n\
    If this is intentional, use the `@[{b.attrName} self]` syntax.\n\
    Otherwise, check that your declaration name is correct \
    (if your declaration is an instance, try naming it)\n\
    or provide an additivised name using the `@[{b.attrName} my_add_name]` syntax."
  if cfg.tgt == pre2.str tgt_auto && !cfg.allowAutoName then
    Linter.logLintIf linter.toAdditiveGenerateName cfg.ref m!"\
      `{b.attrName}` correctly autogenerated target name for {src}.\n\
      You may remove the explicit argument {cfg.tgt}."
  if cfg.tgt != .anonymous then
    trace[to_additive_detail] "The automatically generated name would be {pre.str tgt_auto}"
  return res

/-- if `f src = #[a_1, ..., a_n]` and `f tgt = #[b_1, ... b_n]` then `proceedFieldsAux src tgt f`
will insert translations from `a_i` to `b_i`. -/
def proceedFieldsAux (b : BundledExts) (src tgt : Name) (argInfo : ArgInfo)
    (f : Name → Array Name) : CoreM Unit := do
  let srcFields := f src
  let tgtFields := f tgt
  if srcFields.size != tgtFields.size then
    throwError "Failed to map fields of {src}, {tgt} with {srcFields} ↦ {tgtFields}.\n \
      Lengths do not match."
  for srcField in srcFields, tgtField in tgtFields do
    insertTranslationAndInfo b srcField tgtField argInfo

/-- Add the structure fields of `src` to the translations dictionary
so that future uses of `to_additive` will map them to the corresponding `tgt` fields. -/
def proceedFields (b : BundledExts) (src tgt : Name) (argInfo : ArgInfo) : CoreM Unit := do
  let env ← getEnv
  let aux := proceedFieldsAux b src tgt argInfo
  -- add translations for the structure fields
  aux fun declName ↦
    if isStructure env declName then
      let info := getStructureInfo env declName
      Array.ofFn (n := info.fieldNames.size) (info.getProjFn? · |>.get!)
    else
      #[]
  -- add translations for the automatically generated instances with `extend`.
  aux fun declName ↦
    if isStructure env declName then
      getStructureInfo env declName |>.parentInfo
        |>.filterMap fun c ↦ if !c.subobject then c.projFn else none
    else
      #[]
  -- add translations for the constructors of an inductive type
  aux fun declName ↦ match env.find? declName with
    | some (ConstantInfo.inductInfo { ctors, .. }) => ctors.toArray
    | _ => #[]

/-- Elaboration of the configuration options for `to_additive`.
This function also works for other tranlation attributes like `to_dual`. -/
def elabToAdditive (stx : Syntax) : CoreM Config :=
  match stx[2] with
  | `(toAdditiveRest| $existing? $[$opts:toAdditiveOption]* $[$tgt]? $[$doc]?) => do
    let mut attrs := #[]
    let mut reorder := []
    let mut relevantArg? := none
    let mut dontTranslate := []
    for opt in opts do
      match opt with
      | `(toAdditiveOption| (attr := $[$stxs],*)) =>
        attrs := attrs ++ stxs
      | `(toAdditiveOption| (reorder := $[$[$reorders:num]*],*)) =>
        for cycle in reorders do
          if h : cycle.size = 1 then
            throwErrorAt cycle[0] "\
              invalid cycle `{cycle[0]}`, a cycle must have at least 2 elements.\n\
              `(reorder := ...)` uses cycle notation to specify a permutation.\n\
              For example `(reorder := 1 2, 5 6)` swaps the first two arguments with each other \
              and the fifth and the sixth argument and `(reorder := 3 4 5)` will move \
              the fifth argument before the third argument."
          let cycle ← cycle.toList.mapM fun n => match n.getNat with
            | 0 => throwErrorAt n "invalid position `{n}`, positions are counted starting from 1."
            | n+1 => pure n
          reorder := cycle :: reorder
      | `(toAdditiveOption| (relevant_arg := $n)) =>
        if let some arg := relevantArg? then
          throwErrorAt opt "cannot specify `relevant_arg` multiple times"
        else
          relevantArg? := n.getNat.pred
      | `(toAdditiveOption| (dont_translate := $[$types:ident]*)) =>
        dontTranslate := dontTranslate ++ types.toList
      | _ => throwUnsupportedSyntax
    let (existing, self) := match existing? with
      | `(toAdditiveNameHint| existing) => (true, false)
      | `(toAdditiveNameHint| self) => (true, true)
      | _ => (false, false)
    if self && !attrs.isEmpty then
      throwError "invalid `(attr := ...)` after `self`, \
        as there is only one declaration for the attributes.\n\
        Instead, you can write the attributes in the usual way."
    trace[to_additive_detail] "attributes: {attrs}; reorder arguments: {reorder}"
    let doc ← doc.mapM fun
      | `(str|$doc:str) => open Linter in do
        -- Deprecate `str` docstring syntax (since := "2025-08-12")
        if getLinterValue linter.deprecated (← getLinterOptions) then
          let hintSuggestion := {
            diffGranularity := .none
            toTryThisSuggestion := { suggestion := "/-- " ++ doc.getString.trim ++ " -/" }
          }
          let sugg ← Hint.mkSuggestionsMessage #[hintSuggestion] doc
            (codeActionPrefix? := "Update to: ") (forceList := false)
          logWarningAt doc <| .tagged ``Linter.deprecatedAttr
            m!"String syntax for `to_additive` docstrings is deprecated: Use \
              docstring syntax instead (e.g. `@[to_additive /-- example -/]`)\n\
              \n\
              Update deprecated syntax to:{sugg}"
        return doc.getString
      | `(docComment|$doc:docComment) => do
        -- TODO: rely on `addDocString`s call to `validateDocComment` after removing `str` support
        /-
        #adaptation_note
        Without understanding the consequences, I am commenting out the next line,
        as `validateDocComment` is now in `TermElabM` which is not trivial to reach from here.
        Perhaps the existing comments here suggest it is no longer needed, anyway?
        -/
        -- validateDocComment doc
        /- Note: the following replicates the behavior of `addDocString`. However, this means that
        trailing whitespace might appear in docstrings added via `docComment` syntax when compared
        to those added via `str` syntax. See this [Zulip thread](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Why.20do.20docstrings.20include.20trailing.20whitespace.3F/with/533553356). -/
        return (← getDocStringText doc).removeLeadingSpaces
      | _ => throwUnsupportedSyntax
    return {
      trace := !stx[1].isNone
      tgt := (tgt.map (·.getId)).getD Name.anonymous
      doc, attrs, reorder, relevantArg?, dontTranslate, existing, self
      ref := (tgt.map (·.raw)).getD stx[0] }
  | _ => throwUnsupportedSyntax

mutual
/-- Apply attributes to the multiplicative and additive declarations. -/
partial def applyAttributes (b : BundledExts) (stx : Syntax) (rawAttrs : Array Syntax)
    (thisAttr src tgt : Name) (argInfo : ArgInfo) : TermElabM (Array Name) := do
  -- we only copy the `instance` attribute, since `@[to_additive] instance` is nice to allow
  copyInstanceAttribute src tgt
  -- Warn users if the multiplicative version has an attribute
  if src != tgt && linter.existingAttributeWarning.get (← getOptions) then
    let appliedAttrs ← getAllSimpAttrs src
    if appliedAttrs.size > 0 then
      let appliedAttrs := ", ".intercalate (appliedAttrs.toList.map toString)
      -- Note: we're not bothering to print the correct attribute arguments.
      Linter.logLintIf linter.existingAttributeWarning stx m!"\
        The source declaration {src} was given the simp-attribute(s) {appliedAttrs} before \
        calling @[{thisAttr}].\nThe preferred method is to use something like \
        `@[{thisAttr} (attr := {appliedAttrs})]`\nto apply the attribute to both \
        {src} and the target declaration {tgt}."
    warnAttr stx Lean.Elab.Tactic.Ext.extExtension
      (fun b n => (b.tree.values.any fun t => t.declName = n)) thisAttr `ext src tgt
    warnAttr stx Lean.Meta.Rfl.reflExt (·.values.contains ·) thisAttr `refl src tgt
    warnAttr stx Lean.Meta.Symm.symmExt (·.values.contains ·) thisAttr `symm src tgt
    warnAttr stx Batteries.Tactic.transExt (·.values.contains ·) thisAttr `trans src tgt
    warnAttr stx Lean.Meta.coeExt (·.contains ·) thisAttr `coe src tgt
    warnParametricAttr stx Lean.Linter.deprecatedAttr thisAttr `deprecated src tgt
    -- the next line also warns for `@[to_additive, simps]`, because of the application times
    warnParametricAttr stx simpsAttr thisAttr `simps src tgt
    warnAttrCore stx Term.elabAsElim.hasTag thisAttr `elab_as_elim src tgt
  -- add attributes
  -- the following is similar to `Term.ApplyAttributesCore`, but we hijack the implementation of
  -- `simps` and `to_additive`.
  let attrs ← elabAttrs rawAttrs
  let (additiveAttrs, attrs) := attrs.partition (·.name == thisAttr)
  let nestedDecls ←
    match h : additiveAttrs.size with
      | 0 => pure #[]
      | 1 => addToAdditiveAttr b tgt (← elabToAdditive additiveAttrs[0].stx) additiveAttrs[0].kind
      | _ => throwError "cannot apply {thisAttr} multiple times."
  let allDecls := #[src, tgt] ++ nestedDecls
  if attrs.size > 0 then
    trace[to_additive_detail] "Applying attributes {attrs.map (·.stx)} to {allDecls}"
  for attr in attrs do
    withRef attr.stx do withLogging do
    if attr.name == `simps then
      additivizeLemmas b allDecls argInfo "simps lemmas" (simpsTacFromSyntax · attr.stx)
      return
    let env ← getEnv
    match getAttributeImpl env attr.name with
    | Except.error errMsg => throwError errMsg
    | Except.ok attrImpl =>
      let runAttr := do
        for decl in allDecls do
          attrImpl.add decl attr.stx attr.kind
      -- not truly an elaborator, but a sensible target for go-to-definition
      let elaborator := attrImpl.ref
      if (← getInfoState).enabled && (← getEnv).contains elaborator then
        withInfoContext (mkInfo := return .ofCommandInfo { elaborator, stx := attr.stx }) do
          try runAttr
          finally if attr.stx[0].isIdent || attr.stx[0].isAtom then
            -- Add an additional node over the leading identifier if there is one
            -- to make it look more function-like.
            -- Do this last because we want user-created infos to take precedence
            pushInfoLeaf <| .ofCommandInfo { elaborator, stx := attr.stx[0] }
      else
        runAttr
  return nestedDecls

/--
Copies equation lemmas and attributes from `src` to `tgt`
-/
partial def copyMetaData (b : BundledExts) (cfg : Config) (src tgt : Name) (argInfo : ArgInfo) :
    CoreM (Array Name) := do
  if let some eqns := eqnsAttribute.find? (← getEnv) src then
    unless (eqnsAttribute.find? (← getEnv) tgt).isSome do
      for eqn in eqns do
        _ ← addToAdditiveAttr b eqn cfg
      eqnsAttribute.add tgt (eqns.map (findTranslation? (← getEnv) b · |>.get!))
  else
    /- We need to generate all equation lemmas for `src` and `tgt`, even for non-recursive
    definitions. If we don't do that, the equation lemma for `src` might be generated later
    when doing a `rw`, but it won't be generated for `tgt`. -/
    additivizeLemmas b #[src, tgt] argInfo "equation lemmas" fun nm ↦
      (·.getD #[]) <$> MetaM.run' (getEqnsFor? nm)
  MetaM.run' <| Elab.Term.TermElabM.run' <|
    (applyAttributes b cfg.ref cfg.attrs b.attrName src tgt) argInfo

/--
Make a new copy of a declaration, replacing fragments of the names of identifiers in the type and
the body using the `translations` dictionary.
This is used to implement `@[to_additive]`.
-/
partial def transformDecl (b : BundledExts) (cfg : Config) (src tgt : Name)
    (argInfo : ArgInfo := {}) : CoreM (Array Name) := do
  transformDeclAux b cfg src tgt src
  copyMetaData b cfg src tgt argInfo

/-- Verify that the type of given `srcDecl` translates to that of `tgtDecl`. -/
partial def checkExistingType (b : BundledExts) (src tgt : Name) (reorder : List (List Nat))
    (dont : List Ident) : MetaM Unit := do
  let mut srcDecl ← getConstInfo src
  let tgtDecl ← getConstInfo tgt
  if 0 ∈ reorder.flatten then
    srcDecl := srcDecl.updateLevelParams srcDecl.levelParams.swapFirstTwo
  unless srcDecl.levelParams.length == tgtDecl.levelParams.length do
    throwError "`{b.attrName}` validation failed:\n  expected {srcDecl.levelParams.length} \
      universe levels, but '{tgt}' has {tgtDecl.levelParams.length} universe levels"
  -- instantiate both types with the same universes. `instantiateLevelParams` applies some
  -- normalization, so we have to apply it to both types.
  let type := srcDecl.type.instantiateLevelParams
    srcDecl.levelParams (tgtDecl.levelParams.map mkLevelParam)
  let tgtType := tgtDecl.type.instantiateLevelParams
    tgtDecl.levelParams (tgtDecl.levelParams.map mkLevelParam)
  let dont ← getDontTranslates dont type
  let type  ← reorderForall reorder <| ← applyReplacementForall b dont <| ← unfoldAuxLemmas type
  -- `instantiateLevelParams` normalizes universes, so we have to normalize both expressions
  unless ← withReducible <| isDefEq type tgtType do
    throwError "`{b.attrName}` validation failed: expected{indentExpr type}\nbut '{tgt}' has \
      type{indentExpr tgtType}"

/-- `addToAdditiveAttr src cfg` adds a `@[to_additive]` attribute to `src` with configuration `cfg`.
See the attribute implementation for more details.
It returns an array with names of additive declarations (usually 1, but more if there are nested
`to_additive` calls. -/
partial def addToAdditiveAttr (b : BundledExts) (src : Name) (cfg : Config)
    (kind := AttributeKind.global) : AttrM (Array Name) := do
  if (kind != AttributeKind.global) then
    throwError "`{b.attrName}` can only be used as a global attribute"
  withOptions (· |>.updateBool `trace.to_additive (cfg.trace || ·)) <| do
  if let some tgt := findTranslation? (← getEnv) b src then
    -- we allow `to_additive (reorder := ...)` or `to_additive (relevant_arg := ...)` syntax
    -- for updating this information on constants that are already tagged
    -- for example, this is necessary for `HPow.hPow`
    if cfg.reorder != [] then
      modifyEnv (b.reorderAttr.addEntry · (src, cfg.reorder))
      return #[tgt]
    if let some relevantArg := cfg.relevantArg? then
      modifyEnv (b.relevantArgAttr.addEntry · (src, relevantArg))
      return #[tgt]
  let tgt ← targetName b cfg src
  let alreadyExists := (← getEnv).contains tgt
  if cfg.existing != alreadyExists && !(← isInductive src) && !cfg.self then
    Linter.logLintIf linter.toAdditiveExisting cfg.ref <|
      if alreadyExists then
        m!"The translated declaration already exists. Please specify this explicitly using \
           `@[{b.attrName} existing]`."
      else
        "The additive declaration doesn't exist. Please remove the option `existing`."
  if alreadyExists then
    MetaM.run' <| checkExistingType b src tgt cfg.reorder cfg.dontTranslate
  let relevantArg ← cfg.relevantArg?.getDM <| MetaM.run' <| findMultiplicativeArg b src
  let argInfo := { reorder := cfg.reorder, relevantArg }
  insertTranslationAndInfo b src tgt argInfo alreadyExists
  let nestedNames ←
    if alreadyExists then
      -- since `tgt` already exists, we just need to copy metadata and
      -- add translations `src.x ↦ tgt.x'` for any subfields.
      trace[to_additive_detail] "declaration {tgt} already exists."
      proceedFields b src tgt argInfo
      copyMetaData b cfg src tgt argInfo
    else
      -- tgt doesn't exist, so let's make it
      transformDecl b cfg src tgt argInfo
  -- add pop-up information when mousing over `additive_name` of `@[to_additive additive_name]`
  -- (the information will be over the attribute of no additive name is given)
  pushInfoLeaf <| .ofTermInfo {
    elaborator := .anonymous, lctx := {}, expectedType? := none, isBinder := !alreadyExists,
    stx := cfg.ref, expr := ← mkConstWithLevelParams tgt }
  if let some doc := cfg.doc then
    addDocStringCore tgt doc
  return nestedNames.push tgt

end

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

/-- An extension that stores all the declarations that need their arguments reordered when
applying `@[to_additive]`. It is applied using the `to_additive (reorder := ...)` syntax. -/
initialize reorderAttr : NameMapExtension (List (List Nat)) ←
  registerNameMapExtension _

@[inherit_doc to_additive_relevant_arg]
initialize relevantArgAttr : NameMapExtension Nat ←
  registerNameMapAttribute {
    name := `to_additive_relevant_arg
    descr := "Auxiliary attribute for `to_additive` stating \
      which arguments are the types with a multiplicative structure."
    add := fun
    | _, stx@`(attr| to_additive_relevant_arg $id) => do
      Linter.logLintIf linter.toAdditiveRelevantArg stx
        m!"This attribute is deprecated. Use `@[to_additive (relevant_arg := ...)]` instead."
      pure <| id.getNat.pred
    | _, _ => throwUnsupportedSyntax }

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

/-- The bundle of environment extensions for `to_additive` -/
def toAdditiveBundle : BundledExts where
  ignoreArgsAttr := ignoreArgsAttr
  reorderAttr := reorderAttr
  relevantArgAttr := relevantArgAttr
  dontTranslateAttr := dontTranslateAttr
  translations := translations
  attrName := `to_additive
  changeNumeral := true
  isDual := false
  guessName := guessToAdditiveName

initialize registerBuiltinAttribute {
    name := `to_additive
    descr := "Transport multiplicative to additive"
    add := fun src stx kind ↦ discard do
      addToAdditiveAttr toAdditiveBundle src (← elabToAdditive stx) kind
    -- we (presumably) need to run after compilation to properly add the `simp` attribute
    applicationTime := .afterCompilation
  }

end ToAdditive
