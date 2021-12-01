/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov, Floris van Doorn
-/
import Mathlib.Data.List.Defs
import Mathlib.Data.String.Defs
import Mathlib.Lean.Expr
import Mathlib.Lean.Syntax

/-!
# Transport multiplicative to additive

This file defines an attribute `toAdditive` that can be used to
automatically transport theorems and definitions (but not inductive
types and structures) from a multiplicative theory to an additive theory.

### Missing features

* Currently this is a no-op implementation.
* Does not support camelCase or CamelCase yet

-/

open Lean Meta

namespace ToAdditive

syntax (name := toAdditiveIgnoreArgs) "toAdditiveIgnoreArgs" num* : attr
syntax (name := toAdditiveRelevantArg) "toAdditiveRelevantArg" num : attr
syntax (name := toAdditiveReorder) "toAdditiveReorder" num* : attr
syntax (name := toAdditive) "toAdditive" (ppSpace ident)? (ppSpace str)? : attr
syntax (name := toAdditive!) "toAdditive!" (ppSpace ident)? (ppSpace str)? : attr
syntax (name := toAdditive?) "toAdditive?" (ppSpace ident)? (ppSpace str)? : attr
syntax (name := toAdditive!?) "toAdditive!?" (ppSpace ident)? (ppSpace str)? : attr

/-!
An attribute that tells `@[toAdditive]` that certain arguments of this definition are not
involved when using `@[toAdditive]`.
This helps the heuristic of `@[toAdditive]` by also transforming definitions if `ℕ` or another
fixed type occurs as one of these arguments.
-/
initialize toAdditiveIgnoreArgsAttr : ParametricAttribute (Array Nat) ←
  registerParametricAttribute {
    name := `toAdditiveIgnoreArgs
    descr :=
      "Auxiliary attribute for `toAdditive` stating that certain arguments are not additivized."
    getParam := λ decl stx =>
      match stx with
        | `(attr|toAdditiveIgnoreArgs $[$ns]*) => ns.map (·.toNat)
        | _ => throwError "unexpected toAdditiveIgnoreArgs syntax {stx}"
  }

/-!
An attribute that is automatically added to declarations tagged with `@[toAdditive]`, if needed.

This attribute tells which argument is the type where this declaration uses the multiplicative
structure. If there are multiple argument, we typically tag the first one.
If this argument contains a fixed type, this declaration will note be additivized.
See the Heuristics section of `toAdditive.attr` for more details.

If a declaration is not tagged, it is presumed that the first argument is relevant.
`@[toAdditive]` uses the function `toAdditive.firstMultiplicativeArg` to automatically tag
declarations. It is ok to update it manually if the automatic tagging made an error.

Implementation note: we only allow exactly 1 relevant argument, even though some declarations
(like `Prod.Group`) have multiple arguments with a multiplicative structure on it.
The reason is that whether we additivize a declaration is an all-or-nothing decision, and if
we will not be able to additivize declarations that (e.g.) talk about multiplication on `ℕ × α`
anyway.

Warning: adding `@[toAdditive_reorder]` with an equal or smaller number than the number in this
attribute is currently not supported.
-/
initialize toAdditiveRelevantArgAttr : ParametricAttribute Nat ←
  registerParametricAttribute {
    name := `toAdditiveRelevantArg
    descr :=
      "Auxiliary attribute for `toAdditive` stating which arguments are the types with a " ++
      "multiplicative structure."
    getParam := λ decl stx =>
      match stx with
        | `(attr|toAdditiveRelevantArg $ns) => ns.toNat
        | _ => throwError "unexpected toAdditiveRelevantArg syntax {stx}"
  }

/-!
An attribute that stores all the declarations that needs their arguments reordered when
applying `@[toAdditive]`. Currently, we only support swapping consecutive arguments.
The list of the natural numbers contains the positions of the first of the two arguments
to be swapped.
If the first two arguments are swapped, the first two universe variables are also swapped.
Example: `@[toAdditive_reorder 1 4]` swaps the first two arguments and the arguments in
positions 4 and 5.
-/
initialize toAdditiveReorderAttr : ParametricAttribute (List Nat) ←
  registerParametricAttribute {
    name := `toAdditiveReorder
    descr :=
      "Auxiliary attribute for `toAdditive` that stores arguments that need to be reordered."
    getParam := λ decl stx =>
      match stx with
        | `(attr|toAdditiveReorder $[$ns]*) =>
          if (ns.map (·.isNatLit?)).all λ o => o.get! ≠ 0 then (ns.map (·.toNat)).toList
          else throwError "expected a list of (small) positive natural numbers at {ns}"
        | _ => throwError "unexpected toAdditiveReorder syntax {stx}" -- can this code be reached?
  }

  #check @forallTelescope
  #check MetaM
-- /--
-- Find the first argument of `nm` that has a multiplicative type-class on it.
-- Returns 1 if there are no types with a multiplicative class as arguments.
-- E.g. `Prod.Group` returns 1, and `Pi.One` returns 2.
-- -/
def firstMultiplicativeArg (nm : Name) (dict : NameMap Name) : CoreM Nat := do
  let env ← getEnv
  let some d ← env.find? nm | throwError "Cannot find declaration {nm}."
  let l ← MetaM.run' $ forallTelescope d.type λ es _ =>
    es.mapWithIndexM λ n bi => do
      let tgt := bi.type.piCodomain
      let n_bi := bi.type.piBinders.1.length
      let true ← return true /-hasAttribute `toAdditive tgt.get_app_fn.const_name-/ | return none
      let n2 := tgt.getAppArgs.head.get_app_fn.match_var.map λ m => n + n_bi - m
      return n2
  let l := l.reduceOption
  return if l.isEmpty then 1 else l.foldr min l.head!

/-- A command that can be used to have future uses of `toAdditive` change the `src` namespace
to the `tgt` namespace.

For example:
```
run_cmd toAdditive.mapNamespace `quotientGroup `quotientAddGroup
```

Later uses of `toAdditive` on declarations in the `quotientGroup` namespace will be created
in the `quotientAddGroup` namespaces.
-/
def mapNamespace (src tgt : Name) : CoreM Unit :=
return () -- todo
-- do let n := src.str "_toAdditive"
--    let decl := declaration.thm n [] `(unit) (return (reflect ()))
--    add_decl decl
--    aux_attr.set n tgt tt

/-- `toAdditive.Config` is the type of the arguments that can be provided to `toAdditive`.
`toAdditive.parser` parses the provided arguments:
* `replaceAll`: replace all multiplicative declarations, do not use the heuristic.
* `trace`: output the generated additive declaration.
* `tgt : name`: the name of the target (the additive declaration).
* `doc`: an optional doc string.
* if `allow_auto_name` is `false` (default) then `@[toAdditive]` will check whether the given name
  can be auto-generated.
-/
structure Config : Type :=
(replaceAll : Bool)
(trace : Bool)
(tgt : Name)
(doc : Option String)
(allow_auto_name : Bool)
deriving Inhabited

/-- `addCommPrefix x s` returns `"comm_" ++ s` if `x = tt` and `s` otherwise. -/
def addCommPrefix : Bool → String → String
| true,  s => "comm_" ++ s
| false, s => s

/-- Dictionary used by `toAdditive.guess_name` to autogenerate names. -/
def tr : Bool → List String → List String
| is_comm, "one" :: "le" :: s => addCommPrefix is_comm "nonneg" :: tr false s
| is_comm, "one" :: "lt" :: s => addCommPrefix is_comm "pos" :: tr false s
| is_comm, "le" :: "one" :: s => addCommPrefix is_comm "nonpos" :: tr false s
| is_comm, "lt" :: "one" :: s => addCommPrefix is_comm "neg" :: tr false s
| is_comm, "mul" :: "support" :: s => addCommPrefix is_comm "support" :: tr false s
| is_comm, "mul" :: "indicator" :: s => addCommPrefix is_comm "indicator" :: tr false s
| is_comm, "mul" :: s => addCommPrefix is_comm "add" :: tr false s
| is_comm, "smul" :: s => addCommPrefix is_comm "vadd" :: tr false s
| is_comm, "inv" :: s => addCommPrefix is_comm "neg" :: tr false s
| is_comm, "div" :: s => addCommPrefix is_comm "sub" :: tr false s
| is_comm, "one" :: s => addCommPrefix is_comm "zero" :: tr false s
| is_comm, "prod" :: s => addCommPrefix is_comm "sum" :: tr false s
| is_comm, "finprod" :: s => addCommPrefix is_comm "finsum" :: tr false s
| is_comm, "npow" :: s => addCommPrefix is_comm "nsmul" :: tr false s
| is_comm, "zpow" :: s => addCommPrefix is_comm "zsmul" :: tr false s
| is_comm, "monoid" :: s => ("add_" ++ addCommPrefix is_comm "monoid") :: tr false s
| is_comm, "submonoid" :: s => ("add_" ++ addCommPrefix is_comm "submonoid") :: tr false s
| is_comm, "group" :: s => ("add_" ++ addCommPrefix is_comm "group") :: tr false s
| is_comm, "subgroup" :: s => ("add_" ++ addCommPrefix is_comm "subgroup") :: tr false s
| is_comm, "semigroup" :: s => ("add_" ++ addCommPrefix is_comm "semigroup") :: tr false s
| is_comm, "magma" :: s => ("add_" ++ addCommPrefix is_comm "magma") :: tr false s
| is_comm, "haar" :: s => ("add_" ++ addCommPrefix is_comm "haar") :: tr false s
| is_comm, "prehaar" :: s => ("add_" ++ addCommPrefix is_comm "prehaar") :: tr false s
| is_comm, "comm" :: s => tr true s
| is_comm, x :: s => addCommPrefix is_comm x :: tr false s
| true, [] => ["comm"]
| false, [] => []

/-- Autogenerate target name for `toAdditive`. -/
def guessName : String → String :=
String.mapTokens ''' λ s => String.intercalate (String.singleton '_') $ tr false (s.splitOn "_")

/-- Return the provided target name or autogenerate one if one was not provided. -/
def targetName (src tgt : Name) (dict : NameMap Name) : CoreM Name := do
  let res ←
    if tgt.getPrefix != Name.anonymous -- we use `tgt` if it is a full name
    then return tgt
    else match src with
    | Name.str pre s d => do
      let tgtAuto := guessName s
      if toString tgt == tgtAuto && tgt != src then
        IO.println $
          "`toAdditive " ++ toString src ++ "`: correctly autogenerated target " ++
          "name, you may remove the explicit " ++ tgtAuto ++ " argument."
      return (Name.mkStr (pre.mapPrefix dict.find?) $
        if tgt == Name.anonymous then tgtAuto else toString tgt)
    | _ => throwError ("toAdditive: can't transport " ++ toString src)
  if res == src && tgt != src then throwError
    ("toAdditive: can't transport " ++ toString src ++
    " to itself.\nGive the desired additive name explicitly using `@[toAdditive additive_name]`.")
  else return res

-- /-- the parser for the arguments to `toAdditive`. -/
-- def parser : lean.parser Config := do
--   let bang ← Option.isSome <$> (tk "!")?
--   let ques ← Option.isSome <$> (tk "?")?
--   let tgt ← (ident)?
--   let e ← (texpr)?
--   let doc ←
--     match e with
--       | some pe => some <$> (to_expr pe >>= eval_expr String : tactic String)
--       | none => return none
--   return ⟨bang, ques, tgt.get_or_else Name.anonymous, doc, false⟩

-- def proceedFieldsAux (src tgt : Name) (prio : ℕ) (f : Name → CoreM (List String)) :
--   CoreM Unit := do
--   let srcFields ← f src
--   let tgtFields ← f tgt
--   if srcFields.length != tgtFields.length then
--     throwError ("Failed to map fields of " ++ toString src)
--   (srcFields.zip tgtFields).mapM λ names =>
--     if names.1 != names.2 then auxAttr (src.append names.1) (tgt.append names.2) tt prio
--     else _

-- /-- Add the `auxAttr` attribute to the structure fields of `src`
-- so that future uses of `toAdditive` will map them to the corresponding `tgt` fields. -/
-- def proceed_fields (env : Environment) (src tgt : Name) (prio : ℕ) : CoreM Unit :=
--   let aux := proceed_fields_aux src tgt prio
--   do
--     ((aux fun n => return$ List.map Name.toString$ (env.structureFields n).getOrElse []) >>
--           aux fun n => (List.map fun x : Name => "to_" ++ toString x) <$> getTaggedAncestors n) >>
--         aux
--           fun n =>
--             (env.constructorsOf n).mmap$
--               fun cs =>
--                 match cs with
--                 | Name.str s pre => (guardₓ (pre = n) <|> throwError "Bad constructor name") >> return s
--                 | _ => throwError "Bad constructor name"

/-!
The attribute `toAdditive` can be used to automatically transport theorems
and definitions (but not inductive types and structures) from a multiplicative
theory to an additive theory.

To use this attribute, just write:

```
@[toAdditive]
theorem mul_comm' {α} [CommSemigroup α] (x y : α) : x * y = y * x := CommSemigroup.mul_comm
```

This code will generate a theorem named `add_comm'`.  It is also
possible to manually specify the name of the new declaration, and
provide a documentation string:

```
@[toAdditive add_foo "add_foo doc string"]
/-- foo doc string -/
theorem foo := sorry
```

The transport tries to do the right thing in most cases using several
heuristics described below.  However, in some cases it fails, and
requires manual intervention.

If the declaration to be transported has attributes which need to be
copied to the additive version, then `toAdditive` should come last:

```
@[simp, toAdditive] lemma mul_one' {G : Type*} [Group G] (x : G) : x * 1 = x := mul_one x
```

The following attributes are supported and should be applied correctly by `toAdditive` to
the new additivized declaration, if they were present on the original one:
```
reducible, _refl_lemma, simp, norm_cast, instance, refl, symm, trans, elab_as_eliminator, no_rsimp,
continuity, ext, ematch, measurability, alias, _ext_core, _ext_lemma_core, nolint
```

The exception to this rule is the `simps` attribute, which should come after `toAdditive`:

```
@[toAdditive, simps]
instance {M N} [has_mul M] [has_mul N] : has_mul (M × N) := ⟨λ p q, ⟨p.1 * q.1, p.2 * q.2⟩⟩
```

Additionally the `mono` attribute is not handled by `toAdditive` and should be applied afterwards
to both the original and additivized lemma.

## Implementation notes

The transport process generally works by taking all the names of
identifiers appearing in the name, type, and body of a declaration and
creating a new declaration by mapping those names to additive versions
using a simple string-based dictionary and also using all declarations
that have previously been labeled with `toAdditive`.

In the `mul_comm'` example above, `toAdditive` maps:
* `mul_comm'` to `add_comm'`,
* `CommSemigroup` to `add_CommSemigroup`,
* `x * y` to `x + y` and `y * x` to `y + x`, and
* `CommSemigroup.mul_comm'` to `add_CommSemigroup.add_comm'`.

### Heuristics

`toAdditive` uses heuristics to determine whether a particular identifier has to be
mapped to its additive version. The basic heuristic is

* Only map an identifier to its additive version if its first argument doesn't
  contain any unapplied identifiers.

Examples:
* `@has_mul.mul ℕ n m` (i.e. `(n * m : ℕ)`) will not change to `+`, since its
  first argument is `ℕ`, an identifier not applied to any arguments.
* `@has_mul.mul (α × β) x y` will change to `+`. It's first argument contains only the identifier
  `prod`, but this is applied to arguments, `α` and `β`.
* `@has_mul.mul (α × ℤ) x y` will not change to `+`, since its first argument contains `ℤ`.

The reasoning behind the heuristic is that the first argument is the type which is "additivized",
and this usually doesn't make sense if this is on a fixed type.

There are some exceptions to this heuristic:

* Identifiers that have the `@[toAdditive]` attribute are ignored.
  For example, multiplication in `↥Semigroup` is replaced by addition in `↥AddSemigroup`.
* If an identifier `d` has attribute `@[toAdditive_relevant_arg n]` then the argument
  in position `n` is checked for a fixed type, instead of checking the first argument.
  `@[toAdditive]` will automatically add the attribute `@[toAdditive_relevant_arg n]` to a
  declaration when the first argument has no multiplicative type-class, but argument `n` does.
* If an identifier has attribute `@[toAdditive_ignore_args n1 n2 ...]` then all the arguments in
  positions `n1`, `n2`, ... will not be checked for unapplied identifiers (start counting from 1).
  For example, `times_cont_mdiff_map` has attribute `@[toAdditive_ignore_args 21]`, which means
  that its 21st argument `(n : with_top ℕ)` can contain `ℕ`
  (usually in the form `has_top.top ℕ ...`) and still be additivized.
  So `@has_mul.mul (C^∞⟮I, N; I', G⟯) _ f g` will be additivized.

### Troubleshooting

If `@[toAdditive]` fails because the additive declaration raises a type mismatch, there are
various things you can try.
The first thing to do is to figure out what `@[toAdditive]` did wrong by looking at the type
mismatch error.

* Option 1: It additivized a declaration `d` that should remain multiplicative. Solution:
  * Make sure the first argument of `d` is a type with a multiplicative structure. If not, can you
    reorder the (implicit) arguments of `d` so that the first argument becomes a type with a
    multiplicative structure (and not some indexing type)?
    The reason is that `@[toAdditive]` doesn't additivize declarations if their first argument
    contains fixed types like `ℕ` or `ℝ`. See section Heuristics.
    If the first argument is not the argument with a multiplicative type-class, `@[toAdditive]`
    should have automatically added the attribute `@[toAdditive_relevant_arg]` to the declaration.
    You can test this by running the following (where `d` is the full name of the declaration):
    ```
      run_cmd toAdditive.relevant_arg_attr.get_param `d >>= tactic.trace
    ```
    The expected output is `n` where the `n`-th argument of `d` is a type (family) with a
    multiplicative structure on it. If you get a different output (or a failure), you could add
    the attribute `@[toAdditive_relevant_arg n]` manually, where `n` is an argument with a
    multiplicative structure.
* Option 2: It didn't additivize a declaration that should be additivized.
  This happened because the heuristic applied, and the first argument contains a fixed type,
  like `ℕ` or `ℝ`. Solutions:
  * If the fixed type has an additive counterpart (like `↥Semigroup`), give it the `@[toAdditive]`
    attribute.
  * If the fixed type occurs inside the `k`-th argument of a declaration `d`, and the
    `k`-th argument is not connected to the multiplicative structure on `d`, consider adding
    attribute `[toAdditive_ignore_args k]` to `d`.
  * If you want to disable the heuristic and replace all multiplicative
    identifiers with their additive counterpart, use `@[toAdditive!]`.
* Option 3: Arguments / universe levels are incorrectly ordered in the additive version.
  This likely only happens when the multiplicative declaration involves `pow`/`^`. Solutions:
  * Ensure that the order of arguments of all relevant declarations are the same for the
    multiplicative and additive version. This might mean that arguments have an "unnatural" order
    (e.g. `monoid.npow n x` corresponds to `x ^ n`, but it is convenient that `monoid.npow` has this
    argument order, since it matches `add_monoid.nsmul n x`.
  * If this is not possible, add the `[toAdditive_reorder k]` to the multiplicative declaration
    to indicate that the `k`-th and `(k+1)`-st arguments are reordered in the additive version.

If neither of these solutions work, and `toAdditive` is unable to automatically generate the
additive version of a declaration, manually write and prove the additive version.
Often the proof of a lemma/theorem can just be the multiplicative version of the lemma applied to
`multiplicative G`.
Afterwards, apply the attribute manually:

```
attribute [toAdditive foo_add_bar] foo_bar
```

This will allow future uses of `toAdditive` to recognize that
`foo_bar` should be replaced with `foo_add_bar`.

### Handling of hidden definitions

Before transporting the “main” declaration `src`, `toAdditive` first
scans its type and value for names starting with `src`, and transports
them. This includes auxiliary definitions like `src._match_1`,
`src._proof_1`.

In addition to transporting the “main” declaration, `toAdditive` transports
its equational lemmas and tags them as equational lemmas for the new declaration,
attributes present on the original equational lemmas are also transferred first (notably
`_refl_lemma`).

### Structure fields and constructors

If `src` is a structure, then `toAdditive` automatically adds
structure fields to its mapping, and similarly for constructors of
inductive types.

For new structures this means that `toAdditive` automatically handles
coercions, and for old structures it does the same, if ancestry
information is present in `@[ancestor]` attributes. The `ancestor`
attribute must come before the `toAdditive` attribute, and it is
essential that the order of the base structures passed to `ancestor` matches
between the multiplicative and additive versions of the structure.

### Name generation

* If `@[toAdditive]` is called without a `name` argument, then the
  new name is autogenerated.  First, it takes the longest prefix of
  the source name that is already known to `toAdditive`, and replaces
  this prefix with its additive counterpart. Second, it takes the last
  part of the name (i.e., after the last dot), and replaces common
  name parts (“mul”, “one”, “inv”, “prod”) with their additive versions.

* Namespaces can be transformed using `map_namespace`. For example:
  ```
  run_cmd toAdditive.map_namespace `quotientGroup `quotientAddGroup
  ```

  Later uses of `toAdditive` on declarations in the `quotientGroup`
  namespace will be created in the `quotientAddGroup` namespaces.

* If `@[toAdditive]` is called with a `name` argument `new_name`
  /without a dot/, then `toAdditive` updates the prefix as described
  above, then replaces the last part of the name with `new_name`.

* If `@[toAdditive]` is called with a `name` argument
  `new_namespace.new_name` /with a dot/, then `toAdditive` uses this
  new name as is.

As a safety check, in the first case `toAdditive` double checks
that the new name differs from the original one.

-/
/-
  Note: we cannot use `ParametricAttribute` directly, since there are multiple attributes
  corresponding to 1 environment extension. However, the implementation is very similar.
-/
--× Array AttributeImpl
initialize toAdditiveAttr : PersistentEnvExtension (Name × Name) (Name × Name) (NameMap Name) ←
  let ext : PersistentEnvExtension (Name × Name) (Name × Name) (NameMap Name) ←
    registerPersistentEnvExtension {
      name            := "toAdditive"
      mkInitial       := return {}
      addImportedFn   := λ s => return {}
      addEntryFn      := λ (s : NameMap Name) (p : Name × Name) => s.insert p.1 p.2
      exportEntriesFn := λ m =>
        let r : Array (Name × Name) := m.fold (λ a n p => a.push (n, p)) #[]
        r.qsort λ a b => Name.quickLt a.1 b.1
      statsFn         := λ s => "parametric attribute" ++ Format.line ++ "number of local entries: " ++ format s.size
    }
  let attrImpl (nm : Name) (replaceAll trace : Bool) : AttributeImpl := {
    name  := nm
    descr := "Transport multiplicative declarations to additive ones."
    add   := λ src stx kind => do
      unless kind == AttributeKind.global do throwError "invalid attribute '{nm}', must be global"
      let env ← getEnv
      unless (env.getModuleIdxFor? src).isNone do
        throwError "invalid attribute '{nm}', declaration is in an imported module"
      let (val, doc) ← match stx with
      | `(attr|toAdditive $[$ns]? $[$str]?) =>
        ((ns.map (·.getId.eraseMacroScopes)).getD Name.anonymous, str.bind (·.isStrLit?))
      | _ => throwError "unexpected toAdditive syntax {stx}"
      let dict := ext.getState env
      let ignore := toAdditiveIgnoreArgsAttr.ext.getState env
      let relevant := toAdditiveRelevantArgAttr.ext.getState env
      let reorder := toAdditiveReorderAttr.ext.getState env
      let tgt ← targetName src val dict
      let env := ext.addEntry env (src, tgt)
      setEnv env
      let dict := ext.getState env
      let firstMultArg ← firstMultiplicativeArg src dict,


  /-
    firstMultArg ← firstMultiplicativeArg src,
    when (firstMultArg ≠ 1) $ relevant_arg_attr.set src firstMultArg tt,
    if env.contains tgt
    then proceed_fields env src tgt prio
    else do
      transform_decl_with_prefix_dict dict val.replace_all val.trace relevant ignore reorder src tgt
        [`reducible, `_refl_lemma, `simp, `norm_cast, `instance, `refl, `symm, `trans,
          `elab_as_eliminator, `no_rsimp, `continuity, `ext, `ematch, `measurability, `alias,
          `_ext_core, `_ext_lemma_core, `nolint],
      mwhen (has_attribute' `simps src)
        (trace "Apply the simps attribute after the to_additive attribute"),
      mwhen (has_attribute' `mono src)
        (trace $ "to_additive does not work with mono, apply the mono attribute to both" ++
          "versions after"),
      match val.doc with
      | some doc := add_doc_string tgt doc
      | none := skip
      end }
  -/

  }
  registerBuiltinAttribute $ attrImpl "toAdditive" false false
  registerBuiltinAttribute $ attrImpl "toAdditive!" true false
  registerBuiltinAttribute $ attrImpl "toAdditive?" false true
  registerBuiltinAttribute $ attrImpl "toAdditive!?" true true
  return ext
  -- registerParametricAttribute {
  --   name := `toAdditive
  --   descr := "Transport multiplicative declarations to additive ones."
  --   getParam := λ decl stx => do
  --     match stx with
  --       | `(attr|toAdditive   $[$ns]? $[$str]?) => return Name.anonymous
  --       | `(attr|toAdditive!  $[$ns]? $[$str]?) => return Name.anonymous
  --       | `(attr|toAdditive?  $[$ns]? $[$str]?) => return Name.anonymous
  --       | `(attr|toAdditive!? $[$ns]? $[$str]?) => return Name.anonymous
  --       | _ => throwError "unexpected toAdditive syntax {stx}" -- can this code be reached?
  --   afterSet := λ decl val => return ()
  -- }

end ToAdditive
#print MetaM.run'
-- attribute [toAdditive] Mul HasOne HasInv Div

-- attribute [toAdditive Empty] Empty

-- attribute [toAdditive Pempty] Pempty

-- attribute [toAdditive PUnit] PUnit

-- attribute [toAdditive Unit] Unit


syntax (name := foo) "foo" str : attr
initialize fooAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `foo
    descr := "foo desc."
    getParam := λ decl stx =>
      match stx with
        | `(attr|foo $ns) => do
          IO.println ns
          IO.println ns.toString!
          return ""
        | _ => throwError "unexpected foo syntax {stx}"
  }
