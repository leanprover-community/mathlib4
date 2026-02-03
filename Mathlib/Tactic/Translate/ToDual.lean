/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Bryan Gin-ge Chen
-/
module

public import Mathlib.Tactic.Translate.TagUnfoldBoundary

/-!
# The `@[to_dual]` attribute.

The `@[to_dual]` attribute is used to translate declarations to their dual equivalent.
See the docstrings of `to_dual` and `to_additive` for more information.

Known limitations:
- Reordering arguments of arguments is not yet supported.
  This usually comes up in constructors of structures. e.g. `Pow.mk` or `OrderTop.mk`
- When combining `to_additive` and `to_dual`, we need to make sure that all translations are added.
  For example `attribute [to_dual (attr := to_additive) le_mul] mul_le` should generate
  `le_mul`, `le_add` and `add_le`, and in particular should realize that `le_add` and `add_le`
  are dual to each other. Currently, this requires writing
  `attribute [to_dual existing le_add] add_le`.
-/

public meta section

namespace Mathlib.Tactic.ToDual
open Lean Meta Elab Command Std Translate UnfoldBoundary

@[inherit_doc TranslateData.ignoreArgsAttr]
syntax (name := to_dual_ignore_args) "to_dual_ignore_args" (ppSpace num)* : attr

@[inherit_doc TranslateData.doTranslateAttr]
syntax (name := to_dual_do_translate) "to_dual_do_translate" : attr

@[inherit_doc TranslateData.doTranslateAttr]
syntax (name := to_dual_dont_translate) "to_dual_dont_translate" : attr

/-- The attribute `to_dual` can be used to automatically transport theorems
and definitions (but not inductive types and structures) to their dual version.
It uses the same implementation as `to_additive`.

To use this attribute, just write:

```
@[to_dual]
theorem max_comm' {α} [LinearOrder α] (x y : α) : max x y = max y x := max_comm x y
```

This code will generate a theorem named `min_comm'`. It is also
possible to manually specify the name of the new declaration:

```
@[to_dual le_max_left]
lemma min_le_left (a b : α) : min a b ≤ a := sorry
```

An existing documentation string will _not_ be automatically used, so if the theorem or definition
has a doc string, a doc string for the dual version should be passed explicitly to `to_dual`.

```
/-- The maximum is commutative. -/
@[to_dual /-- The minimum is commutative. -/]
theorem max_comm' {α} [LinearOrder α] (x y : α) : max x y = max y x := max_comm x y
```

Use the `(reorder := ...)` syntax to reorder the arguments compared to the dual declaration.
This is specified using cycle notation. For example `(reorder := α β, 5 6)` swaps the arguments
`α` and `β` with each other and the fifth and the sixth argument and `(reorder := 3 4 5)` will move
the fifth argument before the third argument. For example, this is used when tagging `LE.le`
with `to_dual self (reorder := 3 4)`, so that `a ≤ b` gets transformed into `b ≤ a`.

Use the `to_dual self` syntax to mark the lemma as its own dual. This is needed if the lemma is
its own dual, up to a reordering of its arguments. `to_dual self` (and `to_dual existing`) tries to
autogenerate the `(reorder := ...)` argument, so it is usually not necessary to give it explicitly.

Use the `to_dual existing` syntax to use an existing dual declaration,
instead of automatically generating it.

Use the `(attr := ...)` syntax to apply attributes to both the original and the dual version:
```
@[to_dual (attr := simp)] lemma min_self (a : α) : min a a = a := sorry
```

The `reassoc` attribute in category theory interacts with `to_dual` in a unique way, because it
generates `_assoc` theorems that aren't dual to any other theorem. To deal with this, the `reassoc`
attribute will add a `to_dual none` tag to an `_assoc` theorem if the original theorem was
already tagged with `to_dual`. This also works with `to_dual (attr := reassoc)`.

Some definitions are dual to something other than the dual of their value. Some examples:
- `Ico a b := { x | a ≤ x ∧ x < b }` is dual to `Ioc b a := { x | b < x ∧ x ≤ a }`.
- `Monotone f := ∀ ⦃a b⦄, a ≤ b → f a ≤ f b` is dual to itself.
- `DecidableLE α := ∀ a b : α, Decidable (a ≤ b)` is dual to itself.

To be able to translate a term involving such constants, `to_dual` needs to insert casts,
so that the term's correctness doesn't rely on unfolding them.
You can instruct `to_dual` to do this using the `to_dual_insert_cast` or `to_dual_insert_cast_fun`
commands.

When troubleshooting `to_dual`, you can see what it is doing by replacing it with `to_dual?` and/or
by using `set_option trace.translate_detail true`.
-/
syntax (name := to_dual) "to_dual" "?"? attrArgs : attr

@[inherit_doc to_dual]
macro "to_dual?" rest:attrArgs : attr => `(attr| to_dual ? $rest)

@[inherit_doc to_dual_ignore_args]
initialize ignoreArgsAttr : NameMapExtension (List Nat) ←
  registerNameMapAttribute {
    name  := `to_dual_ignore_args
    descr :=
      "Auxiliary attribute for `to_dual` stating that certain arguments are not dualized."
    add   := fun _ stx ↦ do
        let ids ← match stx with
          | `(attr| to_dual_ignore_args $[$ids:num]*) => pure <| ids.map (·.1.isNatLit?.get!)
          | _ => throwUnsupportedSyntax
        return ids.toList }

@[inherit_doc TranslateData.unfoldBoundaries?]
initialize unfoldBoundaries : UnfoldBoundaryExt ← registerUnfoldBoundaryExt

@[inherit_doc TranslateData.doTranslateAttr]
initialize doTranslateAttr : NameMapExtension Bool ← registerNameMapExtension _

initialize
  registerBuiltinAttribute {
    name := `to_dual_do_translate
    descr := "Auxiliary attribute for `to_dual` stating \
      that the operations on this type should be translated."
    add name _ _ := doTranslateAttr.add name true }
  registerBuiltinAttribute {
    name := `to_dual_dont_translate
    descr := "Auxiliary attribute for `to_dual` stating \
      that the operations on this type should not be translated."
    add name _ _ := doTranslateAttr.add name false }

/-- Maps names to their dual counterparts. -/
initialize translations : NameMapExtension TranslationInfo ← registerNameMapExtension _

@[inherit_doc GuessName.GuessNameData.nameDict]
def nameDict : Std.HashMap String (List String) := .ofList [
  ("top", ["Bot"]),
  ("bot", ["Top"]),
  ("inf", ["Sup"]),
  ("sup", ["Inf"]),
  ("min", ["Max"]),
  ("max", ["Min"]),
  ("untop", ["Unbot"]),
  ("unbot", ["Untop"]),
  ("minimal", ["Maximal"]),
  ("maximal", ["Minimal"]),
  ("lower", ["Upper"]),
  ("upper", ["Lower"]),
  ("below", ["Above"]),
  ("above", ["Below"]),
  ("least", ["Greatest"]),
  ("greatest", ["Least"]),
  ("glb", ["LUB"]),
  ("lub", ["GLB"]),
  ("cofinal", ["Coinitial"]),
  ("coinitial", ["Cofinal"]),
  ("succ", ["Pred"]),
  ("pred", ["Succ"]),
  ("disjoint", ["Codisjoint"]),
  ("codisjoint", ["Disjoint"]),
  ("ioi", ["Iio"]),
  ("iio", ["Ioi"]),
  ("ici", ["Iic"]),
  ("iic", ["Ici"]),
  ("ioc", ["Ico"]),
  ("ico", ["Ioc"]),

  ("epi", ["Mono"]),
  /- `mono` can also refer to monotone, so we don't translate it. -/
  -- ("mono", ["Epi"]),
  ("terminal", ["Initial"]),
  ("initial", ["Terminal"]),
  ("precompose", ["Postcompose"]),
  ("postcompose", ["Precompose"]),
  ("cone", ["Cocone"]),
  ("cocone", ["Cone"]),
  ("cones", ["Cocones"]),
  ("cocones", ["Cones"]),
  ("fan", ["Cofan"]),
  ("cofan", ["Fan"]),
  ("limit", ["Colimit"]),
  ("colimit", ["Limit"]),
  ("limits", ["Colimits"]),
  ("colimits", ["Limits"]),
  ("product", ["Coproduct"]),
  ("coproduct", ["Product"]),
  ("products", ["Coproducts"]),
  ("coproducts", ["Products"]),
  ("pushout", ["Pullback"]),
  ("pullback", ["Pushout"]),
  ("pushouts", ["Pullbacks"]),
  ("pullbacks", ["Pushouts"]),
  ("span", ["Cospan"]),
  ("cospan", ["Span"]),
  ("kernel", ["Cokernel"]),
  ("cokernel", ["Kernel"]),
  ("kernels", ["Cokernels"]),
  ("cokernels", ["Kernels"]),
  ("unit", ["Counit"]),
  ("counit", ["Unit"]),
  ("monad", ["Comonad"]),
  ("comonad", ["Monad"]),
  ("monadic", ["Comonadic"]),
  ("comonadic", ["Monadic"])]

@[inherit_doc GuessName.GuessNameData.abbreviationDict]
def abbreviationDict : Std.HashMap String String := .ofList [
  ("wellFoundedLT", "WellFoundedGT"),
  ("wellFoundedGT", "WellFoundedLT"),
  ("succColimit", "SuccLimit"),
  ("predColimit", "PredLimit")
]

/-- The bundle of environment extensions for `to_dual` -/
def data : TranslateData where
  ignoreArgsAttr; doTranslateAttr; translations
  unfoldBoundaries? := some unfoldBoundaries
  attrName := `to_dual
  changeNumeral := false
  isDual := true
  guessNameData := { nameDict, abbreviationDict }

/-- The `to_dual_insert_cast` attribute is used to tag declarations `foo` that should not be
unfolded in a proof that is translated. Instead, a rewrite with an equality theorem is inserted.
This equality theorem can then be translated by the translation attribute. -/
elab "to_dual_insert_cast" declName:ident " := " valStx:term : command =>
  elabInsertCast declName valStx data

/-- The `to_dual_insert_cast_fun` attribute is used to tag types that should not be unfolded in a
proof that is translated. Instead, a casting function is inserted. This casting function then may be
translated by the translation attribute. -/
elab "to_dual_insert_cast_fun" declName:ident " := " valStx₁:term ", " valStx₂:term : command =>
  elabInsertCastFun declName valStx₁ valStx₂ data

initialize registerBuiltinAttribute {
    name := `to_dual
    descr := "Transport to dual"
    add := fun src stx kind ↦ discard do
      addTranslationAttr data src (← elabTranslationAttr src stx) kind
    applicationTime := .afterCompilation
  }

end Mathlib.Tactic.ToDual
