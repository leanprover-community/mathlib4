/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Bryan Gin-ge Chen
-/
import Mathlib.Tactic.ToAdditive.Frontend

open Lean Meta Elab Command Std ToAdditive

namespace ToDual

/-- See the docstring of `to_addditive_ignore_args` for details about `to_dual_ignore_args`. -/
syntax (name := to_dual_ignore_args) "to_dual_ignore_args" (ppSpace num)* : attr

/-- See the docstring of `to_additive_relevant_arg` for details about `to_dual_relevant_arg`. -/
syntax (name := to_dual_relevant_arg) "to_dual_relevant_arg " num : attr

/-- See the docstring of `to_additive_dont_translate` for details about `to_dual_dont_translate`. -/
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
/-- The maximum is commutative -/
@[to_dual "The minimum is commutative"]
theorem max_comm' {α} [LinearOrder α] (x y : α) : max x y = max y x := max_comm x y
```

Use the `(reorder := ...)` syntax to reorder the arguments compared to the dual declaration.
This is specified using cycle notation. For example `(reorder := 1 2, 5 6)` swaps the first two
arguments with each other and the fifth and the sixth argument and `(reorder := 3 4 5)` will move
the fifth argument before the third argument. For example, this is used to tag `LE.le`
with `(reorder := 3 4)`, so that `a ≤ b` gets transformed into `b ≤ a`.

Use the `to_dual self` syntax to use the lemma itself as its own dual. This is often
combined with the `(reorder := ...)` syntax, because a lemma can be dual to itself
after rearranging its arguments. Use the `to_dual existing` syntax to use an existing
dual declaration, instead of automatically generating it.

Use the `(attr := ...)` syntax to apply attributes to both the original and the dual version:
```
@[to_dual (attr := simp)] lemma min_self (a : α) : min a a = a := sorry
```
 -/
syntax (name := to_dual) "to_dual" "?"? toAdditiveRest : attr

@[inherit_doc to_dual]
macro "to_dual?" rest:toAdditiveRest : attr => `(attr| to_dual ? $rest)

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

/-- An extension that stores all the declarations that need their arguments reordered when
applying `@[to_dual]`. It is applied using the `to_dual (reorder := ...)` syntax. -/
initialize reorderAttr : NameMapExtension (List (List Nat)) ←
  registerNameMapExtension _

@[inherit_doc to_dual_relevant_arg]
initialize relevantArgAttr : NameMapExtension Nat ←
  registerNameMapAttribute {
    name := `to_dual_relevant_arg
    descr := "Auxiliary attribute for `to_dual` stating \
      which arguments are the types with a dual structure."
    add := fun
    | _, `(attr| to_dual_relevant_arg $id) => pure <| id.1.isNatLit?.get!.pred
    | _, _ => throwUnsupportedSyntax }

@[inherit_doc to_dual_dont_translate]
initialize dontTranslateAttr : NameMapExtension Unit ←
  registerNameMapAttribute {
    name := `to_dual_dont_translate
    descr := "Auxiliary attribute for `to_dual` stating \
      that the operations on this type should not be translated."
    add := fun
    | _, `(attr| to_dual_dont_translate) => return
    | _, _ => throwUnsupportedSyntax }

/-- Maps names to their dual counterparts. -/
initialize translations : NameMapExtension Name ← registerNameMapExtension _

def toDualBundle : BundledExtensions where
  ignoreArgsAttr := ignoreArgsAttr
  reorderAttr := reorderAttr
  relevantArgAttr := relevantArgAttr
  dontTranslateAttr := dontTranslateAttr
  translations := translations
  attrName := `to_dual
  changeNumeral := false
  isDual := true

/--
Dictionary used by `guessName` to autogenerate names.

Note: `guessName` capitalizes first element of the output according to
capitalization of the input. Input and first element should therefore be lower-case,
2nd element should be capitalized properly.
-/
def nameDict : String → List String
  | "top"         => ["bot"]
  | "bot"         => ["top"]
  | "inf"         => ["sup"]
  | "sup"         => ["inf"]
  | "min"         => ["max"]
  | "max"         => ["min"]
  | "untop"       => ["unbot"]
  | "unbot"       => ["untop"]

  | "epi"         => ["mono"]
  | "mono"        => ["epi"]
  | "terminal"    => ["initial"]
  | "initial"     => ["terminal"]
  | "precompose"  => ["postcompose"]
  | "postcompose" => ["precompose"]
  | "cone"        => ["cocone"]
  | "cocone"      => ["cone"]
  | "cones"       => ["cocones"]
  | "cocones"     => ["cones"]
  | "fan"         => ["cofan"]
  | "cofan"       => ["fan"]
  | "limit"       => ["colimit"]
  | "colimit"     => ["limit"]
  | "limits"      => ["colimits"]
  | "colimits"    => ["limits"]
  | "product"     => ["coproduct"]
  | "coproduct"   => ["product"]
  | "products"    => ["coproducts"]
  | "coproducts"  => ["products"]
  | "pushout"     => ["pullback"]
  | "pullback"    => ["pushout"]
  | "pushouts"    => ["pullbacks"]
  | "pullbacks"   => ["pushouts"]
  | "span"        => ["cospan"]
  | "cospan"      => ["span"]
  | "kernel"      => ["cokernel"]
  | "cokernel"    => ["kernel"]
  | "kernels"     => ["cokernel"]
  | "cokernels"   => ["kernel"]
  | "unit"        => ["counit"]
  | "counit"      => ["unit"]
  | "monad"       => ["comonad"]
  | "comonad"     => ["monad"]
  | "monadic"     => ["comonadic"]
  | "comonadic"   => ["monadic"]

  | x             => [x]

/-- So far, we don't have any dual abbreviations that need to be fixed. -/
def fixAbbreviation : List String → List String := id

initialize registerBuiltinAttribute {
    name := `to_dual
    descr := "Transport to dual"
    add := fun src stx kind ↦ discard do
      addToAdditiveAttr toDualBundle nameDict fixAbbreviation src (← elabToAdditive stx) kind
    applicationTime := .afterCompilation
  }

end ToDual
