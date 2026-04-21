/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Util.AddRelatedDecl
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Translate.Attributes

/-!
# The `to_fun` attribute

Adding `@[to_fun]` to a lemma named `foo` creates a new lemma named `fun_foo`, which is obtained by
running `pull fun _ ↦ _` on the type of `F`. This can be useful for generating the applied form
of a continuity lemma from the unapplied form.
-/
set_option backward.defeqAttrib.useBackward true

meta section

open Lean Meta Elab Tactic
namespace Mathlib.Tactic

/--
Generate an eta-expanded version of a lemma. Adding `@[to_fun]` to a lemma written in "point-free"
form, e.g.
```
theorem Differentiable.mul (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (f * g)
```
will generate a new lemma `Differentiable.fun_mul` with conclusion
`Differentiable 𝕜 fun x => f x * g x`.

Use the `to_fun (attr := ...)` syntax to add the same attribute to both declarations.
-/
syntax (name := to_fun) "to_fun" optAttrArg : attr

def toFunImpl (src : Name) (stx : Syntax) (kind : AttributeKind) : AttrM Name := do
  let `(attr| to_fun%$tk $optAttr) := stx | throwUnsupportedSyntax
  if (kind != AttributeKind.global) then
    throwError "`to_fun` can only be used as a global attribute"
  let tgt := (src.appendBefore "fun_")
  MetaM.run' <| addRelatedDecl src tgt tk optAttr
    (docstringPrefix? := s!"Eta-expanded form of `{src}`") (hoverInfo := true)
    fun value levels => do
    let type ← inferType value
    let r ← Push.pullCore .lambda type none
    if r.expr == type then
      throwError "`@[to_fun]` failed to eta-expand any part of `{.ofConstName src}`."
    -- Ensure that the returned `value` has type `r.expr`.
    let value ← match r.proof? with
      | none => mkExpectedTypeHint value r.expr
      | some proof => mkAppOptM ``cast #[type, r.expr, proof, value]
    return (value, levels)
  return tgt

initialize
  registerGeneratingAttr `to_fun ((#[·]) <$> toFunImpl · · ·)
  registerBuiltinAttribute {
    name := `to_fun
    descr :=
      "generate a copy of a lemma where point-free functions are expanded to their `fun` form"
    applicationTime := .afterCompilation
    add := (discard <| toFunImpl · · ·)}

end Mathlib.Tactic
