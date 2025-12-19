/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Util.AddRelatedDecl
public import Mathlib.Tactic.Push

/-!
# The `to_fun` attribute

Adding `@[to_fun]` to a lemma named `foo` creates a new lemma named `fun_foo`, which is obtained by
running `pull fun _ ↦ _` on the type of `F`. This can be useful for generating the applied form
of a continuity lemma from the unapplied form.
-/

public meta section

open Lean Meta Elab Tactic
namespace Mathlib.Tactic

/--
Adding `@[to_fun]` to a lemma
```
theorem Continuous.mul (hf : Continuous f) (hg : Continuous g) : Continuous (f * g)
```
will generate a new lemma `Continuous.fun_mul` with conclusion `Continuous fun x => f x * g x`.

Use the `to_fun (attr := ...)` syntax to add the same attribute to both declarations.
-/
syntax (name := to_fun) "to_fun" (" (" &"attr" " := " Parser.Term.attrInstance,* ")")? : attr

initialize registerBuiltinAttribute {
  name := `to_fun
  descr := "generate a copy of a lemma where point-free functions are expanded to their `fun` form"
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| to_fun $[(attr := $stx?,*)]?) => MetaM.run' do
    if (kind != AttributeKind.global) then
      throwError "`to_fun` can only be used as a global attribute"
    addRelatedDecl src "fun_" "" ref stx? (docstringPrefix? := s!"Eta-expanded form of `{src}`")
      fun value levels => do
      let r ← Push.pullCore .lambda (← inferType value) none
      return (← r.mkCast value, levels)
  | _ => throwUnsupportedSyntax }

end Mathlib.Tactic
