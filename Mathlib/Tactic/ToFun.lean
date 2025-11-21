module

public meta import Mathlib.Util.AddRelatedDecl
public meta import Mathlib.Tactic.Push

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
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| to_fun $[(attr := $stx?,*)]?) => MetaM.run' do
    if (kind != AttributeKind.global) then
      throwError "`to_fun` can only be used as a global attribute"
    addRelatedDecl src "fun_" "" ref stx? fun value levels => do
      let r ← Push.pullCore .lambda (← inferType value) none
      return (← r.mkCast value, levels)
  | _ => throwUnsupportedSyntax }

end Mathlib.Tactic
