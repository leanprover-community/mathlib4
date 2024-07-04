/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean

/-!
# Pretty printing projection notation

**Deprecated** as of 2024-05-02 with Lean v4.8.0 since dot notation is now default with
the introduction of `pp.fieldNotation.generalized`, which handles dot notation pervasively
and correctly.


This module contains the `@[pp_dot]` attribute, which is used to configure functions to pretty print
using projection notation (i.e., like `x.f y` rather than `C.f x y`).

Core's projection delaborator collapses chains of ancestor projections.
For example, to turn `x.toFoo.toBar` into `x.toBar`.
The `pp_dot` attribute works together with this delaborator to completely collapse such chains.
-/

namespace Mathlib.ProjectionNotation

open Lean Parser Elab Term
open PrettyPrinter.Delaborator SubExpr
open Lean.Elab.Command

/-- Given a function `f` that is either a true projection or a generalized projection
(i.e., a function that works using extended field notation, a.k.a. "dot notation"), generates
an `app_unexpander` for it to get it to pretty print using dot notation.

See also the docstring of the `pp_dot` attribute. -/
def mkExtendedFieldNotationUnexpander (f : Name) : CommandElabM Unit := do
  let .str A projName := f | throwError "Projection name must end in a string component."
  if let some _ := getStructureInfo? (← getEnv) A then
    -- If this is for a structure, then generate an extra `.toA` remover.
    -- It's easier to handle the two cases completely separately than to try to merge them.
    let .str _ A' := A | throwError "{A} must end in a string component"
    let toA : Name := .str .anonymous ("to" ++ A')
    elabCommand <| ← `(command|
      @[app_unexpander $(mkIdent f)]
      aux_def $(mkIdent <| Name.str f "unexpander") : Lean.PrettyPrinter.Unexpander := fun
        -- Having a zero-argument pattern prevents unnecessary parenthesization in output
        | `($$_ $$(x).$(mkIdent toA))
        | `($$_ $$x) => set_option hygiene false in `($$(x).$(mkIdent (.mkSimple projName)))
        | _ => throw ())
  else
    elabCommand <| ← `(command|
      @[app_unexpander $(mkIdent f)]
      aux_def $(mkIdent <| Name.str f "unexpander") : Lean.PrettyPrinter.Unexpander := fun
        -- Having this zero-argument pattern prevents unnecessary parenthesization in output
        | `($$_ $$x) => set_option hygiene false in `($$(x).$(mkIdent (.mkSimple projName)))
        | _ => throw ())

/--
Adding the `@[pp_dot]` attribute defines an `app_unexpander` for the given function to
support pretty printing the function using extended field notation ("dot notation").
This particular attribute is *only* for functions whose first explicit argument is the
receiver of the generalized field notation. That is to say, it is only meant for
transforming `C.f c x y z ...` to `c.f x y z ...` for `c : C`.

It can be used to help get projection notation to work for function-valued structure fields,
since the built-in projection delaborator cannot handle excess arguments.

Example for generalized field notation:
```
structure A where
  n : Nat

@[pp_dot]
def A.foo (a : A) (m : Nat) : Nat := a.n + m
```
Now, `A.foo x m` pretty prints as `x.foo m`. If `A` is a structure, it also adds a rule that
`A.foo x.toA m` pretty prints as `x.foo m`. This rule is meant to combine with core's
the projection collapse delaborator, where together `A.foo x.toB.toA m`
will pretty print as `x.foo m`.

Since the mentioned rule is a purely syntactic transformation,
it might lead to output that does not round trip, though this can only occur if
there exists an `A`-valued `toA` function that is not a parent projection that
happens to be pretty printable using dot notation.

Here is an example to illustrate the round tripping issue:
```lean
import Mathlib.Tactic.ProjectionNotation

structure A where n : Int

@[pp_dot]
def A.inc (a : A) (k : Int) : Int := a.n + k

structure B where n : Nat

def B.toA (b : B) : A := ⟨b.n⟩

variable (b : B)

#check A.inc b.toA 1
-- (B.toA b).inc 1 : Int

attribute [pp_dot] B.toA
#check A.inc b.toA 1
-- b.inc 1 : Int

#check b.inc 1
-- invalid field 'inc', the environment does not contain 'B.inc'
```
To avoid this, don't use `pp_dot` for coercion functions
such as `B.toA`.
-/
syntax (name := ppDotAttr) "pp_dot" : attr

initialize registerBuiltinAttribute {
  name := `ppDotAttr
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| pp_dot) => do
    logWarning "\
      The @[pp_dot] attribute is deprecated now that dot notation is the default \
      with the introduction of `pp.fieldNotation.generalized` in Lean v4.8.0."
    if (kind != AttributeKind.global) then
      throwError "`pp_dot` can only be used as a global attribute"
    liftCommandElabM <| withRef ref <| mkExtendedFieldNotationUnexpander src
  | _ => throwUnsupportedSyntax }

end Mathlib.ProjectionNotation
