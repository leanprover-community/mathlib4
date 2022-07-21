/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean
open Lean Elab Parser Term Meta Macro

/-!
Defines variants of `have` and `let` syntax which do not produce `let_fun` or `let` bindings,
but instead inline the value instead.

This is useful to declare local instances and proofs in theorem statements
and subgoals, where the extra binding is inconvenient.
-/

namespace Mathlib.Tactic

/-- `haveI` behaves like `have`, but inlines the value instead of producing a `let_fun` term. -/
@[termParser] def «haveI» := leading_parser withPosition ("haveI " >> haveDecl) >> optSemicolon termParser
/-- `letI` behaves like `let`, but inlines the value instead of producing a `let_fun` term. -/
@[termParser] def «letI» := leading_parser withPosition ("letI " >> haveDecl) >> optSemicolon termParser

macro_rules
  | `(haveI $_ : $_ := $_; $_) => throwUnsupported -- handled by elab
  | `(haveI $[: $ty]? := $val; $body) => `(haveI $(mkIdent `this) $[: $ty]? := $val; $body)
  | `(haveI $x := $val; $body) => `(haveI $x : _ := $val; $body)
  | `(haveI $decl:haveDecl; $body) => `(haveI x := have $decl:haveDecl; x; $body)

macro_rules
  | `(letI $_ : $_ := $_; $_) => throwUnsupported -- handled by elab
  | `(letI $[: $ty]? := $val; $body) => `(letI $(mkIdent `this) $[: $ty]? := $val; $body)
  | `(letI $x := $val; $body) => `(letI $x : _ := $val; $body)
  | `(letI $decl:haveDecl; $body) => `(letI x := have $decl:haveDecl; x; $body)

elab_rules <= expectedType
  | `(haveI $x : $ty := $val; $body) => do
    let ty ← elabType ty
    let val ← elabTermEnsuringType val ty
    withLocalDeclD x.getId ty fun x => do
      return (← abstract (← elabTerm body expectedType) #[x]).instantiate #[val]

elab_rules <= expectedType
  | `(letI $x : $ty := $val; $body) => do
    let ty ← elabType ty
    let val ← elabTermEnsuringType val ty
    withLetDecl x.getId ty val fun x => do
      return (← abstract (← elabTerm body expectedType) #[x]).instantiate #[val]

/-- `haveI` behaves like `have`, but inlines the value instead of producing a `let_fun` term. -/
macro "haveI " d:haveDecl : tactic => `(refine_lift haveI $d:haveDecl; ?_)
/-- `letI` behaves like `let`, but inlines the value instead of producing a `let_fun` term. -/
macro "letI " d:haveDecl : tactic => `(refine_lift letI $d:haveDecl; ?_)
