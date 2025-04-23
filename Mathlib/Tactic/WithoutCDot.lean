/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Lean.Elab.SyntheticMVars
import Mathlib.Init

/-!
# The `without_cdot()` elaborator
-/

namespace Lean.Elab.Term

open Parser

private def withoutCDotContents : Parser :=
  withoutPosition <|
    withoutForbidden (termParser >> optional (" :" >> optional (ppSpace >> termParser)))

/-- A set of parentheses, supporting type ascriptions, which does not process `·`.

Primarily, this is useful when quoting user-provided syntax inside parentheses, as it prevents `·`s
from the caller being interpreted in the context of `()`s from the macro. -/
@[term_parser]
def withoutCDot := leading_parser
  "without_cdot(" >> withoutCDotContents >> ")"

/-- Implementation detail of `withoutCDot` -/
@[term_parser]
def withoutCDotImpl := leading_parser
  "without_cdot_impl(" >> withoutCDotContents >> ")"

-- The `no_implicit_lambda%`s here are to emulate the behavior of `blockImplicitLambda`
macro_rules
  | `(without_cdot($e :)) => `(no_implicit_lambda% without_cdot_impl($e :))
  | `(without_cdot($e : $ty)) => `(no_implicit_lambda% without_cdot_impl($e : $ty))
  | `(without_cdot($e)) => `(without_cdot_impl($e))

@[term_elab withoutCDotImpl, inherit_doc withoutCDot]
def elabWithoutCDot : TermElab
  -- copied from `elabTypeAscription`
  | `(without_cdot_impl($e : $type)), _ => do
    let type ← withSynthesize (postpone := .yes) <| elabType type
    let e ← elabTerm e type
    ensureHasType type e
  | `(without_cdot_impl($e :)), expectedType? => do
    let e ← withSynthesize (postpone := .no) <| elabTerm e none
    ensureHasType expectedType? e
  | `(without_cdot_impl($e)), expectedType? => do
    elabTerm e expectedType?
  | _, _ => throwUnsupportedSyntax

end Lean.Elab.Term
