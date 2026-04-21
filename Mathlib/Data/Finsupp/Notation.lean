/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.Finsupp.Single

/-!
# Notation for `Finsupp`

This file provides `fun₀ | 3 => a | 7 => b` notation for `Finsupp`, which desugars to
`Finsupp.update` and `Finsupp.single`, in the same way that `{a, b}` desugars to `insert` and
`singleton`.
-/
set_option backward.defeqAttrib.useBackward true

public section

namespace Finsupp

open Lean Parser Term

-- A variant of `Lean.Parser.Term.matchAlts` with less line wrapping.
@[nolint docBlame] -- we do not want any doc hover on this notation.
meta def fun₀.matchAlts : Parser :=
  leading_parser withPosition <| ppRealGroup <| many1Indent (ppSpace >> ppGroup matchAlt)

/-- `fun₀ | i => a` is notation for `Finsupp.single i a`, and with multiple match arms,
`fun₀ ... | i => a` is notation for `Finsupp.update (fun₀ ...) i a`.

As a result, if multiple match arms coincide, the last one takes precedence. -/
@[term_parser]
meta def fun₀ := leading_parser:maxPrec
  -- Prefer `fun₀` over `λ₀` when pretty printing.
  ppAllowUngrouped >> unicodeSymbol "λ₀" "fun₀" (preserveForPP := true) >> fun₀.matchAlts

namespace Internal

/-- Implementation detail for `fun₀`, used by both `Finsupp` and `DFinsupp` -/
scoped syntax:lead (name := stxSingle₀) "single₀" term:arg term:arg : term
/-- Implementation detail for `fun₀`, used by both `Finsupp` and `DFinsupp` -/
scoped syntax:lead (name := stxUpdate₀) "update₀" term:arg term:arg term:arg : term

/-- `Finsupp` elaborator for `single₀`. -/
@[term_elab stxSingle₀]
meta def elabSingle₀ : Elab.Term.TermElab
  | `(term| single₀ $i $x) => fun ty => do Elab.Term.elabTerm (← `(Finsupp.single $i $x)) ty
  | _ => fun _ => Elab.throwUnsupportedSyntax

/-- `Finsupp` elaborator for `update₀`. -/
@[term_elab stxUpdate₀]
meta def elabUpdate₀ : Elab.Term.TermElab
  | `(term| update₀ $f $i $x) => fun ty => do Elab.Term.elabTerm (← `(Finsupp.update $f $i $x)) ty
  | _ => fun _ => Elab.throwUnsupportedSyntax

macro_rules
  | `(term| fun₀ $x:matchAlt*) => do
    let mut stx : Term ← `(0)
    let mut fst : Bool := true
    for xi in x do
      for xii in Elab.Term.expandMatchAlt xi do
        match xii with
        | `(matchAltExpr| | $pat => $val) =>
          if fst then
            stx ← `(single₀ $pat $val)
          else
            stx ← `(update₀ $stx $pat $val)
          fst := false
        | _ => Macro.throwUnsupported
    pure stx

end Internal

/-- Unexpander for the `fun₀ | i => x` notation. -/
@[app_unexpander Finsupp.single]
meta def singleUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $pat $val) => `(fun₀ | $pat => $val)
  | _ => throw ()

/-- Unexpander for the `fun₀ | i => x` notation. -/
@[app_unexpander Finsupp.update]
meta def updateUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $pat $val) => match f with
    | `(fun₀ $xs:matchAlt*) => `(fun₀ $xs:matchAlt* | $pat => $val)
    | _ => throw ()
  | _ => throw ()

/-- Display `Finsupp` using `fun₀` notation. -/
unsafe instance instRepr {α β} [Repr α] [Repr β] [Zero β] : Repr (α →₀ β) where
  reprPrec f p :=
    if f.support.card = 0 then
      "0"
    else
      let ret : Std.Format := f!"fun₀" ++ .nest 2 (
        .group (.join <| f.support.val.unquot.map fun a =>
          .line ++ .group (f!"| {repr a} =>" ++ .line ++ repr (f a))))
      if p ≥ leadPrec then Format.paren ret else ret

-- This cannot be put in `Mathlib/Data/DFinsupp/Notation.lean` where it belongs, since doc-strings
-- can only be added/modified in the file where the corresponding declaration is defined.
extend_docs Finsupp.fun₀ after
  "If the expected type is `Π₀ i, α i` (`DFinsupp`)
  and `Mathlib/Data/DFinsupp/Notation.lean` is imported,
  then this is notation for `DFinsupp.single` and  `Dfinsupp.update` instead."

end Finsupp
