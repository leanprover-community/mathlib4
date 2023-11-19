/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.Finsupp.Defs

/-!
# Notation for `Finsupp`

This file provides `fun₀ | 3 => a | 7 => b` notation for `Finsupp`, which desugars to
`Finsupp.update` and `Finsupp.single`, in the same way that `{a, b}` desugars to `insert` and
`singleton`.
-/

namespace Finsupp

open Lean
open Lean.Parser
open Lean.Parser.Term

/-- A variant of `Lean.Parser.Term.matchAlts` with less line wrapping. -/
def fun₀.matchAlts : Parser :=
  leading_parser withPosition $ ppRealGroup <| many1Indent (ppSpace >> ppGroup matchAlt)

@[term_parser, inherit_doc Finsupp]
def fun₀ := leading_parser:maxPrec
  ppAllowUngrouped >> unicodeSymbol "λ₀" "fun₀" >> fun₀.matchAlts

macro_rules
  | `(term| fun₀ $x:matchAlt*) => do
    let mut stx : Term ← `(0)
    let mut fst : Bool := true
    for xi in x do
      for xii in (← Elab.Term.expandMatchAlt xi) do
        match xii with
        | `(matchAltExpr| | $pat => $val) =>
          if fst then
            stx ← `(Finsupp.single $pat $val)
          else
            stx ← `(Finsupp.update $stx $pat $val)
          fst := false
        | _ => Macro.throwUnsupported
    pure stx

/-- Unexpander for the `fun₀ | i => x` notation. -/
@[app_unexpander Finsupp.single]
def singleUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $pat $val) => `(fun₀ | $pat => $val)
  | _ => throw ()

/-- Unexpander for the `fun₀ | i => x` notation. -/
@[app_unexpander Finsupp.update]
def updateUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $pat $val) => match f with
    | `(fun₀ $xs:matchAlt*) => `(fun₀ $xs:matchAlt* | $pat => $val)
    | _ => throw ()
  | _ => throw ()

/-- Display `Finsupp` using `fun₀` notation. -/
unsafe instance {α β} [Repr α] [Repr β] [Zero β] : Repr (α →₀ β) where
  reprPrec f p :=
    if f.support.card = 0 then
      "0"
    else
      let ret := "fun₀" ++
        Std.Format.join (f.support.val.unquot.map <|
          fun a => " | " ++ repr a ++ " => " ++ repr (f a))
      if p ≥ leadPrec then Format.paren ret else ret

end Finsupp
