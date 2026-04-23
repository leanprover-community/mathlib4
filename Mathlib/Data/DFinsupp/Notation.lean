/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.DFinsupp.Defs
public import Mathlib.Data.Finsupp.Notation
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Notation for `DFinsupp`

This file extends the existing `fun₀ | 3 => a | 7 => b` notation to work for `DFinsupp`,
which desugars to `DFinsupp.update` and `DFinsupp.single`,
in the same way that `{a, b}` desugars to `insert` and `singleton`.

Note that this syntax is for `Finsupp` by default, but works for `DFinsupp` if the expected type
is correct.
-/

public section

namespace DFinsupp

open Lean Parser Term

namespace Internal
open Finsupp.Internal

/-- `DFinsupp` elaborator for `single₀`. -/
@[term_elab Finsupp.Internal.stxSingle₀]
meta def elabSingle₀ : Elab.Term.TermElab
  | `(term| single₀ $i $x) => fun ty? => do
    Elab.Term.tryPostponeIfNoneOrMVar ty?
    let some ty := ty? | Elab.throwUnsupportedSyntax
    let_expr DFinsupp _ _ _ := ← Meta.withReducible (Meta.whnf ty) | Elab.throwUnsupportedSyntax
    Elab.Term.elabTerm (← `(DFinsupp.single $i $x)) ty?
  | _ => fun _ => Elab.throwUnsupportedSyntax

/-- `DFinsupp` elaborator for `update₀`. -/
@[term_elab Finsupp.Internal.stxUpdate₀]
meta def elabUpdate₀ : Elab.Term.TermElab
  | `(term| update₀ $f $i $x) => fun ty? => do
    Elab.Term.tryPostponeIfNoneOrMVar ty?
    let some ty := ty? | Elab.throwUnsupportedSyntax
    let_expr DFinsupp _ _ _ := ← Meta.withReducible (Meta.whnf ty) | Elab.throwUnsupportedSyntax
    Elab.Term.elabTerm (← `(DFinsupp.update $f $i $x)) ty?
  | _ => fun _ => Elab.throwUnsupportedSyntax

end Internal

/-- Unexpander for the `fun₀ | i => x` notation. -/
@[app_unexpander DFinsupp.single]
meta def singleUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $pat $val) => `(fun₀ | $pat => $val)
  | _ => throw ()

/-- Unexpander for the `fun₀ | i => x` notation. -/
@[app_unexpander DFinsupp.update]
meta def updateUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $pat $val) => match f with
    | `(fun₀ $xs:matchAlt*) => `(fun₀ $xs:matchAlt* | $pat => $val)
    | _ => throw ()
  | _ => throw ()

/-- Display `DFinsupp` using `fun₀` notation. -/
unsafe instance {α : Type*} {β : α → Type*} [Repr α] [∀ i, Repr (β i)] [∀ i, Zero (β i)] :
    Repr (Π₀ a, β a) where
  reprPrec f p :=
    let vals :=
      ((f.support'.unquot.val.map fun i => (repr i, repr (f i))).filter
        (fun p => toString p.2 != "0")).unquot
    let vals_dedup := vals.foldl (fun xs x => x :: xs.eraseP (toString ·.1 == toString x.1)) []
    if vals.length = 0 then
      "0"
    else
      let ret : Std.Format := f!"fun₀" ++ .nest 2 (.group (.join <| vals_dedup.map fun a =>
          .line ++ .group (f!"| {a.1} =>" ++ .line ++ a.2)))
      if p ≥ leadPrec then Format.paren ret else ret

end DFinsupp
