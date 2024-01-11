/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Thomas R. Murrills
-/
import Std.Classes.SetNotation

/-! # Pi type notation

Provides the `Π x : α, β x` notation as an alternative to Lean 4's built-in
`(x : α) → β x` notation. To get all non-`∀` pi types to pretty print this way
then do `open scoped PiNotation`.

The notation also accepts extended binders, like `Π x ∈ s, β x` for `Π x, x ∈ s → β x`.
-/

namespace PiNotation
open Lean.Parser Term
open Lean.PrettyPrinter.Delaborator

/-- Dependent function type (a "pi type"). The notation `Π x : α, β x` can
also be written as `(x : α) → β x`. -/
-- A direct copy of forall notation but with `Π`/`Pi` instead of `∀`/`Forall`.
@[term_parser]
def piNotation := leading_parser:leadPrec
  unicodeSymbol "Π" "PiType" >>
  many1 (ppSpace >> (binderIdent <|> bracketedBinder)) >>
  optType >> ", " >> termParser

/-- Dependent function type (a "pi type"). The notation `Π x ∈ s, β x` is
short for `Π x, x ∈ s → β x`. -/
-- A copy of forall notation from `Std.Util.ExtendedBinder` for pi notation
syntax "Π " binderIdent binderPred ", " term : term

macro_rules
  | `(Π $x:ident $pred:binderPred, $p) => `(Π $x:ident, satisfies_binder_pred% $x $pred → $p)
  | `(Π _ $pred:binderPred, $p) => `(Π x, satisfies_binder_pred% x $pred → $p)

/-- Since pi notation and forall notation are interchangeable, we can
parse it by simply using the pre-existing forall parser. -/
@[macro PiNotation.piNotation] def replacePiNotation : Lean.Macro
  | .node info _ args => return .node info ``Lean.Parser.Term.forall args
  | _ => Lean.Macro.throwUnsupported

/-- Override the Lean 4 pi notation delaborator with one that prints cute binders
such as `∀ ε > 0`. -/
@[delab forallE]
def delabPi : Delab := whenPPOption Lean.getPPNotation do
  let stx ← delabForall
  match stx with
  | `(∀ ($i:ident : $_), $j:ident ∈ $s → $body) =>
    if i == j then `(∀ $i:ident ∈ $s, $body) else pure stx
  | `(∀ ($x:ident : $_), $y:ident > $z → $body) =>
    if x == y then `(∀ $x:ident > $z, $body) else pure stx
  | `(∀ ($x:ident : $_), $y:ident < $z → $body) =>
    if x == y then `(∀ $x:ident < $z, $body) else pure stx
  | `(∀ ($x:ident : $_), $y:ident ≥ $z → $body) =>
    if x == y then `(∀ $x:ident ≥ $z, $body) else pure stx
  | `(∀ ($x:ident : $_), $y:ident ≤ $z → $body) =>
    if x == y then `(∀ $x:ident ≤ $z, $body) else pure stx
  | `(Π ($i:ident : $_), $j:ident ∈ $s → $body) =>
    if i == j then `(Π $i:ident ∈ $s, $body) else pure stx
  | `(∀ ($i:ident : $_), $j:ident ∉ $s → $body) =>
    if i == j then `(∀ $i:ident ∉ $s, $body) else pure stx
  | `(∀ ($i:ident : $_), $j:ident ⊆ $s → $body) =>
    if i == j then `(∀ $i:ident ⊆ $s, $body) else pure stx
  | `(∀ ($i:ident : $_), $j:ident ⊂ $s → $body) =>
    if i == j then `(∀ $i:ident ⊂ $s, $body) else pure stx
  | `(∀ ($i:ident : $_), $j:ident ⊇ $s → $body) =>
    if i == j then `(∀ $i:ident ⊇ $s, $body) else pure stx
  | `(∀ ($i:ident : $_), $j:ident ⊃ $s → $body) =>
    if i == j then `(∀ $i:ident ⊃ $s, $body) else pure stx
  | _ => pure stx

/-- Override the Lean 4 pi notation delaborator with one that uses `Π` and prints
cute binders such as `∀ ε > 0`.
Note that this takes advantage of the fact that `(x : α) → p x` notation is
never used for propositions, so we can match on this result and rewrite it. -/
@[scoped delab forallE]
def delabPi' : Delab := whenPPOption Lean.getPPNotation do
  let stx ← delabPi
  -- Replacements
  let stx : Term ←
    match stx with
    | `($group:bracketedBinder → $body) => `(Π $group:bracketedBinder, $body)
    | _ => pure stx
  -- Merging
  match stx with
  | `(Π $group, Π $groups*, $body) => `(Π $group $groups*, $body)
  | _ => pure stx

end PiNotation

section existential
open Lean Parser Term PrettyPrinter Delaborator

/-- Delaborator for existential quantifier, including extended binders. -/
-- TODO: reduce the duplication in this code
@[delab app.Exists]
def exists_delab : Delab := whenPPOption Lean.getPPNotation do
  let #[ι, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(∃ (_ : $dom), $body)
      else if prop || ppTypes then
        `(∃ ($x:ident : $dom), $body)
      else
        `(∃ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(∃ $i:ident, $j:ident ∈ $s ∧ $body)
    | `(∃ ($i:ident : $_), $j:ident ∈ $s ∧ $body) =>
      if i == j then `(∃ $i:ident ∈ $s, $body) else pure stx
    | `(∃ $x:ident, $y:ident > $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident > $z ∧ $body) =>
      if x == y then `(∃ $x:ident > $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident < $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident < $z ∧ $body) =>
      if x == y then `(∃ $x:ident < $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ≥ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ≥ $z ∧ $body) =>
      if x == y then `(∃ $x:ident ≥ $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ≤ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ≤ $z ∧ $body) =>
      if x == y then `(∃ $x:ident ≤ $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ∉ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ∉ $z ∧ $body) => do
      if x == y then `(∃ $x:ident ∉ $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ⊆ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ⊆ $z ∧ $body) =>
      if x == y then `(∃ $x:ident ⊆ $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ⊂ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ⊂ $z ∧ $body) =>
      if x == y then `(∃ $x:ident ⊂ $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ⊇ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ⊇ $z ∧ $body) =>
      if x == y then `(∃ $x:ident ⊇ $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ⊃ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ⊃ $z ∧ $body) =>
      if x == y then `(∃ $x:ident ⊃ $z, $body) else pure stx
    | _ => pure stx
  match stx with
  | `(∃ $group:bracketedExplicitBinders, ∃ $[$groups:bracketedExplicitBinders]*, $body) =>
    `(∃ $group $groups*, $body)
  | `(∃ $b:binderIdent, ∃ $[$bs:binderIdent]*, $body) => `(∃ $b:binderIdent $[$bs]*, $body)
  | _ => pure stx
end existential

open Lean Lean.PrettyPrinter.Delaborator

/-- Delaborator for `∉`. -/
@[delab app.Not] def delab_not_in := whenPPOption Lean.getPPNotation do
  let #[f] := (← SubExpr.getExpr).getAppArgs | failure
  guard <| f.isAppOfArity ``Membership.mem 5
  let stx₁ ← SubExpr.withAppArg <| SubExpr.withNaryArg 3 delab
  let stx₂ ← SubExpr.withAppArg <| SubExpr.withNaryArg 4 delab
  return ← `($stx₁ ∉ $stx₂)

/-!
# Anonymous mvar suffixes

The option `pp.anonymousMVarSuffixes` controls whether anonymous mvars are printed with numeric s
suffixes. When `false`, all anonymous mvars are printed as `?m✝` (or in the case of universe mvars
in `Sort` or `Type`, `?u✝`).

Note that this does not handle universe mvars in constants.

Note also that mvar names are not distinguished by superscripts as inaccessible fvars are: both
`?m.1` and `?m.2` are delaborated to `?m✝`.
-/

/-- If false, do not use numeric suffixes to distinguish anonymous metavariables. E.g., `?m.1234`
will instead be rendered as `?m✝`. -/
register_option pp.anonymousMVarSuffixes : Bool := {
  defValue := true
  group    := "pp"
  descr    := s!"(pretty printer) if false, do not use numeric suffixes to distinguish anonymous {
              ""}metavariables. E.g., `?m.1234` will instead be rendered as `?m✝`."
}

/-- Get the value of the option `pp.anonymousMVarSuffixes`. -/
def getPPAnonymousMVarSuffixes (o : Options) : Bool := o.get pp.anonymousMVarSuffixes.name true

namespace Lean.Level

/-- Exactly like `PP.toResult`, but uses `?u✝` in the `mvar` case. -/
private def PP.toResultNoSuffix : Level → Result
  | .zero       => Result.num 0
  | .succ l     => Result.succ (toResult l)
  | .max l₁ l₂  => Result.max (toResult l₁) (toResult l₂)
  | .imax l₁ l₂ => Result.imax (toResult l₁) (toResult l₂)
  | .param n    => Result.leaf n
  | .mvar _     => Result.leaf (Name.mkSimple "?u✝")

/-- Exactly like `Level.quote`, but uses `?u✝` for level mvars. -/
private def quoteNoSuffix (u : Level) (prec : Nat := 0) : Syntax.Level :=
  (PP.toResultNoSuffix u).quote prec

end Lean.Level

namespace Lean.PrettyPrinter.Delaborator

open SubExpr

/-- Delaborate `Sort`s/`Type`s without using numeric suffixes to distinguish between level mvars.
E.g., `?u.1234` will instead be rendered as `?u✝`.

Requires `set_option pp.anonymousMVarSuffxies false`. -/
@[delab sort]
def delabSortNoLevelSuffix : Delab := whenNotPPOption getPPAnonymousMVarSuffixes do
  let Expr.sort l ← getExpr | unreachable!
  match l with
  | Level.zero => `(Prop)
  | Level.succ .zero => `(Type)
  | _ => match l.dec with
    | some l' => `(Type $(Level.quoteNoSuffix l' max_prec))
    | none    => `(Sort $(Level.quoteNoSuffix l max_prec))

/-- Delaborate metavariables without using numeric suffixes to distinguish between anonymous mvars.
E.g., `?m.1234` will instead be rendered as `?m✝`.

Requires `set_option pp.anonymousMVarSuffxies false`. -/
@[delab mvar]
def delabMVarNoSuffix : Delab := whenNotPPOption getPPAnonymousMVarSuffixes do
  let Expr.mvar mvarId ← getExpr | unreachable!
  let n := match ← mvarId.getTag with
    | .anonymous => Name.mkSimple "m✝"
    | n => n
  `(?$(mkIdent n))
