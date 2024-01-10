/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Data.Set.Finite
import Mathlib.Util.FlexibleBinders

/-!
# The `finset%` flexible binder domain

Gives an implementation of the `finset%` interpretation of `x ∈ s`.
-/

namespace Mathlib.FlexibleBinders
open Lean Meta

/-- `finset% t` elaborates `t` as a `Finset`.
If `t` is a `Set` at reducible transparency, then inserts `Set.toFinset`.
Does not make use of the expected type; useful for bounded quantifiers over finsets.
```
#check finset% Finset.range 2 -- Finset Nat
#check finset% (Set.univ : Set Bool) -- Finset Bool
```
-/
elab (name := finsetStx) "finset% " t:term : term => do
  let u ← mkFreshLevelMVar
  let ty ← mkFreshExprMVar (mkSort (.succ u))
  -- Elaborate with `Finset _` as a hint
  let x ← Elab.Term.elabTerm t (mkApp (.const ``Finset [u]) ty)
  let xty ← whnfR (← inferType x)
  if xty.isAppOfArity ``Set 1 then
    Elab.Term.elabAppArgs (.const ``Set.toFinset [u]) #[] #[.expr x] none false false
  else
    return x

open Lean.Elab.Term.Quotation in
/-- `quot_precheck` for the `finset%` syntax. -/
@[quot_precheck Mathlib.FlexibleBinders.finsetStx] def precheckFinsetStx : Precheck
  | `(finset% $t) => precheck t
  | _ => Elab.throwUnsupportedSyntax

/-- For the `finset%` domain, `x ∈ s` is a binder over `s` as a `Finset`. -/
macro_rules
  | `(binder%(finset%, $e ∈ $s)) => do
    let (e, ty) ← destructAscription e
    `(binderResolved%($ty, $e, finset% $s))

/-- Binder over a dependent product.
For example, `(x ∈ s) × (y ∈ t x)` is short for `⟨x, y⟩ ∈ Finset.sigma s t`.
This does not require that both sides have exactly one binder,
but it will not switch to `Finset.product` on account of having more than
one binder.

If a variable is `_` it will use `Finset.product`.

```
#test_flexible_binders finset% => (a : Nat) × (x ∈ s) × (y z ∈ t s)
```
-/
macro_rules
  | `(binder%(finset%, $bs:bracketedExplicitBinders × $b2)) => do
    -- bracketedExplicitBinders := "(" binderIdent+ ": " term ")"
    match bs with
    | `(bracketedExplicitBinders| ($bis* : $ty)) =>
      if bis.isEmpty then Macro.throwUnsupported
      let bis' ← bis.mapM fun b => withRef b <|
        match b with
        | `(binderIdent| $id:ident) => `(term| $id)
        | `(binderIdent| _) => `(term| _)
        | _ => Macro.throwUnsupported
      let b1 ← `(term| ($(bis'[0]!) $(bis'.extract 1 bis'.size)* : $ty))
      `(binder%(finset%, $b1 × $b2))
    | _ => Macro.throwUnsupported
  | `(binder%(finset%, $b1 × $b2)) => do
    let fbd ← `(flexibleBindersDom|finset%)
    let bs := (← expandBinder fbd b1) ++ (← expandBinder fbd b2)
    let mut s? := none
    let mut pty? := none
    let mut xs := []
    let mut bs' := []
    for i in [0:bs.size] do
      let b := bs[bs.size - 1 - i]!
      match b with
      | .std ty x dom? =>
        xs := x :: xs
        let dom ← dom?.getDM `(Finset.univ)
        if let some s := s? then
          if let `($x:ident) := x then
            s? := some <| ← `(Finset.sigma $dom (fun ($x : $ty) => $s))
            pty? := some <| ← `(($x:ident : $ty) × $pty?.get!)
          else
            s? := some <| ← `(Finset.product $dom $s)
            pty? := some <| ← `($ty × $pty?.get!)
        else
          s? := some dom
          pty? := some ty
      | .prop p =>
        xs := (← `(_)) :: xs
        let ty ← `(PLift $p)
        let dom ← `(Finset.univ)
        if let some s := s? then
          s? := some <| ← `(Finset.product $dom $s)
          pty? := some <| ← `($ty × $pty?.get!)
        else
          s? := some dom
          pty? := some ty
      | .match discr patt =>
        if let some s := s? then
          s? := some <| ← `(match $discr:term with | $patt => $s)
        bs' := (← `(binderMatch%($discr, $patt))) :: bs'
      | .letI x val =>
        if let some s := s? then
          s? := some <| ← `(letI $x := $val; $s)
        bs' := (← `(binderLetI%($x, $val))) :: bs'
    let some s := s? | Macro.throwError "Expecting at least one binder"
    `(binderResolved%($pty?.get!, ⟨$xs.toArray,*⟩, $s) $bs'.toArray*)

/-- Notation for binders to add a filter condition.
For example, `∑ (x ∈ s) when x < 10, 2 * x`. -/
syntax:0 term:1 " when " term:1 : term

/-- Add a `Finset.filter` on the last binder in `bs` for the given `cond`. -/
partial def processWhen (bs : Array Binder) (cond : Term) (i : Nat) :
    MacroM (Term × List Binder ⊕ List Binder) := do
  if i < bs.size then
    let b := bs[i]!
    match ← processWhen bs cond (i + 1) with
    | .inl (cond', bs'') =>
      match b with
      | .std ty x dom? =>
        let dom ← dom?.getDM `(Finset.univ)
        let b' := .std ty x (← `(Finset.filter (fun $x => $cond') $dom))
        return .inr (b' :: bs'')
      | .prop p =>
        Macro.throwErrorAt p "`when` clause does not support prop binders."
      | .letI x val =>
        return .inl (← `(letI $x := $val; $cond'), b :: bs'')
      | .match discr patt =>
        return .inl (← `(match $discr:term with | $patt => $cond'), b :: bs'')
    | .inr bs'' => return .inr (b :: bs'')
  else
    return .inl (cond, [])

macro_rules
  | `(binder%(finset%, $bs when $cond)) => do
    let fbd ← `(flexibleBindersDom|finset%)
    let bs' ← expandBinder fbd bs
    let .inr bs'' ← processWhen bs' cond 0 |
      Macro.throwErrorAt bs "`when` clause expects a binder"
    return combineBinders <| ← bs''.toArray.mapM fun
      | .std ty x dom? => `(binderResolved%($ty, $x $[, $dom?]?))
      | .prop p => `(binderResolved%($p))
      | .letI x val => `(binderLetI%($x, $val))
      | .match discr patt => `(binderMatch%($discr, $patt))
