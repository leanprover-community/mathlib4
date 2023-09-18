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
