/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset  -- shake: keep (Qq dependency)
public import Mathlib.Data.Finset.Density  -- shake: keep (Qq dependency)
public meta import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.NormNum.Basic

/-!
# Positivity extensions for finsets

This file provides a few `positivity` extensions that cannot be in either the finset files (because
they don't know about ordered fields) or in `Tactic.Positivity.Basic` (because it doesn't want to
know about finiteness).
-/

public meta section

namespace Mathlib.Meta.Positivity

open Qq Lean Meta Finset

/-- Extension for `Finset.card`. `#s` is positive if `s` is nonempty.

It calls `Mathlib.Meta.proveFinsetNonempty` to attempt proving that the finset is nonempty. -/
@[positivity Finset.card _]
meta def evalFinsetCard : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Finset.card $s) =>
    let some ps ← proveFinsetNonempty s | return .none
    assertInstancesCommute
    return .positive q(Finset.Nonempty.card_pos $ps)
  | _ => throwError "not Finset.card"

/-- Extension for `Fintype.card`. `Fintype.card α` is positive if `α` is nonempty. -/
@[positivity Fintype.card _]
meta def evalFintypeCard : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(@Fintype.card $β $instβ) =>
    let instβno ← synthInstanceQ q(Nonempty $β)
    assumeInstancesCommute
    return .positive q(@Fintype.card_pos $β $instβ $instβno)
  | _ => throwError "not Fintype.card"

/-- Extension for `Finset.dens`. `s.dens` is positive if `s` is nonempty.

It calls `Mathlib.Meta.proveFinsetNonempty` to attempt proving that the finset is nonempty. -/
@[positivity Finset.dens _]
meta def evalFinsetDens : PositivityExt where eval {u 𝕜} _ _ e := do
  match u, 𝕜, e with
  | 0, ~q(ℚ≥0), ~q(@Finset.dens $α $instα $s) =>
    let some ps ← proveFinsetNonempty s | return .none
    assumeInstancesCommute
    return .positive q(@Nonempty.dens_pos $α $instα $s $ps)
  | _, _, _ => throwError "not Finset.dens"

attribute [local instance] monadLiftOptionMetaM in
/-- The `positivity` extension which proves that `∑ i ∈ s, f i` is nonnegative if `f` is, and
positive if each `f i` is and `s` is nonempty.

TODO: The following example does not work
```
example (s : Finset ℕ) (f : ℕ → ℤ) (hf : ∀ n, 0 ≤ f n) : 0 ≤ s.sum f := by positivity
```
because `compareHyp` can't look for assumptions behind binders.
-/
@[positivity Finset.sum _ _]
meta def evalFinsetSum : PositivityExt where eval {u α} zα pα e := do
  match e with
  | ~q(@Finset.sum $ι _ $instα $s $f) =>
    let i : Q($ι) ← mkFreshExprMVarQ q($ι) .syntheticOpaque
    have body : Q($α) := .betaRev f #[i]
    let rbody ← core zα pα body
    let p_pos : Option Q(0 < $e) := ← (do
      let .positive pbody := rbody | pure none -- Fail if the body is not provably positive
      let some ps ← proveFinsetNonempty s | pure none
      let .some pα' ← trySynthInstanceQ q(IsOrderedCancelAddMonoid $α) | pure none
      assertInstancesCommute
      let pr : Q(∀ i, 0 < $f i) ← mkLambdaFVars #[i] pbody
      return some q(@sum_pos $ι $α $instα $pα $pα' $f $s (fun i _ ↦ $pr i) $ps))
    -- Try to show that the sum is positive
    if let some p_pos := p_pos then
      return .positive p_pos
    -- Fall back to showing that the sum is nonnegative
    else
      let pbody ← rbody.toNonneg
      let pr : Q(∀ i, 0 ≤ $f i) ← mkLambdaFVars #[i] pbody
      let pα' ← synthInstanceQ q(AddLeftMono $α)
      assertInstancesCommute
      return .nonnegative q(@sum_nonneg $ι $α $instα $pα $f $s $pα' fun i _ ↦ $pr i)
  | _ => throwError "not Finset.sum"

variable {α : Type*} {s : Finset α}

example : 0 ≤ #s := by positivity
example (hs : s.Nonempty) : 0 < #s := by positivity

variable [Fintype α]

example : 0 ≤ Fintype.card α := by positivity
example : 0 ≤ dens s := by positivity
example (hs : s.Nonempty) : 0 < dens s := by positivity
example (hs : s.Nonempty) : dens s ≠ 0 := by positivity
example [Nonempty α] : 0 < #(univ : Finset α) := by positivity
example [Nonempty α] : 0 < Fintype.card α := by positivity
example [Nonempty α] : 0 < dens (univ : Finset α) := by positivity
example [Nonempty α] : dens (univ : Finset α) ≠ 0 := by positivity

example {G : Type*} {A : Finset G} :
    let f := fun _ : G ↦ 1; (∀ s, f s ^ 2 = 1) → 0 ≤ #A := by
  intros
  positivity -- Should succeed despite failing to prove `A` is nonempty.

end Mathlib.Meta.Positivity
