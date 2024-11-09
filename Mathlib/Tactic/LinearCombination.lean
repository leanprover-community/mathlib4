/-
Copyright (c) 2022 Abby J. Goldberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abby J. Goldberg, Mario Carneiro, Heather Macbeth
-/
import Mathlib.Control.Basic
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.Compare

/-!
# linear_combination Tactic

In this file, the `linear_combination` tactic is created.  This tactic, which
works over `CommRing`s, attempts to simplify the target by creating a linear combination
of a list of equalities and subtracting it from the target. A `Syntax.Tactic`
object can also be passed into the tactic, allowing the user to specify a
normalization tactic.

Over ordered algebraic objects (such as `LinearOrderedCommRing`), taking linear combinations of
inequalities is also supported.

## Implementation Notes

This tactic works by creating a weighted sum of the given equations with the
given coefficients.  Then, it subtracts the right side of the weighted sum
from the left side so that the right side equals 0, and it does the same with
the target.  Afterwards, it sets the goal to be the equality between the
lefthand side of the new goal and the lefthand side of the new weighted sum.
Lastly, calls a normalization tactic on this target.

## References

* <https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F.20tactics/topic/Linear.20algebra.20tactic/near/213928196>

-/

namespace Mathlib.Tactic.LinearCombination
open Lean hiding Rat
open Elab Meta Term Mathlib Ineq

/-- Result of `expandLinearCombo`, either an equality/inequality proof or a value. -/
inductive Expanded
  /-- A proof of `a = b`, `a ≤ b`, or `a < b` (according to the value of `Ineq`). -/
  | proof (rel : Ineq) (pf : Syntax.Term)
  /-- A value, equivalently a proof of `c = c`. -/
  | const (c : Syntax.Term)

/--
Performs macro expansion of a linear combination expression,
using `+`/`-`/`*`/`/` on equations and values.
* `.proof eq p` means that `p` is a syntax corresponding to a proof of an equation.
  For example, if `h : a = b` then `expandLinearCombo (2 * h)` returns `.proof (c_add_pf 2 h)`
  which is a proof of `2 * a = 2 * b`.
  Similarly, `.proof le p` means that `p` is a syntax corresponding to a proof of a non-strict
  inequality, and `.proof lt p` means that `p` is a syntax corresponding to a proof of a strict
  inequality.
* `.const c` means that the input expression is not an equation but a value.
-/
partial def expandLinearCombo (ty : Expr) (stx : Syntax.Term) : TermElabM Expanded := withRef stx do
  match stx with
  | `(($e)) => expandLinearCombo ty e
  | `($e₁ + $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ + $c₂)
    | .proof rel₁ p₁, .proof rel₂ p₂ =>
      let (rel, n) := rel₁.addRelRelData rel₂
      .proof rel <$> ``($(mkIdent n) $p₁ $p₂)
    | .proof rel p, .const c | .const c, .proof rel p =>
      logWarningAt c "this constant has no effect on the linear combination; it can be dropped \
        from the term"
      pure (.proof rel p)
  | `($e₁ - $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ - $c₂)
    | .proof rel p, .const c =>
      logWarningAt c "this constant has no effect on the linear combination; it can be dropped \
        from the term"
      pure (.proof rel p)
    | .const c, .proof rel p =>
      logWarningAt c "this constant has no effect on the linear combination; it can be dropped \
        from the term"
      .proof rel <$> ``(Eq.symm $p)
    | .proof rel₁ p₁, .proof eq p₂ =>
      let (rel, n) := rel₁.addRelRelData eq
      .proof rel <$> ``($(mkIdent n) $p₁ (Eq.symm $p₂))
    | .proof _ _, .proof _ _ =>
      throwError "coefficients of inequalities in 'linear_combination' must be nonnegative"
  | `(-$e) => do
      match ← expandLinearCombo ty e with
      | .const c => .const <$> `(-$c)
      | .proof eq p => .proof eq <$> ``(Eq.symm $p)
      | .proof _ _ =>
        throwError "coefficients of inequalities in 'linear_combination' must be nonnegative"
  | `($e₁ *%$tk $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ * $c₂)
    | .proof rel₁ p₁, .const c₂ =>
      let (rel, n) := rel₁.mulRelConstData
      .proof rel <$> ``($(mkIdent n) $p₁ $c₂)
    | .const c₁, .proof rel₂ p₂ =>
      let (rel, n) := rel₂.mulConstRelData
      .proof rel <$> ``($(mkIdent n) $p₂ $c₁)
    | .proof _ _, .proof _ _ =>
      throwErrorAt tk "'linear_combination' supports only linear operations"
  | `($e₁ /%$tk $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ / $c₂)
    | .proof rel₁ p₁, .const c₂ =>
      let (rel, n) := rel₁.divRelConstData
      .proof rel <$> ``($(mkIdent n) $p₁ $c₂)
    | _, .proof _ _ => throwErrorAt tk "'linear_combination' supports only linear operations"
  | e =>
    -- We have the expected type from the goal, so we can fully synthesize this leaf node.
    withSynthesize do
      -- It is OK to use `ty` as the expected type even if `e` is a proof.
      -- The expected type is just a hint.
      let c ← withSynthesizeLight <| Term.elabTerm e ty
      match ← try? (← inferType c).ineq? with
      | some (rel, _) => .proof rel <$> c.toSyntax
      | none => .const <$> c.toSyntax

/-- Implementation of `linear_combination`. -/
def elabLinearCombination (tk : Syntax)
    (norm? : Option Syntax.Tactic) (exp? : Option Syntax.NumLit) (input : Option Syntax.Term) :
    Tactic.TacticM Unit := Tactic.withMainContext <| Tactic.focus do
  let eType ← withReducible <| (← Tactic.getMainGoal).getType'
  let (goalRel, ty, _) ← eType.ineq?
  -- build the specified linear combination of the hypotheses
  let (hypRel, p) ← match input with
  | none => Prod.mk eq <$>  `(Eq.refl 0)
  | some e =>
    match ← expandLinearCombo ty e with
    | .const c =>
      logWarningAt c "this constant has no effect on the linear combination; it can be dropped \
        from the term"
      Prod.mk eq <$> `(Eq.refl 0)
    | .proof hypRel p => pure (hypRel, p)
  -- look up the lemma for the central `refine` in `linear_combination`
  let (reduceLem, newGoalRel) : Name × Ineq := ← do
    match hypRel.relImpRelData goalRel with
    | none => throwError "cannot prove an equality from inequality hypotheses"
    | some n => pure n
  -- build the term for the central `refine` in `linear_combination`
  let p' ← do
    match exp? with
    | some n =>
      if n.getNat = 1 then
        `($(mkIdent reduceLem) $p ?a)
      else
        match hypRel with
        | eq => `(eq_of_add_pow $n $p ?a)
        | _ => throwError
          "linear_combination tactic not implemented for exponentiation of inequality goals"
    | _ => `($(mkIdent reduceLem) $p ?a)
  -- run the central `refine` in `linear_combination`
  Term.withoutErrToSorry <| Tactic.refineCore p' `refine false
  -- if we are in a "true" ring, with well-behaved negation, we rearrange from the form
  -- `[stuff] = [stuff]` (or `≤` or `<`) to the form `[stuff] = 0` (or `≤` or `<`), because this
  -- gives more useful error messages on failure
  let _ ← Tactic.tryTactic <| Tactic.liftMetaTactic fun g ↦ g.applyConst newGoalRel.rearrangeData
  match norm? with
  -- now run the normalization tactic provided
  | some norm => Tactic.evalTactic norm
  -- or the default normalization tactic if none is provided
  | none => withRef tk <| Tactic.liftMetaFinishingTactic <|
    match newGoalRel with
    -- for an equality task the default normalization tactic is (the internals of) `ring1` (but we
    -- use `.instances` transparency, which is arguably more robust in algebraic settings than the
    -- choice `.reducible` made in `ring1`)
    | eq => fun g ↦ AtomM.run .instances <| Ring.proveEq g
    | le => Ring.proveLE
    | lt => Ring.proveLT

/--
The `(norm := $tac)` syntax says to use `tac` as a normalization postprocessor for
`linear_combination`. The default normalizer is `ring1`, but you can override it with `ring_nf`
to get subgoals from `linear_combination` or with `skip` to disable normalization.
-/
syntax normStx := atomic(" (" &"norm" " := ") withoutPosition(tactic) ")"

/--
The `(exp := n)` syntax for `linear_combination` says to take the goal to the `n`th power before
subtracting the given combination of hypotheses.
-/
syntax expStx := atomic(" (" &"exp" " := ") withoutPosition(num) ")"

/--
`linear_combination` attempts to simplify the target by creating a linear combination
  of a list of equalities and subtracting it from the target.
  The tactic will create a linear
  combination by adding the equalities together from left to right, so the order
  of the input hypotheses does matter.  If the `norm` field of the
  tactic is set to `skip`, then the tactic will simply set the user up to
  prove their target using the linear combination instead of normalizing the subtraction.

Note: The left and right sides of all the equalities should have the same type `α`, and the
coefficients should also have type `α`.  For full functionality `α` should be a commutative ring --
strictly speaking, a commutative semiring with "cancellative" addition (in the semiring case,
negation and subtraction will be handled "formally" as if operating in the enveloping ring). If a
nonstandard normalization is used (for example `abel` or `skip`), the tactic will work over types
`α` with less algebraic structure: the minimum is instances of `[Add α] [IsRightCancelAdd α]`
together with instances of whatever operations are used in the tactic call.

* The input `e` in `linear_combination e` is a linear combination of proofs of equalities,
  given as a sum/difference of coefficients multiplied by expressions.
  The coefficients may be arbitrary expressions.
  The expressions can be arbitrary proof terms proving equalities.
  Most commonly they are hypothesis names `h1, h2, ...`.
* `linear_combination (norm := tac) e` runs the "normalization tactic" `tac`
  on the subgoal(s) after constructing the linear combination.
  * The default normalization tactic is `ring1`, which closes the goal or fails.
  * To get a subgoal in the case that it is not immediately provable, use
    `ring_nf` as the normalization tactic.
  * To avoid normalization entirely, use `skip` as the normalization tactic.
* `linear_combination (exp := n) e` will take the goal to the `n`th power before subtracting the
  combination `e`. In other words, if the goal is `t1 = t2`, `linear_combination (exp := n) e`
  will change the goal to `(t1 - t2)^n = 0` before proceeding as above.

Example Usage:
```
example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination 1*h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination (norm := ring_nf) -2*h2
  /- Goal: x * y + x * 2 - 1 = 0 -/

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
    -3*x - 3*y - 4*z = 2 := by
  linear_combination ha - hb - 2*hc

example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
    x*x*y + y*x*y + 6*x = 3*x*y + 14 := by
  linear_combination x*y*h1 + 2*h2

example (x y : ℤ) (h1 : x = -3) (h2 : y = 10) : 2*x = -6 := by
  linear_combination (norm := skip) 2*h1
  simp

axiom qc : ℚ
axiom hqc : qc = 2*qc

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc := by
  linear_combination 3 * h a b + hqc
```
-/
syntax (name := linearCombination) "linear_combination"
  (normStx)? (expStx)? (ppSpace colGt term)? : tactic
elab_rules : tactic
  | `(tactic| linear_combination%$tk $[(norm := $tac)]? $[(exp := $n)]? $(e)?) =>
    elabLinearCombination tk tac n e

end Mathlib.Tactic.LinearCombination
