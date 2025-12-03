/-
Copyright (c) 2022 Abby J. Goldberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abby J. Goldberg, Mario Carneiro, Heather Macbeth
-/
module

public meta import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Compare

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
left-hand side of the new goal and the left-hand side of the new weighted sum.
Lastly, calls a normalization tactic on this target.

## References

* <https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F.20tactics/topic/Linear.20algebra.20tactic/near/213928196>

-/

public meta section

namespace Mathlib.Tactic.LinearCombination
open Lean
open Elab Meta Term Ineq

/-- Result of `expandLinearCombo`, either an equality/inequality proof or a value. -/
inductive Expanded
  /-- A proof of `a = b`, `a ≤ b`, or `a < b` (according to the value of `Ineq`). -/
  | proof (rel : Ineq) (pf : Syntax.Term)
  /-- A value, equivalently a proof of `c = c`. -/
  | const (c : Syntax.Term)

/-- The handling in `linear_combination` of left- and right-multiplication and scalar-multiplication
and of division all five proceed according to the same logic, specified here: given a proof `p` of
an (in)equality and a constant `c`,
* if `p` is a proof of an equation, multiply/divide through by `c`;
* if `p` is a proof of a non-strict inequality, run `positivity` to find a proof that `c` is
  nonnegative, then multiply/divide through by `c`, invoking the nonnegativity of `c` where needed;
* if `p` is a proof of a strict inequality, run `positivity` to find a proof that `c` is positive
  (if possible) or nonnegative (if not), then multiply/divide through by `c`, invoking the
  positivity or nonnegativity of `c` where needed.

This generic logic takes as a parameter the object `lems`: the four lemmas corresponding to the four
cases. -/
def rescale (lems : Ineq.WithStrictness → Name) (ty : Option Expr) (p c : Term) :
    Ineq → TermElabM Expanded
  | eq => do
    let i := mkIdent <| lems .eq
    .proof eq <$> ``($i $p $c)
  | le => do
    let i := mkIdent <| lems .le
    let e₂ ← withSynthesizeLight <| Term.elabTerm c ty
    let hc₂ ← Meta.Positivity.proveNonneg e₂
    .proof le <$> ``($i $p $(← hc₂.toSyntax))
  | lt => do
    let e₂ ← withSynthesizeLight <| Term.elabTerm c ty
    let (strict, hc₂) ← Meta.Positivity.bestResult e₂
    let i := mkIdent <| lems (.lt strict)
    let p' : Term ← ``($i $p $(← hc₂.toSyntax))
    if strict then pure (.proof lt p') else pure (.proof le p')

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
partial def expandLinearCombo (ty : Option Expr) (stx : Syntax.Term) :
    TermElabM Expanded := withRef stx do
  match stx with
  | `(($e)) => expandLinearCombo ty e
  | `($e₁ + $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ + $c₂)
    | .proof rel₁ p₁, .proof rel₂ p₂ =>
      let i := mkIdent <| Ineq.addRelRelData rel₁ rel₂
      .proof (max rel₁ rel₂) <$> ``($i $p₁ $p₂)
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
    | .const c, .proof eq p =>
      logWarningAt c "this constant has no effect on the linear combination; it can be dropped \
        from the term"
      .proof eq <$> ``(Eq.symm $p)
    | .proof rel₁ p₁, .proof eq p₂ =>
      let i := mkIdent <| Ineq.addRelRelData rel₁ eq
      .proof rel₁ <$> ``($i $p₁ (Eq.symm $p₂))
    | _, .proof _ _ =>
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
    | .proof rel₁ p₁, .const c₂ => rescale mulRelConstData ty p₁ c₂ rel₁
    | .const c₁, .proof rel₂ p₂ => rescale mulConstRelData ty p₂ c₁ rel₂
    | .proof _ _, .proof _ _ =>
      throwErrorAt tk "'linear_combination' supports only linear operations"
  | `($e₁ •%$tk $e₂) => do
    match ← expandLinearCombo none e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ • $c₂)
    | .proof rel₁ p₁, .const c₂ => rescale smulRelConstData ty p₁ c₂ rel₁
    | .const c₁, .proof rel₂ p₂ => rescale smulConstRelData none p₂ c₁ rel₂
    | .proof _ _, .proof _ _ =>
      throwErrorAt tk "'linear_combination' supports only linear operations"
  | `($e₁ /%$tk $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ / $c₂)
    | .proof rel₁ p₁, .const c₂ => rescale divRelConstData ty p₁ c₂ rel₁
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
    match Ineq.relImpRelData hypRel goalRel with
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
The `linear_combination` tactic attempts to prove an (in)equality goal by exhibiting it as a
specified linear combination of (in)equality hypotheses, or other (in)equality proof terms, modulo
(A) moving terms between the LHS and RHS of the (in)equalities, and (B) a normalization tactic
which by default is ring-normalization.

Example usage:
```
example {a b : ℚ} (h1 : a = 1) (h2 : b = 3) : (a + b) / 2 = 2 := by
  linear_combination (h1 + h2) / 2

example {a b : ℚ} (h1 : a ≤ 1) (h2 : b ≤ 3) : (a + b) / 2 ≤ 2 := by
  linear_combination (h1 + h2) / 2

example {a b : ℚ} : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  linear_combination sq_nonneg (a - b)

example {x y z w : ℤ} (h₁ : x * z = y ^ 2) (h₂ : y * w = z ^ 2) :
    z * (x * w - y * z) = 0 := by
  linear_combination w * h₁ + y * h₂

example {x : ℚ} (h : x ≥ 5) : x ^ 2 > 2 * x + 11 := by
  linear_combination (x + 3) * h

example {R : Type*} [CommRing R] {a b : R} (h : a = b) : a ^ 2 = b ^ 2 := by
  linear_combination (a + b) * h

example {A : Type*} [AddCommGroup A]
    {x y z : A} (h1 : x + y = 10 • z) (h2 : x - y = 6 • z) :
    2 • x = 2 • (8 • z) := by
  linear_combination (norm := abel) h1 + h2

example (x y : ℤ) (h1 : x * y + 2 * x = 1) (h2 : x = y) :
    x * y = -2 * y + 1 := by
  linear_combination (norm := ring_nf) -2 * h2
  -- leaves goal `⊢ x * y + x * 2 - 1 = 0`
```

The input `e` in `linear_combination e` is a linear combination of proofs of (in)equalities,
given as a sum/difference of coefficients multiplied by expressions.
The coefficients may be arbitrary expressions (with nonnegativity constraints in the case of
inequalities).
The expressions can be arbitrary proof terms proving (in)equalities;
most commonly they are hypothesis names `h1`, `h2`, ....

The left and right sides of all the (in)equalities should have the same type `α`, and the
coefficients should also have type `α`.  For full functionality `α` should be a commutative ring --
strictly speaking, a commutative semiring with "cancellative" addition (in the semiring case,
negation and subtraction will be handled "formally" as if operating in the enveloping ring). If a
nonstandard normalization is used (for example `abel` or `skip`), the tactic will work over types
`α` with less algebraic structure: for equalities, the minimum is instances of
`[Add α] [IsRightCancelAdd α]` together with instances of whatever operations are used in the tactic
call.

The variant `linear_combination (norm := tac) e` specifies explicitly the "normalization tactic"
`tac` to be run on the subgoal(s) after constructing the linear combination.
* The default normalization tactic is `ring1` (for equalities) or `Mathlib.Tactic.Ring.prove{LE,LT}`
  (for inequalities). These are finishing tactics: they close the goal or fail.
* When working in algebraic categories other than commutative rings -- for example fields, abelian
  groups, modules -- it is sometimes useful to use normalization tactics adapted to those categories
  (`field_simp`, `abel`, `module`).
* To skip normalization entirely, use `skip` as the normalization tactic.
* The `linear_combination` tactic creates a linear combination by adding the provided (in)equalities
  together from left to right, so if `tac` is not invariant under commutation of additive
  expressions, then the order of the input hypotheses can matter.

The variant `linear_combination (exp := n) e` will take the goal to the `n`th power before
subtracting the combination `e`. In other words, if the goal is `t1 = t2`,
`linear_combination (exp := n) e` will change the goal to `(t1 - t2)^n = 0` before proceeding as
above.  This variant is implemented only for linear combinations of equalities (i.e., not for
inequalities).
-/
syntax (name := linearCombination) "linear_combination"
  (normStx)? (expStx)? (ppSpace colGt term)? : tactic
elab_rules : tactic
  | `(tactic| linear_combination%$tk $[(norm := $tac)]? $[(exp := $n)]? $(e)?) =>
    elabLinearCombination tk tac n e

end Mathlib.Tactic.LinearCombination
