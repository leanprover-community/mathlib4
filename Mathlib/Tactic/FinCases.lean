/-
Copyright (c) 2022 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Hanting Zhang
-/
import Mathlib.Tactic.Core
import Mathlib.Lean.Expr.Basic
import Mathlib.Data.Fintype.Basic

/-!
# The `fin_cases` tactic.

Given a hypothesis of the form `h : x ∈ (A : List α)`, `x ∈ (A : Finset α)`,
or `x ∈ (A : Multiset α)`,
or a hypothesis of the form `h : A`, where `[Fintype A]` is available,
`fin_cases h` will repeatedly call `cases` to split the goal into
separate cases for each possible value.
-/

open Lean.Meta

namespace Lean.Elab.Tactic

/-- If `e` is of the form `x ∈ (A : List α)`, `x ∈ (A : Finset α)`, or `x ∈ (A : Multiset α)`,
return `some α`, otherwise `none`. -/
def getMemType {m : Type → Type} [Monad m] [MonadError m] (e : Expr) : m (Option Expr) := do
  match e.getAppFnArgs with
  | (``Membership.mem, #[_, type, _, _, _]) =>
    match type.getAppFnArgs with
    | (``List, #[α])     => return α
    | (``Multiset, #[α]) => return α
    | (``Finset, #[α])   => return α
    | _ => throwError "Hypothesis must be of type `x ∈ (A : List α)`, `x ∈ (A : Finset α)`, \
                       or `x ∈ (A : Multiset α)`"
  | _ => return none

/--
Recursively runs the `cases` tactic on a hypothesis `h`.
As long as two goals are produced, `cases` is called recursively on the second goal,
and we return a list of the first goals which appeared.

This is useful for hypotheses of the form `h : a ∈ [l₁, l₂, ...]`,
which will be transformed into a sequence of goals with hypotheses `h : a = l₁`, `h : a = l₂`,
and so on.
-/
partial def unfoldCases (g : MVarId) (h : FVarId) : MetaM (List MVarId) := do
  let gs ← g.cases h
  try
    let #[g₁, g₂] := gs | throwError "unexpected number of cases"
    let gs ← unfoldCases g₂.mvarId g₂.fields[2]!.fvarId!
    return g₁.mvarId :: gs
  catch _ => return []

/-- Implementation of the `fin_cases` tactic. -/
partial def finCasesAt (g : MVarId) (hyp : FVarId) : MetaM (List MVarId) := g.withContext do
  let type ← hyp.getType >>= instantiateMVars
  match ← getMemType type with
  | some _ => unfoldCases g hyp
  | none =>
    -- Deal with `x : A`, where `[Fintype A]` is available:
    let inst ← synthInstance (← mkAppM ``Fintype #[type])
    let elems ← mkAppOptM ``Fintype.elems #[type, inst]
    let t ← mkAppM ``Membership.mem #[.fvar hyp, elems]
    let v ← mkAppOptM ``Fintype.complete #[type, inst, Expr.fvar hyp]
    let (fvar, g) ← (← g.assert `this t v).intro1P
    finCasesAt g fvar

/--
`fin_cases h` performs case analysis on a hypothesis of the form
`h : A`, where `[Fintype A]` is available, or
`h : a ∈ A`, where `A : Finset X`, `A : Multiset X` or `A : List X`.

As an example, in
```
example (f : ℕ → Prop) (p : Fin 3) (h0 : f 0) (h1 : f 1) (h2 : f 2) : f p.val := by
  fin_cases p; simp
  all_goals assumption
```
after `fin_cases p; simp`, there are three goals, `f 0`, `f 1`, and `f 2`.
-/
syntax (name := finCases) "fin_cases " ("*" <|> term,+) (" with " term,+)? : tactic

/-!
`fin_cases` used to also have two modifiers, `fin_cases ... with ...` and `fin_cases ... using ...`.
With neither actually used in mathlib, they haven't been re-implemented here.

In case someone finds a need for them, and wants to re-implement, the relevant sections of
the doc-string are preserved here:

---

`fin_cases h with l` takes a list of descriptions for the cases of `h`.
These should be definitionally equal to and in the same order as the
default enumeration of the cases.

For example,
```
example (x y : ℕ) (h : x ∈ [1, 2]) : x = y := by
  fin_cases h with 1, 1+1
```
produces two cases: `1 = y` and `1 + 1 = y`.

When using `fin_cases a` on data `a` defined with `let`,
the tactic will not be able to clear the variable `a`,
and will instead produce hypotheses `this : a = ...`.
These hypotheses can be given a name using `fin_cases a using ha`.

For example,
```
example (f : ℕ → Fin 3) : True := by
  let a := f 3
  fin_cases a using ha
```
produces three goals with hypotheses
`ha : a = 0`, `ha : a = 1`, and `ha : a = 2`.
-/

/- TODO: In mathlib3 we ran `norm_num` when there is no `with` clause. Is this still useful? -/
/- TODO: can we name the cases generated according to their values,
   rather than `tail.tail.tail.head`? -/

@[tactic finCases] elab_rules : tactic
  | `(tactic| fin_cases $[$hyps:ident],*) => withMainContext <| focus do
    for h in hyps do
      allGoals <| liftMetaTactic (finCasesAt · (← getFVarId h))

end Tactic

end Elab

end Lean
