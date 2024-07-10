/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Simon Hudon, Alice Laroche, Frédéric Dupuis, Jireh Loreaux
-/

import Lean.Elab.Tactic.Location
import Mathlib.Logic.Basic
import Mathlib.Init.Order.Defs
import Mathlib.Tactic.Conv
import Mathlib.Init.Set
import Lean.Elab.Tactic.Location

set_option autoImplicit true

namespace Mathlib.Tactic.PushNeg

open Lean Meta Elab.Tactic Parser.Tactic

variable (p q : Prop) (s : α → Prop)

theorem not_not_eq : (¬ ¬ p) = p := propext not_not
theorem not_and_eq : (¬ (p ∧ q)) = (p → ¬ q) := propext not_and
theorem not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ ¬ q) := propext not_and_or
theorem not_or_eq : (¬ (p ∨ q)) = (¬ p ∧ ¬ q) := propext not_or
theorem not_forall_eq : (¬ ∀ x, s x) = (∃ x, ¬ s x) := propext not_forall
theorem not_exists_eq : (¬ ∃ x, s x) = (∀ x, ¬ s x) := propext not_exists
theorem not_implies_eq : (¬ (p → q)) = (p ∧ ¬ q) := propext Classical.not_imp
theorem not_ne_eq (x y : α) : (¬ (x ≠ y)) = (x = y) := ne_eq x y ▸ not_not_eq _
theorem not_iff : (¬ (p ↔ q)) = ((p ∧ ¬ q) ∨ (¬ p ∧ q)) := propext <|
  _root_.not_iff.trans <| iff_iff_and_or_not_and_not.trans <| by rw [not_not, or_comm]

variable {β : Type u} [LinearOrder β]
theorem not_le_eq (a b : β) : (¬ (a ≤ b)) = (b < a) := propext not_le
theorem not_lt_eq (a b : β) : (¬ (a < b)) = (b ≤ a) := propext not_lt
theorem not_ge_eq (a b : β) : (¬ (a ≥ b)) = (a < b) := propext not_le
theorem not_gt_eq (a b : β) : (¬ (a > b)) = (a ≤ b) := propext not_lt

theorem not_nonempty_eq (s : Set γ) : (¬ s.Nonempty) = (s = ∅) := by
  have A : ∀ (x : γ), ¬(x ∈ (∅ : Set γ)) := fun x ↦ id
  simp only [Set.Nonempty, not_exists, eq_iff_iff]
  exact ⟨fun h ↦ Set.ext (fun x ↦ by simp only [h x, false_iff, A]), fun h ↦ by rwa [h]⟩

theorem ne_empty_eq_nonempty (s : Set γ) : (s ≠ ∅) = s.Nonempty := by
  rw [ne_eq, ← not_nonempty_eq s, not_not]

theorem empty_ne_eq_nonempty (s : Set γ) : (∅ ≠ s) = s.Nonempty := by
  rw [ne_comm, ne_empty_eq_nonempty]

/-- Make `push_neg` use `not_and_or` rather than the default `not_and`. -/
register_option push_neg.use_distrib : Bool :=
  { defValue := false
    group := ""
    descr := "Make `push_neg` use `not_and_or` rather than the default `not_and`." }

/-- Push negations at the top level of the current expression. -/
def transformNegationStep (e : Expr) : SimpM (Option Simp.Step) := do
  -- Wrapper around `Simp.Step.visit`
  let mkSimpStep (e : Expr) (pf : Expr) : Simp.Step :=
    Simp.Step.visit { expr := e, proof? := some pf }
  -- Try applying the inequality lemma and verify that we do get a defeq type.
  -- Sometimes there might be the wrong LinearOrder available!
  let handleIneq (e₁ e₂ : Expr) (notThm : Name) : SimpM (Option Simp.Step) := do
    try
      -- Allowed to fail if it can't synthesize an instance:
      let thm ← mkAppM notThm #[e₁, e₂]
      let some (_, lhs, rhs) := (← inferType thm).eq? | failure -- this should never fail
      -- Make sure the inferred instances are right:
      guard <| ← isDefEq e lhs
      return some <| mkSimpStep rhs thm
    catch _ => return none
  let e_whnf ← whnfR e
  let some ex := e_whnf.not? | return Simp.Step.continue
  let ex := (← instantiateMVars ex).cleanupAnnotations
  match ex.getAppFnArgs with
  | (``Not, #[e]) =>
      return mkSimpStep e (← mkAppM ``not_not_eq #[e])
  | (``And, #[p, q]) =>
      match ← getBoolOption `push_neg.use_distrib with
      | false => return mkSimpStep (.forallE `_ p (mkNot q) default) (← mkAppM ``not_and_eq #[p, q])
      | true  => return mkSimpStep (mkOr (mkNot p) (mkNot q)) (← mkAppM ``not_and_or_eq #[p, q])
  | (``Or, #[p, q]) =>
      return mkSimpStep (mkAnd (mkNot p) (mkNot q)) (← mkAppM ``not_or_eq #[p, q])
  | (``Iff, #[p, q]) =>
      return mkSimpStep (mkOr (mkAnd p (mkNot q)) (mkAnd (mkNot p) q)) (← mkAppM ``not_iff #[p, q])
  | (``Eq, #[ty, e₁, e₂]) =>
      if ty.isAppOfArity ``Set 1 then
        -- test if equality is of the form `s = ∅`, and negate it to `s.Nonempty`
        if e₂.isAppOfArity ``EmptyCollection.emptyCollection 2 then
          let thm ← mkAppM ``ne_empty_eq_nonempty #[e₁]
          let some (_, _, rhs) := (← inferType thm).eq? | return none
          return mkSimpStep rhs thm
        -- test if equality is of the form `∅ = s`, and negate it to `s.Nonempty`
        if e₁.isAppOfArity ``EmptyCollection.emptyCollection 2 then
          let thm ← mkAppM ``empty_ne_eq_nonempty #[e₂]
          let some (_, _, rhs) := (← inferType thm).eq? | return none
          return mkSimpStep rhs thm
      -- negate `a = b` to `a ≠ b`
      return Simp.Step.visit { expr := ← mkAppM ``Ne #[e₁, e₂] }
  | (``Ne, #[_ty, e₁, e₂]) =>
      return mkSimpStep (← mkAppM ``Eq #[e₁, e₂]) (← mkAppM ``not_ne_eq #[e₁, e₂])
  | (``LE.le, #[_ty, _inst, e₁, e₂]) => handleIneq e₁ e₂ ``not_le_eq
  | (``LT.lt, #[_ty, _inst, e₁, e₂]) => handleIneq e₁ e₂ ``not_lt_eq
  | (``GE.ge, #[_ty, _inst, e₁, e₂]) => handleIneq e₁ e₂ ``not_ge_eq
  | (``GT.gt, #[_ty, _inst, e₁, e₂]) => handleIneq e₁ e₂ ``not_gt_eq
  | (``Set.Nonempty, #[_ty, e]) =>
      -- negate `s.Nonempty` to `s = ∅`
      let thm ← mkAppM ``not_nonempty_eq #[e]
      let some (_, _, rhs) := (← inferType thm).eq? | return none
      return mkSimpStep rhs thm
  | (``Exists, #[_, .lam n typ bo bi]) =>
      return mkSimpStep (.forallE n typ (mkNot bo) bi)
                        (← mkAppM ``not_exists_eq #[.lam n typ bo bi])
  | (``Exists, #[_, _]) =>
      return none
  | _ => match ex with
          | .forallE name ty body binfo => do
              if (← isProp ty) && !body.hasLooseBVars then
                return mkSimpStep (← mkAppM ``And #[ty, mkNot body])
                  (← mkAppM ``not_implies_eq #[ty, body])
              else
                let body' : Expr := .lam name ty (mkNot body) binfo
                let body'' : Expr := .lam name ty body binfo
                return mkSimpStep (← mkAppM ``Exists #[body']) (← mkAppM ``not_forall_eq #[body''])
          | _ => return none

/-- Recursively push negations at the top level of the current expression. This is needed
to handle e.g. triple negation. -/
partial def transformNegation (e : Expr) : SimpM Simp.Step := do
  let Simp.Step.visit r₁ ← transformNegationStep e | return Simp.Step.continue
  match r₁.proof? with
  | none => return Simp.Step.continue r₁
  | some _ => do
      let Simp.Step.visit r₂ ← transformNegation r₁.expr | return Simp.Step.visit r₁
      return Simp.Step.visit (← r₁.mkEqTrans r₂)

/-- Common entry point to `push_neg` as a conv. -/
def pushNegCore (tgt : Expr) : MetaM Simp.Result := do
  let myctx : Simp.Context :=
    { config := { eta := true, zeta := false, proj := false },
      simpTheorems := #[ ]
      congrTheorems := (← getSimpCongrTheorems) }
  (·.1) <$> Simp.main tgt myctx (methods := { pre := transformNegation })

/--
Push negations into the conclusion of an expression.
For instance, an expression `¬ ∀ x, ∃ y, x ≤ y` will be transformed by `push_neg` into
`∃ x, ∀ y, y < x`. Variable names are conserved.
This tactic pushes negations inside expressions. For instance, given a hypothesis
```lean
| ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - y₀| ≤ ε)
```
writing `push_neg` will turn the target into
```lean
| ∃ ε, ε > 0 ∧ ∀ δ, δ > 0 → (∃ x, |x - x₀| ≤ δ ∧ ε < |f x - y₀|),
```
(The pretty printer does *not* use the abbreviations `∀ δ > 0` and `∃ ε > 0` but this issue
has nothing to do with `push_neg`).

Note that names are conserved by this tactic, contrary to what would happen with `simp`
using the relevant lemmas.

This tactic has two modes: in standard mode, it transforms `¬(p ∧ q)` into `p → ¬q`, whereas in
distrib mode it produces `¬p ∨ ¬q`. To use distrib mode, use `set_option push_neg.use_distrib true`.
-/
syntax (name := pushNegConv) "push_neg" : conv

/-- Execute `push_neg` as a conv tactic. -/
@[tactic pushNegConv] def elabPushNegConv : Tactic := fun _ ↦ withMainContext do
  Conv.applySimpResult (← pushNegCore (← instantiateMVars (← Conv.getLhs)))

/--
The syntax is `#push_neg e`, where `e` is an expression,
which will print the `push_neg` form of `e`.

`#push_neg` understands local variables, so you can use them to introduce parameters.
-/
macro (name := pushNeg) tk:"#push_neg " e:term : command => `(command| #conv%$tk push_neg => $e)

/-- Execute main loop of `push_neg` at the main goal. -/
def pushNegTarget : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let newGoal ← applySimpResultToTarget goal tgt (← pushNegCore tgt)
  if newGoal == goal then throwError "push_neg made no progress"
  replaceMainGoal [newGoal]


/-- Execute main loop of `push_neg` at a local hypothesis. -/
def pushNegLocalDecl (fvarId : FVarId) : TacticM Unit := withMainContext do
  let ldecl ← fvarId.getDecl
  if ldecl.isAuxDecl then return
  let tgt ← instantiateMVars ldecl.type
  let goal ← getMainGoal
  let myres ← pushNegCore tgt
  let some (_, newGoal) ← applySimpResultToLocalDecl goal fvarId myres False | failure
  if newGoal == goal then throwError "push_neg made no progress"
  replaceMainGoal [newGoal]

/--
Push negations into the conclusion of a hypothesis.
For instance, a hypothesis `h : ¬ ∀ x, ∃ y, x ≤ y` will be transformed by `push_neg at h` into
`h : ∃ x, ∀ y, y < x`. Variable names are conserved.
This tactic pushes negations inside expressions. For instance, given a hypothesis
```lean
h : ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - y₀| ≤ ε)
```
writing `push_neg at h` will turn `h` into
```lean
h : ∃ ε, ε > 0 ∧ ∀ δ, δ > 0 → (∃ x, |x - x₀| ≤ δ ∧ ε < |f x - y₀|),
```
(The pretty printer does *not* use the abbreviations `∀ δ > 0` and `∃ ε > 0` but this issue
has nothing to do with `push_neg`).

Note that names are conserved by this tactic, contrary to what would happen with `simp`
using the relevant lemmas. One can also use this tactic at the goal using `push_neg`,
at every hypothesis and the goal using `push_neg at *` or at selected hypotheses and the goal
using say `push_neg at h h' ⊢` as usual.

This tactic has two modes: in standard mode, it transforms `¬(p ∧ q)` into `p → ¬q`, whereas in
distrib mode it produces `¬p ∨ ¬q`. To use distrib mode, use `set_option push_neg.use_distrib true`.
-/
elab "push_neg" loc:(location)? : tactic =>
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  withLocation loc
    pushNegLocalDecl
    pushNegTarget
    (fun _ ↦ logInfo "push_neg couldn't find a negation to push")
