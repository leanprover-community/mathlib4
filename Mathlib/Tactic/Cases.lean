/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public meta import Lean.Elab.Tactic.Induction
public meta import Batteries.Data.List.Basic
public meta import Batteries.Lean.Expr
import all Lean.Elab.Tactic.Induction
public import Mathlib.Init

/-!
# Backward compatible implementation of lean 3 `cases` tactic

This tactic is similar to the `cases` tactic in Lean 4 core, but the syntax for giving
names is different:

```
example (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

example (h : p ∨ q) : q ∨ p := by
  cases' h with hp hq
  · exact Or.inr hp
  · exact Or.inl hq

example (h : p ∨ q) : q ∨ p := by
  rcases h with hp | hq
  · exact Or.inr hp
  · exact Or.inl hq
```

Prefer `cases` or `rcases` when possible, because these tactics promote structured proofs.
-/

public meta section

namespace Mathlib.Tactic
open Lean Meta Elab Elab.Tactic

private def getAltNumFields (elimInfo : ElimInfo) (altName : Name) : TermElabM Nat := do
  for altInfo in elimInfo.altsInfo do
    if altInfo.name == altName then
      return altInfo.numFields
  throwError "unknown alternative name '{altName}'"

def ElimApp.evalNames (elimInfo : ElimInfo) (alts : Array ElimApp.Alt) (withArg : Syntax)
    (numEqs := 0) (generalized : Array FVarId := #[]) (toClear : Array FVarId := #[])
    (toTag : Array (Ident × FVarId) := #[]) :
    TermElabM (Array MVarId) := do
  let mut names : List Syntax := withArg[1].getArgs |>.toList
  let mut subgoals := #[]
  for { name := altName, mvarId := g, .. } in alts do
    let numFields ← getAltNumFields elimInfo altName
    let (altVarNames, names') := names.splitAtD numFields (Unhygienic.run `(_))
    names := names'
    let (fvars, g) ← g.introN numFields <| altVarNames.map (getNameOfIdent' ·[0])
    let some (g, subst) ← Cases.unifyEqs? numEqs g {} | pure ()
    let (introduced, g) ← g.introNP generalized.size
    let subst := (generalized.zip introduced).foldl (init := subst) fun subst (a, b) =>
      subst.insert a (.fvar b)
    let g ← liftM <| toClear.foldlM (·.tryClear) g
    g.withContext do
      for (stx, fvar) in toTag do
        Term.addLocalVarInfo stx (subst.get fvar)
      for fvar in fvars, stx in altVarNames do
        (subst.get fvar).addLocalVarInfoForBinderIdent ⟨stx⟩
    subgoals := subgoals.push g
  pure subgoals

/-- `induction' x` applies induction on the variable `x` of the inductive type `t` to the main goal,
producing one goal for each constructor of `t`, in which `x` is replaced by that constructor
applied to newly introduced variables. `induction'` adds an inductive hypothesis for
each recursive argument to the constructor. This is a backwards-compatible variant of the
`induction` tactic in Lean 4 core.

Prefer `induction` when possible, because it promotes structured proofs.

* `induction' x with n1 n2 ...` names the introduced hypotheses: arguments to constructors and
  inductive hypotheses. This is the main difference with `induction` in core Lean.
* `induction' e`, where `e` is an expression instead of a variable, generalizes `e` in the goal,
  and then performs induction on the resulting variable.
* `induction' h : e`, where `e` is an expression instead of a variable, generalizes `e` in the goal,
  and then performs induction on the resulting variable, adding to each goal the hypothesis
  `h : e = _` where `_` is the constructor instance.
* `induction' x using r` uses `r` as the principle of induction. Here `r` should be a term whose
  result type is of the form `C t1 t2 ...`, where `C` is a bound variable and `t1`, `t2`, ... (if
  present) are bound variables.
* `induction' x generalizing z1 z2 ...` generalizes over the local variables `z1`, `z2`, ... in the
  inductive hypothesis.

Example:
```
open Nat

example (n : ℕ) : 0 < factorial n := by
  induction' n with n ih
  · rw [factorial_zero]
    simp
  · rw [factorial_succ]
    apply mul_pos (succ_pos n) ih

-- Though the following equivalent spellings should be preferred
example (n : ℕ) : 0 < factorial n := by
  induction n
  case zero =>
    rw [factorial_zero]
    simp
  case succ n ih =>
    rw [factorial_succ]
    apply mul_pos (succ_pos n) ih
```
-/
elab (name := induction') "induction' " tgts:(Parser.Tactic.elimTarget,+)
    usingArg:((" using " ident)?)
    withArg:((" with" (ppSpace colGt binderIdent)+)?)
    genArg:((" generalizing" (ppSpace colGt ident)+)?) : tactic => do
  let (targets, toTag) ← elabElimTargets tgts.1.getSepArgs
  let g :: gs ← getUnsolvedGoals | throwNoGoalsToBeSolved
  g.withContext do
    let elimInfo ← getElimNameInfo usingArg targets (induction := true)
    let targets ← addImplicitTargets elimInfo targets
    checkInductionTargets targets
    let targetFVarIds := targets.map (·.fvarId!)
    g.withContext do
      let genArgs ← if genArg.1.isNone then pure #[] else getFVarIds genArg.1[1].getArgs
      let forbidden ← mkGeneralizationForbiddenSet targets
      let mut s ← getFVarSetToGeneralize targets forbidden
      for v in genArgs do
        if forbidden.contains v then
          throwError "variable cannot be generalized \
            because target depends on it{indentExpr (mkFVar v)}"
        if s.contains v then
          throwError "unnecessary 'generalizing' argument, \
            variable '{mkFVar v}' is generalized automatically"
        s := s.insert v
      let (fvarIds, g) ← g.revert (← sortFVarIds s.toArray)
      g.withContext do
        let result ← withRef tgts <| ElimApp.mkElimApp elimInfo targets (← g.getTag)
        let elimArgs := result.elimApp.getAppArgs
        ElimApp.setMotiveArg g elimArgs[elimInfo.motivePos]!.mvarId! targetFVarIds
        g.assign result.elimApp
        let subgoals ← ElimApp.evalNames elimInfo result.alts withArg
          (generalized := fvarIds) (toClear := targetFVarIds) (toTag := toTag)
        setGoals <| (subgoals ++ result.others).toList ++ gs

/-- `cases' x`, where the variable `x` has inductive type `t`, splits the main goal,
producing one goal for each constructor of `t`, in which `x` is replaced by that constructor
applied to newly introduced variables. This is a backwards-compatible variant of the
`cases` tactic in Lean 4 core.

Prefer `cases`, `rcases`, or `obtain` when possible, because these tactics promote
structured proofs.

* `cases' x with n1 n2 ...` names the arguments to the constructors. This is the main difference
  with `cases` in core Lean.
* `cases' e`, where `e` is an expression instead of a variable, generalizes `e` in the goal,
  and then performs induction on the resulting variable.
* `cases' h : e`, where `e` is an expression instead of a variable, generalizes `e` in the goal,
  and then splits by cases on the resulting variable, adding to each goal the hypothesis
  `h : e = _` where `_` is the constructor instance.
* `cases' x using r` uses `r` as the case matching rule. Here `r` should be a term whose result type
  is of the form `C t1 t2 ...`, where `C` is a bound variable and `t1`, `t2`, ... (if present) are
  bound variables.

Example:
```
example (h : p ∨ q) : q ∨ p := by
  cases' h with hp hq
  · exact Or.inr hp
  · exact Or.inl hq

-- Though the following equivalent spellings should be preferred
example (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

example (h : p ∨ q) : q ∨ p := by
  rcases h with hp | hq
  · exact Or.inr hp
  · exact Or.inl hq
```
-/
elab (name := cases') "cases' " tgts:(Parser.Tactic.elimTarget,+) usingArg:((" using " ident)?)
  withArg:((" with" (ppSpace colGt binderIdent)+)?) : tactic => do
  let (targets, toTag) ← elabElimTargets tgts.1.getSepArgs
  let g :: gs ← getUnsolvedGoals | throwNoGoalsToBeSolved
  g.withContext do
    let elimInfo ← getElimNameInfo usingArg targets (induction := false)
    let targets ← addImplicitTargets elimInfo targets
    let result ← withRef tgts <| ElimApp.mkElimApp elimInfo targets (← g.getTag)
    let elimArgs := result.elimApp.getAppArgs
    let targets ← elimInfo.targetsPos.mapM (instantiateMVars elimArgs[·]!)
    let motive := elimArgs[elimInfo.motivePos]!
    let g ← generalizeTargetsEq g (← inferType motive) targets
    let (targetsNew, g) ← g.introN targets.size
    g.withContext do
      ElimApp.setMotiveArg g motive.mvarId! targetsNew
      g.assign result.elimApp
      let subgoals ← ElimApp.evalNames elimInfo result.alts withArg
         (numEqs := targets.size) (toClear := targetsNew) (toTag := toTag)
      setGoals <| subgoals.toList ++ gs

end Mathlib.Tactic
