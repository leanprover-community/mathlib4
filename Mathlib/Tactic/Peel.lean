/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.Basic

/-!
# The `peel` tactic

`peel h with idents*` tries to apply `forall_imp` (or `Exists.imp`, or `Filter.Eventually.mp`,
`Filter.Frequently.mp` and `Filter.eventually_of_forall`) with the argument `h` and uses `idents*`
to introduce variables with the supplied names.
-/

open Lean Expr Meta Qq Elab Tactic

private lemma and_imp_left_of_imp_imp {p q r : Prop} (h : r → p → q) : r ∧ p → r ∧ q := by tauto

def peelQuantifier (goal : MVarId) (e : Expr) (n : Option Name := none) (n' : Option Name := none) :
    MetaM (List MVarId) := goal.withContext do
  let ty : Q(Prop) ← whnfR (← inferType e)
  let target : Q(Prop) ← whnfR (← goal.getType)
  let freshName ← mkFreshUserName `h_peel
  unless (← isProp ty) && (← isProp target) do
    return [goal]
  match ty, target with
    | .forallE _ t₁ b₁ _, .forallE n₂ t₂ b₂ c => do
      unless ← isDefEq (← whnfR t₁) (← whnfR t₂) do
        return [goal]
      let all_imp ← mkFreshExprMVar <| ← withoutModifyingState <| withLocalDecl n₂ c t₂ fun x => do
        mkForallFVars #[x] (← mkArrow (b₁.instantiate1 x) (b₂.instantiate1 x))
      goal.assign (← mkAppM ``forall_imp #[all_imp, e])
      let (_, new_goal) ← all_imp.mvarId!.introN 2 [n.getD n₂, n'.getD freshName]
      return [new_goal]
    | ~q(∃ x : $α₁, $p x), ~q(∃ x : $α₂, $q x) => do
      unless ← isDefEq (← whnfR α₁) (← whnfR α₂) do
        return [goal]
      let p : Q($α₂ → Prop) := p
      let e : Q(∃ x : $α₂, $p x) := e
      let all_imp : Q(∀ x : $α₂, $p x → $q x) ← mkFreshExprMVar q(∀ x : $α₂, $p x → $q x)
      goal.assign q(Exists.imp $all_imp $e)
      let (_, new_goal) ← all_imp.mvarId!.introN 2 [n.getD `_, n'.getD freshName]
      return [new_goal]
    | ~q($r ∧ $p), ~q($r' ∧ $q) => do
      unless ← isDefEq q($r) q($r') do
        return [goal]
      let and_imp : Q($r' → $p → $q) ← mkFreshExprMVar q($r' → $p → $q)
      let e : Q($r' ∧ $p) := e
      goal.assign q(and_imp_left_of_imp_imp $and_imp $e)
      let (_, new_goal) ← and_imp.mvarId!.introN 2 [n.getD `_, n'.getD freshName]
      return [new_goal]
    | ~q(∀ᶠ (x : $α₁) in $f₁, $p x), ~q(∀ᶠ (x : $α₂) in $f₂, $q x) => do
      unless (← isDefEq (← whnfR α₁) (← whnfR α₂)) && (← isDefEq (← whnfR f₁) (← whnfR f₂)) do
        return [goal]
      let p : Q($α₂ → Prop) := p
      let e : Q(∀ᶠ (x : $α₂) in $f₂, $p x) := e
      let all_imp : Q(∀ x : $α₂, $p x → $q x) ← mkFreshExprMVar q(∀ x : $α₂, $p x → $q x)
      goal.assign q(Filter.Eventually.mp $e (Filter.eventually_of_forall $all_imp))
      let (_, new_goal) ← all_imp.mvarId!.introN 2 [n.getD `_, n'.getD freshName]
      return [new_goal]
    | ~q(∃ᶠ (x : $α₁) in $f₁, $p x), ~q(∃ᶠ (x : $α₂) in $f₂, $q x) => do
      unless (← isDefEq (← whnfR α₁) (← whnfR α₂)) && (← isDefEq (← whnfR f₁) (← whnfR f₂)) do
        return [goal]
      let p : Q($α₂ → Prop) := p
      let e : Q(∃ᶠ (x : $α₂) in $f₂, $p x) := e
      let all_imp : Q(∀ x : $α₂, $p x → $q x) ← mkFreshExprMVar q(∀ x : $α₂, $p x → $q x)
      goal.assign q(Filter.Frequently.mp $e (Filter.eventually_of_forall $all_imp))
      let (_, new_goal) ← all_imp.mvarId!.introN 2 [n.getD `_, n'.getD freshName]
      return [new_goal]
    | _, _ => do
      return [goal]

def peelTacAux (e : TSyntax `term) (n : Option (TSyntax `ident)) (n' : Option (TSyntax `ident)) :
    TacticM Unit := withMainContext do
  let e ← Elab.Term.elabTerm e none
  match n, n' with
    | .some n₁, .some n₂ => liftMetaTactic (peelQuantifier · e (.some n₂.getId) (.some n₁.getId))
    | .none, .some n₂ => liftMetaTactic (peelQuantifier · e (.some n₂.getId))
    | .some n₁, .none => liftMetaTactic (peelQuantifier · e (n' := .some n₁.getId))
    | .none, .none => liftMetaTactic (peelQuantifier · e)


/--
Peels matching quantifiers off of a given term and the goal and introduces the relevant variables.

Given `p q : ℕ → Prop`, `h : ∀ x, p x`, and a goal `⊢ : ∀ x, q x`, the tactic `peel h with h' x`
will introduce `x : ℕ`, `h' : p x` into the context and the new goal will be `⊢ q x`. This works
with `∃`, as well as `∀ᶠ` and `∃ᶠ`, and it can even be applied to a sequence of quantifiers. Note
that this is a logically weaker setup, so using this tactic is not always feasible.

For a more complex example, given a hypothesis and a goal:
```
h : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℝ) < ε
⊢ ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℝ) ≤ ε
```
(which differ only in `<`/`≤`), applying `peel h with h_peel ε hε N n hn` will yield a tactic state:
```
h : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℝ) < ε
ε : ℝ
hε : 0 < ε
N n : ℕ
hn : N ≤ n
h_peel : 1 / (n + 1 : ℝ) < ε
⊢ 1 / (n + 1 : ℝ) ≤ ε
```
and the goal can be closed with `exact h_peel.le`.
Note that in this example, `h` and the goal are logically equivalent statements, but `peel`
*cannot* be immediately applied to show that the goal implies `h`.

`peel` can take an optional numeric argument prior to the supplied hypothesis; in which case it will
autoname the introduced variables, but they may be inaccessible. However, in this case the user must
still introduce a single name such as `with h_peel` for the new hypothesis.

This tactic works by repeatedly applying `forall_imp`, `Exists.imp`, `Filter.Eventually.mp`,
`Filter.Frequently.mp`, and `Filter.eventually_of_forall` and introducing the variables as these
are applied.
-/
syntax (name := peel) "peel" (num)? (ppSpace term) (Mathlib.Tactic.withArgs)? : tactic
@[tactic peel] def peelTac : Tactic := fun stx => do
  match stx with
    | `(tactic| peel $e:term) => peelTacAux e .none .none
    | `(tactic| peel $e:term with $n₁:ident) => peelTacAux e (.some n₁) .none
    | `(tactic| peel $e:term with $n₁:ident $n₂:ident) => peelTacAux e (.some n₁) (.some n₂)
    | `(tactic| peel $e:term with $n₁:ident $n₂:ident $n₃:ident*) =>
        evalTactic (← `(tactic| peel $e:term with $n₁ $n₂; have h' := $n₁; clear $n₁;
          peel h' with $n₁ $n₃:ident*; clear h'))
    | `(tactic| peel $n:num $e:term with $h₁:ident) =>
      match n.getNat with
        | 0 => pure ()
        | 1 => evalTactic (← `(tactic| peel $e:term with $h₁))
        | k + 2 =>
          let j := Syntax.mkNumLit <| toString (k + 1)
          evalTactic (← `(tactic| peel $e:term with $h₁; have h' := $h₁; clear $h₁;
            peel $j h' with $h₁; clear h'))
    | _ => Elab.throwUnsupportedSyntax
