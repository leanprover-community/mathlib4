/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Mario Carneiro
-/
import Qq.MetaM
import Mathlib.Logic.Nontrivial
import Mathlib.Tactic.SolveByElim

/-! # The `nontriviality` tactic. -/

namespace Mathlib.Tactic.Nontriviality
open Lean Elab Meta Tactic Linter Std.Linter UnreachableTactic Qq

register_simp_attr nontriviality

def nontrivialityByAssumption (g : MVarId) : MetaM Unit := do
  g.inferInstance <|> do
    let lems ← [``nontrivial_of_ne, ``nontrivial_of_lt].mapM mkConstWithFreshMVarLevels
    solveByElimImpl false lems 6 g

theorem subsingleton_or_nontrivial_elim {p : Prop} {α : Type u}
    (h₁ : Subsingleton α → p) (h₂ : Nontrivial α → p) : p :=
  (subsingleton_or_nontrivial α).elim @h₁ @h₂

def nontrivialityByElim (α : Q(Type u)) (g : MVarId) (simpArgs : Array Syntax) : MetaM MVarId := do
  let p : Q(Prop) ← g.getType
  guard (← inferType p).isProp
  let g₁ ← mkFreshExprMVarQ q(Subsingleton $α → $p)
  let (_, g₁') ← g₁.mvarId!.intro1
  g₁'.withContext try
    g₁'.inferInstance <|> do
      let simpArgs := simpArgs.push (Unhygienic.run `(Parser.Tactic.simpLemma| nontriviality))
      let stx := open TSyntax.Compat in Unhygienic.run `(tactic| simp [$simpArgs,*])
      let ([], _) ← runTactic g₁' stx | failure
  catch _ => throwError
    "Could not prove goal assuming `{q(Subsingleton $α)}`\n{MessageData.ofGoal g₁'}"
  let g₂ : Q(Nontrivial $α → $p) ← mkFreshExprMVarQ q(Nontrivial $α → $p)
  g.assign q(@subsingleton_or_nontrivial_elim $p $α $g₁ $g₂)
  pure g₂.mvarId!

/-- Attempts to generate a `Nontrivial α` hypothesis.

The tactic first looks for an instance using `infer_instance`.

If the goal is an (in)equality, the type `α` is inferred from the goal.
Otherwise, the type needs to be specified in the tactic invocation, as `nontriviality α`.

The `nontriviality` tactic will first look for strict inequalities amongst the hypotheses,
and use these to derive the `Nontrivial` instance directly.

Otherwise, it will perform a case split on `Subsingleton α ∨ Nontrivial α`, and attempt to discharge
the `Subsingleton` goal using `simp [lemmas, nontriviality]`, where `[lemmas]` is a list of
additional `simp` lemmas that can be passed to `nontriviality` using the syntax
`nontriviality α using [lemmas]`.

```
example {R : Type} [OrderedRing R] {a : R} (h : 0 < a) : 0 < a := by
  nontriviality -- There is now a `nontrivial R` hypothesis available.
  assumption
```

```
example {R : Type} [CommRing R] {r s : R} : r * s = s * r := by
  nontriviality -- There is now a `nontrivial R` hypothesis available.
  apply mul_comm
```

```
example {R : Type} [OrderedRing R] {a : R} (h : 0 < a) : (2 : ℕ) ∣ 4 := by
  nontriviality R -- there is now a `nontrivial R` hypothesis available.
  dec_trivial
```

```
def myeq {α : Type} (a b : α) : Prop := a = b

example {α : Type} (a b : α) (h : a = b) : myeq a b := by
  success_if_fail nontriviality α -- Fails
  nontriviality α using [myeq] -- There is now a `nontrivial α` hypothesis available
  assumption
```
-/
syntax (name := nontriviality) "nontriviality" (ppSpace (colGt term))?
  (" using " Parser.Tactic.simpArg,+)? : tactic

@[tactic nontriviality] def elabNontriviality : Tactic := fun stx => do
    let g ← getMainGoal
    let α ← match stx[1].getOptional? with
    | some e => Term.elabType e
    | none => (do
      let mut tgt ← withReducible g.getType'
      if let some tgt' := tgt.not? then tgt ← withReducible (whnf tgt')
      if let some (α, _) := tgt.eq? then return α
      if let some (α, _) := tgt.app4? ``LE.le then return α
      if let some (α, _) := tgt.app4? ``LT.lt then return α
      throwError "The goal is not an (in)equality, so you'll need to specify the desired {""
        }`Nontrivial α` instance by invoking `nontriviality α`.")
    let .sort (.succ u) ← whnf (← inferType α) | throwError "not a type{indentExpr α}"
    let α : Q(Type u) := α
    let tac := do
      let ty := q(Nontrivial $α)
      let m ← mkFreshExprMVar (some ty)
      nontrivialityByAssumption m.mvarId!
      g.assert `inst ty m
    let g ← liftM <| tac <|> nontrivialityByElim α g stx[2][1].getSepArgs
    replaceMainGoal [(← g.intro1).2]
