/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.GCongr.Core
import Mathlib.Control.Basic
import Qq

/-! # Tactic for isolating a subexpression within a given relation -/

namespace Mathlib.Tactic.Isolate
open Lean Meta Qq


initialize registerTraceClass `Meta.isolate

/-- Environment extension for "isolation" (`isolate`) lemmas. -/
initialize isolateExt : SimpleScopedEnvExtension ((Name × Name × Nat × Bool) × Name)
    (Std.HashMap (Name × Name × Nat × Bool) (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (n, lem) => m.insert n ((m.getD n #[]).push lem)
    initial := {}
  }

/-- Parse a lemma to see whether it has the correct form for a "isolation" (`isolate`) lemma. Such
lemmas must have a conclusion of the form `f a₁ a₂ ... x ... aₖ ~ y ↔ x ~' G`; that is,
* an if-and-only-if statement;
* between two relations `~` and `~'`;
* with a free variable `y` on one side of the relation `~` and a free variable `x` on one side of
  the relation `~'`
* and with a function application as the other side of the relation `~`, with `x` appearing exactly
  once among the arguments to that function.

Such a lemma will be used to isolate a term appearing in the `x` position in a relation like
`f a₁ a₂ ... x ... aₖ ~ y`, converting it to a logically equivalent relation `x ~' G` with the `x`
"isolated".

It is permissible for there to be any number of antecedents to such a lemma; they will generate
"side goals" when the `isolate` tactic is used.

If the given declaration is a valid `@[isolate]` lemma, we return the relation `~'` and function `f`
identified in the key hypothesis, together with the index of the `x` free-variable argument in the
function `f`, and a boolean recording whether `f` occurs on the RHS (`true`) or LHS (`false`) of the
relation `~`. -/
def parseIsolateLemma (decl : Name) : MetaM (Name × Name × Nat × Bool) := do
  let declTy := (← getConstInfo decl).type
  withReducible <| forallTelescopeReducing declTy fun _ targetTy => do
  let failTarget (m : MessageData) : MessageData :=
    m!"@[isolate] attribute only applies to lemmas proving f x ∼ y ↔ x ∼' g y.\n \
    {m} in the conclusion {targetTy}"
  -- verify that conclusion of the lemma is of the form `P ↔ Q`
  let some (lhs, rhs) := (← whnfR targetTy).iff? |
    throwError (failTarget m!"No relation with at least two arguments found")
  -- verify that `P` and `Q` are both relations
  let .app (.app lhsRel lhsA) lhsB := (← whnfR lhs) | throwError (failTarget m!"")
  let .app (.app _ rhsA) rhsB := (← whnfR rhs) | throwError (failTarget m!"")
  let lhsA := lhsA.eta
  let lhsB := lhsB.eta
  let rhsA := rhsA.eta
  let rhsB := rhsB.eta
  -- verify that one side of each of `~` and `~'` is a free variable
  unless lhsA.isFVar || lhsB.isFVar do
    throwError (failTarget m!"")
  unless rhsA.isFVar || rhsB.isFVar do
    throwError (failTarget m!"")
  let lhsSymm := !lhsB.isFVar
  let lhsApp := if lhsSymm then lhsB else lhsA
  let rhsFVar := if !rhsA.isFVar then rhsB.fvarId! else rhsA.fvarId!
  -- verify that the "P", i.e. the LHS of the iff, is of the form `f x₁ ... xₙ ∼ y`
  let some relName := lhsRel.getAppFn.constName? |
    throwError (failTarget m!"No relation found")
  let (lhsHead₀, lhsAppArgs) := lhsApp.withApp fun e a => (e, a)
  let some lhsHead := lhsHead₀.constName? |
    throwError (failTarget m!"Leading LHS function {lhsHead₀} is not a constant")
  let lhsAppContains := lhsAppArgs.map (Expr.containsFVar · rhsFVar)
  -- supposed to be only one argument depending on the "x"
  guard ((lhsAppContains.filter id).size == 1)
  let some i := lhsAppContains.findIdx? id | throwError "dfs"
  guard (lhsAppArgs[i]!).isFVar
  trace[debug] "adding {relName}, {lhsHead}, {i}"
  return (relName, lhsHead, i, lhsSymm)

/-- Attribute marking "isolation" (`isolate`) lemmas.  Such lemmas must have a conclusion of the
form `f a₁ a₂ ... x ... aₖ ~ y ↔ x ~' G`; that is,
* an if-and-only-if statement;
* between two relations `~` and `~'`;
* with a free variable `y` on one side of the relation `~` and a free variable `x` on one side of
  the relation `~'`
* and with a function application as the other side of the relation `~`, with `x` appearing exactly
  once among the arguments to that function.

The antecedents of such a lemma are considered to generate "side goals". -/
initialize registerBuiltinAttribute {
  name := `isolate
  descr := "isolation"
  add decl _ kind := do
    -- parse the proposed isolation lemma to find the the relation `~'` and function `f`
    -- identified in the key hypothesis, together with the index of the designated free variable
    -- in the argument list of `f`, and a boolean specifying which side of the relation `f` is on.
    let key : Name × Name × Nat × Bool ← MetaM.run' (parseIsolateLemma decl)
    trace[Meta.isolate] "Recorded as a isolation lemma for {key}"
    -- store this lemma in the environment extension for isolation lemmas, with the relation,
    -- function, argument index and "side" boolean jointly serving as the lookup key for this lemma.
    isolateExt.add (key, decl) kind
}

/-- This command lets the user check on the current state of the environment extension storing the
`@[isolate]` lemmas.

Example: To see whether there are any lemmas tagged `@[isolate]` whose key hypothesis has the form
`a + x < y` (i.e. `HAdd.hAdd _ _ _ a x < y`), use the following command
syntax:
```
#query_isolate_lemmas `LT.lt `HAdd.hAdd 5 0
```
-/
elab "#query_isolate_lemmas" e0:(ppSpace colGt name)? e1:(ppSpace colGt name)?
    e2:(ppSpace colGt num)? e3:(ppSpace colGt num)? : command => do
  let (some e0, some e1, some e2, some e3) := (e0, e1, e2, e3) |
    logInfo "Please provide the relation, function and index for the isolation hypothesis type \
      you are interested in"
  let rel : Name := TSyntax.getName e0
  let f : Name := TSyntax.getName e1
  let i : Nat := TSyntax.getNat e2
  let b : Bool := ← do
    match TSyntax.getNat e3 with
    | 0  => pure false
    | 1 => pure true
    | _ => throwError "argument {e3} should be a boolean"
  match (isolateExt.getState (← getEnv))[(rel, f, i, b)]? with
  | some lems => logInfo m!"{lems}"
  | none => logInfo "No lemmas with this key found"

open Qq

def isolateStep (x : Expr) (P : Expr) : MetaM (List MVarId × Simp.Result) := do
  let .app (.app rel lhs) rhs ← whnfR P | throwError "{P} should be a relation"
  let lhs' ← Meta.kabstract lhs x
  let rhs' ← Meta.kabstract rhs x
  let lhsContains := lhs'.hasLooseBVar 0
  let rhsContains := rhs'.hasLooseBVar 0
  if (lhsContains && rhsContains) then
    throwError "{x} should appear in only one (not both) of {lhs} and {rhs}"
  if !(lhsContains || rhsContains) then
    throwError "{x} should appear in either {lhs} or {rhs}"
  let xExpr := if lhsContains then lhs else rhs
  let xExpr' := if lhsContains then lhs' else rhs'
  let some relName := rel.getAppFn.constName? | throwError "{rel} is not an explicit relation"
  let (xApp, xArgs) := xExpr'.withApp fun e a => (e, a)
  let some xAppName := xApp.getAppFn.constName? | throwError "{xApp} is not an explicit function"
  guard !(xApp.hasLooseBVar 0) <|> throwError "{x} is not localized to a single argument of {xExpr}"
  let xArg' := xArgs.filter fun arg ↦ arg.hasLooseBVar 0
  match xArg' with
  | #[xArg] =>
    let key := (relName, xAppName, xArgs.findIdx (· == xArg), !lhsContains)
    let env := isolateExt.getState (← getEnv)
    let lemmas := env.getD key #[]
    let s ← saveState
    for lem in lemmas do
      try
        let e ← mkConstWithFreshMVarLevels lem
        let eTy ← inferType e
        let (args, _, ty) ← forallMetaTelescopeReducing eTy
        let .app (.app _ lemLHS) lemRHS := ty | throwError "ill-formed @[isolate] lemma {lem}"
        guard (← isDefEq P lemLHS)
        let Q : Q(Prop) := ← instantiateMVars lemRHS
        let mvars := (← args.mapM getMVars).flatten
        let mut mvars' : Array MVarId := #[]
        for mvar in mvars do
          try
            GCongr.gcongrDischarger mvar
          catch _ => try
            mvar.inferInstance
          catch _ =>
            mvars' := mvars'.push mvar
        let z ← mkAppOptM lem (args.map some)
        let pf ← mkAppM ``propext #[z]
        return (mvars'.toList, { expr := Q, proof? := some pf })
      catch _ => s.restore
    throwError "no suitable lemmas found"
  | _ => throwError "{x} is not localized to a single 'argument of {xExpr}"

partial def isolateStepRec (x : Expr) (P : Expr) : MetaM (List MVarId × Simp.Result) := do
  let (mvars, r) ← isolateStep x P
  try
    let (mvars', r') ← isolateStepRec x r.expr
    return (mvars ++ mvars', ← r.mkEqTrans r')
  catch _ =>
    return (mvars, r)

def isolateStepHyp (x : Expr) (fvar : FVarId) (g : MVarId) : MetaM (List MVarId) := do
  let P ← fvar.getType
  let ⟨mvars, r⟩ ← isolateStepRec x P
  let some (_, newGoal) ← applySimpResultToLocalDecl g fvar r false | throwError "zz"
  pure (newGoal :: mvars)

def isolateStepTarget (x : Expr) (g : MVarId) : MetaM (List MVarId) := do
  let P ← g.getType
  let ⟨mvars, r⟩ ← isolateStepRec x P
  let mainGoal ← applySimpResultToTarget g P r
  pure (mainGoal :: mvars)

open Parser Tactic in
elab "isolate" x:term loc:(location)? : tactic => do
  let x ← Elab.Tactic.elabTerm x none
  let loc := (loc.map Elab.Tactic.expandLocation).getD (.targets #[] true)
  Elab.Tactic.withLocation loc
    (fun fvar ↦ Elab.Tactic.liftMetaTactic <| isolateStepHyp x fvar)
    (Elab.Tactic.liftMetaTactic <| isolateStepTarget x)
    fun _ ↦ throwError m!"No {x} term was found anywhere to isolate"

end Mathlib.Tactic.Isolate
