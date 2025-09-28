/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.GCongr.Core
import Mathlib.Tactic.Relation.Symm

/-! # Tactic for isolating a subexpression within a given relation

The `isolate` tactic "solves for x" in an equation or relation. For example:
```
example (a b : ℝ) (f : ℝ → ℝ) : 5 * f a - 3 < b := by
  isolate f a
  -- new goal: `⊢ f a < (b + 3) / 5`
```

This is done by maintaining an environment extension `Mathlib.Tactic.Isolate.isolateExt`, containing
lemmas (tagged `@[isolate]`) whose conclusion is of the form `f a₁ a₂ ... x ... aₖ ~ y ↔ x ~' G` for
some relations `~` and `~'`, some free variables `x` and `y`, and some operation `f`. When presented
with a relational hypothesis or goal, `isolate e` recursively rewrites by `@[isolate]` lemmas to
make `e` less deeply nested.

This transformation may generate side goals, as needed by the `@[isolate]` lemmas being invoked.
The `isolate` tactic will attempt to justify such side goals using the `gcongr` discharger
(currently a wrapper for `positivity`) (as in the above example), unification, or type class
inference, but if unsuccessful will present the side goal to the user. For example:
```
example (a b c : ℝ) (f : ℝ → ℝ) : c * f a - 3 < b := by
  isolate f a
  -- new goal: `⊢ f a < (b + 3) / c`
  -- second (side) new goal: `⊢ 0 < c`
```
-/

namespace Mathlib.Tactic.Isolate
open Lean Meta

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
* and with a function application on one side of the relation `~` (the other side from `y`), with
  `x` appearing exactly once among the arguments to that function.

Such a lemma will be used to isolate a term appearing in the `x` position in a relation like
`f a₁ a₂ ... x ... aₖ ~ y`, converting it to a logically equivalent relation `x ~' G` with the `x`
"isolated".

It is permissible for there to be any number of antecedents to such a lemma. If not solved by
unification or the discharger, they will generate "side goals" when the `isolate` tactic is used.

If the given declaration is a valid `@[isolate]` lemma, we return the relation `~'` and function `f`
identified in the key hypothesis, together with the index of the `x` free-variable argument in the
function `f`, and a boolean recording whether `f` occurs on the RHS (`true`) or LHS (`false`) of the
relation `~`. -/
def parseIsolateLemma (decl : Name) : MetaM (Name × Name × Nat × Bool) := do
  let declTy := (← getConstInfo decl).type
  withReducible <| forallTelescopeReducing declTy fun _ targetTy => do
  let failTarget (m : MessageData) : MessageData :=
    m!"@[isolate] attribute only applies to lemmas with a conclusion of the form \
      f a₁ a₂ ... x ... aₖ ~ y ↔ x ~' G.\n {m}"
  -- verify that conclusion of the lemma is of the form `P ↔ Q`
  let some (lhs, rhs) := (← whnfR targetTy).iff? |
    throwError
      (failTarget m!"If-and-only-if structure not identified in this lemma's conclusion {targetTy}")
  let failLHS (m : MessageData) : MessageData :=
    failTarget m!"Here the conclusion has the form {lhs} ↔ _, but {m}"
  let failRHS (m : MessageData) : MessageData :=
    failTarget m!"Here the conclusion has the form _ ↔ {rhs}, but {m}"
  -- verify that `P` and `Q` are both relations
  let .app (.app lhsRel lhsA) lhsB := (← whnfR lhs) |
    throwError (failLHS m!"{lhs} could not be parsed as a relation")
  let some relName := lhsRel.getAppFn.constName? |
    throwError "{lhsRel} should be a concrete relation, for example it cannot be a variable"
  let .app (.app _ rhsA) rhsB := (← whnfR rhs) |
    throwError (failLHS m!"{rhs} could not be parsed as a relation")
  let lhsA := lhsA.eta
  let lhsB := lhsB.eta
  let rhsA := rhsA.eta
  let rhsB := rhsB.eta
  -- verify that one side of each of `~` and `~'` is a free variable
  unless lhsA.isFVar || lhsB.isFVar do
    throwError (failLHS m!"one side of {lhs} should be a free variable")
  unless rhsA.isFVar || rhsB.isFVar do
    throwError (failRHS m!"one side of {rhs} should be a free variable")
  let symmLems ← (Symm.symmExt.getState (← getEnv)).getMatch lhsRel
  if !symmLems.isEmpty && !lhsB.isFVar then
    throwError "Please rephrase this lemma in the symmetric form {lhsB} ~ {lhsA} ↔ _."
  let lhsSymm := !lhsB.isFVar
  let e := if lhsSymm then lhsB else lhsA
  let x := if !rhsA.isFVar then rhsB else rhsA
  -- verify that the "P", i.e. the LHS of the iff, is of the form `f x₁ ... xₙ ∼ y`
  let (eFn, eArgs) := e.withApp fun e a => (e, a)
  let some eFnName := eFn.constName? |
    throwError "{eFn} should be a concrete function, for example it cannot be a variable"
  let eArgsContain? := eArgs.map (Expr.containsFVar · x.fvarId!)
  -- supposed to be only one argument depending on the "x"
  match (eArgsContain?.filter id).size with
  | 0 => throwError (failLHS m!"the expression {e} should contain {x}")
  | 1 =>
    let some i := eArgsContain?.findIdx? id | throwError "Internal error in 'isolate' parsing"
    guard (eArgs[i]!).isFVar <|>
      throwError (failLHS m!"the variable {x} should appear as directly as an argument of the \
        operation {eFn}")
    return (relName, eFnName, i, lhsSymm)
  | _ =>
    throwError (failLHS m!"the variable {x} should appear only once in the expression {e}")

/-- Attribute marking "isolation" (`isolate`) lemmas. Candidate lemmas are parsed using the function
`Mathlib.Tactic.Isolate.parseIsolateLemma`. If successful, we obtain a key, comprising
* the relation `~'` and function `f` identified in the key hypothesis;
* the index of the `x` free-variable argument in the function `f`;
* a boolean recording whether `f` occurs on the RHS (`true`) or LHS (`false`) of the relation `~`.

The lemma is then added to the environment extension `Mathlib.Tactic.Isolate.isolateExt`, stored
under this key. -/
initialize registerBuiltinAttribute {
  name := `isolate
  descr := "isolation"
  add decl _ kind := do
    -- parse the proposed isolation lemma to find the relation `~'` and function `f` identified in
    -- the key hypothesis, together with the index of the designated free variable in the argument
    -- list of `f`, and a boolean specifying which side of the relation `f` is on.
    let key : Name × Name × Nat × Bool ← MetaM.run' (parseIsolateLemma decl)
    trace[Meta.isolate] "Recorded as a isolation lemma for {key}"
    -- store this lemma in the environment extension for isolation lemmas, with the relation,
    -- function, argument index and "side" boolean jointly serving as the lookup key for this lemma.
    isolateExt.add (key, decl) kind
}

/-- This command lets the user check on the current state of the environment extension storing the
`@[isolate]` lemmas.

Example: To see whether there are any lemmas tagged `@[isolate]` whose conclusion is an
if-and-only-if from `a + x < y` (i.e. `HAdd.hAdd _ _ _ a x < y`), use the following command syntax:
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
    -- TODO figure out how to parse boolean as "false"/"true", not 0/1
    match TSyntax.getNat e3 with
    | 0  => pure false
    | 1 => pure true
    | _ => throwError "argument {e3} should be a boolean"
  match (isolateExt.getState (← getEnv))[(rel, f, i, b)]? with
  | some lems => logInfo m!"{lems}"
  | none => logInfo "No lemmas with this key found"

/-- Modify the expression `P`, which must be of the form `A ~ B`, by finding the expression `x` as a
subexpression of either `A` or `B` (but not both), and finding an applicable `@[isolate]` lemma to
rewrite by, which makes `x` less deeply nested.

Return the list of side goals generated by the `@[isolate]` lemma used (and which are not discharged
by unification, type class inference, or the standard discharger), together with a `Simp.Result`
(containing the new expression and a proof of its logical equivalence to `P`). -/
def isolateStep (x : Expr) (P : Expr) : MetaM (List MVarId × Simp.Result) := do
  trace[Meta.isolate] "isolating {x} in the expression {P}"
  -- parse `P` as `lhs ~ rhs`, where `~` stands for `rel`
  let .app (.app rel lhs) rhs ← whnfR P | throwError "{P} should be a relation"
  -- check whether `x` appears in `lhs` and `rhs`; it should appear in one but not both
  let lhs' ← Meta.kabstract lhs x
  let rhs' ← Meta.kabstract rhs x
  let lhsContains := lhs'.hasLooseBVar 0
  let rhsContains := rhs'.hasLooseBVar 0
  if (lhsContains && rhsContains) then
    throwError "{x} should appear in only one (not both) of {lhs} and {rhs}"
  if !(lhsContains || rhsContains) then
    throwError "{x} should appear in either {lhs} or {rhs}"
  -- Check whether the relation `rel` is symmetric. If so, WLOG we may assume that `x` appears on
  -- the LHS rather than the RHS. This halves the number of `@[isolate]` lemmas needed for such
  -- relations.
  let symmetric? := !(← (Symm.symmExt.getState (← getEnv)).getMatch rel).isEmpty
  let symmResult ← do if symmetric? && !lhsContains then Expr.eqSymm P else pure { expr := P }
  let P' := symmResult.expr
  -- note the name of the relation
  let some relName := rel.getAppFn.constName? |
    throwError "{rel} should be a concrete relation, for example it cannot be a variable"
  -- Letting `e` denote either `lhs` or `rhs` (whichever one contains `x`), we parse it as an
  -- application of a function `fn` to an array `args` of arguments. We also identify `idx`, the
  -- index in `args` for the argument of `fn` which contains `x` (we require that there be only one
  -- such argument).
  let e := if lhsContains then lhs else rhs
  let e' := if lhsContains then lhs' else rhs'
  let (fn, args) := e'.withApp fun e a => (e, a)
  if args.size == 0 then throwError "{x} is already isolated in {P}"
  let some fnName := fn.getAppFn.constName? |
    throwError "{fn} should be a concrete function, for example it cannot be a variable"
  guard !(fn.hasLooseBVar 0) <|> throwError "{x} is not localized to a single argument of {e}"
  let xArgArray := args.filter fun arg ↦ arg.hasLooseBVar 0
  match xArgArray with
  | #[xArg] =>
    let idx := args.findIdx (· == xArg)
    -- Look up the `@[isolate]` lemmas with the right relation, function, argument index and
    -- LHS/RHS positioning.
    let key := (relName, fnName, idx, !symmetric? && !lhsContains)
    let isolateDict := isolateExt.getState (← getEnv)
    let lemmas := isolateDict.getD key #[]
    let s ← saveState
    -- Loop over the lemmas to see if any apply:
    for lem in lemmas do
      try
        trace[Meta.isolate] "trying the lemma {lem} to rewrite the expression {P'}"
        -- An `@[isolate]` lemma has the structure `_ → _ → ... → _ → (lemLHS ↔ lemRHS)`; parse this
        let e ← mkConstWithFreshMVarLevels lem
        let eTy ← inferType e
        let (args, _, ty) ← forallMetaTelescopeReducing eTy
        let .app (.app _ lemLHS) lemRHS := ty | throwError "ill-formed @[isolate] lemma {lem}"
        -- Attempt to unify `lemLHS` with the expression `P'` being worked on.
        guard (← isDefEq P' lemLHS)
        -- If that succeeded, we know what `P'` will be transformed to, namely the instantiated RHS
        -- of the lemma.
        let Q ← instantiateMVars lemRHS
        -- Collect the unassigned metavariables, i.e. side goals.
        let mvars := (← args.mapM getMVars).flatten
        -- We attempt to resolve each of these side goals;
        -- we collect those side goals which are not resolved.
        let mut unresolvedMVars : Array MVarId := #[]
        for mvar in mvars do
          try
            -- attempt to solve the side goal by typeclass inference
            mvar.inferInstance
          catch _ => try
            -- attempt to solve the side goal using `gcongr`'s discharger (currently this is a
            -- wrapper for `positivity`)
            GCongr.gcongrDischarger mvar
          catch _ =>
            unresolvedMVars := unresolvedMVars.push mvar
        -- Make the proof of `P' ↔ Q` (dependent on these side goals) and send it back.
        let pf ← mkAppM ``propext #[← mkAppOptM lem (args.map some)]
        return (unresolvedMVars.toList, ← symmResult.mkEqTrans { expr := Q, proof? := some pf })
      catch _ => s.restore
    throwError "no suitable lemmas found"
  | _ => throwError "{x} is not localized to a single argument of {e}"

/-- Recursively modify the expression `P`, which must be of the form `A ~ B`, by finding the
expression `x` as a subexpression of either `A` or `B` (but not both), and rewriting by `@[isolate]`
lemmas to make `x` less deeply nested.

Return the list of side goals generated by the `@[isolate]` lemmas used (and which are not
discharged by unification, type class inference, or the standard discharger), together with a
`Simp.Result` (containing the new expression and a proof of its logical equivalence to `P`). -/
partial def isolate (x : Expr) (P : Expr) : MetaM (List MVarId × Simp.Result) := do
  -- we run `isolateStep` once before recursing, so that it will fail and produce a useful error
  -- message if no progress is made
  let (mvars, r) ← isolateStep x P
  try
    let (mvars', r') ← isolate x r.expr
    return (mvars ++ mvars', ← r.mkEqTrans r')
  catch _ =>
    return (mvars, r)

/-- Recursively modify the hypothesis `fvar`, which must have type of the form `A ~ B`, by finding
the expression `x` as a subexpression of either `A` or `B` (but not both), and rewriting by
`@[isolate]` lemmas to make `x` less deeply nested.

Return the new main goal (after the hypothesis `fvar` has been modified in this way), together with
the side goals generated by the `@[isolate]` lemmas used. -/
def isolateAtLocalDecl (x : Expr) (fvar : FVarId) (g : MVarId) : MetaM (List MVarId) := do
  let P ← fvar.getType
  let ⟨mvars, r⟩ ← isolate x P
  let some (_, newGoal) ← applySimpResultToLocalDecl g fvar r false |
    throwError "internal failure of the isolate tactic while transforming {P} to {r.expr}"
  pure (newGoal :: mvars)

/-- Recursively modify the goal `g`, which must have type of the form `A ~ B`, by finding the
expression `x` as a subexpression of either `A` or `B` (but not both), and rewriting by `@[isolate]`
lemmas to make `x` less deeply nested.

Return the new main goal, together with the side goals generated by the `@[isolate]` lemmas used. -/
def isolateAtTarget (x : Expr) (g : MVarId) : MetaM (List MVarId) := do
  let P ← g.getType
  let ⟨mvars, r⟩ ← isolate x P
  let mainGoal ← applySimpResultToTarget g P r
  pure (mainGoal :: mvars)

open Elab Parser Tactic in
/-- The `isolate` tactic "solves for x" in an equation or relation. For example:
```
example (a b : ℝ) (f : ℝ → ℝ) : 5 * f a - 3 < b := by
  isolate f a
  -- new goal: `⊢ f a < (b + 3) / 5`
```

The `isolate` tactic may generate side goals, if these are necessary to justify the transformation.
The tactic will attempt to justify such side goals using `positivity` (as in the above example),
unification, or type class inference, but if unsuccessful will present them to the user. For
example:
```
example (a b c : ℝ) (f : ℝ → ℝ) : c * f a - 3 < b := by
  isolate f a
  -- new goal: `⊢ f a < (b + 3) / c`
  -- second (side) new goal: `⊢ 0 < c`
```

The `isolate` tactic is extensible. Coverage may be extended to new relations and new
operations-to-be-undone by tagging appropriate lemmas with the `@[isolate]` attribute. -/
elab "isolate" x:term loc:(location)? : tactic => withMainContext do
  let x ← elabTerm x none (mayPostpone := true)
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  withLocation loc
    (fun fvar ↦ liftMetaTactic <| isolateAtLocalDecl x fvar)
    (liftMetaTactic <| isolateAtTarget x)
    fun _ ↦ throwError m!"No {x} terms found anywhere which could be isolated"

end Mathlib.Tactic.Isolate
