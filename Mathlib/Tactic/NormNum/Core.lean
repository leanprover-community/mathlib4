/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Ring.Basic
import Qq.MetaM

/-!
## `norm_num` core functionality

This file sets up the `norm_num` tactic and the `@[norm_num]` attribute,
which allow for plugging in new normalization functionality around a simp-based driver.
The actual behavior is in `@[norm_num]`-tagged definitions in `Tactic.NormNum.Basic`
and elsewhere.
-/

open Lean Meta Qq Elab Term

/-- Attribute for identifying `norm_num` extensions. -/
syntax (name := norm_num) "norm_num" term,+ : attr

namespace Mathlib
namespace Meta.NormNum

initialize registerTraceClass `Tactic.norm_num

/-- Assert that an element of a semiring is equal to the coercion of some natural number. -/
def isNat [Semiring α] (a : α) (n : ℕ) := a = n

/-- Asserting that the `OfNat α n` instance provides the same value as the coercion. -/
class LawfulOfNat (α) [Semiring α] (n) [OfNat α n] : Prop where
  /-- Assert `isNat (OfNat.ofNat n α) n`, with the parametrising instance. -/
  isNat_ofNat : isNat (@OfNat.ofNat _ n ‹_› : α) n

instance (α) [Semiring α] [Nat.AtLeastTwo n] : LawfulOfNat α n := ⟨rfl⟩
instance (α) [Semiring α] : LawfulOfNat α (nat_lit 0) := ⟨Nat.cast_zero.symm⟩
instance (α) [Semiring α] : LawfulOfNat α (nat_lit 1) := ⟨Nat.cast_one.symm⟩
instance : LawfulOfNat Nat n := ⟨show n = Nat.cast n by simp⟩
instance : LawfulOfNat Int n := ⟨show Int.ofNat n = Nat.cast n by simp⟩

theorem eval_of_isNat {α} [Semiring α] (n) [OfNat α n] [LawfulOfNat α n] :
  (a : α) → isNat a n → a = OfNat.ofNat n
| _, rfl => LawfulOfNat.isNat_ofNat.symm

/-- The result of `norm_num` running on an expression of type `α` can either be
a natural number literal in `α`
or some new expression `e : α` equipped with a proof of type `isNat e n` for some `n : ℕ`. -/
inductive Result where
  | literal (lit : Expr)
  | isNat (lit proof : Expr)

instance : ToMessageData Result where
  toMessageData
  | .literal lit => m!"(literal {lit})"
  | .isNat lit proof => m!"(isNat {lit} {proof})"

/--
Express a `Result` as a pair of expressions `e : α` and `prf : isNat e n` for some `n : ℕ`.
-/
def Result.toIsNat : Result → Expr × Expr
  | .literal (lit : Q(Nat)) => (lit, q(@Eq.refl Nat $lit))
  | .isNat lit p => (lit, p)

/--
Given a typed expression `e : α`, and a `Result`
(which should have been obtained by running `derive` on `e`,
produce a typed expression `lit : ℕ` and a proof of `isNat e lit`.
-/
def Result.toIsNatQ {α : Q(Type u)} (e : Q($α)) :
    Result → (_inst : Q(Semiring $α) := by assumption) → (lit : Q(Nat)) × Q(NormNum.isNat $e $lit)
  | .literal (lit : Q(Nat)), _ => ⟨lit, (q(@Eq.refl Nat $lit) : Expr)⟩
  | .isNat lit p, _ => ⟨lit, p⟩

/--
Convert a `Result` to a `Simp.Result`.
-/
def Result.toSimpResult (e : Expr) : Result → MetaM Simp.Result
  | .literal lit => pure { expr := lit }
  | .isNat (lit : Q(Nat)) p => by exact do
    let ⟨.succ u, α, e⟩ ← inferTypeQ e | failure
    let sα ← synthInstanceQ (q(Semiring $α) : Q(Type u))
    let p : Q(NormNum.isNat $e $lit) := p
    let ofNatInst ← synthInstanceQ (q(OfNat $α $lit) : Q(Type u))
    let lawfulInst ← synthInstanceQ (q(LawfulOfNat $α $lit) : Q(Prop))
    return { expr := q((OfNat.ofNat $lit : $α)), proof? := q(eval_of_isNat $lit $e $p) }

/--
A extension for `norm_num`.
-/
structure NormNumExt where
  /-- The extension should be run in the `pre` phase when used as simp plugin. -/
  pre := true
  /-- The extension should be run in the `post` phase when used as simp plugin. -/
  post := true
  /-- Attempts to prove an expression is equal to some natural number. -/
  eval : Expr → MetaM Result

/-- Read a `norm_num` extension from a declaration of the right type. -/
def mkNormNumExt (n : Name) : ImportM NormNumExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck NormNumExt opts ``NormNumExt n

/-- Each `norm_num` extension is labelled with a collection of patterns
which determine the expressions to which it should be applied. -/
abbrev Entry := Array (Array DiscrTree.Key) × Name
/-- Environment extensions for `norm_num` declarations -/
initialize normNumExt : PersistentEnvExtension Entry (Entry × NormNumExt)
    (List Entry × DiscrTree NormNumExt) ←
  -- we only need this to deduplicate entries in the DiscrTree
  have : BEq NormNumExt := ⟨fun _ _ => false⟩
  let insert kss v dt := kss.foldl (fun dt ks => dt.insertCore ks v) dt
  registerPersistentEnvExtension {
    name := decl_name%
    mkInitial := pure ([], {})
    addImportedFn := fun s => do
      let dt ← s.foldlM (init := {}) fun dt s => s.foldlM (init := dt) fun dt (kss, n) => do
        pure (insert kss (← mkNormNumExt n) dt)
      pure ([], dt)
    addEntryFn := fun (entries, s) ((kss, n), ext) => ((kss, n) :: entries, insert kss ext s)
    exportEntriesFn := fun s => s.1.reverse.toArray
  }

/-- Run each registered `norm_num` extension on an expression, returning a `NormNum.Result`. -/
def derive (e : Expr) (post := false) : MetaM Result := do
  if e.isNatLit then return .literal e
  let s ← saveState
  let arr ← (normNumExt.getState (← getEnv)).2.getMatch e
  for ext in arr do
    if (bif post then ext.post else ext.pre) then
      try
        let new ← ext.eval e
        trace[Tactic.norm_num] "{e} ==> {new}"
        return new
      catch err =>
        trace[Tactic.norm_num] "{e} failed: {err.toMessageData}"
        s.restore
  throwError "{e}: no norm_nums apply"

/-- Run each registered `norm_num` extension on a typed expression `e : α`,
returning a typed expression `lit : ℕ`, and a proof of `isNat e lit`. -/
def deriveQ {α : Q(Type u)} (e : Q($α))
    (inst : Q(Semiring $α) := by with_reducible assumption) :
    MetaM ((lit : Q(Nat)) × Q(NormNum.isNat $e $lit)) := return (← derive e).toIsNatQ e

/-- Run each registered `norm_num` extension on an expression,
returning a `Simp.Result`. -/
def eval (e : Expr) : MetaM Simp.Result := do (← derive e).toSimpResult e

initialize registerBuiltinAttribute {
  name := `norm_num
  descr := "adds a norm_num extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| norm_num $es,*) => do
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'norm_num', must be global"
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute 'norm_num', declaration is in an imported module"
      if (IR.getSorryDep env declName).isSome then return -- ignore in progress definitions
      let ext ← mkNormNumExt declName
      let keys ← MetaM.run' <| es.getElems.mapM fun stx => do
        let e ← TermElabM.run' <| withSaveInfoContext <| withAutoBoundImplicit <|
          withReader ({ · with ignoreTCFailures := true }) do
            let e ← elabTerm stx none
            let (_, _, e) ← lambdaMetaTelescope (← mkLambdaFVars (← getLCtx).getFVars e)
            return e
        DiscrTree.mkPath e
      setEnv <| normNumExt.addEntry env ((keys, declName), ext)
    | _ => throwUnsupportedSyntax
}

/-- A simp plugin which calls `NormNum.eval`. -/
def tryNormNum? (post := false) (e : Expr) : SimpM (Option Simp.Step) := do
  try return some (.done (← (← derive e post).toSimpResult e))
  catch _ => return none

/--
Constructs a proof that the original expression is true
given a simp result which simplifies the target to `True`.
-/
def _root_.Lean.Meta.Simp.Result.ofTrue (r : Simp.Result) : MetaM (Option Expr) :=
  if r.expr.isConstOf ``True then
    some <$> match r.proof? with
    | some proof => mkOfEqTrue proof
    | none => pure (mkConst ``True.intro)
  else
    pure none

variable (ctx : Simp.Context) (useSimp := true) in
mutual
  /-- A discharger which calls `norm_num`. -/
  partial def discharge (e : Expr) : SimpM (Option Expr) := do (← deriveSimp e).ofTrue

  /-- A `Methods` implementation which calls `norm_num`. -/
  partial def methods : Simp.Methods :=
    if useSimp then {
      pre := fun e => do
        Simp.andThen (← Simp.preDefault e discharge) tryNormNum?
      post := fun e => do
        Simp.andThen (← Simp.postDefault e discharge) (tryNormNum? (post := true))
      discharge? := discharge
    } else {
      pre := fun e => Simp.andThen (.visit { expr := e }) tryNormNum?
      post := fun e => Simp.andThen (.visit { expr := e }) (tryNormNum? (post := true))
      discharge? := discharge
    }

  /-- Traverses the given expression using simp and normalises any numbers it finds. -/
  partial def deriveSimp (e : Expr) : MetaM Simp.Result :=
    (·.1) <$> Simp.main e ctx (methods := methods)
end

-- FIXME: had to inline a bunch of stuff from `simpGoal` here
/--
The core of `norm_num` as a tactic in `MetaM`.

* `g`: The goal to simplify
* `ctx`: The simp context, constructed by `mkSimpContext` and
  containing any additional simp rules we want to use
* `fvarIdsToSimp`: The selected set of hypotheses used in the location argument
* `simplifyTarget`: true if the target is selected in the location argument
* `useSimp`: true if we used `norm_num` instead of `norm_num1`
-/
def normNumAt (g : MVarId) (ctx : Simp.Context) (fvarIdsToSimp : Array FVarId)
    (simplifyTarget := true) (useSimp := true) :
    MetaM (Option (Array FVarId × MVarId)) := g.withContext do
  g.checkNotAssigned `norm_num
  let mut g := g
  let mut toAssert := #[]
  let mut replaced := #[]
  for fvarId in fvarIdsToSimp do
    let localDecl ← fvarId.getDecl
    let type ← instantiateMVars localDecl.type
    let ctx := { ctx with simpTheorems := ctx.simpTheorems.eraseTheorem (.fvar localDecl.fvarId) }
    let r ← deriveSimp ctx useSimp type
    match r.proof? with
    | some _ =>
      let some (value, type) ← applySimpResultToProp g (mkFVar fvarId) type r
        | return none
      toAssert := toAssert.push { userName := localDecl.userName, type, value }
    | none =>
      if r.expr.isConstOf ``False then
        g.assign (← mkFalseElim (← g.getType) (mkFVar fvarId))
        return none
      g ← g.replaceLocalDeclDefEq fvarId r.expr
      replaced := replaced.push fvarId
  if simplifyTarget then
    let res ← g.withContext do
      let target ← instantiateMVars (← g.getType)
      let r ← deriveSimp ctx useSimp target
      let some proof ← r.ofTrue
        | some <$> applySimpResultToTarget g target r
      g.assign proof
      pure none
    let some gNew := res | return none
    g := gNew
  let (fvarIdsNew, gNew) ← g.assertHypotheses toAssert
  let toClear := fvarIdsToSimp.filter fun fvarId => !replaced.contains fvarId
  let gNew ← gNew.tryClearMany toClear
  return some (fvarIdsNew, gNew)

open Qq Lean Meta Elab Tactic Term

open Elab.Tactic in
/--
Elaborates a call to `norm_num only? [args]` or `norm_num1`.
* `args`: the `(simpArgs)?` syntax for simp arguments
* `loc`: the `(location)?` syntax for the optional location argument
* `simpOnly`: true if `only` was used in `norm_num`
* `useSimp`: false if `norm_num1` was used, in which case only the structural parts
  of `simp` will be used, not any of the post-processing that `simp only` does without lemmas
-/
-- FIXME: had to inline a bunch of stuff from `mkSimpContext` and `simpLocation` here
def elabNormNum (args : Syntax) (loc : Syntax)
    (simpOnly := false) (useSimp := true) : TacticM Unit := do
  let simpTheorems ←
    if !useSimp || simpOnly then simpOnlyBuiltins.foldlM (·.addConst ·) {} else getSimpTheorems
  let mut { ctx, starArg } ← elabSimpArgs args (eraseLocal := false) (kind := .simp)
    { simpTheorems := #[simpTheorems], congrTheorems := ← getSimpCongrTheorems }
  if starArg then
    let mut simpTheorems := ctx.simpTheorems
    for h in ← getPropHyps do
      unless simpTheorems.isErased (.fvar h) do
        simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
    ctx := { ctx with simpTheorems }
  let g ← getMainGoal
  let res ← match expandOptLocation loc with
  | .targets hyps simplifyTarget => normNumAt g ctx (← getFVarIds hyps) simplifyTarget useSimp
  | .wildcard => normNumAt g ctx (← g.getNondepPropHyps) (simplifyTarget := true) useSimp
  match res with
  | none => replaceMainGoal []
  | some (_, g) => replaceMainGoal [g]

end Meta.NormNum

namespace Tactic
open Parser.Tactic Meta.NormNum

/-- Normalize numerical expressions. -/
elab "norm_num" only:&" only"? args:(simpArgs ?) loc:(location ?) : tactic =>
  elabNormNum args loc (simpOnly := only.isSome) (useSimp := true)

/-- Basic version of `norm_num` that does not call `simp`. -/
elab "norm_num1" loc:(location ?) : tactic =>
  elabNormNum mkNullNode loc (simpOnly := true) (useSimp := false)
