/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Int.Cast.Defs
import Qq.MetaM
import Qq.Delab

/-!
## `norm_num` core functionality

This file sets up the `norm_num` tactic and the `@[norm_num]` attribute,
which allow for plugging in new normalization functionality around a simp-based driver.
The actual behavior is in `@[norm_num]`-tagged definitions in `Tactic.NormNum.Basic`
and elsewhere.
-/
open Lean hiding Rat
open Lean.Meta Qq Lean.Elab Term

/-- Attribute for identifying `norm_num` extensions. -/
syntax (name := norm_num) "norm_num" term,+ : attr

namespace Mathlib
namespace Meta.NormNum

initialize registerTraceClass `Tactic.norm_num

/-- Assert that an element of a semiring is equal to the coercion of some natural number. -/
structure IsNat [Semiring α] (a : α) (n : ℕ) : Prop where
  /-- The element is equal to the coercion of the natural number. -/
  out : a = n

theorem IsNat.raw_refl (n : ℕ) : IsNat n n := ⟨rfl⟩

@[simp] def _root_.Nat.rawCast [Semiring α] (n : ℕ) : α := n

/-- Asserting that the `OfNat α n` instance provides the same value as the coercion. -/
class LawfulOfNat (α) [Semiring α] (n) [OfNat α n] : Prop where
  /-- Assert `n = (OfNat.ofNat n α)`, with the parametrising instance. -/
  eq_ofNat : n = (@OfNat.ofNat _ n ‹_› : α)

instance (α) [Semiring α] [Nat.AtLeastTwo n] : LawfulOfNat α n := ⟨rfl⟩
instance (α) [Semiring α] : LawfulOfNat α (nat_lit 0) := ⟨Nat.cast_zero⟩
instance (α) [Semiring α] : LawfulOfNat α (nat_lit 1) := ⟨Nat.cast_one⟩
instance : LawfulOfNat ℕ n := ⟨show n = Nat.cast n by simp⟩
instance : LawfulOfNat ℤ n := ⟨show Int.ofNat n = Nat.cast n by simp⟩

theorem IsNat.to_eq [Semiring α] (n) [OfNat α n] [LawfulOfNat α n] :
    (a : α) → IsNat a n → a = OfNat.ofNat n
  | _, ⟨rfl⟩ => LawfulOfNat.eq_ofNat

theorem IsNat.to_raw_eq [Semiring α] : IsNat (a : α) n → a = n.rawCast
  | ⟨e⟩ => e

theorem IsNat.of_raw (α) [Semiring α] (n : ℕ) : IsNat (n.rawCast : α) n := ⟨rfl⟩

/-- Assert that an element of a ring is equal to the coercion of some integer. -/
structure IsInt [Ring α] (a : α) (n : ℤ) : Prop where
  /-- The element is equal to the coercion of the integer. -/
  out : a = n

@[simp] def _root_.Int.rawCast [Ring α] (n : ℤ) : α := n

theorem IsInt.to_isNat {α} [Ring α] : ∀ {a : α} {n}, IsInt a (.ofNat n) → IsNat a n
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

theorem IsNat.to_isInt {α} [Ring α] : ∀ {a : α} {n}, IsNat a n → IsInt a (.ofNat n)
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

theorem IsInt.to_raw_eq [Ring α] : IsInt (a : α) n → a = n.rawCast
  | ⟨e⟩ => e

theorem IsInt.of_raw (α) [Ring α] (n : ℤ) : IsInt (n.rawCast : α) n := ⟨rfl⟩

theorem IsInt.neg_to_eq {α} [Ring α] (n) [OfNat α n] [LawfulOfNat α n] :
    (a : α) → IsInt a (.negOfNat n) → a = -OfNat.ofNat n
  | _, ⟨rfl⟩ => by simp [Int.negOfNat_eq, Int.cast_neg]; apply LawfulOfNat.eq_ofNat

theorem IsInt.nonneg_to_eq {α} [Ring α] (n) [OfNat α n] [LawfulOfNat α n]
    (a : α) (h : IsInt a (.ofNat n)) : a = OfNat.ofNat n := h.to_isNat.to_eq

/-- Represent an integer as a typed expression. -/
def mkRawIntLit (n : ℤ) : Q(ℤ) :=
  let lit : Q(ℕ) := mkRawNatLit n.natAbs
  if 0 ≤ n then q(.ofNat $lit) else q(.negOfNat $lit)

/-- A shortcut (non)instance for `Semiring ℕ` to shrink generated proofs. -/
def instSemiringNat : Semiring ℕ := inferInstance

/-- A shortcut (non)instance for `Ring ℤ` to shrink generated proofs. -/
def instRingInt : Ring ℤ := inferInstance

-- TODO: remove when `algebra.invertible` is ported
/-- `Invertible a` gives a two-sided multiplicative inverse of `a`. -/
class Invertible [Mul α] [One α] (a : α) : Type _ where
  /-- The multiplicative inverse. -/
  invOf : α
  /-- The multiplicative inverse is a left inverse. -/
  invOf_mul_self : invOf * a = 1
  /-- The multiplicative inverse is a right inverse. -/
  mul_invOf_self : a * invOf = 1

/-- Local notation for the inverse of an invertible element. -/
-- This notation has the same precedence as `Inv.inv`.
scoped prefix:max "⅟" => Invertible.invOf

/--
Assert that an element of a ring is equal to `num / denom`
(and `denom` is invertible so that this makes sense).
We will usually also have `num` and `denom` coprime,
although this is not part of the definition.
-/
structure IsRat [Ring α] (a : α) (num : ℤ) (denom : ℕ) where
  /-- The denominator is invertible. -/
  inv : Invertible denom
  /-- The element is equal to the fraction with the specified numerator and denominator. -/
  eq : a = num * ⅟denom

/-- The result of `norm_num` running on an expression `x` of type `α`.
Untyped version of `Result`. -/
inductive Result' where
  /-- Untyped version of `Result.isNat`. -/
  | isNat (inst lit proof : Expr)
  /-- Untyped version of `Result.isNegNat`. -/
  | isNegNat (inst lit proof : Expr)
  /-- Untyped version of `Result.isRat`. -/
  | isRat (inst : Expr) (q : Rat) (n d proof : Expr)
  deriving Inhabited

section
set_option linter.unusedVariables false

/-- The result of `norm_num` running on an expression `x` of type `α`. -/
@[nolint unusedArguments] def Result {α : Q(Type u)} (x : Q($α)) := Result'

instance : Inhabited (Result x) := inferInstanceAs (Inhabited Result')

/-- The result is `lit : ℕ` (a raw nat literal) and `proof : isNat x lit`. -/
@[match_pattern, inline] def Result.isNat {α : Q(Type u)} {x : Q($α)} :
    ∀ (inst : Q(Semiring $α) := by assumption) (lit : Q(ℕ)) (proof : Q(IsNat $x $lit)),
      Result x := Result'.isNat

/-- The result is `-lit` where `lit` is a raw nat literal
and `proof : isInt x (.negOfNat lit)`. -/
@[match_pattern, inline] def Result.isNegNat {α : Q(Type u)} {x : Q($α)} :
    ∀ (inst : Q(Ring $α) := by assumption) (lit : Q(ℕ)) (proof : Q(IsInt $x (.negOfNat $lit))),
      Result x := Result'.isNegNat

/-- The result is `proof : isRat x n d`, where `n` is either `.ofNat lit` or `.negOfNat lit`
with `lit` a raw nat literal and `d` is a raw nat literal (not 0 or 1),
and `q` is the value of `n / d`. -/
@[match_pattern, inline] def Result.isRat {α : Q(Type u)} {x : Q($α)} :
    ∀ (inst : Q(Ring $α) := by assumption) (q : Rat) (n : Q(ℤ)) (d : Q(ℕ))
      (proof : Q(IsRat $x $n $d)), Result x := Result'.isRat

/-- The result is `z : ℤ` and `proof : isNat x z`. -/
-- Note the independent arguments `z : Q(ℤ)` and `n : ℤ`.
-- We ensure these are "the same" when calling.
def Result.isInt {α : Q(Type u)} {x : Q($α)} {z : Q(ℤ)}
    (inst : Q(Ring $α) := by assumption) (n : ℤ) (proof : Q(IsInt $x $z)) : Result x :=
  have lit : Q(ℕ) := z.appArg!
  if 0 ≤ n then
    let proof : Q(IsInt $x (.ofNat $lit)) := proof
    .isNat q(Ring.toSemiring) lit q(IsInt.to_isNat $proof)
  else
    .isNegNat inst lit proof

end

/-- Helper functor to synthesize a typed `Semiring α` expression. -/
def inferSemiring (α : Q(Type u)) : MetaM Q(Semiring $α) :=
  return ← synthInstanceQ (q(Semiring $α) : Q(Type u)) <|> throwError "not a semiring"

/-- Helper functor to synthesize a typed `Ring α` expression. -/
def inferRing (α : Q(Type u)) : MetaM Q(Ring $α) :=
  return ← synthInstanceQ (q(Ring $α) : Q(Type u)) <|> throwError "not a semiring"

def Result.isZero : Result e → Bool
  | .isNat _ lit _ => lit.natLit! == 0
  | _ => false

/--
Extract from a `Result` the integer value (as both a term and an expression),
and the proof that the original expression is equal to this integer.
-/
def Result.toInt {α : Q(Type u)} {e : Q($α)} (_i : Q(Ring $α) := by with_reducible assumption) :
    Result e → Option (ℤ × (lit : Q(ℤ)) × Q(IsInt $e $lit))
  | .isNat _ lit proof => do
    have proof : Q(@IsNat _ Ring.toSemiring $e $lit) := proof
    pure ⟨lit.natLit!, q(.ofNat $lit), q(($proof).to_isInt)⟩
  | .isNegNat _ lit proof => pure ⟨-lit.natLit!, q(.negOfNat $lit), proof⟩
  | _ => failure

instance : ToMessageData (Result x) where
  toMessageData
  | .isNat _ lit proof => m!"isNat {lit} ({proof})"
  | .isNegNat _ lit proof => m!"isNegNat {lit} ({proof})"
  | .isRat _ q _ _ proof => m!"isRat {q} ({proof})"

def Result.toRawEq {α : Q(Type u)} {e : Q($α)} : Result e → (ℤ × (e' : Q($α)) × Q($e = $e'))
  | .isNat _ lit p => ⟨lit.natLit!, q(Nat.rawCast $lit), q(IsNat.to_raw_eq $p)⟩
  | .isNegNat _ lit p => ⟨-lit.natLit!, q(Int.rawCast (.negOfNat $lit)), q(IsInt.to_raw_eq $p)⟩
  | .isRat _ .. => ⟨0, (default : Expr), (default : Expr)⟩ -- TODO

/-- Constructs a `Result` out of a raw nat cast. Assumes `e` is a raw nat cast expression. -/
def Result.ofRawNat {α : Q(Type u)} (e : Q($α)) : Result e := Id.run do
  let .app (.app _ (sα : Q(Semiring $α))) (lit : Q(ℕ)) := e | panic! "not a raw nat cast"
  .isNat sα lit (q(IsNat.of_raw $α $lit) : Expr)

/-- Constructs a `Result` out of a raw int cast.
Assumes `e` is a raw int cast expression denoting `n`. -/
def Result.ofRawInt {α : Q(Type u)} (n : ℤ) (e : Q($α)) : Result e :=
  if 0 ≤ n then
    Result.ofRawNat e
  else Id.run do
    let .app (.app _ (rα : Q(Ring $α))) (.app _ (lit : Q(ℕ))) := e | panic! "not a raw int cast"
    .isNegNat rα lit (q(IsInt.of_raw $α (.negOfNat $lit)) : Expr)

/--
Convert a `Result` to a `Simp.Result`.
-/
def Result.toSimpResult {α : Q(Type u)} {e : Q($α)} : Result e → MetaM Simp.Result
  | .isNat _sα lit p => do
    let _ofNatInst ← synthInstanceQ (q(OfNat $α $lit) : Q(Type u))
    let _lawfulInst ← synthInstanceQ (q(LawfulOfNat $α $lit) : Q(Prop))
    return { expr := q((OfNat.ofNat $lit : $α)), proof? := q(IsNat.to_eq $lit $e $p) }
  | .isNegNat _rα lit p => do
    let _ofNatInst ← synthInstanceQ (q(OfNat $α $lit) : Q(Type u))
    let _lawfulInst ← synthInstanceQ (q(LawfulOfNat $α $lit) : Q(Prop))
    return { expr := q(-(OfNat.ofNat $lit : $α)), proof? := q(IsInt.neg_to_eq $lit $e $p) }
  | .isRat _ .. => failure -- TODO

/--
A extension for `norm_num`.
-/
structure NormNumExt where
  /-- The extension should be run in the `pre` phase when used as simp plugin. -/
  pre := true
  /-- The extension should be run in the `post` phase when used as simp plugin. -/
  post := true
  /-- Attempts to prove an expression is equal to some explicit number of the relevant type. -/
  eval {α : Q(Type u)} (e : Q($α)) : MetaM (Result e)

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
    mkInitial := pure ([], {})
    addImportedFn := fun s => do
      let dt ← s.foldlM (init := {}) fun dt s => s.foldlM (init := dt) fun dt (kss, n) => do
        pure (insert kss (← mkNormNumExt n) dt)
      pure ([], dt)
    addEntryFn := fun (entries, s) ((kss, n), ext) => ((kss, n) :: entries, insert kss ext s)
    exportEntriesFn := fun s => s.1.reverse.toArray
  }

/-- Run each registered `norm_num` extension on an expression, returning a `NormNum.Result`. -/
def derive {α : Q(Type u)} (e : Q($α)) (post := false) : MetaM (Result e) := do
  if e.isNatLit then
    let lit : Q(ℕ) := e
    return .isNat (q(instSemiringNat) : Q(Semiring ℕ)) lit (q(IsNat.raw_refl $lit) : Expr)
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
def deriveNat' {α : Q(Type u)} (e : Q($α)) :
    MetaM ((_inst : Q(Semiring $α)) × (lit : Q(ℕ)) × Q(IsNat $e $lit)) := do
  let .isNat inst lit proof ← derive e | failure
  pure ⟨inst, lit, proof⟩

/-- Run each registered `norm_num` extension on a typed expression `e : α`,
returning a typed expression `lit : ℕ`, and a proof of `isNat e lit`. -/
def deriveNat {α : Q(Type u)} (e : Q($α))
    (_inst : Q(Semiring $α) := by with_reducible assumption) :
    MetaM ((lit : Q(ℕ)) × Q(IsNat $e $lit)) := do
  let .isNat _ lit proof ← derive e | failure
  pure ⟨lit, proof⟩

/-- Run each registered `norm_num` extension on a typed expression `e : α`,
returning a typed expression `lit : ℤ`, and a proof of `isInt e lit`. -/
def deriveInt {α : Q(Type u)} (e : Q($α))
    (_inst : Q(Ring $α) := by with_reducible assumption) :
    MetaM ((lit : Q(ℤ)) × Q(IsInt $e $lit)) := do
  let some ⟨_, lit, proof⟩ := (← derive e).toInt | failure
  pure ⟨lit, proof⟩

/-- Extract the natural number `n` if the expression is of the form `OfNat.ofNat n`. -/
def isNatLit (e : Expr) : Option ℕ := do
  guard <| e.isAppOfArity ``OfNat.ofNat 3
  let .lit (.natVal lit) := e.appFn!.appArg! | none
  lit

/-- Extract the integer `i` if the expression is either a natural number literal
or the negation of one. -/
def isIntLit (e : Expr) : Option ℤ :=
  if e.isAppOfArity ``Neg.neg 3 then
    (- ·) <$> isNatLit e.appArg!
  else
    isNatLit e

/-- Extract the numerator `n : ℤ` and denomination `d : ℕ` if the expression is either
an integer literal, or the division of one integer literal by another. -/
def isRatLit (e : Expr) : Option (ℤ × ℕ) := do
  if e.isAppOfArity ``Div.div 4 then
    pure (← isIntLit e.appFn!.appArg!, ← isNatLit e.appArg!)
  else
    pure (← isIntLit e, 1)

/-- Test if an expression represents an explicit number written in normal form. -/
def isNormalForm : Expr → Bool
  | .lit _ => true
  | .mdata _ e => isNormalForm e
  | e => (isRatLit e).isSome

/-- Run each registered `norm_num` extension on an expression,
returning a `Simp.Result`. -/
def eval (e : Expr) (post := false) : MetaM Simp.Result := do
  if isNormalForm e then return { expr := e }
  let ⟨.succ _, _, e⟩ ← inferTypeQ e | failure
  (← derive e post).toSimpResult

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
  try return some (.done (← eval e post))
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
open Lean.Parser.Tactic Meta.NormNum

/-- Normalize numerical expressions. -/
elab "norm_num" only:&" only"? args:(simpArgs ?) loc:(location ?) : tactic =>
  elabNormNum args loc (simpOnly := only.isSome) (useSimp := true)

/-- Basic version of `norm_num` that does not call `simp`. -/
elab "norm_num1" loc:(location ?) : tactic =>
  elabNormNum mkNullNode loc (simpOnly := true) (useSimp := false)
