/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Lean.Parser
import Mathlib.Algebra.Invertible
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Conv
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
structure IsNat [AddMonoidWithOne α] (a : α) (n : ℕ) : Prop where
  /-- The element is equal to the coercion of the natural number. -/
  out : a = n

theorem IsNat.raw_refl (n : ℕ) : IsNat n n := ⟨rfl⟩

/--
A "raw nat cast" is an expression of the form `(Nat.rawCast lit : α)` where `lit` is a raw
natural number literal. These expressions are used by tactics like `ring` to decrease the number
of typeclass arguments required in each use of a number literal at type `α`.
-/
@[simp] def _root_.Nat.rawCast [AddMonoidWithOne α] (n : ℕ) : α := n

theorem IsNat.to_eq [AddMonoidWithOne α] {n} : {a a' : α} → IsNat a n → n = a' → a = a'
  | _, _, ⟨rfl⟩, rfl => rfl

theorem IsNat.to_raw_eq [AddMonoidWithOne α] : IsNat (a : α) n → a = n.rawCast
  | ⟨e⟩ => e

theorem IsNat.of_raw (α) [AddMonoidWithOne α] (n : ℕ) : IsNat (n.rawCast : α) n := ⟨rfl⟩

/-- Assert that an element of a ring is equal to the coercion of some integer. -/
structure IsInt [Ring α] (a : α) (n : ℤ) : Prop where
  /-- The element is equal to the coercion of the integer. -/
  out : a = n

/--
A "raw int cast" is an expression of the form:

* `(Nat.rawCast lit : α)` where `lit` is a raw natural number literal
* `(Int.rawCast (Int.negOfNat lit) : α)` where `lit` is a nonzero raw natural number literal

(That is, we only actually use this function for negative integers.) This representation is used by
tactics like `ring` to decrease the number of typeclass arguments required in each use of a number
literal at type `α`.
-/
@[simp] def _root_.Int.rawCast [Ring α] (n : ℤ) : α := n

theorem IsInt.to_isNat {α} [Ring α] : ∀ {a : α} {n}, IsInt a (.ofNat n) → IsNat a n
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

theorem IsNat.to_isInt {α} [Ring α] : ∀ {a : α} {n}, IsNat a n → IsInt a (.ofNat n)
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

theorem IsInt.to_raw_eq [Ring α] : IsInt (a : α) n → a = n.rawCast
  | ⟨e⟩ => e

theorem IsInt.of_raw (α) [Ring α] (n : ℤ) : IsInt (n.rawCast : α) n := ⟨rfl⟩

theorem IsInt.neg_to_eq {α} [Ring α] {n} :
    {a a' : α} → IsInt a (.negOfNat n) → n = a' → a = -a'
  | _, _, ⟨rfl⟩, rfl => by simp [Int.negOfNat_eq, Int.cast_neg]

theorem IsInt.nonneg_to_eq {α} [Ring α] {n}
    {a a' : α} (h : IsInt a (.ofNat n)) (e : n = a') : a = a' := h.to_isNat.to_eq e

/-- Represent an integer as a typed expression. -/
def mkRawIntLit (n : ℤ) : Q(ℤ) :=
  let lit : Q(ℕ) := mkRawNatLit n.natAbs
  if 0 ≤ n then q(.ofNat $lit) else q(.negOfNat $lit)

/-- A shortcut (non)instance for `AddMonoidWithOne ℕ` to shrink generated proofs. -/
def instAddMonoidWithOneNat : AddMonoidWithOne ℕ := inferInstance

/-- A shortcut (non)instance for `Ring ℤ` to shrink generated proofs. -/
def instRingInt : Ring ℤ := inferInstance

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
    ∀ (inst : Q(AddMonoidWithOne $α) := by assumption) (lit : Q(ℕ)) (proof : Q(IsNat $x $lit)),
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

/-- A shortcut (non)instance for `AddMonoidWithOne α` from `Ring α` to shrink generated proofs. -/
def instAddMonoidWithOne [Ring α] : AddMonoidWithOne α := inferInstance

/-- The result is `z : ℤ` and `proof : isNat x z`. -/
-- Note the independent arguments `z : Q(ℤ)` and `n : ℤ`.
-- We ensure these are "the same" when calling.
def Result.isInt {α : Q(Type u)} {x : Q($α)} {z : Q(ℤ)}
    (inst : Q(Ring $α) := by assumption) (n : ℤ) (proof : Q(IsInt $x $z)) : Result x :=
  have lit : Q(ℕ) := z.appArg!
  if 0 ≤ n then
    let proof : Q(IsInt $x (.ofNat $lit)) := proof
    .isNat q(instAddMonoidWithOne) lit q(IsInt.to_isNat $proof)
  else
    .isNegNat inst lit proof

/-- Returns the rational number that is the result of norm_num evaluation. -/
def Result.toRat : Result e → Rat
  | .isNat _ lit _ => lit.natLit!
  | .isNegNat _ lit _ => -lit.natLit!
  | .isRat _ q .. => q

end

/-- Helper functor to synthesize a typed `AddMonoidWithOne α` expression. -/
def inferAddMonoidWithOne (α : Q(Type u)) : MetaM Q(AddMonoidWithOne $α) :=
  return ← synthInstanceQ (q(AddMonoidWithOne $α) : Q(Type u)) <|>
    throwError "not a AddMonoidWithOne"

/-- Helper functor to synthesize a typed `Semiring α` expression. -/
def inferSemiring (α : Q(Type u)) : MetaM Q(Semiring $α) :=
  return ← synthInstanceQ (q(Semiring $α) : Q(Type u)) <|> throwError "not a semiring"

/-- Helper functor to synthesize a typed `Ring α` expression. -/
def inferRing (α : Q(Type u)) : MetaM Q(Ring $α) :=
  return ← synthInstanceQ (q(Ring $α) : Q(Type u)) <|> throwError "not a semiring"

/--
Extract from a `Result` the integer value (as both a term and an expression),
and the proof that the original expression is equal to this integer.
-/
def Result.toInt {α : Q(Type u)} {e : Q($α)} (_i : Q(Ring $α) := by with_reducible assumption) :
    Result e → Option (ℤ × (lit : Q(ℤ)) × Q(IsInt $e $lit))
  | .isNat _ lit proof => do
    have proof : Q(@IsNat _ instAddMonoidWithOne $e $lit) := proof
    pure ⟨lit.natLit!, q(.ofNat $lit), q(($proof).to_isInt)⟩
  | .isNegNat _ lit proof => pure ⟨-lit.natLit!, q(.negOfNat $lit), proof⟩
  | _ => failure

instance : ToMessageData (Result x) where
  toMessageData
  | .isNat _ lit proof => m!"isNat {lit} ({proof})"
  | .isNegNat _ lit proof => m!"isNegNat {lit} ({proof})"
  | .isRat _ q _ _ proof => m!"isRat {q} ({proof})"

/--
Given a `NormNum.Result e` (which uses `IsNat` or `IsInt` to express equality to an integer
numeral), converts it to an equality `e = Nat.rawCast n` or `e = Int.rawCast n` to a raw cast
expression, so it can be used for rewriting.
-/
def Result.toRawEq {α : Q(Type u)} {e : Q($α)} : Result e → (ℤ × (e' : Q($α)) × Q($e = $e'))
  | .isNat _ lit p => ⟨lit.natLit!, q(Nat.rawCast $lit), q(IsNat.to_raw_eq $p)⟩
  | .isNegNat _ lit p => ⟨-lit.natLit!, q(Int.rawCast (.negOfNat $lit)), q(IsInt.to_raw_eq $p)⟩
  | .isRat _ .. => ⟨0, (default : Expr), (default : Expr)⟩ -- TODO

/-- Constructs a `Result` out of a raw nat cast. Assumes `e` is a raw nat cast expression. -/
def Result.ofRawNat {α : Q(Type u)} (e : Q($α)) : Result e := Id.run do
  let .app (.app _ (sα : Q(AddMonoidWithOne $α))) (lit : Q(ℕ)) := e | panic! "not a raw nat cast"
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
Constructs an `ofNat` application `a'` with the canonical instance, together with a proof that
the instance is equal to the result of `Nat.cast` on the given `AddMonoidWithOne` instance.

This function is performance-critical, as many higher level tactics have to construct numerals.
So rather than using typeclass search we hardcode the (relatively small) set of solutions
to the typeclass problem.
-/
def mkOfNat (α : Q(Type u)) (_sα : Q(AddMonoidWithOne $α)) (lit : Q(ℕ)) :
    MetaM ((a' : Q($α)) × Q($lit = $a')) := do
  if α.isConstOf ``Nat then
    let a' : Q(ℕ) := q(OfNat.ofNat $lit : ℕ)
    pure ⟨a', (q(Eq.refl $a') : Expr)⟩
  else if α.isConstOf ``Int then
    let a' : Q(ℤ) := q(OfNat.ofNat $lit : ℤ)
    pure ⟨a', (q(Eq.refl $a') : Expr)⟩
  else
    let some n := lit.natLit? | failure
    match n with
    | 0 => pure ⟨q(0 : $α), (q(Nat.cast_zero (R := $α)) : Expr)⟩
    | 1 => pure ⟨q(1 : $α), (q(Nat.cast_one (R := $α)) : Expr)⟩
    | k+2 =>
      let k : Q(ℕ) := mkRawNatLit k
      let _x : Q(Nat.AtLeastTwo $lit) :=
        (q(instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (n := $k)) : Expr)
      let a' : Q($α) := q(OfNat.ofNat $lit)
      pure ⟨a', (q(Eq.refl $a') : Expr)⟩

/-- Convert a `Result` to a `Simp.Result`. -/
def Result.toSimpResult {α : Q(Type u)} {e : Q($α)} : Result e → MetaM Simp.Result
  | .isNat sα lit p => do
    let ⟨a', pa'⟩ ← mkOfNat α sα lit
    return { expr := a', proof? := q(IsNat.to_eq $p $pa') }
  | .isNegNat _rα lit p => do
    let ⟨a', pa'⟩ ← mkOfNat α q(AddCommMonoidWithOne.toAddMonoidWithOne) lit
    return { expr := q(-$a'), proof? := q(IsInt.neg_to_eq $p $pa') }
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
abbrev Entry := Array (Array (DiscrTree.Key true)) × Name
/-- Environment extensions for `norm_num` declarations -/
initialize normNumExt : PersistentEnvExtension Entry (Entry × NormNumExt)
    (List Entry × DiscrTree NormNumExt true) ←
  -- we only need this to deduplicate entries in the DiscrTree
  have : BEq NormNumExt := ⟨fun _ _ ↦ false⟩
  let insert kss v dt := kss.foldl (fun dt ks ↦ dt.insertCore ks v) dt
  registerPersistentEnvExtension {
    mkInitial := pure ([], {})
    addImportedFn := fun s ↦ do
      let dt ← s.foldlM (init := {}) fun dt s ↦ s.foldlM (init := dt) fun dt (kss, n) ↦ do
        pure (insert kss (← mkNormNumExt n) dt)
      pure ([], dt)
    addEntryFn := fun (entries, s) ((kss, n), ext) ↦ ((kss, n) :: entries, insert kss ext s)
    exportEntriesFn := fun s ↦ s.1.reverse.toArray
  }

/-- Run each registered `norm_num` extension on an expression, returning a `NormNum.Result`. -/
def derive {α : Q(Type u)} (e : Q($α)) (post := false) : MetaM (Result e) := do
  if e.isNatLit then
    let lit : Q(ℕ) := e
    return .isNat (q(instAddMonoidWithOneNat) : Q(AddMonoidWithOne ℕ))
      lit (q(IsNat.raw_refl $lit) : Expr)
  profileitM Exception "norm_num" (← getOptions) do
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
    MetaM ((_inst : Q(AddMonoidWithOne $α)) × (lit : Q(ℕ)) × Q(IsNat $e $lit)) := do
  let .isNat inst lit proof ← derive e | failure
  pure ⟨inst, lit, proof⟩

/-- Run each registered `norm_num` extension on a typed expression `e : α`,
returning a typed expression `lit : ℕ`, and a proof of `isNat e lit`. -/
def deriveNat {α : Q(Type u)} (e : Q($α))
    (_inst : Q(AddMonoidWithOne $α) := by with_reducible assumption) :
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
  add := fun declName stx kind ↦ match stx with
    | `(attr| norm_num $es,*) => do
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'norm_num', must be global"
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute 'norm_num', declaration is in an imported module"
      if (IR.getSorryDep env declName).isSome then return -- ignore in progress definitions
      let ext ← mkNormNumExt declName
      let keys ← MetaM.run' <| es.getElems.mapM fun stx ↦ do
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
      pre := fun e ↦ do
        Simp.andThen (← Simp.preDefault e discharge) tryNormNum?
      post := fun e ↦ do
        Simp.andThen (← Simp.postDefault e discharge) (tryNormNum? (post := true))
      discharge? := discharge
    } else {
      pre := fun e ↦ Simp.andThen (.visit { expr := e }) tryNormNum?
      post := fun e ↦ Simp.andThen (.visit { expr := e }) (tryNormNum? (post := true))
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
  let toClear := fvarIdsToSimp.filter fun fvarId ↦ !replaced.contains fvarId
  let gNew ← gNew.tryClearMany toClear
  return some (fvarIdsNew, gNew)

open Qq Lean Meta Elab Tactic Term

/-- Constructs a simp context from the simp argument syntax. -/
def getSimpContext (args : Syntax) (simpOnly := false) :
    TacticM Simp.Context := do
  let simpTheorems ←
    if simpOnly then simpOnlyBuiltins.foldlM (·.addConst ·) {} else getSimpTheorems
  let mut { ctx, starArg } ← elabSimpArgs args (eraseLocal := false) (kind := .simp)
    { simpTheorems := #[simpTheorems], congrTheorems := ← getSimpCongrTheorems }
  unless starArg do return ctx
  let mut simpTheorems := ctx.simpTheorems
  for h in ← getPropHyps do
    unless simpTheorems.isErased (.fvar h) do
      simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
  pure { ctx with simpTheorems }

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
  let ctx ← getSimpContext args (!useSimp || simpOnly)
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

/--
Normalize numerical expressions. Supports the operations `+` `-` `*` `/` `^` and `%`
over numerical types such as `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ` and some general algebraic types,
and can prove goals of the form `A = B`, `A ≠ B`, `A < B` and `A ≤ B`, where `A` and `B` are
numerical expressions. It also has a relatively simple primality prover.
-/
elab (name := normNum) "norm_num" only:&" only"? args:(simpArgs ?) loc:(location ?) : tactic =>
  elabNormNum args loc (simpOnly := only.isSome) (useSimp := true)

/-- Basic version of `norm_num` that does not call `simp`. -/
elab (name := normNum1) "norm_num1" loc:(location ?) : tactic =>
  elabNormNum mkNullNode loc (simpOnly := true) (useSimp := false)

open Lean Elab Tactic

@[inherit_doc normNum1] syntax (name := normNum1Conv) "norm_num1" : conv

/-- Elaborator for `norm_num1` conv tactic. -/
@[tactic normNum1Conv] def elabNormNum1Conv : Tactic := fun _ ↦ withMainContext do
  let ctx ← getSimpContext mkNullNode true
  Conv.applySimpResult (← deriveSimp ctx (← instantiateMVars (← Conv.getLhs)) (useSimp := false))

@[inherit_doc normNum] syntax (name := normNumConv) "norm_num" &" only"? (simpArgs)? : conv

/-- Elaborator for `norm_num` conv tactic. -/
@[tactic normNumConv] def elabNormNumConv : Tactic := fun stx ↦ withMainContext do
  let ctx ← getSimpContext stx[2] !stx[1].isNone
  Conv.applySimpResult (← deriveSimp ctx (← instantiateMVars (← Conv.getLhs)) (useSimp := true))

/--
The basic usage is `#norm_num e`, where `e` is an expression,
which will print the `norm_num` form of `e`.

Syntax: `#norm_num` (`only`)? (`[` simp lemma list `]`)? `:`? expression

This accepts the same options as the `#simp` command.
You can specify additional simp lemmas as usual, for example using `#norm_num [f, g] : e`.
(The colon is optional but helpful for the parser.)
The `only` restricts `norm_num` to using only the provided lemmas, and so
`#norm_num only : e` behaves similarly to `norm_num1`.

Unlike `norm_num`, this command does not fail when no simplifications are made.

`#norm_num` understands local variables, so you can use them to introduce parameters.
-/
macro (name := normNumCmd) "#norm_num" o:(&" only")?
    args:(Parser.Tactic.simpArgs)? " :"? ppSpace e:term : command =>
  `(command| #conv norm_num $[only%$o]? $(args)? => $e)
