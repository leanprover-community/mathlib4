/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import SOS.Core
public import Mathlib.Tactic.SOS.Raw
public meta import SOS.Raw
public meta import Lean.Elab.Tactic.Basic
meta import Mathlib.Lean.Expr.Basic

/-!
# Goal reification for `sos`

The reifier walks a Lean expression of shape

    ∀ x : Fin n → ℝ, (g₁ x ⊳ 0) → … → (gₘ x ⊳ 0) → conclusion

and returns a `ParsedGoal` containing both the typed-AST form (`SOS.Poly n`) of every polynomial
encountered and the original `Lean.Expr` for each polynomial side. Both forms are needed by the
elaborator: the AST drives the search and the verifier; the original expression appears in the
user-facing goal and must be matched syntactically by the bridge.

The recognized fragment consists of rational literals, the standard arithmetic constructors
`HAdd`, `HSub`, `HMul`, `HPow` (with a `Nat`-literal exponent), `Neg`, and rational casts into ℝ.
Anything else is opacified as an atom and tracked by index in the running `atoms` array.
-/

public meta section

namespace SOS.Reify

open Lean Meta Elab CPoly

/-- Trace class for the reifier. Enable with
`set_option trace.sos.reify true` to see why a hypothesis or
conclusion failed to reify. The success path is silent. -/
initialize Lean.registerTraceClass `sos.reify

/-! ### Goal classification -/

/-- The three goal shapes the reifier recognises. -/
inductive ShapeKind where
  | closed
  | strict
  | infeasible
  deriving Inhabited, Repr, DecidableEq

/-- Shape of a constraint hypothesis as written by the user. -/
inductive ConstraintKind where
  /-- `h : 0 ≤ origExpr`. -/
  | nonneg
  /-- `h : origExpr ≤ 0`. The reifier negates the polynomial in
  `pTree` so the certified facet is again `0 ≤ pTree`. -/
  | nonpos
  /-- `h : 0 < origExpr`. Promoted to a `.nonneg` facet via
  `le_of_lt h` in the elaborator. -/
  | pos
  /-- `h : a = b`. The reifier records `pTree := reify(a − b)` so the
  certified equality is `aeval x pTree = 0`. The cofactor `qⱼ` enters
  the certificate freely. -/
  | eq
  deriving Inhabited, Repr, DecidableEq

/-! ### Numeric-literal extraction -/

/-- Extract a rational from an `Expr`. -/
-- We could use `NormNum.derive` here, but keep this lightweight syntactic parser for now.
private partial def ratLit? (e : Expr) : MetaM (Option Rat) := do
  let e ← whnfR e
  if let some n := e.numeral? then return some (n : Rat)
  match_expr e with
  | Neg.neg _ _ a =>
    let some r ← ratLit? a | return none
    return some (-r)
  | HDiv.hDiv _ _ _ _ a b =>
    let some ra ← ratLit? a | return none
    let some rb ← ratLit? b | return none
    if rb = 0 then return none
    return some (ra / rb)
  | IntCast.intCast _ _ a =>
    let some r ← ratLit? a | return none
    return some r
  | NatCast.natCast _ _ a =>
    let some r ← ratLit? a | return none
    return some r
  | Int.ofNat a =>
    let some n := a.numeral? | return none
    return some (n : Rat)
  | Int.negSucc a =>
    let some n := a.numeral? | return none
    return some (-(n + 1) : Rat)
  | _ => return none

/-! ### Atom-collection monad

The new design treats the reifier as a `Nat → ℝ`-indexed walker that
accumulates atoms (arbitrary `ℝ`-typed subterms it doesn't recognise
as ring operators or rational literals) into a state array. The
output is a `SOS.Poly.Raw` whose `.var i` references atom `i` in the
final array.

Atom identity uses `withTransparency .reducible` plus pre-normalisation
(`whnfR` + zeta + beta) before the `isDefEq` check, so e.g. `(fun a =>
a) x` collapses with `x` but `f x` and `f y` (distinct FVars) do not. -/

/-- Reifier state: the running atom array. -/
private structure ReifyState where
  /-- The real expressions represented by polynomial variables. -/
  atoms : Array Expr := #[]

/-- Reifier monad: state-tracking over `MetaM`. -/
private abbrev ReifyM := StateRefT ReifyState MetaM

/-- Run a `ReifyM` action against a pre-existing atom array (so atoms
across multiple reifies share indices). -/
private def ReifyM.goWith {α} (atoms : Array Expr) (act : ReifyM α) :
    MetaM (α × Array Expr) := do
  let (a, st) ← StateRefT'.run act ({ atoms } : ReifyState)
  return (a, st.atoms)

/-- Look up `e` in the atom array, deduplicating by `isDefEq` at
`reducible` transparency. Returns the index. -/
private def addAtom (e : Expr) : ReifyM Nat := do
  let st ← get
  -- Normalise the candidate atom for stable deduplication. `whnfR`
  -- handles `reducible` definitions, beta, and zeta-reduction of let
  -- bindings; this is what `ring`'s atom collector does.
  let eNorm ← liftM (m := MetaM) (whnfR e)
  for i in [:st.atoms.size] do
    let a := st.atoms[i]!
    let aNorm ← liftM (m := MetaM) (whnfR a)
    if ← liftM (m := MetaM) (Meta.withTransparency .reducible (Meta.isDefEq eNorm aNorm)) then
      return i
  let n := st.atoms.size
  set { st with atoms := st.atoms.push e }
  return n

/-! ### Raw-AST reifier -/

/-- Walk an `Expr` of type `ℝ`, accumulating atoms and producing an
untyped `SOS.Poly.Raw`. Recognises:

  * Rational literals via `ratLit?`.
  * `HAdd`, `HSub`, `HMul` over ℝ.
  * `HPow` with a `Nat`-literal exponent.
  * `Neg`.

Anything else becomes an atom via `addAtom`. -/
private partial def reifyRaw (e : Expr) : ReifyM SOS.Poly.Raw := do
  let e ← liftM (m := MetaM) (whnfR e)
  if let some r ← liftM (m := MetaM) (ratLit? e) then
    return SOS.Poly.Raw.const r
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b =>
    return SOS.Poly.Raw.add (← reifyRaw a) (← reifyRaw b)
  | HSub.hSub _ _ _ _ a b =>
    return SOS.Poly.Raw.sub (← reifyRaw a) (← reifyRaw b)
  | HMul.hMul _ _ _ _ a b =>
    return SOS.Poly.Raw.mul (← reifyRaw a) (← reifyRaw b)
  | HPow.hPow _ _ _ _ a k =>
    if let some kNat := k.numeral? then
      return SOS.Poly.Raw.pow (← reifyRaw a) kNat
    -- Non-literal exponent: opacify the whole pow expression.
    return SOS.Poly.Raw.var (← addAtom e)
  | Neg.neg _ _ a =>
    return SOS.Poly.Raw.neg (← reifyRaw a)
  | _ =>
    return SOS.Poly.Raw.var (← addAtom e)

/-! ### Atomic parser

The conservative parser operates directly on the main goal:
introducing ∀ binders (when the binder type is ℝ), introducing
constraint hypotheses (when their shape is recognised), and reifying
the conclusion / each constraint into `SOS.Poly.Raw` against a
shared atom array.

Each speculative intro is wrapped in `Tactic.saveState` /
`state.restore`, so a reify failure deeper in the parser doesn't
leave the local context polluted with introduced binders.
-/

/-- One reified constraint hypothesis: the untyped polynomial AST,
the original ℝ-valued side (the `b` in `0 ≤ b`, the `a` in `a ≤ 0`,
the `b` in `0 < b`), the kind, and the hypothesis FVar.

For general `a ≤ b` / `a < b` hypotheses (neither side a `0` literal),
`orig` is the difference `b − a` and `useSubBridge` is `true`,
signalling the elaborator to wrap the FVar with `sub_nonneg_of_le` /
`sub_pos_of_lt` so it lands in the canonical `0 ≤ orig` / `0 < orig`
form expected by the bridge lemmas. -/
structure ConstraintInfo where
  /-- The reified polynomial. -/
  raw : SOS.Poly.Raw
  /-- The original real-valued expression. -/
  orig : Lean.Expr
  /-- The relation represented by this constraint. -/
  kind : ConstraintKind
  /-- The local hypothesis proving the constraint. -/
  fvar : FVarId
  /-- Whether the constraint was normalized by moving its left side to zero. -/
  useSubBridge : Bool := false

/-- Reified conclusion: untyped polynomial AST plus the original
ℝ-valued side of the user's `0 ≤ p` / `0 < p` goal. Bundled together
because they're both present iff the conclusion isn't `False`.

When the user's goal is the general shape `a ≤ b` / `a < b` (rather
than `0 ≤ b` / `0 < b`), the reifier rewrites it as `0 ≤ b − a` /
`0 < b − a`: `orig` is the difference `b − a` and `useSubBridge` is
`true`, signalling to the closing path that it must wrap the recovered
`0 ≤ b − a` / `0 < b − a` proof with `le_of_sub_nonneg` /
`lt_of_sub_pos` to match the user goal. -/
structure ParsedConcl where
  /-- The reified polynomial. -/
  raw : SOS.Poly.Raw
  /-- The original real-valued expression. -/
  orig : Lean.Expr
  /-- Whether the conclusion was normalized by moving its left side to zero. -/
  useSubBridge : Bool := false

/-- Output of `parseGoalAtomic`. The reified polynomials are kept as
untyped `SOS.Poly.Raw`; the elaborator casts them to `SOS.Poly n` at
`n = atoms.size` via `Raw.cast`. -/
structure ParsedGoal where
  /-- Atom Exprs collected from the conclusion and constraints. -/
  atoms : Array Expr
  /-- Coarse shape of the conclusion. -/
  shape       : ShapeKind
  /-- Reified conclusion. `none` iff `shape = .infeasible`. -/
  concl       : Option ParsedConcl
  /-- Reified constraint hypotheses (from intro or from the local
  context). -/
  constraints : Array ConstraintInfo

/-! Atomic parser entry. Steps through the main goal:

  1. If the conclusion matches a recognised shape (`0 ≤ p`, `0 < p`,
     `False`), reify it via `reifyRaw` against the running atom
     array, package, return.
  2. Otherwise, if the conclusion is `Not p` (which is `p → False`
     by definition but isn't unfolded by `whnfR`), `whnf` it and
     re-enter at step 3.
  3. Otherwise, if the conclusion is a non-dependent `g → body` and
     `g` matches a recognised constraint shape that reifies
     cleanly, intro the hypothesis FVar, record
     `(hFVar, kind, rawG)`, recurse.
  4. Otherwise, if the conclusion is `∀ x : ℝ, body`, intro the
     binder and recurse.
  5. Otherwise, restore the saved state and return `none`.

Each speculative intro is wrapped in `Tactic.saveState`; a deeper
reify failure rolls the intros back. -/

/-- Run `reifyRaw e` against `atoms`, returning `none` if it throws.
Hoisted out of `recogniseConstraint` and `parseGoalAtomicAux` (where
it used to be duplicated).

Failure is intentionally swallowed so that an unrecognised hypothesis
just falls through (it might still be a valid local-context fact;
the parser is supposed to be best-effort). The exception is logged
under `trace.sos.reify` for when "best effort" hides a real bug. -/
private def tryReify (e : Expr) (atoms : Array Expr) :
    Tactic.TacticM (Option (SOS.Poly.Raw × Array Expr)) := do
  try
    let (raw, atoms') ← (reifyRaw e).goWith atoms
    return some (raw, atoms')
  catch ex =>
    trace[sos.reify] "tryReify({e}) failed: {ex.toMessageData}"
    return none

/-- Try to recognise a hypothesis Expr as a constraint of one of the
supported shapes (`0 ≤ b`, `a ≤ 0`, `0 < b`, general `a ≤ b` /
`a < b`, ℝ-valued `a = b`). Returns the ConstraintKind, the reified
polynomial, the original ℝ-typed Expr, a `useSubBridge` flag (true
iff the hypothesis is general `a ≤ b` / `a < b` and the elaborator
must wrap the FVar with `sub_nonneg.mpr` / `sub_pos.mpr` to land in
the canonical `0 ≤ orig` / `0 < orig` form), and the updated atom
array. -/
private def recogniseConstraint (h : Expr) (atoms : Array Expr) :
    Tactic.TacticM (Option
      (ConstraintKind × SOS.Poly.Raw × Lean.Expr × Bool × Array Expr)) := do
  let h ← whnfR h
  match_expr h with
  | LE.le _ _ a b =>
    -- Fast path: `0 ≤ b` and `a ≤ 0` with a literal `0` on the named
    -- side avoid a redundant subtraction.
    if let some r ← ratLit? a then
      if r = 0 then
        let some (raw, atoms') ← tryReify b atoms | return none
        return some (.nonneg, raw, b, false, atoms')
    if let some r ← ratLit? b then
      if r = 0 then
        let some (raw, atoms') ← tryReify a atoms | return none
        return some (.nonpos, .neg raw, a, false, atoms')
    -- General `a ≤ b`: reify `b − a` and use the sub-bridge so the
    -- canonical fact is `0 ≤ b − a`.
    let diff ← Meta.mkAppM ``HSub.hSub #[b, a]
    let some (raw, atoms') ← tryReify diff atoms | return none
    return some (.nonneg, raw, diff, true, atoms')
  | LT.lt _ _ a b =>
    if let some r ← ratLit? a then
      if r = 0 then
        let some (raw, atoms') ← tryReify b atoms | return none
        return some (.pos, raw, b, false, atoms')
    -- General `a < b`: reify `b − a` and use the sub-bridge.
    let diff ← Meta.mkAppM ``HSub.hSub #[b, a]
    let some (raw, atoms') ← tryReify diff atoms | return none
    return some (.pos, raw, diff, true, atoms')
  | Eq α a b =>
    -- Only ℝ-valued equalities count as constraints. Equalities at
    -- other types are not in the supported fragment.
    unless (← Meta.isDefEq α (Lean.mkConst ``Real)) do return none
    -- Reify `a − b` so the certified equality is `aeval x pTree = 0`.
    -- The `orig` field stores the difference `a − b`; downstream the
    -- bridge proves `evalReal x pTree = a − b` and combines with
    -- `h : a = b` (`sub_eq_zero_of_eq`) to get `a − b = 0`.
    let abDiff ← Meta.mkAppM ``HSub.hSub #[a, b]
    let some (raw, atoms') ← tryReify abDiff atoms | return none
    return some (.eq, raw, abDiff, false, atoms')
  | _ => return none

/-- Reify the current goal, introducing supported leading hypotheses as needed. -/
private partial def parseGoalAtomicAux
    (atoms : Array Expr) (constraints : Array ConstraintInfo) :
    Tactic.TacticM (Option ParsedGoal) := Tactic.withMainContext do
  let mv ← Tactic.getMainGoal
  let goalType ← mv.getType >>= instantiateMVars
  -- Step 1: try a recognised-conclusion match first.
  if let some out ← tryReifyConclusion goalType atoms constraints then
    return some out
  -- Step 2 / 3: descend into ∀ or →.
  let goalType' ← whnfR goalType
  -- `Not p` (= `p → False`) isn't unfolded by whnfR; recognise it explicitly.
  if let .app (.const ``Not _) _ := goalType' then
    -- Reduce by hand to `p → False`, then re-enter the parser.
    let unfolded ← Meta.whnf goalType'
    if let .forallE _ _ _ _ := unfolded then
      if let some out ← tryConstraintIntro unfolded atoms constraints then
        return some out
    return none
  if let .forallE _ binderType body _ := goalType' then
    if !body.hasLooseBVars then
      return ← tryConstraintIntro goalType' atoms constraints
    if (← Meta.isDefEq binderType (Lean.mkConst ``Real)) then
      let st ← Tactic.saveState
      let (_, mv') ← mv.intro1
      Tactic.replaceMainGoal [mv']
      match ← parseGoalAtomicAux atoms constraints with
      | some out => return some out
      | none => st.restore; return none
  return none
where
  /-- Try to match the goal against a recognised conclusion shape.
  Reifies via `reifyRaw` against the running `atoms`. -/
  tryReifyConclusion (goalType : Expr) (atoms : Array Expr)
      (constraints : Array ConstraintInfo) :
      Tactic.TacticM (Option ParsedGoal) := do
    let goalType ← whnfR goalType
    match_expr goalType with
    | LE.le α _ a b =>
      -- Only ℝ-valued inequalities are in the supported fragment;
      -- the lift pre-pass converts ℕ/ℤ/Rat goals before we get here.
      unless (← Meta.isDefEq α (Lean.mkConst ``Real)) do return none
      -- Fast path: `0 ≤ b` matches the canonical reified form directly.
      if let some r ← ratLit? a then
        if r = 0 then
          let some (raw, atoms') ← tryReify b atoms | return none
          return some
            { atoms := atoms', shape := .closed,
              concl := some { raw, orig := b }, constraints }
      -- General `a ≤ b`: reify `b − a` and use the sub-bridge.
      let diff ← Meta.mkAppM ``HSub.hSub #[b, a]
      let some (raw, atoms') ← tryReify diff atoms | return none
      return some
        { atoms := atoms', shape := .closed,
          concl := some { raw, orig := diff, useSubBridge := true },
          constraints }
    | LT.lt α _ a b =>
      unless (← Meta.isDefEq α (Lean.mkConst ``Real)) do return none
      if let some r ← ratLit? a then
        if r = 0 then
          let some (raw, atoms') ← tryReify b atoms | return none
          return some
            { atoms := atoms', shape := .strict,
              concl := some { raw, orig := b }, constraints }
      let diff ← Meta.mkAppM ``HSub.hSub #[b, a]
      let some (raw, atoms') ← tryReify diff atoms | return none
      return some
        { atoms := atoms', shape := .strict,
          concl := some { raw, orig := diff, useSubBridge := true },
          constraints }
    | False =>
      return some
        { atoms, shape := .infeasible, concl := none, constraints }
    | _ => return none
  /-- Try to recognise `g → body` and recurse. The hypothesis must
  reify cleanly under the current atom set; otherwise we restore. -/
  tryConstraintIntro (goalType : Expr) (atoms : Array Expr)
      (constraints : Array ConstraintInfo) :
      Tactic.TacticM (Option ParsedGoal) := do
    let .forallE _ hypType body _ := goalType | return none
    unless !body.hasLooseBVars do return none
    let some (kind, rawG, origG, useSubBridge, atoms') ←
      recogniseConstraint hypType atoms | return none
    let st ← Tactic.saveState
    let mv ← Tactic.getMainGoal
    let (hFV, mv') ← mv.intro `h
    Tactic.replaceMainGoal [mv']
    let info : ConstraintInfo :=
      { raw := rawG, orig := origG, kind, fvar := hFV, useSubBridge }
    match ← parseGoalAtomicAux atoms' (constraints.push info) with
    | some out => return some out
    | none => st.restore; return none

/-- Scan the local context for hypothesis FVars matching a constraint
shape, and merge them into `pg`. Skips FVars already recorded in
`pg.constraints` (intro'd by the iterative parser) and FVars whose
type isn't `Prop`. -/
private def mergeLocalCtxConstraints (pg : ParsedGoal) :
    Tactic.TacticM ParsedGoal := Tactic.withMainContext do
  let mut atoms := pg.atoms
  let mut constraints := pg.constraints
  let known : Std.HashSet FVarId := constraints.foldl (·.insert ·.fvar) {}
  let lctx ← Lean.getLCtx
  for ldecl in lctx do
    if ldecl.isImplementationDetail then continue
    if known.contains ldecl.fvarId then continue
    let ty ← Lean.Meta.inferType ldecl.type
    unless ty.isProp do continue
    if let some (kind, rawG, origG, useSubBridge, atoms') ←
        recogniseConstraint ldecl.type atoms then
      atoms := atoms'
      constraints := constraints.push
        { raw := rawG, orig := origG, kind, fvar := ldecl.fvarId, useSubBridge }
  return { pg with atoms, constraints }

/-- Top-level entry. Intros all parseable ∀-binders and constraint
hypotheses, scans the local context for additional constraint
hypotheses, then returns the parsed goal. Returns `none` if the
conclusion isn't in the supported fragment. -/
def parseGoalAtomic : Tactic.TacticM (Option ParsedGoal) := do
  let st ← Tactic.saveState
  match ← parseGoalAtomicAux #[] #[] with
  | some out => return some (← mergeLocalCtxConstraints out)
  | none => st.restore; return none

end SOS.Reify
