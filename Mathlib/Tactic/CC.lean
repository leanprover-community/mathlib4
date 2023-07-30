/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Init.CCLemmas
import Mathlib.Data.Option.Defs
import Mathlib.Init.Propext

#align_import init.meta.smt.congruence_closure from "leanprover-community/lean"@"9eae65f7144bcc692858b9dadf2e48181f4270b9"

/-!
## Congruence closures
-/

universe u

open Lean Meta Elab Tactic Parser.Tactic Std

syntax (name := Lean.Parser.Tactic.cc) "cc" : tactic

namespace Mathlib.Tactic.CC

initialize
  registerTraceClass `Meta.Tactic.cc.merge
  registerTraceClass `Meta.Tactic.cc.failure
  registerTraceClass `Debug.Meta.Tactic.cc
  registerTraceClass `Debug.Meta.Tactic.cc.ac
  registerTraceClass `Debug.Meta.Tactic.cc.parentOccs


def isNum : Expr → Bool
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal _))) _ => true
  | .lit (.natVal _) => true
  | _ => false

def toNat : Expr → Option Nat
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ => some n
  | .lit (.natVal n) => some n
  | _ => none

def toInt : Expr → Option Int
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ => some n
  | .lit (.natVal n) => some n
  | .app (.app (.app (.const ``Neg.neg _) _) _) r =>
    match toNat r with
    | some n => some (-n)
    | none => none
  | _ => none

def isSignedNum (e : Expr) : Bool :=
  if isNum e then true
  else if let .app (.app (.app (.const ``Neg.neg _) _) _) r := e then isNum r
  else false

/-- Return true if `e` represents a value (numeral, character, or string). -/
def isValue (e : Expr) : Bool :=
  isSignedNum e || e.isCharLit || e.isStringLit

private def getAppAppsAux : Expr → Array Expr → Nat → Array Expr
  | .app f a, as, i => getAppAppsAux f (as.set! i (.app f a)) (i-1)
  | _,       as, _ => as

/-- Given `f a b c`, return `#[f a, f a b, f a b c]`.
    Remark: this procedure is very similar to `getAppArgs`. -/
@[inline]
def getAppApps (e : Expr) : Array Expr :=
  let dummy := mkSort levelZero
  let nargs := e.getAppNumArgs
  getAppAppsAux e (mkArray nargs dummy) (nargs-1)

/-- Determines whether two expressions are definitionally equal to each other without any mvar
    assignments. -/
@[inline]
def pureIsDefEq (e₁ e₂ : Expr) : MetaM Bool :=
  withNewMCtxDepth <| isDefEq e₁ e₂

/-- Return true if `e` represents a value (nat/int numereal, character, or string). -/
def isInterpretedValue (e : Expr) : MetaM Bool := do
  if e.isCharLit || e.isStringLit then
    return true
  else if isSignedNum e then
    let type ← inferType e
    pureIsDefEq type (.const ``Nat []) <||> pureIsDefEq type (.const ``Int [])
  else
    return false

/-- Similar to `mkAppM n #[lhs, rhs]`, but handles `Eq` and `Iff` more efficiently. -/
def mkRel (n : Name) (lhs rhs : Expr) : MetaM Expr :=
  if n == ``Eq then
    mkEq lhs rhs
  else if n == ``Iff then
    return mkApp2 (.const ``Iff []) lhs rhs
  else
    mkAppM n #[lhs, rhs]

/-- Given a reflexive relation `R`, and a proof `H : a = b`, build a proof for `R a b` -/
def liftFromEq (R : Name) (H : Expr) : MetaM Expr := do
  if R == ``Eq then return H
  let HType ← whnf (← inferType H)
  -- `HType : @Eq A a _`
  let some (A, a, _) := HType.eq?
    | throwError "failed to build lift_of_eq equality proof expected: {H}"
  let motive ←
    withLocalDeclD `x A fun x => do
      let hType ← mkEq a x
      withLocalDeclD `h hType fun h =>
        mkRel R a x >>= mkLambdaFVars #[x, h]
  let minor ← do
    let mt ← mkRel R a a
    let m ← mkFreshExprSyntheticOpaqueMVar mt
    m.mvarId!.rfl
    instantiateMVars m
  mkEqRec motive minor H

/-- Ordering on `Expr`. -/
local instance : Ord Expr where
  compare a b := if Expr.lt a b then .lt else if Expr.eqv b a then .eq else .gt

def reduceProjStruct? (e : Expr) : MetaM (Option Expr) :=
  e.withApp fun cfn args => do
    let some cname := cfn.constName? | return none
    let some pinfo ← getProjectionFnInfo? cname | return none
    if ha : args.size = pinfo.numParams + 1 then
      let sarg := args[pinfo.numParams]'(ha ▸ pinfo.numParams.lt_succ_self)
      sarg.withApp fun sc sfds => do
        unless sc.constName? = some pinfo.ctorName do
          return none
        let sidx := pinfo.numParams + pinfo.i
        if hs : sidx < sfds.size then
          return some (sfds[sidx]'hs)
        else
          throwError
            (m!"ill-formed expression, {sc} is the {pinfo.i}-th projection function" ++
              m!" but {sarg} has not enough arguments")
    else
      return none

/-- Given `(hNotEx : Not (@Exists.{lvl} A p))`,
    return a `forall x, Not (p x)` and a proof for it.

    This function handles nested existentials. -/
partial def toForallNotAux (lvl : Level) (A p hNotEx : Expr) : MetaM (Expr × Expr) := do
  let xn ← mkFreshUserName `x
  withLocalDeclD xn A fun x => do
    let px := p.beta #[x]
    let notPx := mkNot px
    let hAllNotPx := mkApp3 (.const ``forall_not_of_not_exists [lvl]) A p hNotEx
    if let .app (.app (.const ``Exists [lvl']) A') p' := px then
      let hNotPxN ← mkFreshUserName `h
      withLocalDeclD hNotPxN notPx fun hNotPx => do
        let (qx, hQx) ← toForallNotAux lvl' A' p' hNotPx
        let allQx ← mkForallFVars #[x] qx
        let hNotPxImpQx ← mkLambdaFVars #[hNotPx] hQx
        let hAllQx ← mkLambdaFVars #[x] (.app hNotPxImpQx (.app hAllNotPx x))
        return (allQx, hAllQx)
    else
      let allNotPx ← mkForallFVars #[x] notPx
      return (allNotPx, hAllNotPx)

/-- Given `(hNotEx : Not ex)` where `ex` is of the form `Exists x, p x`,
    return a `forall x, Not (p x)` and a proof for it.

    This function handles nested existentials. -/
def toForallNot (ex hNotEx : Expr) : MetaM (Expr × Expr) := do
  let .app (.app (.const ``Exists [lvl]) A) p := ex | failure
  toForallNotAux lvl A p hNotEx

def isReflRelation (e : Expr) : MetaM (Option (Name × Expr × Expr)) := do
  if let some (_, lhs, rhs) := e.eq? then
    return (``Eq, lhs, rhs)
  if let some (lhs, rhs) := e.iff? then
    return (``Iff, lhs, rhs)
  if let some (_, lhs, _, rhs) := e.heq? then
    return (``HEq, lhs, rhs)
  if let .app (.app rel lhs) rhs := e then
    unless (← (Mathlib.Tactic.reflExt.getState (← getEnv)).getMatch rel).isEmpty do
      match rel.getAppFn.constName? with
      | some n => return some (n, lhs, rhs)
      | none => return none
  return none

def isSymmRelation (e : Expr) : MetaM (Option (Name × Expr × Expr)) := do
  if let some (_, lhs, rhs) := e.eq? then
    return (``Eq, lhs, rhs)
  if let some (lhs, rhs) := e.iff? then
    return (``Iff, lhs, rhs)
  if let some (_, lhs, _, rhs) := e.heq? then
    return (``HEq, lhs, rhs)
  if let .app (.app rel lhs) rhs := e then
    unless (← (Mathlib.Tactic.symmExt.getState (← getEnv)).getMatch rel).isEmpty do
      match rel.getAppFn.constName? with
      | some n => return some (n, lhs, rhs)
      | none => return none
  return none

abbrev RBExprMap (α : Type u) := Std.RBMap Expr α compare

abbrev RBExprSet := Std.RBSet Expr compare

structure ExtCongrTheorem where
  /-- The basic `CongrTheorem` object defined at `Lean.Meta.CongrTheorems` -/
  congrTheorem : CongrTheorem
  /-- If `heqResult` is true, then lemma is based on heterogeneous equality
      and the conclusion is a heterogeneous equality. -/
  heqResult : Bool := false
  /-- If `hcongrTheorem` is true, then lemma was created using `mkHCongrWithArity`. -/
  hcongrTheorem : Bool := false

/-- Automatically generated congruence lemma based on heterogeneous equality. -/
def mkExtHCongrWithArity (fn : Expr) (nargs : Nat) :
    MetaM (Option ExtCongrTheorem) := do
  let eqCongr ← try mkHCongrWithArity fn nargs catch _ => return none
  let type := eqCongr.type
  forallTelescope type fun _ type => do
    guard (type.isEq || type.isHEq)
    let res₁ : ExtCongrTheorem :=
      { congrTheorem := eqCongr
        heqResult := type.isHEq
        hcongrTheorem := true }
    return some res₁

structure ExtCongrTheoremKey where
  fn : Expr
  nargs : Nat
  deriving BEq, Hashable

abbrev ExtCongrTheoremCache := Std.HashMap ExtCongrTheoremKey (Option ExtCongrTheorem)

def isNot : Expr → Bool × Expr
  | .app (.const ``Not []) a => (true, a)
  | .forallE _ a (.const ``False []) _ => (true, a)
  | e => (false, e)

def isNotOrNe : Expr → Bool × Expr
  | .app (.const ``Not []) a => (true, a)
  | .forallE _ a (.const ``False []) _ => (true, a)
  | .app (.app (.app (.const ``Ne [u]) α) lhs) rhs =>
    (true, .app (.app (.app (.const ``Eq [u]) α) lhs) rhs)
  | e => (false, e)

structure CCConfig where
  /-- If `true`, congruence closure will treat implicit instance arguments as constants. -/
  ignoreInstances : Bool := true
  /-- If `true`, congruence closure modulo AC. -/
  ac : Bool := true
  /-- If `hoFns` is `some fns`, then full (and more expensive) support for higher-order functions is
     *only* considered for the functions in fns and local functions. The performance overhead is
     described in the paper "Congruence Closure in Intensional Type Theory". If `hoFns` is `none`,
     then full support is provided for *all* constants. -/
  hoFns : Option (List Name) := none
  /-- If `true`, then use excluded middle -/
  em : Bool := true
  /-- If `true`, we treat values as atomic symbols -/
  values : Bool := true
  deriving Inhabited
#align cc_config Mathlib.Tactic.CC.CCConfig

inductive ACApp where
  | ofExpr : Expr → ACApp
  | app (op : Expr) (args : Array Expr) : ACApp
  deriving Inhabited, BEq

instance : Coe Expr ACApp := ⟨ACApp.ofExpr⟩

/-- Ordering on `ACApp`. -/
local instance : Ord ACApp where
  compare a b :=
  match a, b with
    | .ofExpr a, .ofExpr b => compare a b
    | .ofExpr _, .app _ _ => .lt
    | .app _ _, .ofExpr _ => .gt
    | .app op₁ args₁, .app op₂ args₂ =>
      compare op₁ op₂ |>.then <| compare args₁.size args₂.size |>.then <| Id.run do
        for i in [:args₁.size] do
          let o := compare args₁[i]! args₂[i]!
          if o != .eq then return o
        return .eq

/-- Return true iff `e₁` is a "subset" of `e₂`.
    Example: The result is `true` for `e₁ := a*a*a*b*d` and `e₂ := a*a*a*a*b*b*c*d*d` -/
def ACApp.isSubset : (e₁ e₂ : ACApp) → Bool
  | .ofExpr a, .ofExpr b => a == b
  | .ofExpr a, .app _ args => args.contains a
  | .app _ _, .ofExpr _ => false
  | .app op₁ args₁, .app op₂ args₂ =>
    if op₁ == op₂ then
      if args₁.size ≤ args₂.size then Id.run do
        let mut i₁ := 0
        let mut i₂ := 0
        while i₁ < args₁.size ∧ i₂ < args₂.size do
          if args₁[i₁]! == args₂[i₂]! then
            i₁ := i₁ + 1
            i₂ := i₂ + 1
          else if Expr.lt args₂[i₂]! args₁[i₁]! then
            i₂ := i₂ + 1
          else return false
        return i₁ == args₁.size
      else false
    else false

/-- Store in `r` `e₁ \ e₂`.
    Example: given `e₁ := a*a*a*a*b*b*c*d*d*d` and `e₂ := a*a*a*b*b*d`,
    the result is `#[a, c, d, d]`

    Precondition: `e₂.isSubset e₁` -/
def ACApp.diff (e₁ e₂ : ACApp) (r : Array Expr) : Array Expr :=
  match e₁ with
  | .app op₁ args₁ => Id.run do
    let mut r := r
    match e₂ with
    | .app op₂ args₂ =>
      if op₁ == op₂ then
        let mut i₂ := 0
        for i₁ in [:args₁.size] do
          if i₂ == args₂.size then
            r := r.push args₁[i₁]!
          else if args₁[i₁]! == args₂[i₂]! then
            i₂ := i₂ + 1
          else
            r := r.push args₁[i₁]!
    | .ofExpr e₂ =>
      let mut found := false
      for i in [:args₁.size] do
        if !found && args₁[i]! == e₂ then
          found := true
        else
          r := r.push args₁[i]!
    return r
  | .ofExpr _ => r

def ACApp.append (op : Expr) (e : ACApp) (r : Array Expr) : Array Expr :=
  match e with
  | .app op' args =>
    if op' == op then r ++ args else r
  | .ofExpr e =>
    r.push e

def ACApp.intersection (e₁ e₂ : ACApp) (r : Array Expr) : Array Expr :=
  match e₁, e₂ with
  | .app _ args₁, .app _ args₂ => Id.run do
    let mut r := r
    let mut i₁ := 0
    let mut i₂ := 0
    while i₁ < args₁.size ∧ i₂ < args₂.size do
      if args₁[i₁]! == args₂[i₂]! then
        r := r.push args₁[i₁]!
        i₁ := i₁ + 1
        i₂ := i₂ + 1
      else if Expr.lt args₂[i₂]! args₁[i₁]! then
        i₂ := i₂ + 1
      else
        i₁ := i₁ + 1
    return r
  | _, _ => r

def ACApp.mkApp (op : Expr) (args : Array Expr) : ACApp :=
  .app op (args.qsort Expr.lt)

def ACApp.mkFlatApp (op : Expr) (e₁ e₂ : ACApp) : ACApp :=
  let newArgs := ACApp.append op e₁ #[]
  let newArgs := ACApp.append op e₂ newArgs
  ACApp.mkApp op newArgs

def ACApp.toExpr : ACApp → Option Expr
  | .app _ ⟨[]⟩ => none
  | .app op ⟨arg₀ :: args⟩ => some <| args.foldl (fun e arg => mkApp2 op e arg) arg₀
  | .ofExpr e => some e

abbrev RBACAppSet := Std.RBSet ACApp compare

abbrev RBACAppMap (α : Type u) := Std.RBMap ACApp α compare

inductive DelayedExpr where
  | ofExpr : Expr → DelayedExpr
  | eqProof (lhs rhs : Expr) : DelayedExpr
  | congrArg (f : Expr) (h : DelayedExpr) : DelayedExpr
  | congrFun (h : DelayedExpr) (a : ACApp) : DelayedExpr
  | eqSymm (h : DelayedExpr) : DelayedExpr
  | eqSymmOpt (a₁ a₂ : ACApp) (h : DelayedExpr) : DelayedExpr
  | eqTrans (h₁ h₂ : DelayedExpr) : DelayedExpr
  | eqTransOpt (a₁ a₂ a₃ : ACApp) (h₁ h₂ : DelayedExpr) : DelayedExpr
  | heqOfEq (h : DelayedExpr) : DelayedExpr
  | heqSymm (h : DelayedExpr) : DelayedExpr
  deriving Inhabited

instance : Coe Expr DelayedExpr := ⟨DelayedExpr.ofExpr⟩

inductive EntryExpr
  | ofExpr : Expr → EntryExpr
  /-- dummy congruence proof, it is just a placeholder. -/
  | congr : EntryExpr
  /-- dummy eq_true proof, it is just a placeholder -/
  | eqTrue : EntryExpr
  /-- dummy refl proof, it is just a placeholder. -/
  | refl : EntryExpr
  | ofDExpr : DelayedExpr → EntryExpr
  deriving Inhabited

instance : ToMessageData EntryExpr where
  toMessageData
  | .ofExpr e => toMessageData e
  | .congr => m!"[congruence proof]"
  | .eqTrue => m!"[eq_true proof]"
  | .refl => m!"[refl proof]"
  | .ofDExpr _ => m!"[delayed expression]"

instance : Coe Expr EntryExpr := ⟨EntryExpr.ofExpr⟩

/-- Equivalence class data associated with an expression `e` -/
structure Entry where
  /-- next element in the equivalence class. -/
  next : Expr
  /-- root (aka canonical) representative of the equivalence class. -/
  root : Expr
  /-- root of the congruence class, it is meaningless if `e` is not an application. -/
  cgRoot : Expr
  /-- When `e` was added to this equivalence class because of an equality `(H : e = tgt)`, then
      we store `tgt` at `target`, and `H` at `proof`. Both fields are none if `e == root` -/
  target : Option Expr := none
  /-- When `e` was added to this equivalence class because of an equality `(H : e = tgt)`, then
      we store `tgt` at `target`, and `H` at `proof`. Both fields are none if `e == root` -/
  proof : Option EntryExpr := none
  /-- Variable in the AC theory. -/
  acVar : Option Expr := none
  /-- proof has been flipped -/
  flipped : Bool
  /-- `true` if the node should be viewed as an abstract value -/
  interpreted : Bool
  /-- `true` if head symbol is a constructor -/
  constructor : Bool
  /-- `true` if equivalence class contains lambda expressions -/
  hasLambdas : Bool
  /-- `heqProofs == true` iff some proofs in the equivalence class are based on heterogeneous
      equality. We represent equality and heterogeneous equality in a single equivalence class. -/
  heqProofs : Bool
  /-- If `fo == true`, then the expression associated with this entry is an application, and we are
      using first-order approximation to encode it. That is, we ignore its partial applications. -/
  fo : Bool
  /-- number of elements in the equivalence class, it is meaningless if `e != root` -/
  size : Nat
  /-- The field `mt` is used to implement the mod-time optimization introduce by the Simplify
      theorem prover. The basic idea is to introduce a counter gmt that records the number of
      heuristic instantiation that have occurred in the current branch. It is incremented after each
      round of heuristic instantiation. The field `mt` records the last time any proper descendant
      of of thie entry was involved in a merge. -/
  mt : Nat
  generation : Nat
  deriving Inhabited

abbrev Entries := RBExprMap Entry

structure ACOccurrences where
  occs : RBACAppSet := ∅
  size : Nat := 0
  deriving Inhabited

def ACOccurrences.insert (aco : ACOccurrences) (e : ACApp) : ACOccurrences :=
  { occs := aco.occs.insert e
    size := aco.size + 1 }

def ACOccurrences.erase (aco : ACOccurrences) (e : ACApp) : ACOccurrences :=
  if aco.occs.contains e then
    { occs := aco.occs.erase (compare e)
      size := aco.size - 1 }
  else aco

instance : ForIn m ACOccurrences ACApp where
  forIn o := forIn o.occs

structure ACEntry where
  idx : Nat
  RLHSOccs : ACOccurrences := {}
  RRHSOccs : ACOccurrences := {}
  deriving Inhabited

@[inline] def ACEntry.ROccs (ent : ACEntry) : (inLHS : Bool) → ACOccurrences
  | true => ent.RLHSOccs
  | false => ent.RRHSOccs

structure ParentOcc where
  expr : Expr
  /-- If `symmTable` is true, then we should use the `symmCongruences`, otherwise `congruences`.
      Remark: this information is redundant, it can be inferred from `expr`. We use store it for
      performance reasons. -/
  symmTable : Bool

abbrev ParentOccSet := Std.RBSet ParentOcc (byKey ParentOcc.expr compare)

abbrev Parents := RBExprMap ParentOccSet

inductive CongruencesKey
  | fo (fn : Expr) (args : Array Expr) : CongruencesKey
  | ho (fn : Expr) (arg : Expr) : CongruencesKey
  deriving BEq, Hashable

abbrev Congruences := Std.HashMap CongruencesKey (List Expr)

structure SymmCongruencesKey where
  (h₁ h₂ : Expr)
  deriving BEq, Hashable

abbrev SymmCongruences := Std.HashMap SymmCongruencesKey (List (Expr × Name))

abbrev SubsingletonReprs := RBExprMap Expr

/-- Stores the root representatives of `.instImplicit` arguments. -/
abbrev InstImplicitReprs := RBExprMap (List Expr)

abbrev TodoEntry := Expr × Expr × EntryExpr × Bool

abbrev ACTodoEntry := ACApp × ACApp × DelayedExpr

/-- Congruence closure state.
This may be considered to be a set of expressions and an equivalence class over this set.
The equivalence class is generated by the equational rules that are added to the `CCState` and
congruence, that is, if `a = b` then `f(a) = f(b)` and so on. -/
structure CCState where
  entries : Entries := ∅
  parents : Parents := ∅
  congruences : Congruences := ∅
  symmCongruences : SymmCongruences := ∅
  subsingletonReprs : SubsingletonReprs := ∅
  /-- Stores the root representatives of `.instImplicit` arguments. -/
  instImplicitReprs : InstImplicitReprs := ∅
  /-- The congruence closure module has a mode where the root of each equivalence class is marked as
      an interpreted/abstract value. Moreover, in this mode proof production is disabled.
      This capability is useful for heuristic instantiation. -/
  frozePartitions : Bool := false
  /-- Mapping from operators occurring in terms and their canonical
      representation in this module -/
  canOps : RBExprMap Expr := ∅
  /-- Whether the canonical operator is suppoted by AC. -/
  opInfo : RBExprMap Bool := ∅
  nextACIdx : Nat := 0
  acEntries : RBExprMap ACEntry := ∅
  acR : RBACAppMap (ACApp × DelayedExpr) := ∅
  /-- Returns true if the `CCState` is inconsistent. For example if it had both `a = b` and `a ≠ b`
      in it.-/
  inconsistent : Bool := false
  /-- "Global Modification Time". gmt is a number stored on the `CCState`,
      it is compared with the modification time of a cc_entry in e-matching. See `CCState.mt`. -/
  gmt : Nat := 0
  config : CCConfig
  deriving Inhabited
#align cc_state Mathlib.Tactic.CC.CCState
#align cc_state.inconsistent Mathlib.Tactic.CC.CCState.inconsistent
#align cc_state.gmt Mathlib.Tactic.CC.CCState.gmt

def CCState.mkEntryCore (ccs : CCState) (e : Expr) (interpreted : Bool) (constructor : Bool)
    (gen : Nat) : CCState :=
  assert! ccs.entries.find? e |>.isNone
  let n : Entry :=
    { next := e
      root := e
      cgRoot := e
      size := 1
      flipped := false
      interpreted
      constructor
      hasLambdas := e.isLambda
      heqProofs := false
      mt := ccs.gmt
      fo := false
      generation := gen }
  { ccs with entries := ccs.entries.insert e n }

namespace CCState

/-- Get the root representative of the given expression. -/
def root (ccs : CCState) (e : Expr) : Expr :=
  match ccs.entries.find? e with
  | some n => n.root
  | none => e
#align cc_state.root Mathlib.Tactic.CC.CCState.root

/-- Get the next element in the equivalence class.
Note that if the given `Expr` `e` is not in the graph then it will just return `e`. -/
def next (ccs : CCState) (e : Expr) : Expr :=
  match ccs.entries.find? e with
  | some n => n.next
  | none => e
#align cc_state.next Mathlib.Tactic.CC.CCState.next

/-- Check if `e` is the root of the congruence class. -/
def isCgRoot (ccs : CCState) (e : Expr) : Bool :=
  match ccs.entries.find? e with
  | some n => e == n.cgRoot
  | none => true
#align cc_state.is_cg_root Mathlib.Tactic.CC.CCState.isCgRoot

/--
"Modification Time". The field `mt` is used to implement the mod-time optimization introduce by the
Simplify theorem prover. The basic idea is to introduce a counter `gmt` that records the number of
heuristic instantiation that have occurred in the current branch. It is incremented after each round
of heuristic instantiation. The field `mt` records the last time any proper descendant of of thie
entry was involved in a merge. -/
def mt (ccs : CCState) (e : Expr) : Nat :=
  match ccs.entries.find? e with
  | some n => n.mt
  | none => ccs.gmt
#align cc_state.mt Mathlib.Tactic.CC.CCState.mt

def inSingletonEqc (ccs : CCState) (e : Expr) : Bool :=
  match ccs.entries.find? e with
  | some it => it.next == e
  | none => true
#align cc_state.in_singlenton_eqc Mathlib.Tactic.CC.CCState.inSingletonEqc

def getRoots (ccs : CCState) (roots : Array Expr) (nonsingletonOnly : Bool) : Array Expr :=
  Id.run do
    let mut roots := roots
    for (k, n) in ccs.entries do
      if k == n.root && (!nonsingletonOnly || !ccs.inSingletonEqc k) then
        roots := roots.push k
    return roots

def checkEqc (ccs : CCState) (e : Expr) : Bool :=
  toBool <| Id.run <| OptionT.run do
    let root := ccs.root e
    let mut size : Nat := 0
    let mut it := e
    repeat
      let some itN := ccs.entries.find? it | failure
      guard (itN.root == root)
      let mut it₂ := it
      -- following `target` fields should lead to root
      repeat
        let it₂N := ccs.entries.find? it₂
        match it₂N.bind Entry.target with
        | some it₃ => it₂ := it₃
        | none => break
      guard (it₂ == root)
      it := itN.next
      size := size + 1
    until it == e
    guard (ccs.entries.find? root |>.any (·.size == size))

def checkInvariant (ccs : CCState) : Bool :=
  ccs.entries.all fun k n => k != n.root || checkEqc ccs k

def getNumROccs (ccs : CCState) (e : Expr) (inLHS : Bool) : Nat :=
  match ccs.acEntries.find? e with
  | some ent => (ent.ROccs inLHS).size
  | none => 0

def getVarWithLeastOccs (ccs : CCState) (e : ACApp) (inLHS : Bool) : Option Expr :=
  match e with
  | .app _ args => Id.run do
    let mut r := args[0]?
    let mut numOccs := r.casesOn 0 fun r' => ccs.getNumROccs r' inLHS
    for hi : i in [1:args.size] do
      if (args[i]'hi.2) != (args[i - 1]'(Nat.lt_of_le_of_lt (i.sub_le 1) hi.2)) then
        let currOccs := ccs.getNumROccs (args[i]'hi.2) inLHS
        if currOccs < numOccs then
          r := (args[i]'hi.2)
          numOccs := currOccs
    return r
  | .ofExpr e => e

def getVarWithLeastLHSOccs (ccs : CCState) (e : ACApp) : Option Expr :=
  ccs.getVarWithLeastOccs e true

def getVarWithLeastRHSOccs (ccs : CCState) (e : ACApp) : Option Expr :=
  ccs.getVarWithLeastOccs e false

open MessageData

/-- Pretty print the entry associated with the given expression. -/
def ppEqc (ccs : CCState) (e : Expr) : MessageData := Id.run do
  let mut lr : List MessageData := []
  let mut it := e
  repeat
    let some itN := ccs.entries.find? it | break
    let mdIt : MessageData :=
      if it.isForall || it.isLambda || it.isLet then paren (ofExpr it) else ofExpr it
    lr := mdIt :: lr
    it := itN.next
  until it == e
  let l := lr.reverse
  return bracket "{" (group <| joinSep l (ofFormat ("," ++ .line))) "}"
#align cc_state.pp_eqc Mathlib.Tactic.CC.CCState.ppEqc

/-- Pretty print the entire cc graph.
If the `nonSingleton` argument is set to `true` then singleton equivalence classes will be
omitted. -/
def ppEqcs (ccs : CCState) (nonSingleton : Bool := true) : MessageData :=
  let roots := ccs.getRoots #[] nonSingleton
  let a := roots.map (fun root => ccs.ppEqc root)
  let l := a.toList
  bracket "{" (group <| joinSep l (ofFormat ("," ++ .line))) "}"
#align cc_state.pp_core Mathlib.Tactic.CC.CCState.ppEqcs

def ppParentOccsAux (ccs : CCState) (e : Expr) : MessageData :=
  match ccs.parents.find? e with
  | some poccs =>
    let r := ofExpr e ++ ofFormat (.line ++ ":=" ++ .line)
    let ps := poccs.toList.map fun o => ofExpr o.expr
    group (r ++ bracket "{" (group <| joinSep ps (ofFormat ("," ++ .line))) "}")
  | none => ofFormat .nil

def ppParentOccs (ccs : CCState) : MessageData :=
  let r := ccs.parents.toList.map fun (k, _) => ccs.ppParentOccsAux k
  bracket "{" (group <| joinSep r (ofFormat ("," ++ .line))) "}"

def ppACDecl (ccs : CCState) (e : Expr) : MessageData :=
  match ccs.acEntries.find? e with
  | some it => group (ofFormat (s!"x_{it.idx}" ++ .line ++ ":=" ++ .line) ++ ofExpr e)
  | none => nil

def ppACDecls (ccs : CCState) : MessageData :=
  let r := ccs.acEntries.toList.map fun (k, _) => ccs.ppACDecl k
  bracket "{" (joinSep r (ofFormat ("," ++ .line))) "}"

def ppACExpr (ccs : CCState) (e : Expr) : MessageData :=
  if let some it := ccs.acEntries.find? e then
    s!"x_{it.idx}"
  else
    ofExpr e

partial def ppACApp (ccs : CCState) : ACApp → MessageData
  | .app op args =>
    let r := ofExpr op :: args.toList.map fun arg => ccs.ppACExpr arg
    sbracket (joinSep r (ofFormat .line))
  | .ofExpr e => ccs.ppACExpr e

def ppACR (ccs : CCState) : MessageData :=
  let r := ccs.acR.toList.map fun (k, p, _) => group <|
    ccs.ppACApp k ++ ofFormat (Format.line ++ "--> ") ++ nest 4 (Format.line ++ ccs.ppACApp p)
  bracket "{" (joinSep r (ofFormat ("," ++ .line))) "}"

def ppAC (ccs : CCState) : MessageData :=
  sbracket (ccs.ppACDecls ++ ofFormat ("," ++ .line) ++ ccs.ppACR)

end CCState

/-- The congruence closure module (optionally) uses a normalizer.
    The idea is to use it (if available) to normalize auxiliary expressions
    produced by internal propagation rules (e.g., subsingleton propagator).  -/
structure CCNormalizer where
  normalize : Expr → MetaM Expr

structure CCPropagationHandler where
  propagated : Array Expr → MetaM Unit
  /-- Congruence closure module invokes the following method when
      a new auxiliary term is created during propagation. -/
  newAuxCCTerm : Expr → MetaM Unit

structure CCStructure where
  state : CCState
  todo : Array TodoEntry := #[]
  acTodo : Array ACTodoEntry := #[]
  normalizer : Option CCNormalizer := none
  phandler : Option CCPropagationHandler := none
  cache : ExtCongrTheoremCache := ∅
  deriving Inhabited

abbrev CCM := StateRefT CCStructure MetaM

namespace CCM

@[inline]
def run {α : Type} (x : CCM α) (c : CCStructure) : MetaM (α × CCStructure) := StateRefT'.run x c

@[inline]
def modifyState (f : CCState → CCState) : CCM Unit :=
  modify fun cc => { cc with state := f cc.state }

@[inline]
def modifyTodo (f : Array TodoEntry → Array TodoEntry) : CCM Unit :=
  modify fun cc => { cc with todo := f cc.todo }

@[inline]
def modifyACTodo (f : Array ACTodoEntry → Array ACTodoEntry) : CCM Unit :=
  modify fun cc => { cc with acTodo := f cc.acTodo }

@[inline]
def modifyCache (f : ExtCongrTheoremCache → ExtCongrTheoremCache) : CCM Unit :=
  modify fun cc => { cc with cache := f cc.cache }

@[inline]
def getState : CCM CCState := do
  return (← get).state

@[inline]
def getTodo : CCM (Array TodoEntry) := do
  return (← get).todo

@[inline]
def getACTodo : CCM (Array ACTodoEntry) := do
  return (← get).acTodo

@[inline]
def getCache : CCM ExtCongrTheoremCache := do
  return (← get).cache

def getEntry (e : Expr) : CCM (Option Entry) := do
  return (← getState).entries.find? e

def getGenerationOf (e : Expr) : CCM Nat := do
  if let some it ← getEntry e then
    return it.generation
  else
    return 0

def normalize (e : Expr) : CCM Expr := do
  if let some normalizer := (← get).normalizer then
    normalizer.normalize e
  else
    return e

def pushTodo (lhs rhs : Expr) (H : EntryExpr) (heqProof : Bool) : CCM Unit := do
  modifyTodo fun todo => todo.push (lhs, rhs, H, heqProof)

def pushEq (lhs rhs : Expr) (H : EntryExpr) : CCM Unit :=
  modifyTodo fun todo => todo.push (lhs, rhs, H, false)

def pushHEq (lhs rhs : Expr) (H : EntryExpr) : CCM Unit :=
  modifyTodo fun todo => todo.push (lhs, rhs, H, true)

def pushReflEq (lhs rhs : Expr) : CCM Unit :=
  modifyTodo fun todo => todo.push (lhs, rhs, .refl, false)

def getRoot (e : Expr) : CCM Expr := do
  return (← getState).root e

def isCgRoot (e : Expr) : CCM Bool := do
  return (← getState).isCgRoot e

def addOccurrence (parent child : Expr) (symmTable : Bool) : CCM Unit := do
  let childRoot ← getRoot child
  modifyState fun ccs =>
    { ccs with
      parents := ccs.parents.alter childRoot fun ps? =>
        let ps := ps?.getD ∅
        ps.insert { expr := parent, symmTable } }

/--
Return true iff the given function application are congruent

See paper: Congruence Closure for Intensional Type Theory. -/
partial def isCongruent (e₁ e₂ : Expr) : CCM Bool := do
  let .app f a := e₁ | failure
  let .app g b := e₂ | failure
  if (← getEntry e₁).any Entry.fo then
    e₁.withApp fun f₁ args₁ =>
    e₂.withApp fun f₂ args₂ => do
      if ha : args₁.size = args₂.size then
        for hi : i in [:args₁.size] do
          if (← getRoot (args₁[i]'hi.2)) != (← getRoot (args₂[i]'(ha.symm ▸ hi.2))) then
            return false
        if f₁ == f₂ then return true
        else if (← getRoot f₁) != (← getRoot f₂) then
          -- `f₁` and `f₂` are not equivalent
          return false
        else if ← pureIsDefEq (← inferType f₁) (← inferType f₂) then
          return true
        else return false
      else return false
  else
    -- Given `e₁ := f a`, `e₂ := g b`
    if (← getRoot a) != (← getRoot b) then
      -- `a` and `b` are not equivalent
      return false
    else if (← getRoot f) != (← getRoot g) then
      -- `f` and `g` are not equivalent
      return false
    else if ← pureIsDefEq (← inferType f) (← inferType g) then
      /- Case 1: `f` and `g` have the same type, then we can create a congruence proof for
         `HEq (f a) (g b)` -/
      return true
    else if f.isApp && g.isApp then
      -- Case 2: `f` and `g` are congruent
      isCongruent f g
    else
      /-
      f and g are not congruent nor they have the same type.
      We can't generate a congruence proof in this case because the following lemma
        `hcongr : HEq f₁ f₂ → HEq a₁ a₂ → HEq (f₁ a₁) (f₂ a₂)`
      is not provable.
      Remark: it is also not provable in MLTT, Coq and Agda (even if we assume UIP).
      -/
      return false

def mkCongruencesKey (e : Expr) : CCM CongruencesKey := do
  let .app f a := e | failure
  if (← getEntry e).any Entry.fo then
    -- first-order case, where we do not consider all partial applications
    e.withApp fun fn args => do
      return .fo (← getRoot fn) (← args.mapM getRoot)
  else
    return .ho (← getRoot f) (← getRoot a)

def mkSymmCongruencesKey (lhs rhs : Expr) : CCM SymmCongruencesKey := do
  let lhs ← getRoot lhs
  let rhs ← getRoot rhs
  if hash lhs > hash rhs then return { h₁ := rhs, h₂ := lhs } else return { h₁ := lhs, h₂ := rhs }

def mkExtCongrTheorem (e : Expr) : CCM (Option ExtCongrTheorem) := do
  let fn := e.getAppFn
  let nargs := e.getAppNumArgs
  let cache ← getCache

  -- Check if `{ fn, nargs }` is in the cache
  let key₁ : ExtCongrTheoremKey := { fn, nargs }
  if let some it₁ := cache.findEntry? key₁ then
    return it₁.2

  -- Try automatically generated congruence lemma with support for heterogeneous equality.
  let lemm ← mkExtHCongrWithArity fn nargs

  if let some lemm := lemm then
    modifyCache fun ccc => ccc.insert key₁ (some lemm)
    return lemm

  -- cache failure
  modifyCache fun ccc => ccc.insert key₁ none
  return none

def mkExtHCongrTheorem (fn : Expr) (nargs : Nat) : CCM (Option ExtCongrTheorem) := do
  let cache ← getCache

  -- Check if `{ fn, nargs }` is in the cache
  let key₁ : ExtCongrTheoremKey := { fn, nargs }
  if let some it₁ := cache.findEntry? key₁ then
    return it₁.2

  -- Try automatically generated congruence lemma with support for heterogeneous equality.
  let lemm ← mkExtHCongrWithArity fn nargs

  if let some lemm := lemm then
    modifyCache fun ccc => ccc.insert key₁ (some lemm)
    return lemm

  -- cache failure
  modifyCache fun ccc => ccc.insert key₁ none
  return none

def propagateInstImplicit (e : Expr) : CCM Unit := do
  let type ← inferType e
  let type ← normalize type
  match (← getState).instImplicitReprs.find? type with
  | some l =>
    for e' in l do
      if ← pureIsDefEq e e' then
        pushReflEq e e'
        return
    modifyState fun ccs =>
      { ccs with instImplicitReprs := ccs.instImplicitReprs.insert type (e :: l) }
  | none =>
    modifyState fun ccs =>
      { ccs with instImplicitReprs := ccs.instImplicitReprs.insert type [e] }

def setFO (e : Expr) : CCM Unit := do
  modifyState fun ccs =>
    { ccs with entries := ccs.entries.modify e fun d => { d with fo := true } }

partial def updateMT (e : Expr) : CCM Unit := do
  let r ← getRoot e
  let some ps := (← getState).parents.find? r | return
  for p in ps do
    let some it ← getEntry p.expr | failure
    let gmt := (← getState).gmt
    if it.mt < gmt then
      let newIt := { it with mt := gmt }
      modifyState fun ccs =>
        { ccs with entries := ccs.entries.insert p.expr newIt }
      updateMT p.expr

def hasHEqProofs (root : Expr) : CCM Bool := do
  let some n ← getEntry root | failure
  guard (n.root == root)
  return n.heqProofs

def flipProofCore (H : Expr) (flipped heqProofs : Bool) : CCM Expr := do
  let mut newH := H
  if ← liftM <| pure heqProofs <&&> Expr.isEq <$> (inferType H >>= whnf) then
    newH ← mkAppM ``heq_of_eq #[H]
  if !flipped then
    return newH
  else if heqProofs then
    mkHEqSymm newH
  else
    mkEqSymm newH

def flipDelayedProofCore (H : DelayedExpr) (flipped heqProofs : Bool) : CCM DelayedExpr := do
  let mut newH := H
  if heqProofs then
    newH := .heqOfEq H
  if !flipped then
    return newH
  else if heqProofs then
    return .heqSymm newH
  else
    return .eqSymm newH

def flipProof (H : EntryExpr) (flipped heqProofs : Bool) : CCM EntryExpr :=
  match H with
  | .ofExpr H => EntryExpr.ofExpr <$> flipProofCore H flipped heqProofs
  | .ofDExpr H => EntryExpr.ofDExpr <$> flipDelayedProofCore H flipped heqProofs
  | _ => return H

def isEqv (e₁ e₂ : Expr) : CCM Bool := do
  let some n₁ ← getEntry e₁ | return false
  let some n₂ ← getEntry e₂ | return false
  return n₁.root == n₂.root

def isNotEqv (e₁ e₂ : Expr) : CCM Bool := do
  let tmp ← mkEq e₁ e₂
  if ← isEqv tmp (.const ``False []) then return true
  let tmp ← mkHEq e₁ e₂
  isEqv tmp (.const ``False [])

def isEqTrue (e : Expr) : CCM Bool :=
  isEqv e (.const ``True [])

def isEqFalse (e : Expr) : CCM Bool :=
  isEqv e (.const ``False [])

def mkTrans (H₁ H₂ : Expr) (heqProofs : Bool) : MetaM Expr :=
  if heqProofs then mkHEqTrans H₁ H₂ else mkEqTrans H₁ H₂

def mkTransOpt (H₁? : Option Expr) (H₂ : Expr) (heqProofs : Bool) : MetaM Expr :=
  match H₁? with
  | some H₁ => mkTrans H₁ H₂ heqProofs
  | none => pure H₂

mutual
partial def mkCongrProofCore (lhs rhs : Expr) (heqProofs : Bool) : CCM Expr := do
  let mut lhsArgsRev : Array Expr := #[]
  let mut rhsArgsRev : Array Expr := #[]
  let mut lhsIt := lhs
  let mut rhsIt := rhs
  if lhs != rhs then
    repeat
      let .app lhsItFn lhsItArg := lhsIt | failure
      let .app rhsItFn rhsItArg := rhsIt | failure
      lhsArgsRev := lhsArgsRev.push lhsItArg
      rhsArgsRev := rhsArgsRev.push rhsItArg
      lhsIt := lhsItFn
      rhsIt := rhsItFn
      if lhsIt == rhsIt then
        break
      if ← pureIsDefEq lhsIt rhsIt then
        break
      if ← isEqv lhsIt rhsIt <&&>
          inferType lhsIt >>= fun i₁ => inferType rhsIt >>= fun i₂ => pureIsDefEq i₁ i₂ then
        break
  if lhsArgsRev.isEmpty then
    if heqProofs then
      return (← mkHEqRefl lhs)
    else
      return (← mkEqRefl lhs)
  let lhsArgs := lhsArgsRev.reverse
  let rhsArgs := rhsArgsRev.reverse
  let PLift.up ha ← if ha : lhsArgs.size = rhsArgs.size then pure (PLift.up ha) else failure
  let lhsFn := lhsIt
  let rhsFn := rhsIt
  guard (← isEqv lhsFn rhsFn <||> pureIsDefEq lhsFn rhsFn)
  guard (← pureIsDefEq (← inferType lhsFn) (← inferType rhsFn))
  /- Create proof for
        `lhsFn lhsArgs[0] ... lhsArgs[n-1] = lhsFn rhsArgs[0] ... rhsArgs[n-1]`
     where
        `n := lhsArgs.size` -/
  let some specLemma ← mkExtHCongrTheorem lhsFn lhsArgs.size | failure
  let mut kindsIt := specLemma.congrTheorem.argKinds
  let mut lemmaArgs : Array Expr := #[]
  for hi : i in [:lhsArgs.size] do
    guard !kindsIt.isEmpty
    lemmaArgs := lemmaArgs.push (lhsArgs[i]'hi.2) |>.push (rhsArgs[i]'(ha.symm ▸ hi.2))
    if kindsIt[0]! matches CongrArgKind.heq then
      let some p ← getHEqProof (lhsArgs[i]'hi.2) (rhsArgs[i]'(ha.symm ▸ hi.2)) | failure
      lemmaArgs := lemmaArgs.push p
    else
      guard (kindsIt[0]! matches .eq)
      let some p ← getEqProof (lhsArgs[i]'hi.2) (rhsArgs[i]'(ha.symm ▸ hi.2)) | failure
      lemmaArgs := lemmaArgs.push p
    kindsIt := kindsIt.eraseIdx 0
  let mut r := mkAppN specLemma.congrTheorem.proof lemmaArgs
  if specLemma.heqResult && !heqProofs then
    r ← mkAppM ``eq_of_heq #[r]
  else if !specLemma.heqResult && heqProofs then
    r ← mkAppM ``heq_of_eq #[r]
  if ← pureIsDefEq lhsFn rhsFn then
    return r
  /- Convert `r` into a proof of `lhs = rhs` using `Eq.rec` and
     the proof that `lhsFn = rhsFn` -/
  let some lhsFnEqRhsFn ← getEqProof lhsFn rhsFn | failure
  let motive ←
    withLocalDeclD `x (← inferType lhsFn) fun x => do
      let motiveRhs := mkAppN x rhsArgs
      let motive ← if heqProofs then mkHEq lhs motiveRhs else mkEq lhs motiveRhs
      let hType ← mkEq lhsFn x
      withLocalDeclD `h hType fun h =>
        mkLambdaFVars #[x, h] motive
  mkEqRec motive r lhsFnEqRhsFn

partial def mkSymmCongrProof (e₁ e₂ : Expr) (heqProofs : Bool) : CCM (Option Expr) := do
  let some (R₁, lhs₁, rhs₁) ← isSymmRelation e₁ | return none
  let some (R₂, lhs₂, rhs₂) ← isSymmRelation e₂ | return none
  if R₁ != R₂ then return none
  if !(← isEqv lhs₁ lhs₂) then
    guard (← isEqv lhs₁ rhs₂)
    /- We must apply symmetry.
       The symm congruence table is implicitly using symmetry.
       That is, we have
         `e₁ := lhs₁ ~R₁~ rhs₁`
       and
         `e2 := lhs₂ ~R₁~ rhs₂`
       But,
       `lhs₁ ~R₁~ rhs₂` and `rhs₁ ~R₁~ lhs₂` -/
    /- Given `e₁ := lhs₁ ~R₁~ rhs₁`,
       create proof for
         `lhs₁ ~R₁~ rhs₁` = `rhs₁ ~R₁~ lhs₁` -/
    let newE₁ ← mkRel R₁ rhs₁ lhs₁
    let e₁IffNewE₁ ←
      withLocalDeclD `h₁ e₁ fun h₁ =>
      withLocalDeclD `h₂ newE₁ fun h₂ => do
        mkAppM ``Iff.intro #[← mkLambdaFVars #[h₁] (← h₁.symm), ← mkLambdaFVars #[h₂] (← h₂.symm)]
    let mut e₁EqNewE₁ := mkApp3 (.const ``propext []) e₁ newE₁ e₁IffNewE₁
    let newE₁EqE₂ ← mkCongrProofCore newE₁ e₂ heqProofs
    if heqProofs then
      e₁EqNewE₁ ← mkAppM ``heq_of_eq #[e₁EqNewE₁]
    return some (← mkTrans e₁EqNewE₁ newE₁EqE₂ heqProofs)
  return none

partial def mkCongrProof (e₁ e₂ : Expr) (heqProofs : Bool) : CCM Expr := do
  if let some r ← mkSymmCongrProof e₁ e₂ heqProofs then
    return r
  else
    mkCongrProofCore e₁ e₂ heqProofs

partial def mkDelayedProof (H : DelayedExpr) : CCM Expr := do
  match H with
  | .ofExpr H => return H
  | .eqProof lhs rhs => liftOption (← getEqProof lhs rhs)
  | .congrArg f h => mkCongrArg f (← mkDelayedProof h)
  | .congrFun h a => mkCongrFun (← mkDelayedProof h) (← liftOption a.toExpr)
  | .eqSymm h => mkEqSymm (← mkDelayedProof h)
  | .eqSymmOpt a₁ a₂ h =>
    mkAppOptM ``Eq.symm #[none, ← liftOption a₁.toExpr, ← liftOption a₂.toExpr, ← mkDelayedProof h]
  | .eqTrans h₁ h₂ => mkEqTrans (← mkDelayedProof h₁) (← mkDelayedProof h₂)
  | .eqTransOpt a₁ a₂ a₃ h₁ h₂ =>
    mkAppOptM ``Eq.trans
      #[none, ← liftOption a₁.toExpr, ← liftOption a₂.toExpr, ← liftOption a₃.toExpr,
        ← mkDelayedProof h₁, ← mkDelayedProof h₂]
  | .heqOfEq h => mkAppM ``heq_of_eq #[← mkDelayedProof h]
  | .heqSymm h => mkHEqSymm (← mkDelayedProof h)

partial def mkProof (lhs rhs : Expr) (H : EntryExpr) (heqProofs : Bool) : CCM Expr := do
  match H with
  | .congr => mkCongrProof lhs rhs heqProofs
  | .eqTrue =>
    let (flip, some (R, a, b)) ←
      if lhs == .const ``True [] then
        ((true, ·)) <$> isReflRelation rhs
      else
        ((false, ·)) <$> isReflRelation lhs
      | failure
    let aRb ←
      if R == ``Eq then
        getEqProof a b >>= liftOption
      else if R == ``HEq then
        getHEqProof a b >>= liftOption
      else
        -- TODO(Leo): the following code assumes R is homogeneous.
        -- We should add support arbitrary heterogenous reflexive relations.
        getEqProof a b >>= liftOption >>= fun aEqb => liftM (liftFromEq R aEqb)
    let aRbEqTrue ← mkEqTrue aRb
    if flip then
      mkEqSymm aRbEqTrue
    else
      return aRbEqTrue
  | .refl =>
    let type ← if heqProofs then mkHEq lhs rhs else mkEq lhs rhs
    let proof ← if heqProofs then mkHEqRefl lhs else mkEqRefl lhs
    mkExpectedTypeHint proof type
  | .ofExpr H => return H
  | .ofDExpr H => mkDelayedProof H

/--
If `asHEq` is `true`, then build a proof for `HEq e₁ e₂`.
Otherwise, build a proof for `e₁ = e₂`.
The result is `none` if `e₁` and `e₂` are not in the same equivalence class. -/
partial def getEqProofCore (e₁ e₂ : Expr) (asHEq : Bool) : CCM (Option Expr) := do
  if e₁.hasExprMVar || e₂.hasExprMVar then return none
  if ← pureIsDefEq e₁ e₂ then
    if asHEq then
      return some (← mkHEqRefl e₁)
    else
      return some (← mkEqRefl e₁)
  let some n₁ ← getEntry e₁ | return none
  let some n₂ ← getEntry e₂ | return none
  if n₁.root != n₂.root then return none
  let heqProofs ← hasHEqProofs n₁.root
  -- 1. Retrieve "path" from `e₁` to `root`
  let mut path₁ : Array Expr := #[]
  let mut Hs₁ : Array EntryExpr := #[]
  let mut visited : RBExprSet := ∅
  let mut it₁ := e₁
  repeat
    visited := visited.insert it₁
    let some it₁N ← getEntry it₁ | failure
    let some t := it₁N.target | break
    path₁ := path₁.push t
    let some p := it₁N.proof | failure
    Hs₁ := Hs₁.push (← flipProof p it₁N.flipped heqProofs)
    it₁ := t
  guard (it₁ == n₁.root)
  -- 2. The path from `e₂` to root must have at least one element `c` in visited
  -- Retrieve "path" from `e₂` to `c`
  let mut path₂ : Array Expr := #[]
  let mut Hs₂ : Array EntryExpr := #[]
  let mut it₂ := e₂
  repeat
    if visited.contains it₂ then
      break -- found common
    let some it₂N ← getEntry it₂ | failure
    let some t := it₂N.target | failure
    path₂ := path₂.push it₂
    let some p := it₂N.proof | failure
    Hs₂ := Hs₂.push (← flipProof p (!it₂N.flipped) heqProofs)
    it₂ := t
  -- `it₂` is the common element...
  -- 3. Shrink `path₁`/`Hs₁` until we find `it₂` (the common element)
  repeat
    if path₁.isEmpty then
      guard (it₂ == e₁)
      break
    if path₁.back == it₂ then
      -- found it!
      break
    path₁ := path₁.pop
    Hs₁ := Hs₁.pop

  -- 4. Build transitivity proof
  let mut pr? : Option Expr := none
  let mut lhs := e₁
  for i in [:path₁.size] do
    pr? ← some <$> mkTransOpt pr? (← mkProof lhs path₁[i]! Hs₁[i]! heqProofs) heqProofs
    lhs := path₁[i]!
  let mut i := Hs₂.size
  while i > 0 do
    i := i - 1
    pr? ← some <$> mkTransOpt pr? (← mkProof lhs path₂[i]! Hs₂[i]! heqProofs) heqProofs
    lhs := path₂[i]!
  let mut some pr := pr? | failure
  if heqProofs && !asHEq then
    pr ← mkAppM ``eq_of_heq #[pr]
  else if !heqProofs && asHEq then
    pr ← mkAppM ``heq_of_eq #[pr]
  return pr

partial def getEqProof (e₁ e₂ : Expr) : CCM (Option Expr) :=
  getEqProofCore e₁ e₂ false

partial def getHEqProof (e₁ e₂ : Expr) : CCM (Option Expr) :=
  getEqProofCore e₁ e₂ true
end

def getEqTrueProof (e : Expr) : CCM Expr := do
  guard (← isEqTrue e)
  let some p ← getEqProof e (.const ``True []) | failure
  return p

def getEqFalseProof (e : Expr) : CCM Expr := do
  guard (← isEqFalse e)
  let some p ← getEqProof e (.const ``False []) | failure
  return p

def getPropEqProof (a b : Expr) : CCM Expr := do
  guard (← isEqv a b)
  let some p ← getEqProof a b | failure
  return p

def getInconsistencyProof : CCM (Option Expr) := do
  guard !(← getState).frozePartitions
  if let some p ← getEqProof (.const ``True []) (.const ``False []) then
    return some (← mkAppM ``false_of_true_eq_false #[p])
  else
    return none

/-- Auxiliary function for comparing `lhs₁ ~ rhs₁` and `lhs₂ ~ rhs₂`,
    when `~` is symmetric/commutative.
    It returns true (equal) for `a ~ b` `b ~ a`-/
def compareSymmAux (lhs₁ rhs₁ lhs₂ rhs₂ : Expr) : CCM Bool := do
  let lhs₁ ← getRoot lhs₁
  let rhs₁ ← getRoot rhs₁
  let lhs₂ ← getRoot lhs₂
  let rhs₂ ← getRoot rhs₂
  let (lhs₁, rhs₁) := if rhs₁.lt lhs₁ then (rhs₁, lhs₁) else (lhs₁, rhs₁)
  let (lhs₂, rhs₂) := if rhs₂.lt lhs₂ then (rhs₂, lhs₂) else (lhs₂, rhs₂)
  return lhs₁ == lhs₂ && rhs₁ == rhs₂

def compareSymm (k₁ k₂ : Expr × Name) : CCM Bool := do
  if k₁.2 != k₂.2 then return false
  let e₁ := k₁.1
  let e₂ := k₂.1
  if k₁.2 == ``Eq || k₁.2 == ``Iff then
    compareSymmAux e₁.appFn!.appArg! e₁.appArg! e₂.appFn!.appArg! e₂.appArg!
  else
    let some (_, lhs₁, rhs₁) ← isSymmRelation e₁ | failure
    let some (_, lhs₂, rhs₂) ← isSymmRelation e₂ | failure
    compareSymmAux lhs₁ rhs₁ lhs₂ rhs₂

def checkEqTrue (e : Expr) : CCM Unit := do
  let some (_, lhs, rhs) ← isReflRelation e | return
  if ← isEqv e (.const ``True []) then return -- it is already equivalent to `True`
  let lhsR ← getRoot lhs
  let rhsR ← getRoot rhs
  if lhsR != rhsR then return
  -- Add `e = True`
  pushEq e (.const ``True []) .eqTrue

def addCongruenceTable (e : Expr) : CCM Unit := do
  guard e.isApp
  let k ← mkCongruencesKey e
  if let some es := (← getState).congruences.find? k then
    for oldE in es do
      if ← isCongruent e oldE then
        -- Found new equivalence: `e ~ oldE`
        -- 1. Update `cgRoot` field for `e`
        let some currEntry ← getEntry e | failure
        let newEntry := { currEntry with cgRoot := oldE }
        modifyState fun ccs => { ccs with entries := ccs.entries.insert e newEntry }
        -- 2. Put new equivalence in the todo queue
        -- TODO(Leo): check if the following line is a bottleneck
        let heqProof ← (!·) <$> pureIsDefEq (← inferType e) (← inferType oldE)
        pushTodo e oldE .congr heqProof
        return
    modifyState fun ccs =>
      { ccs with congruences := ccs.congruences.insert k (e :: es) }
  else
    modifyState fun ccs =>
      { ccs with congruences := ccs.congruences.insert k [e] }

def addSymmCongruenceTable (e : Expr) : CCM Unit := do
  let some (rel, lhs, rhs) ← isSymmRelation e | failure
  let k ← mkSymmCongruencesKey lhs rhs
  let newP := (e, rel)
  if let some ps := (← getState).symmCongruences.find? k then
    for p in ps do
      if ← compareSymm newP p then
        -- Found new equivalence: `e ~ p.1`
        -- 1. Update `cgRoot` field for `e`
        let some currEntry ← getEntry e | failure
        let newEntry := { currEntry with cgRoot := p.1 }
        modifyState fun ccs => { ccs with entries := ccs.entries.insert e newEntry }
        -- 2. Put new equivalence in the TODO queue
        -- NOTE(gabriel): support for symmetric relations is pretty much broken,
        -- since it ignores all arguments except the last two ones.
        -- e.g. this would claim that `ModEq n a b` and `ModEq m a b` are equivalent.
        -- Whitelist some relations to contain breakage:
        if rel == ``Eq || e.getAppNumArgs == 2 then
          pushEq e p.1 .congr
        checkEqTrue e
        return
    modifyState fun ccs =>
      { ccs with symmCongruences := ccs.symmCongruences.insert k (newP :: ps) }
    checkEqTrue e
  else
    modifyState fun ccs =>
      { ccs with symmCongruences := ccs.symmCongruences.insert k [newP] }
    checkEqTrue e

def pushSubsingletonEq (a b : Expr) : CCM Unit := do
  -- Remark: we must use normalize here because we have use it before
  -- internalizing the types of `a` and `b`.
  let A ← normalize (← inferType a)
  let B ← normalize (← inferType b)
  -- TODO(Leo): check if the following test is a performance bottleneck
  if ← pureIsDefEq A B then
    -- TODO(Leo): to improve performance we can create the following proof lazily
    let proof ← mkAppM ``Subsingleton.elim #[a, b]
    pushEq a b proof
  else
    let some AEqB ← getEqProof A B | failure
    let proof ← mkAppM ``Subsingleton.helim #[AEqB, a, b]
    pushHEq a b proof

def checkNewSubsingletonEq (oldRoot newRoot : Expr) : CCM Unit := do
  guard (← isEqv oldRoot newRoot)
  guard ((← getRoot oldRoot) == newRoot)
  let some it₁ := (← getState).subsingletonReprs.find? oldRoot | return
  if let some it₂ := (← getState).subsingletonReprs.find? newRoot then
    pushSubsingletonEq it₁ it₂
  else
    modifyState fun ccs =>
      { ccs with subsingletonReprs := ccs.subsingletonReprs.insert newRoot it₁ }

def getEqcLambdas (e : Expr) (r : Array Expr) : CCM (Array Expr) := do
  guard ((← getRoot e) == e)
  let mut r := r
  let some ee ← getEntry e | failure
  unless ee.hasLambdas do return r
  let mut it := e
  repeat
    if it.isLambda then
      r := r.push it
    let some itN ← getEntry it | failure
    it := itN.next
  until it == e
  return r

def propagateBeta (fn : Expr) (revArgs : Array Expr) (lambdas newLambdaApps : Array Expr) :
    CCM (Array Expr) := do
  let mut newLambdaApps := newLambdaApps
  for lambda in lambdas do
    guard lambda.isLambda
    if fn != lambda then
      if ← pureIsDefEq (← inferType fn) (← inferType lambda) then
        let newApp := mkAppRev lambda revArgs
        newLambdaApps := newLambdaApps.push newApp
  return newLambdaApps

def mkNeOfEqOfNe (a a₁ a₁NeB : Expr) : CCM (Option Expr) := do
  guard (← isEqv a a₁)
  if a == a₁ then
    return some a₁NeB
  let aEqA₁ ← getEqProof a a₁
  match aEqA₁ with
  | none => return none -- failed to build proof
  | some aEqA₁ => mkAppM ``ne_of_eq_of_ne #[aEqA₁, a₁NeB]

def mkNeOfNeOfEq (aNeB₁ b₁ b : Expr) : CCM (Option Expr) := do
  guard (← isEqv b b₁)
  if b == b₁ then
    return some aNeB₁
  let b₁EqB ← getEqProof b b₁
  match b₁EqB with
  | none => return none -- failed to build proof
  | some b₁EqB => mkAppM ``ne_of_ne_of_eq #[aNeB₁, b₁EqB]

def isAC (e : Expr) : CCM (Option Expr) := do
  let .app (.app op _) _ := e | return none
  let ccs ← getState
  if let some cop := ccs.canOps.find? op then
    let some b := ccs.opInfo.find? cop
      | throwError "opInfo should contain all canonical operators in canOps"
    return bif b then some cop else none
  for (cop, b) in ccs.opInfo do
    if ← pureIsDefEq op cop then
      modifyState fun _ => { ccs with canOps := ccs.canOps.insert op cop }
      return bif b then some cop else none
  let b ←
    try
      let aop ← mkAppM ``Lean.IsAssociative #[op]
      let some _ ← synthInstance? aop | failure
      let cop ← mkAppM ``Lean.IsCommutative #[op]
      let some _ ← synthInstance? cop | failure
      pure true
    catch _ =>
      pure false
  modifyState fun _ =>
    { ccs with
      canOps := ccs.canOps.insert op op
      opInfo := ccs.opInfo.insert op b }
  return bif b then some op else none

open MessageData in
def dbgTraceACEq (header : String) (lhs rhs : ACApp) : CCM Unit := do
  let ccs ← getState
  trace[Debug.Meta.Tactic.cc.ac]
    group (ofFormat (header ++ .line) ++ ccs.ppACApp lhs ++
      ofFormat (.line ++ "=" ++ .line) ++ ccs.ppACApp rhs)

open MessageData in
def dbgTraceACState : CCM Unit := do
  let ccs ← getState
  trace[Debug.Meta.Tactic.cc.ac] group ("state: " ++ nest 6 ccs.ppAC)

def mkACProof (e₁ e₂ : Expr) : MetaM Expr := do
  let eq ← mkEq e₁ e₂
  let .mvar m ← mkFreshExprSyntheticOpaqueMVar eq | failure
  AC.rewriteUnnormalized m
  let pr ← instantiateMVars (.mvar m)
  mkExpectedTypeHint pr eq

/-- Given `tr := t*r` `sr := s*r` `tEqs : t = s`, return a proof for `tr = sr`

    We use `a*b` to denote an AC application. That is, `(a*b)*(c*a)` is the term `a*a*b*c`. -/
def mkACSimpProof (tr t s r sr : ACApp) (tEqs : DelayedExpr) : MetaM DelayedExpr := do
  if tr == t then
    return tEqs
  else if tr == sr then
    let some tre := tr.toExpr | failure
    DelayedExpr.ofExpr <$> mkEqRefl tre
  else
    let .app op _ := tr | failure
    let some re := r.toExpr | failure
    let opr := op.app re
    let some te := t.toExpr | failure
    let rt := opr.app te
    let some se := s.toExpr | failure
    let rs := mkApp2 op re se
    let rtEqrs := DelayedExpr.congrArg opr tEqs
    let some tre := tr.toExpr | failure
    let trEqrt ← mkACProof tre rt
    let some sre := sr.toExpr | failure
    let rsEqsr ← mkACProof rs sre
    return .eqTrans (.eqTrans trEqrt rtEqrs) rsEqsr

/-- Given `ra := a*r` `sb := b*s` `ts := t*s` `tr := t*r` `tsEqa : t*s = a` `trEqb : t*r = b`,
    return a proof for `ra = sb`.

    We use `a*b` to denote an AC application. That is, `(a*b)*(c*a)` is the term `a*a*b*c`. -/
def mkACSuperposeProof (ra sb a b r s ts tr : ACApp) (tsEqa trEqb : DelayedExpr) :
    MetaM DelayedExpr := do
  let .app _ _ := tr | failure
  let .app op _ := ts | failure
  let tsrEqar := DelayedExpr.congrFun (.congrArg op tsEqa) r
  let trsEqbs := DelayedExpr.congrFun (.congrArg op trEqb) s
  let some tse := ts.toExpr | failure
  let some re := r.toExpr | failure
  let tsr := mkApp2 op tse re
  let some tre := tr.toExpr | failure
  let some se := s.toExpr | failure
  let trs := mkApp2 op tre se
  let tsrEqtrs ← mkACProof tsr trs
  let some ae := a.toExpr | failure
  let ar := mkApp2 op ae re
  let some be := b.toExpr | failure
  let bs := mkApp2 op be se
  let some rae := ra.toExpr | failure
  let raEqar ← mkACProof rae ar
  let some sbe := sb.toExpr | failure
  let bsEqsb ← mkACProof bs sbe
  return .eqTrans raEqar (.eqTrans (.eqSymm tsrEqar) (.eqTrans tsrEqtrs (.eqTrans trsEqbs bsEqsb)))

def simplifyACCore (e lhs rhs : ACApp) (H : DelayedExpr) :
    CCM (Option (ACApp × DelayedExpr)) := do
  guard (lhs.isSubset e)
  if e == lhs then
    return (rhs, H)
  else
    let .app op _ := e | failure
    let dummy := Expr.sort .zero
    let newArgs := e.diff lhs #[]
    let r : ACApp := if newArgs.isEmpty then dummy else .mkApp op newArgs
    let newArgs := ACApp.append op rhs newArgs
    let newE := ACApp.mkApp op newArgs
    let some true := (← getState).opInfo.find? op | failure
    let newPr ← mkACSimpProof e lhs rhs r newE H
    return (newE, newPr)

def simplifyACStep (e : ACApp) : CCM (Option (ACApp × DelayedExpr)) := do
  if let .app _ args := e then
    for h : i in [:args.size] do
      if i == 0 || (args[i]'h.2) != (args[i - 1]'(Nat.lt_of_le_of_lt (i.sub_le 1) h.2)) then
        let some ae := (← getState).acEntries.find? (args[i]'h.2) | failure
        let occs := ae.RLHSOccs
        let mut Rlhs? : Option ACApp := none
        for Rlhs in occs do
          if Rlhs?.isNone then
            if Rlhs.isSubset e then
              Rlhs? := some Rlhs
        if let some Rlhs := Rlhs? then
          let some (Rrhs, H) := (← getState).acR.find? Rlhs | failure
          return (← simplifyACCore e Rlhs Rrhs H)
  else if let some p := (← getState).acR.find? e then
    return some p
  return none

def simplifyAC (e : ACApp) : CCM (Option (ACApp × DelayedExpr)) := do
  let mut some (curr, pr) ← simplifyACStep e | return none
  repeat
    let some (newCurr, newPr) ← simplifyACStep curr | break
    pr := .eqTransOpt e curr newCurr pr newPr
    curr := newCurr
  return some (curr, pr)

def insertEraseROcc (arg : Expr) (lhs : ACApp) (inLHS isInsert : Bool) : CCM Unit := do
  let some entry := (← getState).acEntries.find? arg | failure
  let occs := entry.ROccs inLHS
  let newOccs := if isInsert then occs.insert lhs else occs.erase lhs
  let newEntry :=
    if inLHS then { entry with RLHSOccs := newOccs } else { entry with RRHSOccs := newOccs }
  modifyState fun ccs => { ccs with acEntries := ccs.acEntries.insert arg newEntry }

def insertEraseROccs (e lhs : ACApp) (inLHS isInsert : Bool) : CCM Unit := do
  match e with
  | .app _ args =>
    insertEraseROcc args[0]! lhs inLHS isInsert
    for i in [1:args.size] do
      if args[i]! != args[i - 1]! then
        insertEraseROcc args[i]! lhs inLHS isInsert
  | .ofExpr e => insertEraseROcc e lhs inLHS isInsert

@[inline]
def insertROccs (e lhs : ACApp) (inLHS : Bool) : CCM Unit :=
  insertEraseROccs e lhs inLHS true

@[inline]
def eraseROccs (e lhs : ACApp) (inLHS : Bool) : CCM Unit :=
  insertEraseROccs e lhs inLHS false

@[inline]
def insertRBHSOccs (lhs rhs : ACApp) : CCM Unit := do
  insertROccs lhs lhs true
  insertROccs rhs lhs false

@[inline]
def eraseRBHSOccs (lhs rhs : ACApp) : CCM Unit := do
  eraseROccs lhs lhs true
  eraseROccs rhs lhs false

@[inline]
def insertRRHSOccs (e lhs : ACApp) : CCM Unit :=
  insertROccs e lhs false

@[inline]
def eraseRRHSOccs (e lhs : ACApp) : CCM Unit :=
  eraseROccs e lhs false

open MessageData in
def composeAC (lhs rhs : ACApp) (H : DelayedExpr) : CCM Unit := do
  let some x := (← getState).getVarWithLeastRHSOccs lhs | failure
  let some ent := (← getState).acEntries.find? x | failure
  let occs := ent.RRHSOccs
  for Rlhs in occs do
    let some (Rrhs, RH) := (← getState).acR.find? Rlhs | failure
    if lhs.isSubset Rrhs then
      let some (newRrhs, RrhsEqNewRrhs) ← simplifyACCore Rrhs lhs rhs H | failure
      let newRH := DelayedExpr.eqTransOpt Rlhs Rrhs newRrhs RH RrhsEqNewRrhs
      modifyState fun ccs => { ccs with acR := ccs.acR.insert Rlhs (newRrhs, newRH) }
      eraseRRHSOccs Rrhs Rlhs
      insertRRHSOccs newRrhs Rlhs
      let ccs ← getState
      let oldRw :=
        paren (ccs.ppACApp Rlhs ++ ofFormat (Format.line ++ "-->" ++ .line) ++ ccs.ppACApp Rrhs)
      let newRw :=
        paren (ccs.ppACApp lhs ++ ofFormat (Format.line ++ "-->" ++ .line) ++ ccs.ppACApp rhs)
      let r :=
        "compose: " ++ nest 9 (group
          (oldRw ++ ofFormat (Format.line ++ "with" ++ .line) ++ newRw) ++
            ofFormat (Format.line ++ ":=" ++ .line) ++ ccs.ppACApp newRrhs)
      trace[Debug.Meta.Tactic.cc.ac] group r

open MessageData in
def collapseAC (lhs rhs : ACApp) (H : DelayedExpr) : CCM Unit := do
  let some x := (← getState).getVarWithLeastLHSOccs lhs | failure
  let some ent := (← getState).acEntries.find? x | failure
  let occs := ent.RLHSOccs
  for Rlhs in occs do
    if lhs.isSubset Rlhs then
      let some (Rrhs, RH) := (← getState).acR.find? Rlhs | failure
      eraseRBHSOccs Rlhs Rrhs
      modifyState fun ccs => { ccs with acR := ccs.acR.erase Rlhs }
      let some (newRlhs, RlhsEqNewRlhs) ← simplifyACCore Rlhs lhs rhs H | failure
      let newRlhsEqRlhs := DelayedExpr.eqSymmOpt Rlhs newRlhs RlhsEqNewRlhs
      let newRH := DelayedExpr.eqTransOpt newRlhs Rlhs Rrhs newRlhsEqRlhs RH
      modifyACTodo fun todo => todo.push (newRlhs, Rrhs, newRH)
      let ccs ← getState
      let newRw :=
        paren (ccs.ppACApp lhs ++ ofFormat (Format.line ++ "-->" ++ .line) ++ ccs.ppACApp rhs)
      let oldRw :=
        paren (ccs.ppACApp Rrhs ++ ofFormat (Format.line ++ "<--" ++ .line) ++ ccs.ppACApp Rlhs)
      let r :=
        "collapse: " ++ nest 10 (group
          (newRw ++ ofFormat (Format.line ++ "at" ++ .line) ++ oldRw) ++
            ofFormat (Format.line ++ ":=" ++ .line) ++ ccs.ppACApp newRlhs)
      trace[Debug.Meta.Tactic.cc.ac] group r

open MessageData in
def superposeAC (ts a : ACApp) (tsEqa : DelayedExpr) : CCM Unit := do
  let .app op args := ts | return
  for hi : i in [:args.size] do
    if i == 0 || (args[i]'hi.2) != (args[i - 1]'(Nat.lt_of_le_of_lt (i.sub_le 1) hi.2)) then
      let some ent := (← getState).acEntries.find? (args[i]'hi.2) | failure
      let occs := ent.RLHSOccs
      for tr in occs do
        let .app optr _ := tr | continue
        unless optr == op do continue
        let some (b, trEqb) := (← getState).acR.find? tr | failure
        let tArgs := ts.intersection tr #[]
        guard !tArgs.isEmpty
        let t := ACApp.mkApp op tArgs
        let sArgs := ts.diff t #[]
        guard !sArgs.isEmpty
        let rArgs := tr.diff t #[]
        guard !rArgs.isEmpty
        let s := ACApp.mkApp op sArgs
        let r := ACApp.mkApp op rArgs
        let ra := ACApp.mkFlatApp op r a
        let sb := ACApp.mkFlatApp op s b
        let some true := (← getState).opInfo.find? op | failure
        let raEqsb ← mkACSuperposeProof ra sb a b r s ts tr tsEqa trEqb
        modifyACTodo fun todo => todo.push (ra, sb, raEqsb)
        let ccs ← getState
        let rw₁ :=
          paren (ccs.ppACApp ts ++ ofFormat (Format.line ++ "-->" ++ .line) ++ ccs.ppACApp a)
        let rw₂ :=
          paren (ccs.ppACApp tr ++ ofFormat (Format.line ++ "-->" ++ .line) ++ ccs.ppACApp b)
        let eq :=
          paren (ccs.ppACApp ra ++ ofFormat (Format.line ++ "-->" ++ .line) ++ ccs.ppACApp sb)
        let r :=
        "superpose: " ++ nest 11 (group
          (rw₁ ++ ofFormat (Format.line ++ "with" ++ .line) ++ rw₂) ++
            ofFormat (Format.line ++ ":=" ++ .line) ++ eq)
        trace[Debug.Meta.Tactic.cc.ac] group r

open MessageData in
def processAC : CCM Unit := do
  repeat
    let acTodo ← getACTodo
    let mut some (lhs, rhs, H) := acTodo.back? | break
    modifyACTodo fun _ => acTodo.pop
    let lhs₀ := lhs
    let rhs₀ := rhs
    dbgTraceACEq "process eq:" lhs rhs

    -- Forward simplification lhs/rhs
    if let some p ← simplifyAC lhs then
      H := .eqTransOpt p.1 lhs rhs (.eqSymmOpt lhs p.1 p.2) H
      lhs := p.1
    if let some p ← simplifyAC rhs then
      H := .eqTransOpt lhs rhs p.1 H p.2
      rhs := p.1

    if lhs != lhs₀ || rhs != rhs₀ then
      dbgTraceACEq "after simp:" lhs rhs

    -- Check trivial
    if lhs == rhs then
      trace[Debug.Meta.Tactic.cc.ac] "trivial"
      continue

    -- Propagate new equality to congruence closure module
    if let .ofExpr lhse := lhs then
      if let .ofExpr rhse := rhs then
        if (← getRoot lhse) != (← getRoot rhse) then
          pushEq lhse rhse (.ofDExpr H)

    -- Orient
    if compare lhs rhs == .lt then
      H := .eqSymmOpt lhs rhs H
      (lhs, rhs) := (rhs, lhs)

    -- Backward simplification
    composeAC lhs rhs H
    collapseAC lhs rhs H

    -- Superposition
    superposeAC lhs rhs H

    -- Update R
    modifyState fun ccs => { ccs with acR := ccs.acR.insert lhs (rhs, H) }
    insertRBHSOccs lhs rhs

    let ccs ← getState
    let newRw :=
      group (ccs.ppACApp lhs ++ ofFormat (Format.line ++ "-->" ++ .line) ++ ccs.ppACApp rhs)
    trace[Debug.Meta.Tactic.cc.ac] group ("new rw: " ++ newRw)

def addACEq (e₁ e₂ : Expr) : CCM Unit := do
  dbgTraceACEq "cc eq:" e₁ e₂
  modifyACTodo fun acTodo => acTodo.push (e₁, e₂, .eqProof e₁ e₂)
  processAC
  dbgTraceACState

def setACVar (e : Expr) : CCM Unit := do
  let eRoot ← getRoot e
  let some rootEntry ← getEntry eRoot | failure
  if let some acVar := rootEntry.acVar then
    addACEq acVar e
  else
    let newRootEntry := { rootEntry with acVar := some e }
    modifyState fun ccs => { ccs with entries := ccs.entries.insert eRoot newRootEntry }

def internalizeACVar (e : Expr) : CCM Bool := do
  let ccs ← getState
  if ccs.acEntries.contains e then return false
  modifyState fun _ =>
    { ccs with
      acEntries := ccs.acEntries.insert e { idx := ccs.nextACIdx }
      nextACIdx := ccs.nextACIdx + 1 }
  setACVar e
  return true

partial def convertAC (op e : Expr) (args : Array Expr) : CCM (Array Expr × Expr) := do
  if let some currOp ← isAC e then
    if op == currOp then
      let (args, arg₁) ← convertAC op e.appFn!.appArg! args
      let (args, arg₂) ← convertAC op e.appArg! args
      return (args, mkApp2 op arg₁ arg₂)

  let _ ← internalizeACVar e
  return (args.push e, e)

open MessageData in
def internalizeAC (e : Expr) (parent? : Option Expr) : CCM Unit := do
  let some op ← isAC e | return
  let parentOp? ← parent?.casesOn (pure none) isAC
  if parentOp?.any (op == ·) then return

  unless (← internalizeACVar e) do return

  let (args, norme) ← convertAC op e #[]
  let rep := ACApp.mkApp op args
  let some true := (← getState).opInfo.find? op | failure
  let some repe := rep.toExpr | failure
  let pr ← mkACProof norme repe

  let ccs ← getState
  let d := paren (ccs.ppACApp e ++ ofFormat (" :=" ++ Format.line) ++ ofExpr e)
  let r := "new term: " ++ d ++ ofFormat (Format.line ++ "===>" ++ .line) ++ ccs.ppACApp rep
  trace[Debug.Meta.Tactic.cc.ac] group r

  modifyACTodo fun todo => todo.push (e, rep, pr)
  processAC
  dbgTraceACState

mutual
partial def internalizeApp (e : Expr) (gen : Nat) : CCM Unit := do
  if ← isInterpretedValue e then
    mkEntry e true gen
    if (← getState).config.values then return -- we treat values as atomic symbols
  else
    mkEntry e false gen
    if (← getState).config.values && isValue e then return -- we treat values as atomic symbols
  if let some (_, lhs, rhs) ← isSymmRelation e then
    internalizeCore lhs (some e) gen
    internalizeCore rhs (some e) gen
    addOccurrence e lhs true
    addOccurrence e rhs true
    addSymmCongruenceTable e
  else if (← mkExtCongrTheorem e).isSome then
    let fn := e.getAppFn
    let apps := getAppApps e
    guard (apps.size > 0)
    guard (apps.back == e)
    let mut pinfo : List ParamInfo := []
    let config := (← getState).config
    if config.ignoreInstances then
      pinfo := (← getFunInfoNArgs fn apps.size).paramInfo.toList
    if config.hoFns.isSome && fn.isConst && !(config.hoFns.iget.contains fn.constName) then
      for h : i in [:apps.size] do
        let arg := (apps[i]'h.2).appArg!
        addOccurrence e arg false
        if pinfo.head?.any ParamInfo.isInstImplicit then
          -- We do not recurse on instances when `(← getState).config.ignoreInstances` is `true`.
          mkEntry arg false gen
          propagateInstImplicit arg
        else
          internalizeCore arg (some e) gen
        unless pinfo.isEmpty do
          pinfo := pinfo.tail
      internalizeCore fn (some e) gen
      addOccurrence e fn false
      setFO e
      addCongruenceTable e
    else
      -- Expensive case where we store a quadratic number of occurrences,
      -- as described in the paper "Congruence Closure in Internsional Type Theory"
      for h : i in [:apps.size] do
        let curr := apps[i]'h.2
        let .app currFn currArg := curr | unreachable!
        if i < apps.size - 1 then
          mkEntry curr false gen
        for h : j in [i:apps.size] do
          addOccurrence (apps[j]'h.2) currArg false
          addOccurrence (apps[j]'h.2) currFn false
        if pinfo.head?.any ParamInfo.isInstImplicit then
          -- We do not recurse on instances when `(← getState).config.ignoreInstances` is `true`.
          mkEntry currArg false gen
          mkEntry currFn false gen
          propagateInstImplicit currArg
        else
          internalizeCore currArg (some e) gen
          mkEntry currFn false gen
        unless pinfo.isEmpty do
          pinfo := pinfo.tail
        addCongruenceTable curr
  applySimpleEqvs e

partial def internalizeCore (e : Expr) (parent? : Option Expr) (gen : Nat) : CCM Unit := do
  guard !e.hasLooseBVars
  /- We allow metavariables after partitions have been frozen. -/
  if e.hasExprMVar && !(← getState).frozePartitions then
    return
  /- Check whether `e` has already been internalized. -/
  if (← getEntry e).isNone then
    match e with
    | .bvar _ => unreachable!
    | .sort _ => pure ()
    | .const _ _ | .mvar _ => mkEntry e false gen
    | .lam _ _ _ _ | .letE _ _ _ _ _ => mkEntry e false gen
    | .fvar f =>
      mkEntry e false gen
      if let some v ← f.getValue? then
        pushReflEq e v
    | .mdata _ e' =>
      mkEntry e false gen
      internalizeCore e' e gen
      addOccurrence e e' false
      pushReflEq e e'
    | .forallE _ t b _ =>
      if e.isArrow then
        if ← isProp t <&&> isProp b then
          internalizeCore t e gen
          internalizeCore b e gen
          addOccurrence e t false
          addOccurrence e b false
          propagateImpUp e
      if ← isProp e then
        mkEntry e false gen
    | .app _ _ | .lit _ => internalizeApp e gen
    | .proj sn i pe =>
      mkEntry e false gen
      let some fn := (getStructureFields (← getEnv) sn)[i]? | failure
      let e' ← pe.mkDirectProjection fn
      internalizeApp e' gen
      pushReflEq e e'

  /- Remark: if should invoke `internalizeAC` even if the test `(← getEntry e).isNone` above failed.
     Reason, the first time `e` was visited, it may have been visited with a different parent. -/
  if (← getState).config.ac then
    internalizeAC e parent?

partial def propagateIffUp (e : Expr) : CCM Unit := do
  let some (a, b) := e.iff? | failure
  if ← isEqTrue a then
    -- `a = True  → (Iff a b) = b`
    pushEq e b (mkApp3 (.const ``iff_eq_of_eq_true_left []) a b (← getEqTrueProof a))
  else if ← isEqTrue b then
    -- `b = True  → (Iff a b) = a`
    pushEq e a (mkApp3 (.const ``iff_eq_of_eq_true_right []) a b (← getEqTrueProof b))
  else if ← isEqv a b then
    -- `a = b     → (Iff a b) = True`
    pushEq e (.const ``True []) (mkApp3 (.const ``iff_eq_true_of_eq []) a b (← getPropEqProof a b))

partial def propagateAndUp (e : Expr) : CCM Unit := do
  let some (a, b) := e.and? | failure
  if ← isEqTrue a then
    -- `a = True  → (And a b) = b`
    pushEq e b (mkApp3 (.const ``and_eq_of_eq_true_left []) a b (← getEqTrueProof a))
  else if ← isEqTrue b then
    -- `b = True  → (And a b) = a`
    pushEq e a (mkApp3 (.const ``and_eq_of_eq_true_right []) a b (← getEqTrueProof b))
  else if ← isEqFalse a then
    -- `a = False → (And a b) = False`
    pushEq e (.const ``False [])
      (mkApp3 (.const ``and_eq_of_eq_false_left []) a b (← getEqFalseProof a))
  else if ← isEqFalse b then
    -- `b = False → (And a b) = False`
    pushEq e (.const ``False [])
      (mkApp3 (.const ``and_eq_of_eq_false_right []) a b (← getEqFalseProof b))
  else if ← isEqv a b then
    -- `a = b     → (And a b) = a`
    pushEq e a (mkApp3 (.const ``and_eq_of_eq []) a b (← getPropEqProof a b))
  -- We may also add `a = Not b -> (And a b) = False`

partial def propagateOrUp (e : Expr) : CCM Unit := do
  let some (a, b) := e.app2? ``Or | failure
  if ← isEqTrue a then
    -- `a = True  → (Or a b) = True`
    pushEq e (.const ``True [])
      (mkApp3 (.const ``or_eq_of_eq_true_left []) a b (← getEqTrueProof a))
  else if ← isEqTrue b then
    -- `b = True  → (Or a b) = True`
    pushEq e (.const ``True [])
      (mkApp3 (.const ``or_eq_of_eq_true_right []) a b (← getEqTrueProof b))
  else if ← isEqFalse a then
    -- `a = False → (Or a b) = b`
    pushEq e b (mkApp3 (.const ``or_eq_of_eq_false_left []) a b (← getEqFalseProof a))
  else if ← isEqFalse b then
    -- `b = False → (Or a b) = a`
    pushEq e a (mkApp3 (.const ``or_eq_of_eq_false_right []) a b (← getEqFalseProof b))
  else if ← isEqv a b then
    -- `a = b     → (Or a b) = a`
    pushEq e a (mkApp3 (.const ``or_eq_of_eq []) a b (← getPropEqProof a b))
  -- We may also add `a = Not b -> (Or a b) = True`

partial def propagateNotUp (e : Expr) : CCM Unit := do
  let some a := e.not? | failure
  if ← isEqTrue a then
    -- `a = True  → Not a = False`
    pushEq e (.const ``False []) (mkApp2 (.const ``not_eq_of_eq_true []) a (← getEqTrueProof a))
  else if ← isEqFalse a then
    -- `a = False → Not a = True`
    pushEq e (.const ``True []) (mkApp2 (.const ``not_eq_of_eq_false []) a (← getEqFalseProof a))
  else if ← isEqv a e then
    let falsePr := mkApp2 (.const ``false_of_a_eq_not_a []) a (← getPropEqProof a e)
    let H := Expr.app (.const ``true_eq_false_of_false []) falsePr
    pushEq (.const ``True []) (.const ``False []) H


partial def propagateImpUp (e : Expr) : CCM Unit := do
  guard e.isArrow
  let .forallE _ a b _ := e | unreachable!
  if ← isEqTrue a then
    -- `a = True  → (a → b) = b`
    pushEq e b (mkApp3 (.const ``imp_eq_of_eq_true_left []) a b (← getEqTrueProof a))
  else if ← isEqFalse a then
    -- `a = False → (a → b) = True`
    pushEq e (.const ``True [])
      (mkApp3 (.const ``imp_eq_of_eq_false_left []) a b (← getEqFalseProof a))
  else if ← isEqTrue b then
    -- `b = True  → (a → b) = True`
    pushEq e (.const ``True [])
      (mkApp3 (.const ``imp_eq_of_eq_true_right []) a b (← getEqTrueProof b))
  else if ← isEqFalse b then
    if let (true, arg) := isNot a then
      if (← getState).config.em then
        -- `b = False → (Not a → b) = a`
        pushEq e arg
          (mkApp3 (.const ``not_imp_eq_of_eq_false_right []) arg b (← getEqFalseProof b))
    else
      -- `b = False → (a → b) = Not a`
      let notA := mkApp (.const ``Not []) a
      internalizeCore notA none (← getGenerationOf e)
      pushEq e notA
        (mkApp3 (.const ``imp_eq_of_eq_false_right []) a b (← getEqFalseProof b))
  else if ← isEqv a b then
    pushEq e (.const ``True [])
      (mkApp3 (.const ``imp_eq_true_of_eq []) a b (← getPropEqProof a b))

partial def propagateIteUp (e : Expr) : CCM Unit := do
  let .app (.app (.app (.app (.app (.const ``ite [lvl]) A) c) d) a) b := e | failure
  if ← isEqTrue c then
    -- `c = True  → (ite c a b) = a`
    pushEq e a (mkApp6 (.const ``if_eq_of_eq_true [lvl]) c d A a b (← getEqTrueProof c))
  else if ← isEqFalse c then
    -- `c = False → (ite c a b) = b`
    pushEq e b (mkApp6 (.const ``if_eq_of_eq_false [lvl]) c d A a b (← getEqFalseProof c))
  else if ← isEqv a b then
    -- `a = b     → (ite c a b) = a`
    pushEq e a (mkApp6 (.const ``if_eq_of_eq [lvl]) c d A a b (← getPropEqProof a b))

partial def propagateEqUp (e : Expr) : CCM Unit := do
  -- Remark: the positive case is implemented at `checkEqTrue` for any reflexive relation.
  let some (_, a, b) := e.eq? | failure
  let ra ← getRoot a
  let rb ← getRoot b
  if ra != rb then
    let mut raNeRb : Option Expr := none
    if ← isInterpretedValue ra <&&> isInterpretedValue rb then
      raNeRb := some
        (Expr.app (.proj ``Iff 0 (← mkAppM ``bne_iff_ne #[ra, rb])) (← mkEqRefl (.const ``true [])))
    else
      let env ← getEnv
      if let some c₁ := ra.isConstructorApp? env then
      if let some c₂ := rb.isConstructorApp? env then
      if c₁.name != c₂.name then
        raNeRb ← withLocalDeclD `h (← mkEq ra rb) fun h => do
          mkLambdaFVars #[h] (← mkNoConfusion (.const ``False []) h)
    if let some raNeRb' := raNeRb then
    if let some aNeRb ← mkNeOfEqOfNe a ra raNeRb' then
    if let some aNeB ← mkNeOfNeOfEq aNeRb rb b then
      pushEq e (.const ``False []) (← mkEqFalse aNeB)

partial def propagateUp (e : Expr) : CCM Unit := do
  if (← getState).inconsistent then return
  if e.isAppOfArity ``Iff 2 then
    propagateIffUp e
  else if e.isAppOfArity ``And 2 then
    propagateAndUp e
  else if e.isAppOfArity ``Or 2 then
    propagateOrUp e
  else if e.isAppOfArity ``Not 1 then
    propagateNotUp e
  else if e.isArrow then
    propagateImpUp e
  else if e.isIte then
    propagateIteUp e
  else if e.isEq then
    propagateEqUp e

/--
This method is invoked during internalization and eagerly apply basic equivalences for term `e`
Examples:
- If `e := cast H e'`, then it merges the equivalence classes of `cast H e'` and `e'`

In principle, we could mark theorems such as `cast_eq` as simplification rules, but this creates
problems with the builtin support for cast-introduction in the ematching module.

Eagerly merging the equivalence classes is also more efficient. -/
partial def applySimpleEqvs (e : Expr) : CCM Unit := do
  if let .app (.app (.app (.app (.const ``cast [l₁]) A) B) H) a := e then
    /-
    ```
    HEq (cast H a) a

    theorem cast_heq : ∀ {A B : Type.{l_1}} (H : A = B) (a : A), HEq (@cast.{l_1} A B H a) a
    ```
    -/
    let proof := mkApp4 (.const ``cast_heq [l₁]) A B H a
    pushHEq e a proof

  if let .app (.app (.app (.app (.app (.app (.const ``Eq.recOn [l₁, l₂]) A) a) P) a') H) p := e then
    /-
    ```
    HEq (Eq.recOn H p) p

    theorem eq_rec_heq : ∀ {A : Type.{l_1}} {P : A → Type.{l_2}} {a a' : A} (H : a = a')
      (p : P a), HEq (@Eq.recOn.{l_2 l_1} A a P a' H p) p
    ```
    -/
    let proof := mkApp6 (.const ``eq_rec_heq [l₁, l₂]) A P a a' H p
    pushHEq e p proof

  if let .app (.app (.app (.const ``Ne [l₁]) α) a) b := e then
    -- `(a ≠ b) = (Not (a = b))`
    let newE := Expr.app (.const ``Not []) (mkApp3 (.const ``Eq [l₁]) α a b)
    internalizeCore newE none (← getGenerationOf e)
    pushReflEq e newE

  if let some r ← reduceProjStruct? e then
    pushReflEq e r

  let fn := e.getAppFn
  if fn.isLambda then
    let reducedE := e.headBeta
    if let some phandler := (← get).phandler then
      phandler.newAuxCCTerm reducedE
    internalizeCore reducedE none (← getGenerationOf e)
    pushReflEq e reducedE

  let mut revArgs : Array Expr := #[]
  let mut it := e
  while it.isApp do
    revArgs := revArgs.push it.appArg!
    let fn := it.appFn!
    let rootFn ← getRoot fn
    let en ← getEntry rootFn
    if en.any Entry.hasLambdas then
      let lambdas ← getEqcLambdas rootFn #[]
      let newLambdaApps ← propagateBeta fn revArgs lambdas #[]
      for newApp in newLambdaApps do
        internalizeCore newApp none (← getGenerationOf e)
    it := fn

  propagateUp e

partial def processSubsingletonElem (e : Expr) : CCM Unit := do
  let type ← inferType e
  let ss ← synthInstance? (← mkAppM ``Subsingleton #[type])
  if ss.isNone then return -- type is not a subsingleton
  let type ← normalize type
  -- Make sure type has been internalized
  internalizeCore type none (← getGenerationOf e)
  -- Try to find representative
  if let some it := (← getState).subsingletonReprs.find? type then
    pushSubsingletonEq e it
  else
    modifyState fun ccs =>
      { ccs with
        subsingletonReprs := ccs.subsingletonReprs.insert type e }
  let typeRoot ← getRoot type
  if typeRoot == type then return
  if let some it2 := (← getState).subsingletonReprs.find? typeRoot then
    pushSubsingletonEq e it2
  else
    modifyState fun ccs =>
      { ccs with
        subsingletonReprs := ccs.subsingletonReprs.insert typeRoot e }

partial def mkEntry (e : Expr) (interpreted : Bool) (gen : Nat) : CCM Unit := do
  if (← getEntry e).isSome then return
  let constructor := e.isConstructorApp (← getEnv)
  modifyState fun ccs => ccs.mkEntryCore e interpreted constructor gen
  processSubsingletonElem e
end

def mayPropagate (e : Expr) : Bool :=
  e.isAppOfArity ``Iff 2 || e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 ||
    e.isAppOfArity ``Not 1 || e.isArrow || e.isIte

def removeParents (e : Expr) (parentsToPropagate : Array Expr) : CCM (Array Expr) := do
  let some ps := (← getState).parents.find? e | return parentsToPropagate
  let mut parentsToPropagate := parentsToPropagate
  for pocc in ps do
    let p := pocc.expr
    trace[Debug.Meta.Tactic.cc] "remove parent: {p}"
    if mayPropagate p then
      parentsToPropagate := parentsToPropagate.push p
    if p.isApp then
      if pocc.symmTable then
        let some (rel, lhs, rhs) ← isSymmRelation p | failure
        let k' ← mkSymmCongruencesKey lhs rhs
        if let some lst := (← getState).symmCongruences.find? k' then
          let k := (p, rel)
          let newLst ← lst.filterM fun k₂ => (!·) <$> compareSymm k k₂
          if !newLst.isEmpty then
            modifyState fun ccs =>
              { ccs with symmCongruences := ccs.symmCongruences.insert k' newLst }
          else
            modifyState fun ccs =>
              { ccs with symmCongruences := ccs.symmCongruences.erase k' }
      else
        let k' ← mkCongruencesKey p
        if let some es := (← getState).congruences.find? k' then
          let newEs := es.erase p
          if !newEs.isEmpty then
            modifyState fun ccs =>
              { ccs with congruences := ccs.congruences.insert k' newEs }
          else
            modifyState fun ccs =>
              { ccs with congruences := ccs.congruences.erase k' }
  return parentsToPropagate

/--
The fields `target` and `proof` in `e`'s entry are encoding a transitivity proof
Let `e.rootTarget` and `e.rootProof` denote these fields.
```lean
e = e.rootTarget            := e.rootProof
_ = e.rootTarget.rootTarget := e.rootTarget.rootProof
 ...
_ = e.root                  := ...
```
The transitivity proof eventually reaches the root of the equivalence class.
This method "inverts" the proof. That is, the `target` goes from `e.root` to e after
we execute it.
-/
partial def invertTrans (e : Expr) (newFlipped : Bool := false) (newTarget : Option Expr := none)
    (newProof : Option EntryExpr := none) : CCM Unit := do
  let some n ← getEntry e | failure
  if let some t := n.target then
    invertTrans t (!n.flipped) (some e) n.proof
  let newN : Entry :=
    { n with
      flipped := newFlipped
      target := newTarget
      proof := newProof }
  modifyState fun ccs => { ccs with entries := ccs.entries.insert e newN }

/-- Traverse the `root`'s equivalence class, and collect the function's equivalence class roots. -/
def collectFnRoots (root : Expr) (fnRoots : Array Expr) : CCM (Array Expr) := do
  guard ((← getRoot root) == root)
  let mut fnRoots : Array Expr := fnRoots
  let mut visited : RBExprSet := ∅
  let mut it := root
  repeat
    let fnRoot ← getRoot (it.getAppFn)
    if !visited.contains fnRoot then
      visited := visited.insert fnRoot
      fnRoots := fnRoots.push fnRoot
    let some itN ← getEntry it | failure
    it := itN.next
  until it == root
  return fnRoots

def reinsertParents (e : Expr) : CCM Unit := do
  let some ps := (← getState).parents.find? e | return
  for p in ps do
    trace[Debug.Meta.Tactic.cc] "reinsert parent: {p.expr}"
    if p.expr.isApp then
      if p.symmTable then
        addSymmCongruenceTable p.expr
      else
        addCongruenceTable p.expr

def checkInvariant : CCM Unit := do
  guard (← getState).checkInvariant

/--
For each `fnRoot` in `fnRoots` traverse its parents, and look for a parent prefix that is
in the same equivalence class of the given lambdas.

remark All expressions in lambdas are in the same equivalence class
-/
def propagateBetaToEqc (fnRoots lambdas newLambdaApps : Array Expr) : CCM (Array Expr) := do
  if lambdas.isEmpty then return newLambdaApps
  let mut newLambdaApps := newLambdaApps
  let lambdaRoot ← getRoot lambdas.back
  guard (← lambdas.allM fun l => pure l.isLambda <&&> (· == lambdaRoot) <$> getRoot l)
  for fnRoot in fnRoots do
    if let some ps := (← getState).parents.find? fnRoot then
      for { expr := p,.. } in ps do
        let mut revArgs : Array Expr := #[]
        let mut it₂ := p
        while it₂.isApp do
          let fn := it₂.appFn!
          revArgs := revArgs.push it₂.appArg!
          if (← getRoot fn) == lambdaRoot then
            -- found it
            newLambdaApps ← propagateBeta fn revArgs lambdas newLambdaApps
            break
          it₂ := it₂.appFn!
  return newLambdaApps

/--
Given `c` a constructor application, if `p` is a projection application (not `.proj _ _ _`, but
`.app (.const projName _) _`) such that major premise is
equal to `c`, then propagate new equality.

Example: if `p` is of the form `b.fst`, `c` is of the form `(x, y)`, and `b = c`, we add the
equality `(x, y).fst = x` -/
def propagateProjectionConstructor (p c : Expr) : CCM Unit := do
  let env ← getEnv
  guard (c.isConstructorApp env)
  p.withApp fun pFn pArgs => do
    let some pFnN := pFn.constName? | return
    let some info ← getProjectionFnInfo? pFnN | return
    let mkidx := info.numParams
    if h : mkidx < pArgs.size then
      unless ← isEqv (pArgs[mkidx]'h) c do return
      unless ← pureIsDefEq (← inferType (pArgs[mkidx]'h)) (← inferType c) do return
      /- Create new projection application using c (e.g., `(x, y).fst`), and internalize it.
        The internalizer will add the new equality. -/
      let pArgs := pArgs.set ⟨mkidx, h⟩ c
      let newP := mkAppN pFn pArgs
      internalizeCore newP none (← getGenerationOf p)
    else
      return

/--
Given a new equality `e₁ = e₂`, where `e₁` and `e₂` are constructor applications.
Implement the following implications:
```lean
c a₁ ... aₙ = c b₁ ... bₙ => a₁ = b₁, ..., aₙ = bₙ

c₁ ... = c₂ ... => False
```
where `c`, `c₁` and `c₂` are constructors -/
partial def propagateConstructorEq (e₁ e₂ : Expr) : CCM Unit := do
  let env ← getEnv
  let some c₁ := e₁.isConstructorApp? env | failure
  let some c₂ := e₂.isConstructorApp? env | failure
  unless ← pureIsDefEq (← inferType e₁) (← inferType e₂) do
    -- The implications above only hold if the types are equal.
    -- TODO(Leo): if the types are different, we may still propagate by searching the equivalence
    --            classes of `e₁` and `e₂` for other constructors that may have compatible types.
    return
  let some h ← getEqProof e₁ e₂ | failure
  if c₁.name == c₂.name then
    if 0 < c₁.numFields then
      let name := mkInjectiveTheoremNameFor c₁.name
      if env.contains name then
        let rec go (type val : Expr) : CCM Unit := do
          let push (type val : Expr) : CCM Unit :=
            match type.eq? with
            | some (_, lhs, rhs) => pushEq lhs rhs val
            | none =>
              match type.heq? with
              | some (_, _, lhs, rhs) => pushHEq lhs rhs val
              | none => failure
          match type.and? with
          | some (l, r) =>
            push l (.proj ``And 0 val)
            go r (.proj ``And 1 val)
          | none =>
            push type val
        let val ← mkAppM name #[h]
        let type ← inferType val
        go type val
  else
    let falsePr ← mkNoConfusion (.const ``False []) h
    let H := Expr.app (.const ``true_eq_false_of_false []) falsePr
    pushEq (.const ``True []) (.const ``False []) H

def propagateValueInconsistency (e₁ e₂ : Expr) : CCM Unit := do
  guard (← isInterpretedValue e₁)
  guard (← isInterpretedValue e₂)
  let neProof :=
    Expr.app (.proj ``Iff 0 (← mkAppM ``bne_iff_ne #[e₁, e₂])) (← mkEqRefl (.const ``true []))
  let some eqProof ← getEqProof e₁ e₂ | failure
  let trueEqFalse ← mkEq (.const ``True []) (.const ``False [])
  let H ← mkAbsurd trueEqFalse eqProof neProof
  pushEq (.const ``True []) (.const ``False []) H

def propagateAndDown (e : Expr) : CCM Unit := do
  if ← isEqTrue e then
    let some (a, b) := e.and? | failure
    let h ← getEqTrueProof e
    pushEq a (.const ``True []) (mkApp3 (.const ``eq_true_of_and_eq_true_left []) a b h)
    pushEq b (.const ``True []) (mkApp3 (.const ``eq_true_of_and_eq_true_right []) a b h)

def propagateOrDown (e : Expr) : CCM Unit := do
  if ← isEqFalse e then
    let some (a, b) := e.app2? ``Or | failure
    let h ← getEqFalseProof e
    pushEq a (.const ``False []) (mkApp3 (.const ``eq_false_of_or_eq_false_left []) a b h)
    pushEq b (.const ``False []) (mkApp3 (.const ``eq_false_of_or_eq_false_right []) a b h)

def propagateNotDown (e : Expr) : CCM Unit := do
  if ← isEqTrue e then
    let some a := e.not? | failure
    pushEq a (.const ``False [])
      (mkApp2 (.const ``eq_false_of_not_eq_true []) a (← getEqTrueProof e))
  else if ← (·.config.em) <$> getState <&&> isEqFalse e then
    let some a := e.not? | failure
    pushEq a (.const ``True [])
      (mkApp2 (.const ``eq_true_of_not_eq_false []) a (← getEqFalseProof e))

def propagateEqDown (e : Expr) : CCM Unit := do
  if ← isEqTrue e then
    let some (a, b) := e.eqOrIff? | failure
    pushEq a b (← mkAppM ``of_eq_true #[← getEqTrueProof e])

def propagateExistsDown (e : Expr) : CCM Unit := do
  if ← isEqFalse e then
    let hNotE ← mkAppM ``not_of_eq_false #[← getEqFalseProof e]
    let (all, hAll) ← toForallNot e hNotE
    internalizeCore all none (← getGenerationOf e)
    pushEq all (.const ``True []) (← mkEqTrue hAll)

def propagateDown (e : Expr) : CCM Unit := do
  if e.isAppOfArity ``And 2 then
    propagateAndDown e
  else if e.isAppOfArity ``Or 2 then
    propagateOrDown e
  else if e.isAppOfArity ``Not 1 then
    propagateNotDown e
  else if e.isEq || e.isAppOfArity ``Iff 2 then
    propagateEqDown e
  else if e.isAppOfArity ``Exists 2 then
    propagateExistsDown e

def addEqvStep (e₁ e₂ : Expr) (H : EntryExpr) (heqProof : Bool) : CCM Unit := do
  let some n₁ ← getEntry e₁ | return -- `e₁` have not been internalized
  let some n₂ ← getEntry e₂ | return -- `e₂` have not been internalized
  if n₁.root == n₂.root then return -- they are already in the same equivalence class.
  let some r₁ ← getEntry n₁.root | failure
  let some r₂ ← getEntry n₂.root | failure

  -- We want `r₂` to be the root of the combined class.

  /-
    We swap `(e₁,n₁,r₁)` with `(e₂,n₂,r₂)` when
    1- `r₁.interpreted && !r₂.interpreted`.
      Reason: to decide when to propagate we check whether the root of the equivalence class
      is `True`/`False`. So, this condition is to make sure if `True`/`False` is in an equivalence
      class, then one of them is the root. If both are, it doesn't matter, since the state is
      inconsistent anyway.
    2- `r₁.constructor && !r₂.interpreted && !r₂.constructor`
      Reason: we want constructors to be the representative of their equivalence classes.
    3- `r₁.size > r₂.size && !r₂.interpreted && !r₂.constructor`
      Reason: performance.
  -/
  if (r₁.interpreted && !r₂.interpreted) ||
      (r₁.constructor && !r₂.interpreted && !r₂.constructor) ||
      (decide (r₁.size > r₂.size) && !r₂.interpreted && !r₂.constructor) then
    go e₂ e₁ n₂ n₁ r₂ r₁ true H heqProof
  else
    go e₁ e₂ n₁ n₂ r₁ r₂ false H heqProof
where
  go (e₁ e₂: Expr) (n₁ n₂ r₁ r₂ : Entry) (flipped : Bool) (H : EntryExpr) (heqProof : Bool) :
      CCM Unit := do
    let mut valueInconsistency := false
    if r₁.interpreted && r₂.interpreted then
      if n₁.root.isConstOf ``True || n₂.root.isConstOf ``True then
        modifyState fun ccs => { ccs with inconsistent := true }
      else if isNum n₁.root && isNum n₂.root then
        valueInconsistency := toInt n₁.root != toInt n₂.root
      else
        valueInconsistency := true

    let constructorEq := r₁.constructor && r₂.constructor
    let e₁Root := n₁.root
    let e₂Root := n₂.root
    trace[Debug.Meta.Tactic.cc] "merging\n{e₁} ==> {e₁Root}\nwith\n{e₂Root} <== {e₂}"

    /-
    Following target/proof we have
    `e₁ → ... → r₁`
    `e₂ → ... → r₂`
    We want
    `r₁ → ... → e₁ → e₂ → ... → r₂`
    -/
    invertTrans e₁
    let newN₁ : Entry :=
      { n₁ with
        target := e₂
        proof := H
        flipped }
    modifyState fun ccs => { ccs with entries := ccs.entries.insert e₁ newN₁ }

    -- The hash code for the parents is going to change
    let parentsToPropagate ← removeParents e₁Root #[]

    let lambdas₁ ← getEqcLambdas e₁Root #[]
    let lambdas₂ ← getEqcLambdas e₂Root #[]
    let fnRoots₂ ← if !lambdas₁.isEmpty then collectFnRoots e₂Root #[] else pure #[]
    let fnRoots₁ ← if !lambdas₂.isEmpty then collectFnRoots e₁Root #[] else pure #[]

    -- force all `root` fields in `e₁` equivalence class to point to `e₂Root`
    let propagate := e₂Root.isConstOf ``True || e₂Root.isConstOf ``False
    let mut toPropagate : Array Expr := #[]
    let mut it := e₁
    repeat
      let some itN ← getEntry it | failure
      if propagate then
        toPropagate := toPropagate.push it
      let newItN : Entry := { itN with root := e₂Root }
      modifyState fun ccs => { ccs with entries := ccs.entries.insert it newItN }
      it := newItN.next
    until it == e₁

    reinsertParents e₁Root

    -- update next of `e₁Root` and `e₂Root`, ac representative, and size of `e₂Root`
    let some r₁ ← getEntry e₁Root | failure
    let some r₂ ← getEntry e₂Root | failure
    guard (r₁.root == e₂Root)

    let acVar?₁ := r₁.acVar
    let acVar?₂ := r₂.acVar
    let newR₁ : Entry :=
      { r₁ with
        next := r₂.next }
    let newR₂ : Entry :=
      { r₂ with
        next := r₁.next
        size := r₂.size + r₁.size
        hasLambdas := r₂.hasLambdas || r₁.hasLambdas
        heqProofs := r₂.heqProofs || heqProof
        acVar := acVar?₂.orElse fun _ => acVar?₁ }
    modifyState fun ccs =>
      { ccs with
        entries :=
          ccs.entries.insert e₁Root newR₁ |>.insert e₂Root newR₂ }
    checkInvariant

    let lambdaAppsToInternalize ← propagateBetaToEqc fnRoots₂ lambdas₁ #[]
    let lambdaAppsToInternalize ← propagateBetaToEqc fnRoots₁ lambdas₂ lambdaAppsToInternalize

    -- copy `e₁Root` parents to `e₂Root`
    if let some ps₁ := (← getState).parents.find? e₁Root then
      let mut ps₂ : ParentOccSet := ∅
      if let some it' := (← getState).parents.find? e₂Root then
        ps₂ := it'
      for p in ps₁ do
        if ← pure p.expr.isApp <||> isCgRoot p.expr then
          if !constructorEq && r₂.constructor then
            propagateProjectionConstructor p.expr e₂Root
          ps₂ := ps₂.insert p
      modifyState fun ccs =>
        { ccs with
          parents := ccs.parents.erase e₁Root |>.insert e₂Root ps₂ }

    if !(← getState).inconsistent then
      if let some acVar₁ := acVar?₁ then
      if let some acVar₂ := acVar?₂ then
        addACEq acVar₁ acVar₂

    if !(← getState).inconsistent && constructorEq then
      propagateConstructorEq e₁Root e₂Root

    if !(← getState).inconsistent && valueInconsistency then
      propagateValueInconsistency e₁Root e₂Root

    if !(← getState).inconsistent then
      updateMT e₂Root
      checkNewSubsingletonEq e₁Root e₂Root

    if !(← getState).inconsistent then
      for p in parentsToPropagate do
        propagateUp p

    if !(← getState).inconsistent && !toPropagate.isEmpty then
      for e in toPropagate do
        propagateDown e
      if let some phandler := (← get).phandler then
        phandler.propagated toPropagate

    if !(← getState).inconsistent then
      for e in lambdaAppsToInternalize do
        internalizeCore e none (← getGenerationOf e)

    let ccs ← getState
    trace[Meta.Tactic.cc.merge] "{e₁Root} = {e₂Root}"
    trace[Debug.Meta.Tactic.cc] "merged: {e₁Root} = {e₂Root}\n{ccs.ppEqcs}"
    trace[Debug.Meta.Tactic.cc.parentOccs] ccs.ppParentOccs

def processTodo : CCM Unit := do
  repeat
    let todo ← getTodo
    let some (lhs, rhs, H, heqProof) := todo.back? | return
    if (← getState).inconsistent then
      modifyTodo fun _ => #[]
      return
    modifyTodo Array.pop
    addEqvStep lhs rhs H heqProof

def internalize (e : Expr) (gen : Nat) : CCM Unit := do
  internalizeCore e none gen
  processTodo

def addEqvCore (lhs rhs H : Expr) (heqProof : Bool) : CCM Unit := do
  pushTodo lhs rhs H heqProof
  processTodo

def add (type : Expr) (proof : Expr) (gen : Nat) : CCM Unit := do
  if (← getState).inconsistent then return
  modifyTodo fun _ => #[]
  let (isNeg, p) := isNotOrNe type
  match p with
  | .app (.app (.app (.const ``Eq _) _) lhs) rhs =>
    if isNeg then
      internalizeCore p none gen
      addEqvCore p (.const ``False []) (← mkEqFalse proof) false
    else
      internalizeCore lhs none gen
      internalizeCore rhs none gen
      addEqvCore lhs rhs proof false
  | .app (.app (.app (.app (.const ``HEq _) _) lhs) _) rhs =>
    if isNeg then
      internalizeCore p none gen
      addEqvCore p (.const ``False []) (← mkEqFalse proof) false
    else
      internalizeCore lhs none gen
      internalizeCore rhs none gen
      addEqvCore lhs rhs proof true
  | .app (.app (.const ``Iff _) lhs) rhs =>
    if isNeg then
      let neqProof ← mkAppM ``neq_of_not_iff #[proof]
      internalizeCore p none gen
      addEqvCore p (.const ``False []) (← mkEqFalse neqProof) false
    else
      internalizeCore lhs none gen
      internalizeCore rhs none gen
      addEqvCore lhs rhs (mkApp3 (.const ``propext []) lhs rhs proof) false
  | _ =>
    if ← pure isNeg <||> isProp p then
      internalizeCore p none gen
      if isNeg then
        addEqvCore p (.const ``False []) (← mkEqFalse proof) false
      else
        addEqvCore p (.const ``True []) (← mkEqTrue proof) false

end CCM

namespace CCState

open CCM

def mkCore (config : CCConfig) : CCState :=
  let s : CCState := { config }
  s.mkEntryCore (.const ``True []) true false 0 |>.mkEntryCore (.const ``False []) true false 0
#align cc_state.mk_core Mathlib.Tactic.CC.CCState.mkCore

/-- Create a congruence closure state object using the hypotheses in the current goal. -/
def mkUsingHsCore (cfg : CCConfig) : MetaM CCState := do
  let ctx ← getLCtx
  let ctx ← instantiateLCtxMVars ctx
  let (_, c) ← CCM.run (ctx.forM fun dcl => do
    unless dcl.isImplementationDetail do
      if ← isProp dcl.type then
        add dcl.type dcl.toExpr 0) { state := mkCore cfg }
  return c.state
#align cc_state.mk_using_hs_core Mathlib.Tactic.CC.CCState.mkUsingHsCore

/-- Returns the root expression for each equivalence class in the graph.
If the `Bool` argument is set to `true` then it only returns roots of non-singleton classes. -/
def rootsCore (ccs : CCState) (nonsingleton : Bool) : List Expr :=
  ccs.getRoots #[] nonsingleton |>.toList
#align cc_state.roots_core Mathlib.Tactic.CC.CCState.rootsCore

/-- Increment the Global Modification time. -/
def incGMT (ccs : CCState) : CCState :=
  { ccs with gmt := ccs.gmt + 1 }
#align cc_state.inc_gmt Mathlib.Tactic.CC.CCState.incGMT

/-- Add the given expression to the graph. -/
def internalize (ccs : CCState) (e : Expr) : MetaM CCState := do
  let (_, c) ← CCM.run (CCM.internalize e 0) { state := ccs }
  return c.state
#align cc_state.internalize Mathlib.Tactic.CC.CCState.internalize

/-- Add the given proof term as a new rule.
The proof term `H` must be an `Eq _ _`, `HEq _ _`, `Iff _ _`, or a negation of these. -/
def add (ccs : CCState) (H : Expr) : MetaM CCState := do
  let type ← inferType H
  unless ← isProp type do
    throwError "CCState.add failed, given expression is not a proof term"
  let (_, c) ← CCM.run (CCM.add type H 0) { state := ccs }
  return c.state
#align cc_state.add Mathlib.Tactic.CC.CCState.add

/-- Check whether two expressions are in the same equivalence class. -/
def isEqv (ccs : CCState) (e₁ e₂ : Expr) : MetaM Bool := do
  let (b, _) ← CCM.run (CCM.isEqv e₁ e₂) { state := ccs }
  return b
#align cc_state.is_eqv Mathlib.Tactic.CC.CCState.isEqv

/-- Check whether two expressions are not in the same equivalence class. -/
def isNotEqv (ccs : CCState) (e₁ e₂ : Expr) : MetaM Bool := do
  let (b, _) ← CCM.run (CCM.isNotEqv e₁ e₂) { state := ccs }
  return b
#align cc_state.is_not_eqv Mathlib.Tactic.CC.CCState.isNotEqv

/-- Returns a proof term that the given terms are equivalent in the given `CCState` -/
def eqvProof (ccs : CCState) (e₁ e₂ : Expr) : MetaM Expr := do
  let (some r, _) ← CCM.run (CCM.getEqProof e₁ e₂) { state := ccs }
    | throwError "CCState.eqvProof failed to build proof"
  return r
#align cc_state.eqv_proof Mathlib.Tactic.CC.CCState.eqvProof

/-- `proofFor cc e` constructs a proof for e if it is equivalent to true in `CCState` -/
def proofFor (ccs : CCState) (e : Expr) : MetaM Expr := do
  let (some r, _) ← CCM.run (CCM.getEqProof e (.const ``True [])) { state := ccs }
    | throwError "CCState.proofFor failed to build proof"
  mkAppM ``of_eq_true #[r]
#align cc_state.proof_for Mathlib.Tactic.CC.CCState.proofFor

/-- `refutationFor cc e` constructs a proof for `Not e` if it is equivalent to `False` in `CCState`
-/
def refutationFor (ccs : CCState) (e : Expr) : MetaM Expr := do
  let (some r, _) ← CCM.run (CCM.getEqProof e (.const ``False [])) { state := ccs }
    | throwError "CCState.refutationFor failed to build proof"
  mkAppM ``not_of_eq_false #[r]
#align cc_state.refutation_for Mathlib.Tactic.CC.CCState.refutationFor

/-- If the given state is inconsistent, return a proof for `False`. Otherwise fail. -/
def proofForFalse (ccs : CCState) : MetaM Expr := do
  let (some pr, _) ← CCM.run CCM.getInconsistencyProof { state := ccs }
    | throwError "CCState.proofForFalse failed, state is not inconsistent"
  return pr
#align cc_state.proof_for_false Mathlib.Tactic.CC.CCState.proofForFalse

def mk' : CCState :=
  CCState.mkCore {}
#align cc_state.mk Mathlib.Tactic.CC.CCState.mk'

def mkUsingHs : MetaM CCState :=
  CCState.mkUsingHsCore {}
#align cc_state.mk_using_hs Mathlib.Tactic.CC.CCState.mkUsingHs

def roots (s : CCState) : List Expr :=
  CCState.rootsCore s true
#align cc_state.roots Mathlib.Tactic.CC.CCState.roots

instance : ToMessageData CCState :=
  ⟨fun s => CCState.ppEqcs s true⟩

partial def eqcOfCore (s : CCState) (e : Expr) (f : Expr) (r : List Expr) : List Expr :=
    let n := s.next e
    if n == f then e :: r else eqcOfCore s n f (e :: r)
#align cc_state.eqc_of_core Mathlib.Tactic.CC.CCState.eqcOfCore

def eqcOf (s : CCState) (e : Expr) : List Expr :=
  s.eqcOfCore e e []
#align cc_state.eqc_of Mathlib.Tactic.CC.CCState.eqcOf

def eqcSize (s : CCState) (e : Expr) : Nat :=
  s.eqcOf e |>.length
#align cc_state.eqc_size Mathlib.Tactic.CC.CCState.eqcSize

partial def foldEqcCore {α} (s : CCState) (f : α → Expr → α) (first : Expr) (c : Expr) (a : α) :
    α :=
  let new_a := f a c
  let next := s.next c
  if next == first then new_a else foldEqcCore s f first next new_a
#align cc_state.fold_eqc_core Mathlib.Tactic.CC.CCState.foldEqcCore

def foldEqc {α} (s : CCState) (e : Expr) (a : α) (f : α → Expr → α) : α :=
  foldEqcCore s f e e a
#align cc_state.fold_eqc Mathlib.Tactic.CC.CCState.foldEqc

def mfoldEqc {α} {m : Type → Type} [Monad m] (s : CCState) (e : Expr) (a : α)
    (f : α → Expr → m α) : m α :=
  foldEqc s e (return a) fun act e => do
    let a ← act
    f a e
#align cc_state.mfold_eqc Mathlib.Tactic.CC.CCState.mfoldEqc

end CCState

def _root_.Lean.MVarId.ccCore (m : MVarId) (cfg : CCConfig) : MetaM Unit := do
  let (_, m) ← m.intros
  m.withContext do
    let s ← CCState.mkUsingHsCore cfg
    let t ← m.getType >>= instantiateMVars
    let s ← s.internalize t
    if s.inconsistent then
        let pr ← s.proofForFalse
        mkAppOptM ``False.elim #[t, pr] >>= m.assign
    else
      let tr := Expr.const ``True []
      let b ← s.isEqv t tr
      if b then
        let pr ← s.eqvProof t tr
        mkAppM ``of_eq_true #[pr] >>= m.assign
      else
        let dbg ← getBoolOption `trace.Meta.Tactic.cc.failure false
        if dbg then
          throwError m!"cc tactic failed, equivalence classes: {s}"
        else
          throwError "cc tactic failed"
#align tactic.cc_core Lean.MVarId.ccCore

def _root_.Lean.MVarId.cc (m : MVarId) : MetaM Unit :=
  m.ccCore {}
#align tactic.cc Lean.MVarId.cc

elab_rules : tactic
  | `(tactic| cc) => withMainContext do liftMetaFinishingTactic (·.cc)

#noalign tactic.cc_dbg_core

#noalign tactic.cc_dbg

#align tactic.ac_refl Lean.Meta.AC.acRflTactic

end Mathlib.Tactic.CC
