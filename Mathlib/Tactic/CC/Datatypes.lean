/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Miyahara Kō
-/
import Batteries.Classes.Order
import Mathlib.Lean.Meta.Basic
import Mathlib.Lean.Meta.CongrTheorems
import Mathlib.Data.Ordering.Basic

/-!
# Datatypes for `cc`

Some of the data structures here are used in multiple parts of the tactic.
We split them into their own file.

## TODO

This file is ported from C++ code, so many declarations lack documents.
-/

universe u

open Lean Meta Elab Tactic

namespace Mathlib.Tactic.CC

/-- Return true if `e` represents a constant value (numeral, character, or string). -/
def isValue (e : Expr) : Bool :=
  e.int?.isSome || e.isCharLit || e.isStringLit

/-- Return true if `e` represents a value (nat/int numeral, character, or string).

In addition to the conditions in `Mathlib.Tactic.CC.isValue`, this also checks that
kernel computation can compare the values for equality. -/
def isInterpretedValue (e : Expr) : MetaM Bool := do
  if e.isCharLit || e.isStringLit then
    return true
  else if e.int?.isSome then
    let type ← inferType e
    pureIsDefEq type (.const ``Nat []) <||> pureIsDefEq type (.const ``Int [])
  else
    return false

/-- Given a reflexive relation `R`, and a proof `H : a = b`, build a proof for `R a b` -/
def liftFromEq (R : Name) (H : Expr) : MetaM Expr := do
  if R == ``Eq then return H
  let HType ← whnf (← inferType H)
  -- `HType : @Eq A a _`
  let some (A, a, _) := HType.eq?
    | throwError "failed to build liftFromEq equality proof expected: {H}"
  -- `motive : (x : _) → a = x → Prop := fun x h => R a x`
  let motive ←
    withLocalDeclD `x A fun x => do
      let hType ← mkEq a x
      withLocalDeclD `h hType fun h =>
        mkRel R a x >>= mkLambdaFVars #[x, h]
  -- `minor : R a a := by rfl`
  let minor ← do
    let mt ← mkRel R a a
    let m ← mkFreshExprSyntheticOpaqueMVar mt
    m.mvarId!.applyRfl
    instantiateMVars m
  mkEqRec motive minor H

/-- Ordering on `Expr`. -/
scoped instance : Ord Expr where
  compare a b := bif Expr.lt a b then .lt else bif Expr.eqv b a then .eq else .gt

/-- Red-black maps whose keys are `Expr`s.

TODO: the choice between `TreeMap` and `HashMap` is not obvious:
once the `cc` tactic is used a lot in Mathlib, we should profile and see
if `HashMap` could be more optimal. -/
abbrev ExprMap (α : Type u) := Std.TreeMap Expr α compare

/-- Red-black sets of `Expr`s.

TODO: the choice between `TreeSet` and `HashSet` is not obvious:
once the `cc` tactic is used a lot in Mathlib, we should profile and see
if `HashSet` could be more optimal. -/
abbrev ExprSet := Std.TreeSet Expr compare

/-- `CongrTheorem`s equipped with additional infos used by congruence closure modules. -/
structure CCCongrTheorem extends CongrTheorem where
  /-- If `heqResult` is true, then lemma is based on heterogeneous equality
  and the conclusion is a heterogeneous equality. -/
  heqResult : Bool := false
  /-- If `hcongrTheorem` is true, then lemma was created using `mkHCongrWithArity`. -/
  hcongrTheorem : Bool := false

/-- Automatically generated congruence lemma based on heterogeneous equality.

This returns an annotated version of the result from `Lean.Meta.mkHCongrWithArity`. -/
def mkCCHCongrWithArity (fn : Expr) (nargs : Nat) : MetaM (Option CCCongrTheorem) := do
  let eqCongr ← try mkHCongrWithArity fn nargs catch _ => return none
  return some { eqCongr with
    heqResult := true
    hcongrTheorem := true }

/-- Keys used to find corresponding `CCCongrTheorem`s. -/
structure CCCongrTheoremKey where
  /-- The function of the given `CCCongrTheorem`. -/
  fn : Expr
  /-- The number of arguments of `fn`. -/
  nargs : Nat
  deriving BEq, Hashable

/-- Caches used to find corresponding `CCCongrTheorem`s. -/
abbrev CCCongrTheoremCache := Std.HashMap CCCongrTheoremKey (Option CCCongrTheorem)

/-- Configs used in congruence closure modules. -/
structure CCConfig where
  /-- If `true`, congruence closure will treat implicit instance arguments as constants.

  This means that setting `ignoreInstances := false` will fail to unify two definitionally equal
  instances of the same class. -/
  ignoreInstances : Bool := true
  /-- If `true`, congruence closure modulo Associativity and Commutativity. -/
  ac : Bool := true
  /-- If `hoFns` is `some fns`, then full (and more expensive) support for higher-order functions is
  *only* considered for the functions in fns and local functions. The performance overhead is
  described in the paper "Congruence Closure in Intensional Type Theory". If `hoFns` is `none`,
  then full support is provided for *all* constants. -/
  hoFns : Option (List Name) := none
  /-- If `true`, then use excluded middle -/
  em : Bool := true
  /-- If `true`, we treat values as atomic symbols -/
  values : Bool := false
  deriving Inhabited

/-- An `ACApps` represents either just an `Expr` or applications of an associative and commutative
  binary operator. -/
inductive ACApps where
  /-- An `ACApps` of just an `Expr`. -/
  | ofExpr (e : Expr) : ACApps
  /-- An `ACApps` of applications of a binary operator. `args` are assumed to be sorted.

    See also `ACApps.mkApps` if `args` are not yet sorted. -/
  | apps (op : Expr) (args : Array Expr) : ACApps
  deriving Inhabited, BEq

instance : Coe Expr ACApps := ⟨ACApps.ofExpr⟩
attribute [coe] ACApps.ofExpr

/-- Ordering on `ACApps` sorts `.ofExpr` before `.apps`, and sorts `.apps` by function symbol,
  then by shortlex order. -/
scoped instance : Ord ACApps where
  compare
    | .ofExpr a, .ofExpr b => compare a b
    | .ofExpr _, .apps _ _ => .lt
    | .apps _ _, .ofExpr _ => .gt
    | .apps op₁ args₁, .apps op₂ args₂ =>
      compare op₁ op₂ |>.then <| compare args₁.size args₂.size |>.dthen fun hs => Id.run do
        have hs := eq_of_beq <| Std.LawfulBEqCmp.compare_eq_iff_beq.mp hs
        for hi : i in [:args₁.size] do
          have hi := hi.right
          let o := compare args₁[i] (args₂[i]'(hs ▸ hi.1))
          if o != .eq then return o
        return .eq

/-- Return true iff `e₁` is a "subset" of `e₂`.

Example: The result is `true` for `e₁ := a*a*a*b*d` and `e₂ := a*a*a*a*b*b*c*d*d`.
The result is also `true` for `e₁ := a` and `e₂ := a*a*a*b*c`. -/
def ACApps.isSubset : (e₁ e₂ : ACApps) → Bool
  | .ofExpr a, .ofExpr b => a == b
  | .ofExpr a, .apps _ args => args.contains a
  | .apps _ _, .ofExpr _ => false
  | .apps op₁ args₁, .apps op₂ args₂ =>
    if op₁ == op₂ then
      if args₁.size ≤ args₂.size then Id.run do
        let mut i₁ := 0
        let mut i₂ := 0
        while h : i₁ < args₁.size ∧ i₂ < args₂.size do
          if args₁[i₁] == args₂[i₂] then
            i₁ := i₁ + 1
            i₂ := i₂ + 1
          else if Expr.lt args₂[i₂] args₁[i₁] then
            i₂ := i₂ + 1
          else return false
        return i₁ == args₁.size
      else false
    else false

/-- Appends elements of the set difference `e₁ \ e₂` to `r`.
Example: given `e₁ := a*a*a*a*b*b*c*d*d*d` and `e₂ := a*a*a*b*b*d`,
the result is `#[a, c, d, d]`

Precondition: `e₂.isSubset e₁` -/
def ACApps.diff (e₁ e₂ : ACApps) (r : Array Expr := #[]) : Array Expr :=
  match e₁ with
  | .apps op₁ args₁ => Id.run do
    let mut r := r
    match e₂ with
    | .apps op₂ args₂ =>
      if op₁ == op₂ then
        let mut i₂ := 0
        for h : i₁ in [:args₁.size] do
          if i₂ == args₂.size then
            r := r.push args₁[i₁]
          else if args₁[i₁] == args₂[i₂]! then
            i₂ := i₂ + 1
          else
            r := r.push args₁[i₁]
    | .ofExpr e₂ =>
      let mut found := false
      for h : i in [:args₁.size] do
        if !found && args₁[i] == e₂ then
          found := true
        else
          r := r.push args₁[i]
    return r
  | .ofExpr e => if e₂ == e then r else r.push e

/-- Appends arguments of `e` to `r`. -/
def ACApps.append (op : Expr) (e : ACApps) (r : Array Expr := #[]) : Array Expr :=
  match e with
  | .apps op' args =>
    if op' == op then r ++ args else r
  | .ofExpr e =>
    r.push e

/-- Appends elements in the intersection of `e₁` and `e₂` to `r`. -/
def ACApps.intersection (e₁ e₂ : ACApps) (r : Array Expr := #[]) : Array Expr :=
  match e₁, e₂ with
  | .apps _ args₁, .apps _ args₂ => Id.run do
    let mut r := r
    let mut i₁ := 0
    let mut i₂ := 0
    while h : i₁ < args₁.size ∧ i₂ < args₂.size do
      if args₁[i₁] == args₂[i₂] then
        r := r.push args₁[i₁]
        i₁ := i₁ + 1
        i₂ := i₂ + 1
      else if Expr.lt args₂[i₂] args₁[i₁] then
        i₂ := i₂ + 1
      else
        i₁ := i₁ + 1
    return r
  | _, _ => r

/-- Sorts `args` and applies them to `ACApps.apps`. -/
def ACApps.mkApps (op : Expr) (args : Array Expr) : ACApps :=
  .apps op (args.qsort Expr.lt)

/-- Flattens given two `ACApps`. -/
def ACApps.mkFlatApps (op : Expr) (e₁ e₂ : ACApps) : ACApps :=
  let newArgs := ACApps.append op e₁
  let newArgs := ACApps.append op e₂ newArgs
  -- TODO: this does a full sort but `newArgs` consists of two sorted subarrays,
  -- so if we want to optimize this, some form of merge sort might be faster.
  ACApps.mkApps op newArgs

/-- Converts an `ACApps` to an `Expr`. This returns `none` when the empty applications are given. -/
def ACApps.toExpr : ACApps → Option Expr
  | .apps _ ⟨[]⟩ => none
  | .apps op ⟨arg₀ :: args⟩ => some <| args.foldl (fun e arg => mkApp2 op e arg) arg₀
  | .ofExpr e => some e

/-- Red-black maps whose keys are `ACApps`es.

TODO: the choice between `TreeMap` and `HashMap` is not obvious:
once the `cc` tactic is used a lot in Mathlib, we should profile and see
if `HashMap` could be more optimal. -/
abbrev ACAppsMap (α : Type u) := Std.TreeMap ACApps α compare

/-- Red-black sets of `ACApps`es.

TODO: the choice between `TreeSet` and `HashSet` is not obvious:
once the `cc` tactic is used a lot in Mathlib, we should profile and see
if `HashSet` could be more optimal. -/
abbrev ACAppsSet := Std.TreeSet ACApps compare

/-- For proof terms generated by AC congruence closure modules, we want a placeholder as an equality
  proof between given two terms which will be generated by non-AC congruence closure modules later.
  `DelayedExpr` represents it using `eqProof`. -/
inductive DelayedExpr where
  /-- A `DelayedExpr` of just an `Expr`. -/
  | ofExpr (e : Expr) : DelayedExpr
  /-- A placeholder as an equality proof between given two terms which will be generated by non-AC
  congruence closure modules later. -/
  | eqProof (lhs rhs : Expr) : DelayedExpr
  /-- Will be applied to `congr_arg`. -/
  | congrArg (f : Expr) (h : DelayedExpr) : DelayedExpr
  /-- Will be applied to `congr_fun`. -/
  | congrFun (h : DelayedExpr) (a : ACApps) : DelayedExpr
  /-- Will be applied to `Eq.symm`. -/
  | eqSymm (h : DelayedExpr) : DelayedExpr
  /-- Will be applied to `Eq.symm`. -/
  | eqSymmOpt (a₁ a₂ : ACApps) (h : DelayedExpr) : DelayedExpr
  /-- Will be applied to `Eq.trans`. -/
  | eqTrans (h₁ h₂ : DelayedExpr) : DelayedExpr
  /-- Will be applied to `Eq.trans`. -/
  | eqTransOpt (a₁ a₂ a₃ : ACApps) (h₁ h₂ : DelayedExpr) : DelayedExpr
  /-- Will be applied to `heq_of_eq`. -/
  | heqOfEq (h : DelayedExpr) : DelayedExpr
  /-- Will be applied to `HEq.symm`. -/
  | heqSymm (h : DelayedExpr) : DelayedExpr
  deriving Inhabited

instance : Coe Expr DelayedExpr := ⟨DelayedExpr.ofExpr⟩
attribute [coe] DelayedExpr.ofExpr

/-- This is used as a proof term in `Entry`s instead of `Expr`. -/
inductive EntryExpr
  /-- An `EntryExpr` of just an `Expr`. -/
  | ofExpr (e : Expr) : EntryExpr
  /-- dummy congruence proof, it is just a placeholder. -/
  | congr : EntryExpr
  /-- dummy eq_true proof, it is just a placeholder -/
  | eqTrue : EntryExpr
  /-- dummy refl proof, it is just a placeholder. -/
  | refl : EntryExpr
  /-- An `EntryExpr` of a `DelayedExpr`. -/
  | ofDExpr (e : DelayedExpr) : EntryExpr
  deriving Inhabited

instance : ToMessageData EntryExpr where
  toMessageData
  | .ofExpr e => toMessageData e
  | .congr => m!"[congruence proof]"
  | .eqTrue => m!"[eq_true proof]"
  | .refl => m!"[refl proof]"
  | .ofDExpr _ => m!"[delayed expression]"

instance : Coe Expr EntryExpr := ⟨EntryExpr.ofExpr⟩
attribute [coe] EntryExpr.ofExpr

/-- Equivalence class data associated with an expression `e`. -/
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
  of this entry was involved in a merge. -/
  mt : Nat
  deriving Inhabited

/-- Stores equivalence class data associated with an expression `e`. -/
abbrev Entries := ExprMap Entry

/-- Equivalence class data associated with an expression `e` used by AC congruence closure
modules. -/
structure ACEntry where
  /-- Natural number associated to an expression. -/
  idx : Nat
  /-- AC variables that occur on the left hand side of an equality which `e` occurs as the left hand
  side of in `CCState.acR`. -/
  RLHSOccs : ACAppsSet := ∅
  /-- AC variables that occur on the **left** hand side of an equality which `e` occurs as the right
  hand side of in `CCState.acR`. Don't confuse. -/
  RRHSOccs : ACAppsSet := ∅
  deriving Inhabited

/-- Returns the occurrences of this entry in either the LHS or RHS. -/
def ACEntry.ROccs (ent : ACEntry) : (inLHS : Bool) → ACAppsSet
  | true => ent.RLHSOccs
  | false => ent.RRHSOccs

/-- Used to record when an expression processed by `cc` occurs in another expression. -/
structure ParentOcc where
  expr : Expr
  /-- If `symmTable` is true, then we should use the `symmCongruences`, otherwise `congruences`.
  Remark: this information is redundant, it can be inferred from `expr`. We use store it for
  performance reasons. -/
  symmTable : Bool

/-- Red-black sets of `ParentOcc`s. -/
abbrev ParentOccSet := Std.TreeSet ParentOcc (Ordering.byKey ParentOcc.expr compare)

/-- Used to map an expression `e` to another expression that contains `e`.

When `e` is normalized, its parents should also change. -/
abbrev Parents := ExprMap ParentOccSet

inductive CongruencesKey
  /-- `fn` is First-Order: we do not consider all partial applications. -/
  | fo (fn : Expr) (args : Array Expr) : CongruencesKey
  /-- `fn` is Higher-Order. -/
  | ho (fn : Expr) (arg : Expr) : CongruencesKey
  deriving BEq, Hashable

/-- Maps each expression (via `mkCongruenceKey`) to expressions it might be congruent to. -/
abbrev Congruences := Std.HashMap CongruencesKey (List Expr)

structure SymmCongruencesKey where
  (h₁ h₂ : Expr)
  deriving BEq, Hashable

/-- The symmetric variant of `Congruences`.

The `Name` identifies which relation the congruence is considered for.
Note that this only works for two-argument relations: `ModEq n` and `ModEq m` are considered the
same. -/
abbrev SymmCongruences := Std.HashMap SymmCongruencesKey (List (Expr × Name))

/-- Stores the root representatives of subsingletons, this uses `FastSingleton` instead of
`Subsingleton`. -/
abbrev SubsingletonReprs := ExprMap Expr

/-- Stores the root representatives of `.instImplicit` arguments. -/
abbrev InstImplicitReprs := ExprMap (List Expr)

abbrev TodoEntry := Expr × Expr × EntryExpr × Bool

abbrev ACTodoEntry := ACApps × ACApps × DelayedExpr

/-- Congruence closure state.
This may be considered to be a set of expressions and an equivalence class over this set.
The equivalence class is generated by the equational rules that are added to the `CCState` and
congruence, that is, if `a = b` then `f(a) = f(b)` and so on. -/
structure CCState extends CCConfig where
  /-- Maps known expressions to their equivalence class data. -/
  entries : Entries := ∅
  /-- Maps an expression `e` to the expressions `e` occurs in. -/
  parents : Parents := ∅
  /-- Maps each expression to a set of expressions it might be congruent to. -/
  congruences : Congruences := ∅
  /-- Maps each expression to a set of expressions it might be congruent to,
  via the symmetrical relation. -/
  symmCongruences : SymmCongruences := ∅
  subsingletonReprs : SubsingletonReprs := ∅
  /-- Records which instances of the same class are defeq. -/
  instImplicitReprs : InstImplicitReprs := ∅
  /-- The congruence closure module has a mode where the root of each equivalence class is marked as
  an interpreted/abstract value. Moreover, in this mode proof production is disabled.
  This capability is useful for heuristic instantiation. -/
  frozePartitions : Bool := false
  /-- Mapping from operators occurring in terms and their canonical
  representation in this module -/
  canOps : ExprMap Expr := ∅
  /-- Whether the canonical operator is supported by AC. -/
  opInfo : ExprMap Bool := ∅
  /-- Extra `Entry` information used by the AC part of the tactic. -/
  acEntries : ExprMap ACEntry := ∅
  /-- Records equality between `ACApps`. -/
  acR : ACAppsMap (ACApps × DelayedExpr) := ∅
  /-- Returns true if the `CCState` is inconsistent. For example if it had both `a = b` and `a ≠ b`
  in it. -/
  inconsistent : Bool := false
  /-- "Global Modification Time". gmt is a number stored on the `CCState`,
  it is compared with the modification time of a cc_entry in e-matching. See `CCState.mt`. -/
  gmt : Nat := 0
  deriving Inhabited

attribute [inherit_doc SubsingletonReprs] CCState.subsingletonReprs

/-- Update the `CCState` by constructing and inserting a new `Entry`. -/
def CCState.mkEntryCore (ccs : CCState) (e : Expr) (interpreted : Bool) (constructor : Bool) :
    CCState :=
  assert! ccs.entries[e]? |>.isNone
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
      fo := false }
  { ccs with entries := ccs.entries.insert e n }

namespace CCState

/-- Get the root representative of the given expression. -/
def root (ccs : CCState) (e : Expr) : Expr :=
  match ccs.entries[e]? with
  | some n => n.root
  | none => e

/-- Get the next element in the equivalence class.
Note that if the given `Expr` `e` is not in the graph then it will just return `e`. -/
def next (ccs : CCState) (e : Expr) : Expr :=
  match ccs.entries[e]? with
  | some n => n.next
  | none => e

/-- Check if `e` is the root of the congruence class. -/
def isCgRoot (ccs : CCState) (e : Expr) : Bool :=
  match ccs.entries[e]? with
  | some n => e == n.cgRoot
  | none => true

/--
"Modification Time". The field `mt` is used to implement the mod-time optimization introduced by the
Simplify theorem prover. The basic idea is to introduce a counter `gmt` that records the number of
heuristic instantiation that have occurred in the current branch. It is incremented after each round
of heuristic instantiation. The field `mt` records the last time any proper descendant of this
entry was involved in a merge. -/
def mt (ccs : CCState) (e : Expr) : Nat :=
  match ccs.entries[e]? with
  | some n => n.mt
  | none => ccs.gmt

/-- Is the expression in an equivalence class with only one element (namely, itself)? -/
def inSingletonEqc (ccs : CCState) (e : Expr) : Bool :=
  match ccs.entries[e]? with
  | some it => it.next == e
  | none => true

/-- Append to `roots` all the roots of equivalence classes in `ccs`.

If `nonsingletonOnly` is true, we skip all the singleton equivalence classes. -/
def getRoots (ccs : CCState) (roots : Array Expr) (nonsingletonOnly : Bool) : Array Expr :=
  Id.run do
    let mut roots := roots
    for (k, n) in ccs.entries do
      if k == n.root && (!nonsingletonOnly || !ccs.inSingletonEqc k) then
        roots := roots.push k
    return roots

/-- Check for integrity of the `CCState`. -/
def checkEqc (ccs : CCState) (e : Expr) : Bool :=
  toBool <| Id.run <| OptionT.run do
    let root := ccs.root e
    let mut size : Nat := 0
    let mut it := e
    repeat
      let some itN := ccs.entries[it]? | failure
      guard (itN.root == root)
      let mut it₂ := it
      -- following `target` fields should lead to root
      repeat
        let it₂N := ccs.entries[it₂]?
        match it₂N.bind Entry.target with
        | some it₃ => it₂ := it₃
        | none => break
      guard (it₂ == root)
      it := itN.next
      size := size + 1
    until it == e
    guard (ccs.entries[root]? |>.any (·.size == size))

/-- Check for integrity of the `CCState`. -/
def checkInvariant (ccs : CCState) : Bool :=
  ccs.entries.all fun k n => k != n.root || checkEqc ccs k

def getNumROccs (ccs : CCState) (e : Expr) (inLHS : Bool) : Nat :=
  match ccs.acEntries[e]? with
  | some ent => (ent.ROccs inLHS).size
  | none => 0

/-- Search for the AC-variable (`Entry.acVar`) with the least occurrences in the state. -/
def getVarWithLeastOccs (ccs : CCState) (e : ACApps) (inLHS : Bool) : Option Expr :=
  match e with
  | .apps _ args => Id.run do
    let mut r := args[0]?
    let mut numOccs := r.casesOn 0 fun r' => ccs.getNumROccs r' inLHS
    for hi : i in [1:args.size] do
      if args[i] != (args[i - 1]'(Nat.lt_of_le_of_lt (i.sub_le 1) hi.2.1)) then
        let currOccs := ccs.getNumROccs args[i] inLHS
        if currOccs < numOccs then
          r := args[i]
          numOccs := currOccs
    return r
  | .ofExpr e => e

/-- Search for the AC-variable (`Entry.acVar`) with the fewest occurrences in the LHS. -/
def getVarWithLeastLHSOccs (ccs : CCState) (e : ACApps) : Option Expr :=
  ccs.getVarWithLeastOccs e true

/-- Search for the AC-variable (`Entry.acVar`) with the fewest occurrences in the RHS. -/
def getVarWithLeastRHSOccs (ccs : CCState) (e : ACApps) : Option Expr :=
  ccs.getVarWithLeastOccs e false

open MessageData

/-- Pretty print the entry associated with the given expression. -/
def ppEqc (ccs : CCState) (e : Expr) : MessageData := Id.run do
  let mut lr : List MessageData := []
  let mut it := e
  repeat
    let some itN := ccs.entries[it]? | break
    let mdIt : MessageData :=
      if it.isForall || it.isLambda || it.isLet then paren (ofExpr it) else ofExpr it
    lr := mdIt :: lr
    it := itN.next
  until it == e
  let l := lr.reverse
  return bracket "{" (group <| joinSep l (ofFormat ("," ++ .line))) "}"

/-- Pretty print the entire cc graph.
If the `nonSingleton` argument is set to `true` then singleton equivalence classes will be
omitted. -/
def ppEqcs (ccs : CCState) (nonSingleton : Bool := true) : MessageData :=
  let roots := ccs.getRoots #[] nonSingleton
  let a := roots.map (fun root => ccs.ppEqc root)
  let l := a.toList
  bracket "{" (group <| joinSep l (ofFormat ("," ++ .line))) "}"

def ppParentOccsAux (ccs : CCState) (e : Expr) : MessageData :=
  match ccs.parents[e]? with
  | some poccs =>
    let r := ofExpr e ++ ofFormat (.line ++ ":=" ++ .line)
    let ps := poccs.toList.map fun o => ofExpr o.expr
    group (r ++ bracket "{" (group <| joinSep ps (ofFormat ("," ++ .line))) "}")
  | none => ofFormat .nil

def ppParentOccs (ccs : CCState) : MessageData :=
  let r := ccs.parents.toList.map fun (k, _) => ccs.ppParentOccsAux k
  bracket "{" (group <| joinSep r (ofFormat ("," ++ .line))) "}"

def ppACDecl (ccs : CCState) (e : Expr) : MessageData :=
  match ccs.acEntries[e]? with
  | some it => group (ofFormat (s!"x_{it.idx}" ++ .line ++ ":=" ++ .line) ++ ofExpr e)
  | none => nil

def ppACDecls (ccs : CCState) : MessageData :=
  let r := ccs.acEntries.toList.map fun (k, _) => ccs.ppACDecl k
  bracket "{" (joinSep r (ofFormat ("," ++ .line))) "}"

def ppACExpr (ccs : CCState) (e : Expr) : MessageData :=
  if let some it := ccs.acEntries[e]? then
    s!"x_{it.idx}"
  else
    ofExpr e

partial def ppACApps (ccs : CCState) : ACApps → MessageData
  | .apps op args =>
    let r := ofExpr op :: args.toList.map fun arg => ccs.ppACExpr arg
    sbracket (joinSep r (ofFormat .line))
  | .ofExpr e => ccs.ppACExpr e

def ppACR (ccs : CCState) : MessageData :=
  let r := ccs.acR.toList.map fun (k, p, _) => group <|
    ccs.ppACApps k ++ ofFormat (Format.line ++ "--> ") ++ nest 4 (Format.line ++ ccs.ppACApps p)
  bracket "{" (joinSep r (ofFormat ("," ++ .line))) "}"

def ppAC (ccs : CCState) : MessageData :=
  sbracket (ccs.ppACDecls ++ ofFormat ("," ++ .line) ++ ccs.ppACR)

end CCState

/-- The congruence closure module (optionally) uses a normalizer.
The idea is to use it (if available) to normalize auxiliary expressions
produced by internal propagation rules (e.g., subsingleton propagator). -/
structure CCNormalizer where
  normalize : Expr → MetaM Expr

attribute [inherit_doc CCNormalizer] CCNormalizer.normalize

structure CCPropagationHandler where
  propagated : Array Expr → MetaM Unit
  /-- Congruence closure module invokes the following method when
  a new auxiliary term is created during propagation. -/
  newAuxCCTerm : Expr → MetaM Unit

/-- `CCStructure` extends `CCState` (which records a set of facts derived by congruence closure)
by recording which steps still need to be taken to solve the goal.
-/
structure CCStructure extends CCState where
  /-- Equalities that have been discovered but not processed. -/
  todo : Array TodoEntry := #[]
  /-- AC-equalities that have been discovered but not processed. -/
  acTodo : Array ACTodoEntry := #[]
  normalizer : Option CCNormalizer := none
  phandler : Option CCPropagationHandler := none
  cache : CCCongrTheoremCache := ∅
  deriving Inhabited

initialize
  registerTraceClass `Meta.Tactic.cc.merge
  registerTraceClass `Meta.Tactic.cc.failure
  registerTraceClass `Debug.Meta.Tactic.cc
  registerTraceClass `Debug.Meta.Tactic.cc.ac
  registerTraceClass `Debug.Meta.Tactic.cc.parentOccs

end Mathlib.Tactic.CC
