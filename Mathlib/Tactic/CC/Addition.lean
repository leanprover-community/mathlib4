/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Miyahara Kō
-/
import Mathlib.Logic.Basic
import Mathlib.Data.Option.Defs
import Mathlib.Lean.Expr.Basic
import Mathlib.Tactic.Relation.Rfl
import Mathlib.Tactic.Relation.Symm
import Mathlib.Tactic.CC.Datatypes
import Mathlib.Tactic.CC.Lemmas

/-!
# Process when an new equation is added to a congruence closure
-/

universe u

open Lean Meta Elab Tactic Std

namespace Mathlib.Tactic.CC

initialize
  registerTraceClass `Meta.Tactic.cc.merge
  registerTraceClass `Meta.Tactic.cc.failure
  registerTraceClass `Debug.Meta.Tactic.cc
  registerTraceClass `Debug.Meta.Tactic.cc.ac
  registerTraceClass `Debug.Meta.Tactic.cc.parentOccs

/-- The monad for the `cc` tactic stores the current state of the tactic. -/
abbrev CCM := StateRefT CCStructure MetaM

namespace CCM

/-- Run a computation in the `CCM` monad. -/
@[inline]
def run {α : Type} (x : CCM α) (c : CCStructure) : MetaM (α × CCStructure) := StateRefT'.run x c

/-- Update the `todo` field of the state. -/
@[inline]
def modifyTodo (f : Array TodoEntry → Array TodoEntry) : CCM Unit :=
  modify fun cc => { cc with todo := f cc.todo }

/-- Update the `acTodo` field of the state. -/
@[inline]
def modifyACTodo (f : Array ACTodoEntry → Array ACTodoEntry) : CCM Unit :=
  modify fun cc => { cc with acTodo := f cc.acTodo }

/-- Update the `cache` field of the state. -/
@[inline]
def modifyCache (f : CCCongrTheoremCache → CCCongrTheoremCache) : CCM Unit :=
  modify fun cc => { cc with cache := f cc.cache }

/-- Read the `todo` field of the state. -/
@[inline]
def getTodo : CCM (Array TodoEntry) := do
  return (← get).todo

/-- Read the `acTodo` field of the state. -/
@[inline]
def getACTodo : CCM (Array ACTodoEntry) := do
  return (← get).acTodo

/-- Read the `cache` field of the state. -/
@[inline]
def getCache : CCM CCCongrTheoremCache := do
  return (← get).cache

/-- Look up an entry associated with the given expression. -/
def getEntry (e : Expr) : CCM (Option Entry) := do
  return (← get).entries.find? e

/-- Use the normalizer to normalize `e`.

If no normalizer was configured, returns `e` itself. -/
def normalize (e : Expr) : CCM Expr := do
  if let some normalizer := (← get).normalizer then
    normalizer.normalize e
  else
    return e

/-- Add a new entry to the end of the todo list.

See also `pushEq`, `pushHEq` and `pushReflEq`. -/
def pushTodo (lhs rhs : Expr) (H : EntryExpr) (heqProof : Bool) : CCM Unit := do
  modifyTodo fun todo => todo.push (lhs, rhs, H, heqProof)

/-- Add the equality proof `H : lhs = rhs` to the end of the todo list. -/
@[inline]
def pushEq (lhs rhs : Expr) (H : EntryExpr) : CCM Unit :=
  pushTodo lhs rhs H false

/-- Add the heterogeneous equality proof `H : HEq lhs rhs` to the end of the todo list. -/
@[inline]
def pushHEq (lhs rhs : Expr) (H : EntryExpr) : CCM Unit :=
  pushTodo lhs rhs H true

/-- Add `rfl : lhs = rhs` to the todo list. -/
@[inline]
def pushReflEq (lhs rhs : Expr) : CCM Unit :=
  pushEq lhs rhs .refl

/-- Return the root expression of the expression's congruence class. -/
def getRoot (e : Expr) : CCM Expr := do
  return (← get).root e

/-- Is `e` the root of its congruence class? -/
def isCgRoot (e : Expr) : CCM Bool := do
  return (← get).isCgRoot e

/-- Update the `child` so its parent becomes `parent`. -/
def addOccurrence (parent child : Expr) (symmTable : Bool) : CCM Unit := do
  let childRoot ← getRoot child
  modify fun ccs =>
    { ccs with
      parents := ccs.parents.alter childRoot fun ps? =>
        let ps := ps?.getD ∅
        ps.insert { expr := parent, symmTable } }

/--
Return true iff the given function application are congruent

`e₁` should have the form `f a` and `e₂` the form `g b`.

See paper: Congruence Closure for Intensional Type Theory. -/
partial def isCongruent (e₁ e₂ : Expr) : CCM Bool := do
  let .app f a := e₁ | failure
  let .app g b := e₂ | failure
  -- If they are non-dependent functions, then we can compare all arguments at once.
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

/-- Return the `CongruencesKey` associated with an expression of the form `f a`. -/
def mkCongruencesKey (e : Expr) : CCM CongruencesKey := do
  let .app f a := e | failure
  if (← getEntry e).any Entry.fo then
    -- first-order case, where we do not consider all partial applications
    e.withApp fun fn args => do
      return .fo (← getRoot fn) (← args.mapM getRoot)
  else
    return .ho (← getRoot f) (← getRoot a)

/-- Return the `SymmCongruencesKey` associated with the equality `lhs = rhs`. -/
def mkSymmCongruencesKey (lhs rhs : Expr) : CCM SymmCongruencesKey := do
  let lhs ← getRoot lhs
  let rhs ← getRoot rhs
  if hash lhs > hash rhs then return { h₁ := rhs, h₂ := lhs } else return { h₁ := lhs, h₂ := rhs }

/-- Try to find a congruence theorem for an application of `fn` with `nargs` arguments, with support
for `HEq`. -/
def mkCCHCongrTheorem (fn : Expr) (nargs : Nat) : CCM (Option CCCongrTheorem) := do
  let cache ← getCache

  -- Check if `{ fn, nargs }` is in the cache
  let key₁ : CCCongrTheoremKey := { fn, nargs }
  if let some it₁ := cache.findEntry? key₁ then
    return it₁.2

  -- Try automatically generated congruence lemma with support for heterogeneous equality.
  let lemm ← mkCCHCongrWithArity fn nargs

  if let some lemm := lemm then
    modifyCache fun ccc => ccc.insert key₁ (some lemm)
    return lemm

  -- cache failure
  modifyCache fun ccc => ccc.insert key₁ none
  return none

/-- Try to find a congruence theorem for the expression `e` with support for `HEq`. -/
def mkCCCongrTheorem (e : Expr) : CCM (Option CCCongrTheorem) := do
  let fn := e.getAppFn
  let nargs := e.getAppNumArgs
  mkCCHCongrTheorem fn nargs

/-- Record the instance `e` and add it to the set of known defeq instances. -/
def propagateInstImplicit (e : Expr) : CCM Unit := do
  let type ← inferType e
  let type ← normalize type
  match (← get).instImplicitReprs.find? type with
  | some l =>
    for e' in l do
      if ← pureIsDefEq e e' then
        pushReflEq e e'
        return
    modify fun ccs =>
      { ccs with instImplicitReprs := ccs.instImplicitReprs.insert type (e :: l) }
  | none =>
    modify fun ccs =>
      { ccs with instImplicitReprs := ccs.instImplicitReprs.insert type [e] }

/-- Treat the entry associated with `e` as a first-order function. -/
def setFO (e : Expr) : CCM Unit :=
  modify fun ccs =>
    { ccs with entries := ccs.entries.modify e fun d => { d with fo := true } }

/-- Update the modification time of the congruence class of `e`. -/
partial def updateMT (e : Expr) : CCM Unit := do
  let r ← getRoot e
  let some ps := (← get).parents.find? r | return
  for p in ps do
    let some it ← getEntry p.expr | failure
    let gmt := (← get).gmt
    if it.mt < gmt then
      let newIt := { it with mt := gmt }
      modify fun ccs =>
        { ccs with entries := ccs.entries.insert p.expr newIt }
      updateMT p.expr

/-- Does the congruence class with root `root` have any `HEq` proofs? -/
def hasHEqProofs (root : Expr) : CCM Bool := do
  let some n ← getEntry root | failure
  guard (n.root == root)
  return n.heqProofs

/-- Apply symmetry to `H`, which is an `Eq` or a `HEq`.

* If `heqProofs` is true, ensure the result is a `HEq` (otherwise it is assumed to be `Eq`).
* If `flipped` is true, apply `symm`, otherwise keep the same direction. -/
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

/-- In a delayed way, apply symmetry to `H`, which is an `Eq` or a `HEq`.

* If `heqProofs` is true, ensure the result is a `HEq` (otherwise it is assumed to be `Eq`).
* If `flipped` is true, apply `symm`, otherwise keep the same direction. -/
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

/-- Apply symmetry to `H`, which is an `Eq` or a `HEq`.

* If `heqProofs` is true, ensure the result is a `HEq` (otherwise it is assumed to be `Eq`).
* If `flipped` is true, apply `symm`, otherwise keep the same direction. -/
def flipProof (H : EntryExpr) (flipped heqProofs : Bool) : CCM EntryExpr :=
  match H with
  | .ofExpr H => EntryExpr.ofExpr <$> flipProofCore H flipped heqProofs
  | .ofDExpr H => EntryExpr.ofDExpr <$> flipDelayedProofCore H flipped heqProofs
  | _ => return H

/-- Are `e₁` and `e₂` known to be in the same equivalence class? -/
def isEqv (e₁ e₂ : Expr) : CCM Bool := do
  let some n₁ ← getEntry e₁ | return false
  let some n₂ ← getEntry e₂ | return false
  return n₁.root == n₂.root

/-- Is `e₁ ≠ e₂` known to be true?

Note that this is stronger than `not (isEqv e₁ e₂)`:
only if we can prove they are distinct this returns `true`. -/
def isNotEqv (e₁ e₂ : Expr) : CCM Bool := do
  let tmp ← mkEq e₁ e₂
  if ← isEqv tmp (.const ``False []) then return true
  let tmp ← mkHEq e₁ e₂
  isEqv tmp (.const ``False [])

/-- Is the proposition `e` known to be true? -/
@[inline]
def isEqTrue (e : Expr) : CCM Bool :=
  isEqv e (.const ``True [])

/-- Is the proposition `e` known to be false? -/
@[inline]
def isEqFalse (e : Expr) : CCM Bool :=
  isEqv e (.const ``False [])

/-- Apply transitivity to `H₁` and `H₂`, which are both `Eq` or `HEq` depending on `heqProofs`. -/
def mkTrans (H₁ H₂ : Expr) (heqProofs : Bool) : MetaM Expr :=
  if heqProofs then mkHEqTrans H₁ H₂ else mkEqTrans H₁ H₂

/-- Apply transitivity to `H₁?` and `H₂`, which are both `Eq` or `HEq` depending on `heqProofs`.

If `H₁?` is `none`, return `H₂` instead. -/
def mkTransOpt (H₁? : Option Expr) (H₂ : Expr) (heqProofs : Bool) : MetaM Expr :=
  match H₁? with
  | some H₁ => mkTrans H₁ H₂ heqProofs
  | none => pure H₂

mutual
/-- Use congruence on arguments to prove `lhs = rhs`.

That is, tries to prove that `lhsFn lhsArgs[0] ... lhsArgs[n-1] = lhsFn rhsArgs[0] ... rhsArgs[n-1]`
by showing that `lhsArgs[i] = rhsArgs[i]` for all `i`.

Fails if the head function of `lhs` is not that of `rhs`. -/
partial def mkCongrProofCore (lhs rhs : Expr) (heqProofs : Bool) : CCM Expr := do
  let mut lhsArgsRev : Array Expr := #[]
  let mut rhsArgsRev : Array Expr := #[]
  let mut lhsIt := lhs
  let mut rhsIt := rhs
  -- Collect the arguments to `lhs` and `rhs`.
  -- As an optimization, we stop collecting arguments as soon as the functions are defeq,
  -- so `lhsFn` and `rhsFn` might end up still of the form `(f x y z)` and `(f x' y' z')`.
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
  -- If we collect no arguments, the expressions themselves are defeq; return `rfl`.
  if lhsArgsRev.isEmpty then
    if heqProofs then
      return (← mkHEqRefl lhs)
    else
      return (← mkEqRefl lhs)
  let lhsArgs := lhsArgsRev.reverse
  let rhsArgs := rhsArgsRev.reverse
  -- Ensure that `lhsFn = rhsFn`, they have the same type and the same list of arguments.
  let PLift.up ha ← if ha : lhsArgs.size = rhsArgs.size then pure (PLift.up ha) else failure
  let lhsFn := lhsIt
  let rhsFn := rhsIt
  guard (← isEqv lhsFn rhsFn <||> pureIsDefEq lhsFn rhsFn)
  guard (← pureIsDefEq (← inferType lhsFn) (← inferType rhsFn))
  /- Create `r`, a proof for
        `lhsFn lhsArgs[0] ... lhsArgs[n-1] = lhsFn rhsArgs[0] ... rhsArgs[n-1]`
     where `n := lhsArgs.size` -/
  let some specLemma ← mkCCHCongrTheorem lhsFn lhsArgs.size | failure
  let mut kindsIt := specLemma.argKinds
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
  let mut r := mkAppN specLemma.proof lemmaArgs
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

/-- If `e₁ : R lhs₁ rhs₁`, `e₂ : R lhs₂ rhs₂` and `lhs₁ = rhs₂`, where `R` is a symmetric relation,
prove `R lhs₁ rhs₁` is equivalent to `R lhs₂ rhs₂`.

 * if `lhs₁` is known to equal `lhs₂`, return `none`
 * if `lhs₁` is not known to equal `rhs₂`, fail. -/
partial def mkSymmCongrProof (e₁ e₂ : Expr) (heqProofs : Bool) : CCM (Option Expr) := do
  let some (R₁, lhs₁, rhs₁) ← e₁.relSidesIfSymm? | return none
  let some (R₂, lhs₂, rhs₂) ← e₂.relSidesIfSymm? | return none
  if R₁ != R₂ then return none
  if (← isEqv lhs₁ lhs₂) then
    return none
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
      mkAppM ``Iff.intro
        #[← mkLambdaFVars #[h₁] (← h₁.applySymm), ← mkLambdaFVars #[h₂] (← h₂.applySymm)]
  let mut e₁EqNewE₁ := mkApp3 (.const ``propext []) e₁ newE₁ e₁IffNewE₁
  let newE₁EqE₂ ← mkCongrProofCore newE₁ e₂ heqProofs
  if heqProofs then
    e₁EqNewE₁ ← mkAppM ``heq_of_eq #[e₁EqNewE₁]
  return some (← mkTrans e₁EqNewE₁ newE₁EqE₂ heqProofs)

/-- Use congruence on arguments to prove `e₁ = e₂`.

Special case: if `e₁` and `e₂` have the form `R lhs₁ rhs₁` and `R lhs₂ rhs₂` such that
`R` is symmetric and `lhs₁ = rhs₂`, then use those facts instead. -/
partial def mkCongrProof (e₁ e₂ : Expr) (heqProofs : Bool) : CCM Expr := do
  if let some r ← mkSymmCongrProof e₁ e₂ heqProofs then
    return r
  else
    mkCongrProofCore e₁ e₂ heqProofs

/-- Turn a delayed proof into an actual proof term. -/
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

/-- Use the format of `H` to try and construct a proof or `lhs = rhs`:
 * If `H = .congr`, then use congruence.
 * If `H = .eqTrue`, try to prove `lhs = True` or `rhs = True`,
   if they have the format `R a b`, by proving `a = b`.
 * Otherwise, return the (delayed) proof encoded by `H` itself. -/
partial def mkProof (lhs rhs : Expr) (H : EntryExpr) (heqProofs : Bool) : CCM Expr := do
  match H with
  | .congr => mkCongrProof lhs rhs heqProofs
  | .eqTrue =>
    let (flip, some (R, a, b)) ←
      if lhs == .const ``True [] then
        ((true, ·)) <$> rhs.relSidesIfRefl?
      else
        ((false, ·)) <$> lhs.relSidesIfRefl?
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

/-- Build a proof for `e₁ = e₂`.
The result is `none` if `e₁` and `e₂` are not in the same equivalence class. -/
@[inline]
partial def getEqProof (e₁ e₂ : Expr) : CCM (Option Expr) :=
  getEqProofCore e₁ e₂ false

/-- Build a proof for `HEq e₁ e₂`.
The result is `none` if `e₁` and `e₂` are not in the same equivalence class. -/
@[inline]
partial def getHEqProof (e₁ e₂ : Expr) : CCM (Option Expr) :=
  getEqProofCore e₁ e₂ true
end

/-- Build a proof for `e = True`. Fails if `e` is not known to be true. -/
def getEqTrueProof (e : Expr) : CCM Expr := do
  guard (← isEqTrue e)
  let some p ← getEqProof e (.const ``True []) | failure
  return p

/-- Build a proof for `e = False`. Fails if `e` is not known to be false. -/
def getEqFalseProof (e : Expr) : CCM Expr := do
  guard (← isEqFalse e)
  let some p ← getEqProof e (.const ``False []) | failure
  return p

/-- Build a proof for `a = b`. Fails if `a` and `b` are not known to be equal. -/
def getPropEqProof (a b : Expr) : CCM Expr := do
  guard (← isEqv a b)
  let some p ← getEqProof a b | failure
  return p

/-- Build a proof of `False` if the context is inconsistent.
Returns `none` if `False` is not known to be true. -/
def getInconsistencyProof : CCM (Option Expr) := do
  guard !(← get).frozePartitions
  if let some p ← getEqProof (.const ``True []) (.const ``False []) then
    return some (← mkAppM ``false_of_true_eq_false #[p])
  else
    return none

/-- Auxiliary function for comparing `lhs₁ ~ rhs₁` and `lhs₂ ~ rhs₂`,
    when `~` is symmetric/commutative.
    It returns `true` (equal) for `a ~ b` `b ~ a`-/
def compareSymmAux (lhs₁ rhs₁ lhs₂ rhs₂ : Expr) : CCM Bool := do
  let lhs₁ ← getRoot lhs₁
  let rhs₁ ← getRoot rhs₁
  let lhs₂ ← getRoot lhs₂
  let rhs₂ ← getRoot rhs₂
  let (lhs₁, rhs₁) := if rhs₁.lt lhs₁ then (rhs₁, lhs₁) else (lhs₁, rhs₁)
  let (lhs₂, rhs₂) := if rhs₂.lt lhs₂ then (rhs₂, lhs₂) else (lhs₂, rhs₂)
  return lhs₁ == lhs₂ && rhs₁ == rhs₂

/-- Given ``k₁ := (R₁ lhs₁ rhs₁, `R₁)`` and ``k₂ := (R₂ lhs₂ rhs₂, `R₂)``, return `true` if
`R₁ lhs₁ rhs₁` is equivalent to `R₂ lhs₂ rhs₂` modulo the symmetry of `R₁` and `R₂`. -/
def compareSymm : (k₁ k₂ : Expr × Name) → CCM Bool
  | (e₁, n₁), (e₂, n₂) => do
    if n₁ != n₂ then return false
    if n₁ == ``Eq || n₁ == ``Iff then
      compareSymmAux e₁.appFn!.appArg! e₁.appArg! e₂.appFn!.appArg! e₂.appArg!
    else
      let some (_, lhs₁, rhs₁) ← e₁.relSidesIfSymm? | failure
      let some (_, lhs₂, rhs₂) ← e₂.relSidesIfSymm? | failure
      compareSymmAux lhs₁ rhs₁ lhs₂ rhs₂

/-- Given `e := R lhs rhs`, if `R` is a reflexive relation and `lhs` is equivalent to `rhs`, add
equality `e = True`. -/
def checkEqTrue (e : Expr) : CCM Unit := do
  let some (_, lhs, rhs) ← e.relSidesIfRefl? | return
  if ← isEqv e (.const ``True []) then return -- it is already equivalent to `True`
  let lhsR ← getRoot lhs
  let rhsR ← getRoot rhs
  if lhsR != rhsR then return
  -- Add `e = True`
  pushEq e (.const ``True []) .eqTrue

/-- If the congruence table (`congruences` field) has congruent expression to `e`, add the
equality to the todo list. If not, add `e` to the congruence table. -/
def addCongruenceTable (e : Expr) : CCM Unit := do
  guard e.isApp
  let k ← mkCongruencesKey e
  if let some es := (← get).congruences.find? k then
    for oldE in es do
      if ← isCongruent e oldE then
        -- Found new equivalence: `e ~ oldE`
        -- 1. Update `cgRoot` field for `e`
        let some currEntry ← getEntry e | failure
        let newEntry := { currEntry with cgRoot := oldE }
        modify fun ccs => { ccs with entries := ccs.entries.insert e newEntry }
        -- 2. Put new equivalence in the todo queue
        -- TODO(Leo): check if the following line is a bottleneck
        let heqProof ← (!·) <$> pureIsDefEq (← inferType e) (← inferType oldE)
        pushTodo e oldE .congr heqProof
        return
    modify fun ccs =>
      { ccs with congruences := ccs.congruences.insert k (e :: es) }
  else
    modify fun ccs =>
      { ccs with congruences := ccs.congruences.insert k [e] }

/-- If the symm congruence table (`symmCongruences` field) has congruent expression to `e`, add the
equality to the todo list. If not, add `e` to the symm congruence table. -/
def addSymmCongruenceTable (e : Expr) : CCM Unit := do
  let some (rel, lhs, rhs) ← e.relSidesIfSymm? | failure
  let k ← mkSymmCongruencesKey lhs rhs
  let newP := (e, rel)
  if let some ps := (← get).symmCongruences.find? k then
    for p in ps do
      if ← compareSymm newP p then
        -- Found new equivalence: `e ~ p.1`
        -- 1. Update `cgRoot` field for `e`
        let some currEntry ← getEntry e | failure
        let newEntry := { currEntry with cgRoot := p.1 }
        modify fun ccs => { ccs with entries := ccs.entries.insert e newEntry }
        -- 2. Put new equivalence in the TODO queue
        -- NOTE(gabriel): support for symmetric relations is pretty much broken,
        -- since it ignores all arguments except the last two ones.
        -- e.g. this would claim that `ModEq n a b` and `ModEq m a b` are equivalent.
        -- Whitelist some relations to contain breakage:
        if rel == ``Eq || e.getAppNumArgs == 2 then
          pushEq e p.1 .congr
        checkEqTrue e
        return
    modify fun ccs =>
      { ccs with symmCongruences := ccs.symmCongruences.insert k (newP :: ps) }
    checkEqTrue e
  else
    modify fun ccs =>
      { ccs with symmCongruences := ccs.symmCongruences.insert k [newP] }
    checkEqTrue e

/-- Given subsingleton elements `a` and `b` which are not necessarily of the same type, if the
types of `a` and `b` are equivalent, add the (heterogeneous) equality proof between `a` and `b` to
the todo list. -/
def pushSubsingletonEq (a b : Expr) : CCM Unit := do
  -- Remark: we must normalize here because we have to do so before
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

/-- Given the equivalent expressions `oldRoot` and `newRoot` the root of `oldRoot` is
`newRoot`, if `oldRoot` has root representative of subsingletons, try to push the equality proof
between their root representatives to the todo list, or update the root representative to
`newRoot`. -/
def checkNewSubsingletonEq (oldRoot newRoot : Expr) : CCM Unit := do
  guard (← isEqv oldRoot newRoot)
  guard ((← getRoot oldRoot) == newRoot)
  let some it₁ := (← get).subsingletonReprs.find? oldRoot | return
  if let some it₂ := (← get).subsingletonReprs.find? newRoot then
    pushSubsingletonEq it₁ it₂
  else
    modify fun ccs =>
      { ccs with subsingletonReprs := ccs.subsingletonReprs.insert newRoot it₁ }

/-- Get all lambda expressions in the equivalence class of `e` and append to `r`.

`e` must be the root of its equivalence class. -/
def getEqcLambdas (e : Expr) (r : Array Expr := #[]) : CCM (Array Expr) := do
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

/-- Remove `fn` and expressions whose type isn't def-eq to `fn`'s type out from `lambdas`,
return the remaining lambdas applied to the reversed arguments. -/
def propagateBeta (fn : Expr) (revArgs : Array Expr) (lambdas : Array Expr)
    (newLambdaApps : Array Expr := #[]) : CCM (Array Expr) := do
  let mut newLambdaApps := newLambdaApps
  for lambda in lambdas do
    guard lambda.isLambda
    if fn != lambda then
      if ← pureIsDefEq (← inferType fn) (← inferType lambda) then
        let newApp := mkAppRev lambda revArgs
        newLambdaApps := newLambdaApps.push newApp
  return newLambdaApps

/-- Given `a`, `a₁` and `a₁NeB : a₁ ≠ b`, return a proof of `a ≠ b` if `a` and `a₁` are in the
same equivalence class. -/
def mkNeOfEqOfNe (a a₁ a₁NeB : Expr) : CCM (Option Expr) := do
  guard (← isEqv a a₁)
  if a == a₁ then
    return some a₁NeB
  let aEqA₁ ← getEqProof a a₁
  match aEqA₁ with
  | none => return none -- failed to build proof
  | some aEqA₁ => mkAppM ``ne_of_eq_of_ne #[aEqA₁, a₁NeB]

/-- Given `aNeB₁ : a ≠ b₁`, `b₁` and `b`, return a proof of `a ≠ b` if `b` and `b₁` are in the
same equivalence class. -/
def mkNeOfNeOfEq (aNeB₁ b₁ b : Expr) : CCM (Option Expr) := do
  guard (← isEqv b b₁)
  if b == b₁ then
    return some aNeB₁
  let b₁EqB ← getEqProof b b₁
  match b₁EqB with
  | none => return none -- failed to build proof
  | some b₁EqB => mkAppM ``ne_of_ne_of_eq #[aNeB₁, b₁EqB]

/-- If `e` is of the form `op e₁ e₂` where `op` is an associative and commutative binary operator,
return the canonical form of `op`. -/
def isAC (e : Expr) : CCM (Option Expr) := do
  let .app (.app op _) _ := e | return none
  let ccs ← get
  if let some cop := ccs.canOps.find? op then
    let some b := ccs.opInfo.find? cop
      | throwError "opInfo should contain all canonical operators in canOps"
    return bif b then some cop else none
  for (cop, b) in ccs.opInfo do
    if ← pureIsDefEq op cop then
      modify fun _ => { ccs with canOps := ccs.canOps.insert op cop }
      return bif b then some cop else none
  let b ←
    try
      let aop ← mkAppM ``Std.Associative #[op]
      let some _ ← synthInstance? aop | failure
      let cop ← mkAppM ``Std.Commutative #[op]
      let some _ ← synthInstance? cop | failure
      pure true
    catch _ =>
      pure false
  modify fun _ =>
    { ccs with
      canOps := ccs.canOps.insert op op
      opInfo := ccs.opInfo.insert op b }
  return bif b then some op else none

open MessageData in
/-- Given `lhs`, `rhs`, and `header := "my header:"`, Trace `my header: lhs = rhs`. -/
def dbgTraceACEq (header : String) (lhs rhs : ACApps) : CCM Unit := do
  let ccs ← get
  trace[Debug.Meta.Tactic.cc.ac]
    group (ofFormat (header ++ .line) ++ ccs.ppACApps lhs ++
      ofFormat (.line ++ "=" ++ .line) ++ ccs.ppACApps rhs)

open MessageData in
/-- Trace the state of AC module. -/
def dbgTraceACState : CCM Unit := do
  let ccs ← get
  trace[Debug.Meta.Tactic.cc.ac] group ("state: " ++ nest 6 ccs.ppAC)

/-- Return the proof of `e₁ = e₂` using `ac_rfl` tactic. -/
def mkACProof (e₁ e₂ : Expr) : MetaM Expr := do
  let eq ← mkEq e₁ e₂
  let .mvar m ← mkFreshExprSyntheticOpaqueMVar eq | failure
  AC.rewriteUnnormalized m
  let pr ← instantiateMVars (.mvar m)
  mkExpectedTypeHint pr eq

/-- Given `tr := t*r` `sr := s*r` `tEqs : t = s`, return a proof for `tr = sr`

    We use `a*b` to denote an AC application. That is, `(a*b)*(c*a)` is the term `a*a*b*c`. -/
def mkACSimpProof (tr t s r sr : ACApps) (tEqs : DelayedExpr) : MetaM DelayedExpr := do
  if tr == t then
    return tEqs
  else if tr == sr then
    let some tre := tr.toExpr | failure
    DelayedExpr.ofExpr <$> mkEqRefl tre
  else
    let .apps op _ := tr | failure
    let some re := r.toExpr | failure
    let some te := t.toExpr | failure
    let some se := s.toExpr | failure
    let some tre := tr.toExpr | failure
    let some sre := sr.toExpr | failure
    let opr := op.app re -- `(*) r`
    let rt := mkApp2 op re te -- `r * t`
    let rs := mkApp2 op re se -- `r * s`
    let rtEqrs := DelayedExpr.congrArg opr tEqs
    let trEqrt ← mkACProof tre rt
    let rsEqsr ← mkACProof rs sre
    return .eqTrans (.eqTrans trEqrt rtEqrs) rsEqsr

/-- Given `ra := a*r` `sb := b*s` `ts := t*s` `tr := t*r` `tsEqa : t*s = a` `trEqb : t*r = b`,
    return a proof for `ra = sb`.

    We use `a*b` to denote an AC application. That is, `(a*b)*(c*a)` is the term `a*a*b*c`. -/
def mkACSuperposeProof (ra sb a b r s ts tr : ACApps) (tsEqa trEqb : DelayedExpr) :
    MetaM DelayedExpr := do
  let .apps _ _ := tr | failure
  let .apps op _ := ts | failure
  let some tse := ts.toExpr | failure
  let some re := r.toExpr | failure
  let some tre := tr.toExpr | failure
  let some se := s.toExpr | failure
  let some ae := a.toExpr | failure
  let some be := b.toExpr | failure
  let some rae := ra.toExpr | failure
  let some sbe := sb.toExpr | failure
  let tsrEqar := DelayedExpr.congrFun (.congrArg op tsEqa) r -- `(t * s) * r = a * r`
  let trsEqbs := DelayedExpr.congrFun (.congrArg op trEqb) s -- `(t * r) * s = b * s`
  let tsr := mkApp2 op tse re -- `(t * s) * r`
  let trs := mkApp2 op tre se -- `(t * r) * s`
  let ar := mkApp2 op ae re -- `a * r`
  let bs := mkApp2 op be se -- `b * r`
  let tsrEqtrs ← mkACProof tsr trs -- `(t * s) * r = (t * r) * s`
  let raEqar ← mkACProof rae ar -- `r * a = a * r`
  let bsEqsb ← mkACProof bs sbe -- `b * s = s * b`
  return .eqTrans raEqar (.eqTrans (.eqSymm tsrEqar) (.eqTrans tsrEqtrs (.eqTrans trsEqbs bsEqsb)))

/-- Given `e := lhs * r` and `H : lhs = rhs`, return `rhs * r` and the proof of `e = rhs * r`. -/
def simplifyACCore (e lhs rhs : ACApps) (H : DelayedExpr) :
    CCM (ACApps × DelayedExpr) := do
  guard (lhs.isSubset e)
  if e == lhs then
    return (rhs, H)
  else
    let .apps op _ := e | failure
    let newArgs := e.diff lhs
    let r : ACApps := if newArgs.isEmpty then default else .mkApps op newArgs
    let newArgs := ACApps.append op rhs newArgs
    let newE := ACApps.mkApps op newArgs
    let some true := (← get).opInfo.find? op | failure
    let newPr ← mkACSimpProof e lhs rhs r newE H
    return (newE, newPr)

/-- The single step of `simplifyAC`.

Simplifies an expression `e` by either simplifying one argument to the AC operator, or the whole
expression. -/
def simplifyACStep (e : ACApps) : CCM (Option (ACApps × DelayedExpr)) := do
  if let .apps _ args := e then
    for h : i in [:args.size] do
      if i == 0 || (args[i]'h.2) != (args[i - 1]'(Nat.lt_of_le_of_lt (i.sub_le 1) h.2)) then
        let some ae := (← get).acEntries.find? (args[i]'h.2) | failure
        let occs := ae.RLHSOccs
        let mut Rlhs? : Option ACApps := none
        for Rlhs in occs do
          if Rlhs.isSubset e then
            Rlhs? := some Rlhs
            break
        if let some Rlhs := Rlhs? then
          let some (Rrhs, H) := (← get).acR.find? Rlhs | failure
          return (some <| ← simplifyACCore e Rlhs Rrhs H)
  else if let some p := (← get).acR.find? e then
    return some p
  return none

/-- If `e` can be simplified by the AC module, return the simplified term and the proof term of the
equality. -/
def simplifyAC (e : ACApps) : CCM (Option (ACApps × DelayedExpr)) := do
  let mut some (curr, pr) ← simplifyACStep e | return none
  repeat
    let some (newCurr, newPr) ← simplifyACStep curr | break
    pr := .eqTransOpt e curr newCurr pr newPr
    curr := newCurr
  return some (curr, pr)

/-- Insert or erase `lhs` to the occurrences of `arg` on an equality in `acR`. -/
def insertEraseROcc (arg : Expr) (lhs : ACApps) (inLHS isInsert : Bool) : CCM Unit := do
  let some entry := (← get).acEntries.find? arg | failure
  let occs := entry.ROccs inLHS
  let newOccs := if isInsert then occs.insert lhs else occs.erase (compare lhs)
  let newEntry :=
    if inLHS then { entry with RLHSOccs := newOccs } else { entry with RRHSOccs := newOccs }
  modify fun ccs => { ccs with acEntries := ccs.acEntries.insert arg newEntry }

/-- Insert or erase `lhs` to the occurrences of arguments of `e` on an equality in `acR`. -/
def insertEraseROccs (e lhs : ACApps) (inLHS isInsert : Bool) : CCM Unit := do
  match e with
  | .apps _ args =>
    insertEraseROcc args[0]! lhs inLHS isInsert
    for i in [1:args.size] do
      if args[i]! != args[i - 1]! then
        insertEraseROcc args[i]! lhs inLHS isInsert
  | .ofExpr e => insertEraseROcc e lhs inLHS isInsert

/-- Insert `lhs` to the occurrences of arguments of `e` on an equality in `acR`. -/
@[inline]
def insertROccs (e lhs : ACApps) (inLHS : Bool) : CCM Unit :=
  insertEraseROccs e lhs inLHS true

/-- Erase `lhs` to the occurrences of arguments of `e` on an equality in `acR`. -/
@[inline]
def eraseROccs (e lhs : ACApps) (inLHS : Bool) : CCM Unit :=
  insertEraseROccs e lhs inLHS false

/-- Insert `lhs` to the occurrences on an equality in `acR` corresponding to the equality
`lhs := rhs`. -/
@[inline]
def insertRBHSOccs (lhs rhs : ACApps) : CCM Unit := do
  insertROccs lhs lhs true
  insertROccs rhs lhs false

/-- Erase `lhs` to the occurrences on an equality in `acR` corresponding to the equality
`lhs := rhs`. -/
@[inline]
def eraseRBHSOccs (lhs rhs : ACApps) : CCM Unit := do
  eraseROccs lhs lhs true
  eraseROccs rhs lhs false

/-- Insert `lhs` to the occurrences of arguments of `e` on the right hand side of
an equality in `acR`. -/
@[inline]
def insertRRHSOccs (e lhs : ACApps) : CCM Unit :=
  insertROccs e lhs false

/-- Erase `lhs` to the occurrences of arguments of `e` on the right hand side of
an equality in `acR`. -/
@[inline]
def eraseRRHSOccs (e lhs : ACApps) : CCM Unit :=
  eraseROccs e lhs false

open MessageData in
/-- Try to simplify the right hand sides of equalities in `acR` by `H : lhs = rhs`. -/
def composeAC (lhs rhs : ACApps) (H : DelayedExpr) : CCM Unit := do
  let some x := (← get).getVarWithLeastRHSOccs lhs | failure
  let some ent := (← get).acEntries.find? x | failure
  let occs := ent.RRHSOccs
  for Rlhs in occs do
    let some (Rrhs, RH) := (← get).acR.find? Rlhs | failure
    if lhs.isSubset Rrhs then
      let (newRrhs, RrhsEqNewRrhs) ← simplifyACCore Rrhs lhs rhs H
      let newRH := DelayedExpr.eqTransOpt Rlhs Rrhs newRrhs RH RrhsEqNewRrhs
      modify fun ccs => { ccs with acR := ccs.acR.insert Rlhs (newRrhs, newRH) }
      eraseRRHSOccs Rrhs Rlhs
      insertRRHSOccs newRrhs Rlhs
      let ccs ← get
      trace[Debug.Meta.Tactic.cc.ac] group <|
        let oldRw :=
          paren (ccs.ppACApps Rlhs ++ ofFormat (Format.line ++ "-->" ++ .line) ++ ccs.ppACApps Rrhs)
        let newRw :=
          paren (ccs.ppACApps lhs ++ ofFormat (Format.line ++ "-->" ++ .line) ++ ccs.ppACApps rhs)
        "compose: " ++ nest 9 (group
          (oldRw ++ ofFormat (Format.line ++ "with" ++ .line) ++ newRw) ++
            ofFormat (Format.line ++ ":=" ++ .line) ++ ccs.ppACApps newRrhs)

open MessageData in
/-- Try to simplify the left hand sides of equalities in `acR` by `H : lhs = rhs`. -/
def collapseAC (lhs rhs : ACApps) (H : DelayedExpr) : CCM Unit := do
  let some x := (← get).getVarWithLeastLHSOccs lhs | failure
  let some ent := (← get).acEntries.find? x | failure
  let occs := ent.RLHSOccs
  for Rlhs in occs do
    if lhs.isSubset Rlhs then
      let some (Rrhs, RH) := (← get).acR.find? Rlhs | failure
      eraseRBHSOccs Rlhs Rrhs
      modify fun ccs => { ccs with acR := ccs.acR.erase Rlhs }
      let (newRlhs, RlhsEqNewRlhs) ← simplifyACCore Rlhs lhs rhs H
      let newRlhsEqRlhs := DelayedExpr.eqSymmOpt Rlhs newRlhs RlhsEqNewRlhs
      let newRH := DelayedExpr.eqTransOpt newRlhs Rlhs Rrhs newRlhsEqRlhs RH
      modifyACTodo fun todo => todo.push (newRlhs, Rrhs, newRH)
      let ccs ← get
      trace[Debug.Meta.Tactic.cc.ac] group <|
        let newRw :=
          paren (ccs.ppACApps lhs ++ ofFormat (Format.line ++ "-->" ++ .line) ++ ccs.ppACApps rhs)
        let oldRw :=
          paren (ccs.ppACApps Rrhs ++ ofFormat (Format.line ++ "<--" ++ .line) ++ ccs.ppACApps Rlhs)
        "collapse: " ++ nest 10 (group
          (newRw ++ ofFormat (Format.line ++ "at" ++ .line) ++ oldRw) ++
            ofFormat (Format.line ++ ":=" ++ .line) ++ ccs.ppACApps newRlhs)

open MessageData in
/-- Given `tsEqa : ts = a`, for each equality `trEqb : tr = b` in `acR` where
the intersection `t` of `ts` and `tr` is nonempty, let `ts = t*s` and `tr := t*r`, add a new
equality `r*a = s*b`. -/
def superposeAC (ts a : ACApps) (tsEqa : DelayedExpr) : CCM Unit := do
  let .apps op args := ts | return
  for hi : i in [:args.size] do
    if i == 0 || (args[i]'hi.2) != (args[i - 1]'(Nat.lt_of_le_of_lt (i.sub_le 1) hi.2)) then
      let some ent := (← get).acEntries.find? (args[i]'hi.2) | failure
      let occs := ent.RLHSOccs
      for tr in occs do
        let .apps optr _ := tr | continue
        unless optr == op do continue
        let some (b, trEqb) := (← get).acR.find? tr | failure
        let tArgs := ts.intersection tr
        guard !tArgs.isEmpty
        let t := ACApps.mkApps op tArgs
        let sArgs := ts.diff t
        guard !sArgs.isEmpty
        let rArgs := tr.diff t
        guard !rArgs.isEmpty
        let s := ACApps.mkApps op sArgs
        let r := ACApps.mkApps op rArgs
        let ra := ACApps.mkFlatApps op r a
        let sb := ACApps.mkFlatApps op s b
        let some true := (← get).opInfo.find? op | failure
        let raEqsb ← mkACSuperposeProof ra sb a b r s ts tr tsEqa trEqb
        modifyACTodo fun todo => todo.push (ra, sb, raEqsb)
        let ccs ← get
        trace[Debug.Meta.Tactic.cc.ac] group <|
          let rw₁ :=
            paren (ccs.ppACApps ts ++ ofFormat (Format.line ++ "-->" ++ .line) ++ ccs.ppACApps a)
          let rw₂ :=
            paren (ccs.ppACApps tr ++ ofFormat (Format.line ++ "-->" ++ .line) ++ ccs.ppACApps b)
          let eq :=
            paren (ccs.ppACApps ra ++ ofFormat (Format.line ++ "-->" ++ .line) ++ ccs.ppACApps sb)
          "superpose: " ++ nest 11 (group
            (rw₁ ++ ofFormat (Format.line ++ "with" ++ .line) ++ rw₂) ++
              ofFormat (Format.line ++ ":=" ++ .line) ++ eq)

open MessageData in
/-- Process the tasks in the `acTodo` field. -/
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

    -- Skip propagation if the equality is trivial.
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

    -- Update acR
    modify fun ccs => { ccs with acR := ccs.acR.insert lhs (rhs, H) }
    insertRBHSOccs lhs rhs

    let ccs ← get
    trace[Debug.Meta.Tactic.cc.ac] group <|
      "new rw: " ++
        group (ccs.ppACApps lhs ++ ofFormat (Format.line ++ "-->" ++ .line) ++ ccs.ppACApps rhs)

/-- Given AC variables `e₁` and `e₂` which are in the same equivalence class, add the proof of
`e₁ = e₂` to the AC module. -/
def addACEq (e₁ e₂ : Expr) : CCM Unit := do
  dbgTraceACEq "cc eq:" e₁ e₂
  modifyACTodo fun acTodo => acTodo.push (e₁, e₂, .eqProof e₁ e₂)
  processAC
  dbgTraceACState

/-- If the root expression of `e` is AC variable, add equality to AC module. If not, register the
AC variable to the root entry. -/
def setACVar (e : Expr) : CCM Unit := do
  let eRoot ← getRoot e
  let some rootEntry ← getEntry eRoot | failure
  if let some acVar := rootEntry.acVar then
    addACEq acVar e
  else
    let newRootEntry := { rootEntry with acVar := some e }
    modify fun ccs => { ccs with entries := ccs.entries.insert eRoot newRootEntry }

/-- If `e` isn't an AC variable, set `e` as an new AC variable. -/
def internalizeACVar (e : Expr) : CCM Bool := do
  let ccs ← get
  if ccs.acEntries.contains e then return false
  modify fun _ =>
    { ccs with
      acEntries := ccs.acEntries.insert e { idx := ccs.acEntries.size } }
  setACVar e
  return true

/-- Given `e := op₁ (op₂ a₁ a₂) (op₃ a₃ a₄)` where `opₙ`s are canonicalized to `op`, internalize
`aₙ`s as AC variables and return `(op (op a₁ a₂) (op a₃ a₄), args ++ #[a₁, a₂, a₃, a₄])`. -/
partial def convertAC (op e : Expr) (args : Array Expr := #[]) : CCM (Array Expr × Expr) := do
  if let some currOp ← isAC e then
    if op == currOp then
      let (args, arg₁) ← convertAC op e.appFn!.appArg! args
      let (args, arg₂) ← convertAC op e.appArg! args
      return (args, mkApp2 op arg₁ arg₂)

  let _ ← internalizeACVar e
  return (args.push e, e)

open MessageData in
/-- Internalize `e` so that the AC module can deal with the given expression.

If the expression does not contain an AC operator, or the parent expression
is already processed by `internalizeAC`, this operation does nothing. -/
def internalizeAC (e : Expr) (parent? : Option Expr) : CCM Unit := do
  let some op ← isAC e | return
  let parentOp? ← parent?.casesOn (pure none) isAC
  if parentOp?.any (op == ·) then return

  unless (← internalizeACVar e) do return

  let (args, norme) ← convertAC op e
  let rep := ACApps.mkApps op args
  let some true := (← get).opInfo.find? op | failure
  let some repe := rep.toExpr | failure
  let pr ← mkACProof norme repe

  let ccs ← get
  trace[Debug.Meta.Tactic.cc.ac] group <|
    let d := paren (ccs.ppACApps e ++ ofFormat (" :=" ++ Format.line) ++ ofExpr e)
    "new term: " ++ d ++ ofFormat (Format.line ++ "===>" ++ .line) ++ ccs.ppACApps rep

  modifyACTodo fun todo => todo.push (e, rep, pr)
  processAC
  dbgTraceACState

mutual
/-- The specialized `internalizeCore` for applications or literals. -/
partial def internalizeAppLit (e : Expr) : CCM Unit := do
  if ← isInterpretedValue e then
    mkEntry e true
    if (← get).values then return -- we treat values as atomic symbols
  else
    mkEntry e false
    if (← get).values && isValue e then return -- we treat values as atomic symbols
  -- At this point we should have handled a literal; otherwise we fail.
  unless e.isApp do return
  if let some (_, lhs, rhs) ← e.relSidesIfSymm? then
    internalizeCore lhs (some e)
    internalizeCore rhs (some e)
    addOccurrence e lhs true
    addOccurrence e rhs true
    addSymmCongruenceTable e
  else if (← mkCCCongrTheorem e).isSome then
    let fn := e.getAppFn
    let apps := e.getAppApps
    guard (apps.size > 0)
    guard (apps.back == e)
    let mut pinfo : List ParamInfo := []
    let state ← get
    if state.ignoreInstances then
      pinfo := (← getFunInfoNArgs fn apps.size).paramInfo.toList
    if state.hoFns.isSome && fn.isConst && !(state.hoFns.iget.contains fn.constName) then
      for h : i in [:apps.size] do
        let arg := (apps[i]'h.2).appArg!
        addOccurrence e arg false
        if pinfo.head?.any ParamInfo.isInstImplicit then
          -- We do not recurse on instances when `(← get).config.ignoreInstances` is `true`.
          mkEntry arg false
          propagateInstImplicit arg
        else
          internalizeCore arg (some e)
        unless pinfo.isEmpty do
          pinfo := pinfo.tail
      internalizeCore fn (some e)
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
          mkEntry curr false
        for h : j in [i:apps.size] do
          addOccurrence (apps[j]'h.2) currArg false
          addOccurrence (apps[j]'h.2) currFn false
        if pinfo.head?.any ParamInfo.isInstImplicit then
          -- We do not recurse on instances when `(← get).config.ignoreInstances` is `true`.
          mkEntry currArg false
          mkEntry currFn false
          propagateInstImplicit currArg
        else
          internalizeCore currArg (some e)
          mkEntry currFn false
        unless pinfo.isEmpty do
          pinfo := pinfo.tail
        addCongruenceTable curr
  applySimpleEqvs e

/-- Internalize `e` so that the congruence closure can deal with the given expression. Don't forget
to process the tasks in the `todo` field later. -/
partial def internalizeCore (e : Expr) (parent? : Option Expr) : CCM Unit := do
  guard !e.hasLooseBVars
  /- We allow metavariables after partitions have been frozen. -/
  if e.hasExprMVar && !(← get).frozePartitions then
    return
  /- Check whether `e` has already been internalized. -/
  if (← getEntry e).isNone then
    match e with
    | .bvar _ => unreachable!
    | .sort _ => pure ()
    | .const _ _ | .mvar _ => mkEntry e false
    | .lam _ _ _ _ | .letE _ _ _ _ _ => mkEntry e false
    | .fvar f =>
      mkEntry e false
      if let some v ← f.getValue? then
        pushReflEq e v
    | .mdata _ e' =>
      mkEntry e false
      internalizeCore e' e
      addOccurrence e e' false
      pushReflEq e e'
    | .forallE _ t b _ =>
      if e.isArrow then
        if ← isProp t <&&> isProp b then
          internalizeCore t e
          internalizeCore b e
          addOccurrence e t false
          addOccurrence e b false
          propagateImpUp e
      if ← isProp e then
        mkEntry e false
    | .app _ _ | .lit _ => internalizeAppLit e
    | .proj sn i pe =>
      mkEntry e false
      let some fn := (getStructureFields (← getEnv) sn)[i]? | failure
      let e' ← pe.mkDirectProjection fn
      internalizeAppLit e'
      pushReflEq e e'

  /- Remark: if should invoke `internalizeAC` even if the test `(← getEntry e).isNone` above failed.
     Reason, the first time `e` was visited, it may have been visited with a different parent. -/
  if (← get).ac then
    internalizeAC e parent?

/-- Propagate equality from `a` and `b` to `a ↔ b`. -/
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

/-- Propagate equality from `a` and `b` to `a ∧ b`. -/
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

/-- Propagate equality from `a` and `b` to `a ∨ b`. -/
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

/-- Propagate equality from `a` to `¬a`. -/
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

/-- Propagate equality from `a` and `b` to `a → b`. -/
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
    let isNot : Expr → Bool × Expr
      | .app (.const ``Not []) a => (true, a)
      | .forallE _ a (.const ``False []) _ => (true, a)
      | e => (false, e)
    if let (true, arg) := isNot a then
      if (← get).em then
        -- `b = False → (Not a → b) = a`
        pushEq e arg
          (mkApp3 (.const ``not_imp_eq_of_eq_false_right []) arg b (← getEqFalseProof b))
    else
      -- `b = False → (a → b) = Not a`
      let notA := mkApp (.const ``Not []) a
      internalizeCore notA none
      pushEq e notA
        (mkApp3 (.const ``imp_eq_of_eq_false_right []) a b (← getEqFalseProof b))
  else if ← isEqv a b then
    pushEq e (.const ``True [])
      (mkApp3 (.const ``imp_eq_true_of_eq []) a b (← getPropEqProof a b))

/-- Propagate equality from `p`, `a` and `b` to `if p then a else b`. -/
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

/-- Propagate equality from `a` and `b` to *disprove* `a = b`. -/
partial def propagateEqUp (e : Expr) : CCM Unit := do
  -- Remark: the positive case is implemented at `checkEqTrue` for any reflexive relation.
  let some (_, a, b) := e.eq? | failure
  let ra ← getRoot a
  let rb ← getRoot b
  if ra != rb then
    let mut raNeRb : Option Expr := none
    /-
    We disprove inequality for interpreted values here.
    The possible types of interpreted values are in `{String, Char, Int, Nat}`.
    1- `String`
      `ra` & `rb` are string literals, so if `ra != rb`, `ra.int?.isNone` is `true` and we can
      prove `$ra ≠ $rb`.
    2- `Char`
      `ra` & `rb` are the form of `Char.ofNat (nat_lit n)`, so if `ra != rb`, `ra.int?.isNone` is
      `true` and we can prove `$ra ≠ $rb` (assuming that `n` is not pathological value, i.e.
      `n.isValidChar`).
    3- `Int`, `Nat`
      `ra` & `rb` are the form of `@OfNat.ofNat ℤ (nat_lit n) i` or
      `@Neg.neg ℤ i' (@OfNat.ofNat ℤ (nat_lit n) i)`, so even if `ra != rb`, `$ra ≠ $rb` can be
      false when `i` or `i'` in `ra` & `rb` are not alpha-equivalent but def-eq.
      If `ra.int? != rb.int?`, we can prove `$ra ≠ $rb` (assuming that `i` & `i'` are not
      pathological instances).
    -/
    if ← isInterpretedValue ra <&&> isInterpretedValue rb <&&>
        pure (ra.int?.isNone || ra.int? != rb.int?) then
      raNeRb := some
        (Expr.app (.proj ``Iff 0 (← mkAppM ``bne_iff_ne #[ra, rb])) (← mkEqRefl (.const ``true [])))
    else
      if let some c₁ ← isConstructorApp? ra then
      if let some c₂ ← isConstructorApp? rb then
      if c₁.name != c₂.name then
        raNeRb ← withLocalDeclD `h (← mkEq ra rb) fun h => do
          mkLambdaFVars #[h] (← mkNoConfusion (.const ``False []) h)
    if let some raNeRb' := raNeRb then
    if let some aNeRb ← mkNeOfEqOfNe a ra raNeRb' then
    if let some aNeB ← mkNeOfNeOfEq aNeRb rb b then
      pushEq e (.const ``False []) (← mkEqFalse aNeB)

/-- Propagate equality from subexpressions of `e` to `e`. -/
partial def propagateUp (e : Expr) : CCM Unit := do
  if (← get).inconsistent then return
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

In principle, we could mark theorems such as `cast_eq` as simplification rules, but this created
problems with the builtin support for cast-introduction in the ematching module in Lean 3.
TODO: check if this is now possible in Lean 4.

Eagerly merging the equivalence classes is also more efficient. -/
partial def applySimpleEqvs (e : Expr) : CCM Unit := do
  if let .app (.app (.app (.app (.const ``cast [l₁]) A) B) H) a := e then
    /-
    ```
    HEq (cast H a) a

    theorem cast_heq.{l₁} : ∀ {A B : Sort l₁} (H : A = B) (a : A), HEq (@cast.{l₁} A B H a) a
    ```
    -/
    let proof := mkApp4 (.const ``cast_heq [l₁]) A B H a
    pushHEq e a proof

  if let .app (.app (.app (.app (.app (.app (.const ``Eq.rec [l₁, l₂]) A) a) P) p) a') H := e then
    /-
    ```
    HEq (t ▸ p) p

    theorem eqRec_heq'.{l₁, l₂} : ∀ {A : Sort l₂} {a : A} {P : (a' : A) → a = a' → Sort l₁}
      (p : P a) {a' : A} (H : a = a'), HEq (@Eq.rec.{l₁ l₂} A a P p a' H) p
    ```
    -/
    let proof := mkApp6 (.const ``eqRec_heq' [l₁, l₂]) A a P p a' H
    pushHEq e p proof

  if let .app (.app (.app (.const ``Ne [l₁]) α) a) b := e then
    -- `(a ≠ b) = (Not (a = b))`
    let newE := Expr.app (.const ``Not []) (mkApp3 (.const ``Eq [l₁]) α a b)
    internalizeCore newE none
    pushReflEq e newE

  if let some r ← e.reduceProjStruct? then
    pushReflEq e r

  let fn := e.getAppFn
  if fn.isLambda then
    let reducedE := e.headBeta
    if let some phandler := (← get).phandler then
      phandler.newAuxCCTerm reducedE
    internalizeCore reducedE none
    pushReflEq e reducedE

  let mut revArgs : Array Expr := #[]
  let mut it := e
  while it.isApp do
    revArgs := revArgs.push it.appArg!
    let fn := it.appFn!
    let rootFn ← getRoot fn
    let en ← getEntry rootFn
    if en.any Entry.hasLambdas then
      let lambdas ← getEqcLambdas rootFn
      let newLambdaApps ← propagateBeta fn revArgs lambdas
      for newApp in newLambdaApps do
        internalizeCore newApp none
    it := fn

  propagateUp e

/-- If `e` is a subsingleton element, push the equality proof between `e` and its canonical form
to the todo list or register `e` as the canonical form of itself. -/
partial def processSubsingletonElem (e : Expr) : CCM Unit := do
  let type ← inferType e
  -- TODO: this is likely to become a bottleneck. See e.g.
  -- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/convert.20is.20often.20slow/near/433830798
  let ss ← synthInstance? (← mkAppM ``Subsingleton #[type])
  if ss.isNone then return -- type is not a subsingleton
  let type ← normalize type
  -- Make sure type has been internalized
  internalizeCore type none
  -- Try to find representative
  if let some it := (← get).subsingletonReprs.find? type then
    pushSubsingletonEq e it
  else
    modify fun ccs =>
      { ccs with
        subsingletonReprs := ccs.subsingletonReprs.insert type e }
  let typeRoot ← getRoot type
  if typeRoot == type then return
  if let some it2 := (← get).subsingletonReprs.find? typeRoot then
    pushSubsingletonEq e it2
  else
    modify fun ccs =>
      { ccs with
        subsingletonReprs := ccs.subsingletonReprs.insert typeRoot e }

/-- Add an new entry for `e` to the congruence closure. -/
partial def mkEntry (e : Expr) (interpreted : Bool) : CCM Unit := do
  if (← getEntry e).isSome then return
  let constructor ← isConstructorApp e
  modify fun ccs =>
    { ccs with toCCState := ccs.toCCState.mkEntryCore e interpreted constructor }
  processSubsingletonElem e
end

/-- Can we propagate equality from subexpressions of `e` to `e`? -/
def mayPropagate (e : Expr) : Bool :=
  e.isAppOfArity ``Iff 2 || e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 ||
    e.isAppOfArity ``Not 1 || e.isArrow || e.isIte

/-- Remove parents of `e` from the congruence table and the symm congruence table, and append
parents to propagate equality, to `parentsToPropagate`.
Returns the new value of `parentsToPropagate`. -/
def removeParents (e : Expr) (parentsToPropagate : Array Expr := #[]) : CCM (Array Expr) := do
  let some ps := (← get).parents.find? e | return parentsToPropagate
  let mut parentsToPropagate := parentsToPropagate
  for pocc in ps do
    let p := pocc.expr
    trace[Debug.Meta.Tactic.cc] "remove parent: {p}"
    if mayPropagate p then
      parentsToPropagate := parentsToPropagate.push p
    if p.isApp then
      if pocc.symmTable then
        let some (rel, lhs, rhs) ← p.relSidesIfSymm? | failure
        let k' ← mkSymmCongruencesKey lhs rhs
        if let some lst := (← get).symmCongruences.find? k' then
          let k := (p, rel)
          let newLst ← lst.filterM fun k₂ => (!·) <$> compareSymm k k₂
          if !newLst.isEmpty then
            modify fun ccs =>
              { ccs with symmCongruences := ccs.symmCongruences.insert k' newLst }
          else
            modify fun ccs =>
              { ccs with symmCongruences := ccs.symmCongruences.erase k' }
      else
        let k' ← mkCongruencesKey p
        if let some es := (← get).congruences.find? k' then
          let newEs := es.erase p
          if !newEs.isEmpty then
            modify fun ccs =>
              { ccs with congruences := ccs.congruences.insert k' newEs }
          else
            modify fun ccs =>
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
  modify fun ccs => { ccs with entries := ccs.entries.insert e newN }

/-- Traverse the `root`'s equivalence class, and for each function application,
collect the function's equivalence class root. -/
def collectFnRoots (root : Expr) (fnRoots : Array Expr := #[]) : CCM (Array Expr) := do
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

/-- Reinsert parents of `e` to the congruence table and the symm congruence table.

Together with `removeParents`, this allows modifying parents of an expression. -/
def reinsertParents (e : Expr) : CCM Unit := do
  let some ps := (← get).parents.find? e | return
  for p in ps do
    trace[Debug.Meta.Tactic.cc] "reinsert parent: {p.expr}"
    if p.expr.isApp then
      if p.symmTable then
        addSymmCongruenceTable p.expr
      else
        addCongruenceTable p.expr

/-- Check for integrity of the `CCStructure`. -/
def checkInvariant : CCM Unit := do
  guard (← get).checkInvariant

/--
For each `fnRoot` in `fnRoots` traverse its parents, and look for a parent prefix that is
in the same equivalence class of the given lambdas.

remark All expressions in lambdas are in the same equivalence class -/
def propagateBetaToEqc (fnRoots lambdas : Array Expr) (newLambdaApps : Array Expr := #[]) :
    CCM (Array Expr) := do
  if lambdas.isEmpty then return newLambdaApps
  let mut newLambdaApps := newLambdaApps
  let lambdaRoot ← getRoot lambdas.back
  guard (← lambdas.allM fun l => pure l.isLambda <&&> (· == lambdaRoot) <$> getRoot l)
  for fnRoot in fnRoots do
    if let some ps := (← get).parents.find? fnRoot then
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
  guard (← isConstructorApp c)
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
      internalizeCore newP none
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
  let some c₁ ← isConstructorApp? e₁ | failure
  let some c₂ ← isConstructorApp? e₂ | failure
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
        let rec
          /-- Given an injective theorem `val : type`, whose `type` is the form of
          `a₁ = a₂ ∧ HEq b₁ b₂ ∧ ..`, destruct `val` and push equality proofs to the todo list. -/
          go (type val : Expr) : CCM Unit := do
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

/-- Derive contradiction if we can get equality between different values. -/
def propagateValueInconsistency (e₁ e₂ : Expr) : CCM Unit := do
  guard (← isInterpretedValue e₁)
  guard (← isInterpretedValue e₂)
  let some eqProof ← getEqProof e₁ e₂ | failure
  let trueEqFalse ← mkEq (.const ``True []) (.const ``False [])
  let neProof :=
    Expr.app (.proj ``Iff 0 (← mkAppM ``bne_iff_ne #[e₁, e₂])) (← mkEqRefl (.const ``true []))
  let H ← mkAbsurd trueEqFalse eqProof neProof
  pushEq (.const ``True []) (.const ``False []) H

/-- Propagate equality from `a ∧ b = True` to `a = True` and `b = True`. -/
def propagateAndDown (e : Expr) : CCM Unit := do
  if ← isEqTrue e then
    let some (a, b) := e.and? | failure
    let h ← getEqTrueProof e
    pushEq a (.const ``True []) (mkApp3 (.const ``eq_true_of_and_eq_true_left []) a b h)
    pushEq b (.const ``True []) (mkApp3 (.const ``eq_true_of_and_eq_true_right []) a b h)

/-- Propagate equality from `a ∨ b = False` to `a = False` and `b = False`. -/
def propagateOrDown (e : Expr) : CCM Unit := do
  if ← isEqFalse e then
    let some (a, b) := e.app2? ``Or | failure
    let h ← getEqFalseProof e
    pushEq a (.const ``False []) (mkApp3 (.const ``eq_false_of_or_eq_false_left []) a b h)
    pushEq b (.const ``False []) (mkApp3 (.const ``eq_false_of_or_eq_false_right []) a b h)

/-- Propagate equality from `¬a` to `a`. -/
def propagateNotDown (e : Expr) : CCM Unit := do
  if ← isEqTrue e then
    let some a := e.not? | failure
    pushEq a (.const ``False [])
      (mkApp2 (.const ``eq_false_of_not_eq_true []) a (← getEqTrueProof e))
  else if ← (·.em) <$> get <&&> isEqFalse e then
    let some a := e.not? | failure
    pushEq a (.const ``True [])
      (mkApp2 (.const ``eq_true_of_not_eq_false []) a (← getEqFalseProof e))

/-- Propagate equality from `(a = b) = True` to `a = b`. -/
def propagateEqDown (e : Expr) : CCM Unit := do
  if ← isEqTrue e then
    let some (a, b) := e.eqOrIff? | failure
    pushEq a b (← mkAppM ``of_eq_true #[← getEqTrueProof e])

/-- Propagate equality from `¬∃ x, p x` to `∀ x, ¬p x`. -/
def propagateExistsDown (e : Expr) : CCM Unit := do
  if ← isEqFalse e then
    let hNotE ← mkAppM ``not_of_eq_false #[← getEqFalseProof e]
    let (all, hAll) ← e.forallNot_of_notExists hNotE
    internalizeCore all none
    pushEq all (.const ``True []) (← mkEqTrue hAll)

/-- Propagate equality from `e` to subexpressions of `e`. -/
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

/-- Performs one step in the process when the new equation is added.

Here, `H` contains the proof that `e₁ = e₂` (if `heqProof` is false)
or `HEq e₁ e₂` (if `heqProof` is true). -/
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
  /-- The auxiliary definition for `addEqvStep` to flip the input. -/
  go (e₁ e₂: Expr) (n₁ n₂ r₁ r₂ : Entry) (flipped : Bool) (H : EntryExpr) (heqProof : Bool) :
      CCM Unit := do
    -- Interpreted values are already in the correct equivalence class,
    -- so merging two different classes means we found an inconsistency.
    let mut valueInconsistency := false
    if r₁.interpreted && r₂.interpreted then
      if n₁.root.isConstOf ``True || n₂.root.isConstOf ``True then
        modify fun ccs => { ccs with inconsistent := true }
      else if n₁.root.int?.isSome && n₂.root.int?.isSome then
        valueInconsistency := n₁.root.int? != n₂.root.int?
      else
        valueInconsistency := true

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
    modify fun ccs => { ccs with entries := ccs.entries.insert e₁ newN₁ }

    -- The hash code for the parents is going to change
    let parentsToPropagate ← removeParents e₁Root

    let lambdas₁ ← getEqcLambdas e₁Root
    let lambdas₂ ← getEqcLambdas e₂Root
    let fnRoots₂ ← if !lambdas₁.isEmpty then collectFnRoots e₂Root else pure #[]
    let fnRoots₁ ← if !lambdas₂.isEmpty then collectFnRoots e₁Root else pure #[]

    -- force all `root` fields in `e₁` equivalence class to point to `e₂Root`
    let propagate := e₂Root.isConstOf ``True || e₂Root.isConstOf ``False
    let mut toPropagate : Array Expr := #[]
    let mut it := e₁
    repeat
      let some itN ← getEntry it | failure
      if propagate then
        toPropagate := toPropagate.push it
      let newItN : Entry := { itN with root := e₂Root }
      modify fun ccs => { ccs with entries := ccs.entries.insert it newItN }
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
        acVar := acVar?₂ <|> acVar?₁ }
    modify fun ccs =>
      { ccs with
        entries :=
          ccs.entries.insert e₁Root newR₁ |>.insert e₂Root newR₂ }
    checkInvariant

    let lambdaAppsToInternalize ← propagateBetaToEqc fnRoots₂ lambdas₁
    let lambdaAppsToInternalize ← propagateBetaToEqc fnRoots₁ lambdas₂ lambdaAppsToInternalize

    -- copy `e₁Root` parents to `e₂Root`
    let constructorEq := r₁.constructor && r₂.constructor
    if let some ps₁ := (← get).parents.find? e₁Root then
      let mut ps₂ : ParentOccSet := ∅
      if let some it' := (← get).parents.find? e₂Root then
        ps₂ := it'
      for p in ps₁ do
        if ← pure p.expr.isApp <||> isCgRoot p.expr then
          if !constructorEq && r₂.constructor then
            propagateProjectionConstructor p.expr e₂Root
          ps₂ := ps₂.insert p
      modify fun ccs =>
        { ccs with
          parents := ccs.parents.erase e₁Root |>.insert e₂Root ps₂ }

    if !(← get).inconsistent then
      if let some acVar₁ := acVar?₁ then
      if let some acVar₂ := acVar?₂ then
        addACEq acVar₁ acVar₂

    if !(← get).inconsistent && constructorEq then
      propagateConstructorEq e₁Root e₂Root

    if !(← get).inconsistent && valueInconsistency then
      propagateValueInconsistency e₁Root e₂Root

    if !(← get).inconsistent then
      updateMT e₂Root
      checkNewSubsingletonEq e₁Root e₂Root

    if !(← get).inconsistent then
      for p in parentsToPropagate do
        propagateUp p

    if !(← get).inconsistent && !toPropagate.isEmpty then
      for e in toPropagate do
        propagateDown e
      if let some phandler := (← get).phandler then
        phandler.propagated toPropagate

    if !(← get).inconsistent then
      for e in lambdaAppsToInternalize do
        internalizeCore e none

    let ccs ← get
    trace[Meta.Tactic.cc.merge] "{e₁Root} = {e₂Root}"
    trace[Debug.Meta.Tactic.cc] "merged: {e₁Root} = {e₂Root}\n{ccs.ppEqcs}"
    trace[Debug.Meta.Tactic.cc.parentOccs] ccs.ppParentOccs

/-- Process the tasks in the `todo` field. -/
def processTodo : CCM Unit := do
  repeat
    let todo ← getTodo
    let some (lhs, rhs, H, heqProof) := todo.back? | return
    if (← get).inconsistent then
      modifyTodo fun _ => #[]
      return
    modifyTodo Array.pop
    addEqvStep lhs rhs H heqProof

/-- Internalize `e` so that the congruence closure can deal with the given expression. -/
def internalize (e : Expr) : CCM Unit := do
  internalizeCore e none
  processTodo

/-- Add `H : lhs = rhs` or `H : HEq lhs rhs` to the congruence closure. Don't forget to internalize
`lhs` and `rhs` beforehand. -/
def addEqvCore (lhs rhs H : Expr) (heqProof : Bool) : CCM Unit := do
  pushTodo lhs rhs H heqProof
  processTodo

/-- Add `proof : type` to the congruence closure. -/
def add (type : Expr) (proof : Expr) : CCM Unit := do
  if (← get).inconsistent then return
  modifyTodo fun _ => #[]
  let (isNeg, p) :=
    match type with
    | .app (.const ``Not []) a => (true, a)
    | .forallE _ a (.const ``False []) _ => (true, a)
    | .app (.app (.app (.const ``Ne [u]) α) lhs) rhs =>
      (true, .app (.app (.app (.const ``Eq [u]) α) lhs) rhs)
    | e => (false, e)
  match p with
  | .app (.app (.app (.const ``Eq _) _) lhs) rhs =>
    if isNeg then
      internalizeCore p none
      addEqvCore p (.const ``False []) (← mkEqFalse proof) false
    else
      internalizeCore lhs none
      internalizeCore rhs none
      addEqvCore lhs rhs proof false
  | .app (.app (.app (.app (.const ``HEq _) _) lhs) _) rhs =>
    if isNeg then
      internalizeCore p none
      addEqvCore p (.const ``False []) (← mkEqFalse proof) false
    else
      internalizeCore lhs none
      internalizeCore rhs none
      addEqvCore lhs rhs proof true
  | .app (.app (.const ``Iff _) lhs) rhs =>
    if isNeg then
      let neqProof ← mkAppM ``neq_of_not_iff #[proof]
      internalizeCore p none
      addEqvCore p (.const ``False []) (← mkEqFalse neqProof) false
    else
      internalizeCore lhs none
      internalizeCore rhs none
      addEqvCore lhs rhs (mkApp3 (.const ``propext []) lhs rhs proof) false
  | _ =>
    if ← pure isNeg <||> isProp p then
      internalizeCore p none
      if isNeg then
        addEqvCore p (.const ``False []) (← mkEqFalse proof) false
      else
        addEqvCore p (.const ``True []) (← mkEqTrue proof) false

end CCM

end Mathlib.Tactic.CC
