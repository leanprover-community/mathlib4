/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Miyahara Kō
-/
import Mathlib.Tactic.CC.Datatypes
import Mathlib.Tactic.CC.Lemmas
import Mathlib.Tactic.Relation.Rfl
import Mathlib.Tactic.Relation.Symm

/-!
# Make proofs from a congruence closure
-/

open Lean Meta Elab Tactic Std

namespace Mathlib.Tactic.CC

/-- The monad for the `cc` tactic stores the current state of the tactic. -/
abbrev CCM := StateRefT CCStructure MetaM

namespace CCM

/-- Run a computation in the `CCM` monad. -/
@[inline]
def run {α : Type} (x : CCM α) (c : CCStructure) : MetaM (α × CCStructure) := StateRefT'.run x c

/-- Update the `cache` field of the state. -/
@[inline]
def modifyCache (f : CCCongrTheoremCache → CCCongrTheoremCache) : CCM Unit :=
  modify fun cc => { cc with cache := f cc.cache }

/-- Read the `cache` field of the state. -/
@[inline]
def getCache : CCM CCCongrTheoremCache := do
  return (← get).cache

/-- Look up an entry associated with the given expression. -/
def getEntry (e : Expr) : CCM (Option Entry) := do
  return (← get).entries[e]?

/-- Use the normalizer to normalize `e`.

If no normalizer was configured, returns `e` itself. -/
def normalize (e : Expr) : CCM Expr := do
  if let some normalizer := (← get).normalizer then
    normalizer.normalize e
  else
    return e

/-- Return the root expression of the expression's congruence class. -/
def getRoot (e : Expr) : CCM Expr := do
  return (← get).root e

/-- Is `e` the root of its congruence class? -/
def isCgRoot (e : Expr) : CCM Bool := do
  return (← get).isCgRoot e

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
          if (← getRoot args₁[i]) != (← getRoot (args₂[i]'(ha.symm ▸ hi.2.1))) then
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
         `f a ≍ g b` -/
      return true
    else if f.isApp && g.isApp then
      -- Case 2: `f` and `g` are congruent
      isCongruent f g
    else
      /-
      f and g are not congruent nor they have the same type.
      We can't generate a congruence proof in this case because the following lemma
        `hcongr : f₁ ≍ f₂ → a₁ ≍ a₂ → f₁ a₁ ≍ f₂ a₂`
      is not provable.
      Remark: it is also not provable in MLTT, Coq and Agda (even if we assume UIP).
      -/
      return false

/-- Try to find a congruence theorem for an application of `fn` with `nargs` arguments, with support
for `HEq`. -/
def mkCCHCongrTheorem (fn : Expr) (nargs : Nat) : CCM (Option CCCongrTheorem) := do
  let cache ← getCache

  -- Check if `{ fn, nargs }` is in the cache
  let key₁ : CCCongrTheoremKey := { fn, nargs }
  if let some it := cache[key₁]? then
    return it

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

/-- Treat the entry associated with `e` as a first-order function. -/
def setFO (e : Expr) : CCM Unit :=
  modify fun ccs =>
    { ccs with entries := ccs.entries.modify e fun d => { d with fo := true } }

/-- Update the modification time of the congruence class of `e`. -/
partial def updateMT (e : Expr) : CCM Unit := do
  let r ← getRoot e
  let some ps := (← get).parents[r]? | return
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
    lemmaArgs := lemmaArgs.push lhsArgs[i] |>.push (rhsArgs[i]'(ha.symm ▸ hi.2.1))
    if kindsIt[0]! matches CongrArgKind.heq then
      let some p ← getHEqProof lhsArgs[i] (rhsArgs[i]'(ha.symm ▸ hi.2.1)) | failure
      lemmaArgs := lemmaArgs.push p
    else
      guard (kindsIt[0]! matches .eq)
      let some p ← getEqProof lhsArgs[i] (rhsArgs[i]'(ha.symm ▸ hi.2.1)) | failure
      lemmaArgs := lemmaArgs.push p
    kindsIt := kindsIt.eraseIdx! 0
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
        -- We should add support arbitrary heterogeneous reflexive relations.
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
If `asHEq` is `true`, then build a proof for `e₁ ≍ e₂`.
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
  let mut visited : ExprSet := ∅
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
    if path₁.back! == it₂ then
      -- found it!
      break
    path₁ := path₁.pop
    Hs₁ := Hs₁.pop

  -- 4. Build transitivity proof
  let mut pr? : Option Expr := none
  let mut lhs := e₁
  for h : i in [:path₁.size] do
    pr? ← some <$> mkTransOpt pr? (← mkProof lhs path₁[i] Hs₁[i]! heqProofs) heqProofs
    lhs := path₁[i]
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

/-- Build a proof for `e₁ ≍ e₂`.
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

/-- Return the proof of `e₁ = e₂` using `ac_rfl` tactic. -/
def mkACProof (e₁ e₂ : Expr) : MetaM Expr := do
  let eq ← mkEq e₁ e₂
  let .mvar m ← mkFreshExprSyntheticOpaqueMVar eq | failure
  AC.rewriteUnnormalizedRefl m
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
    let some true := (← get).opInfo[op]? | failure
    let newPr ← mkACSimpProof e lhs rhs r newE H
    return (newE, newPr)

/-- The single step of `simplifyAC`.

Simplifies an expression `e` by either simplifying one argument to the AC operator, or the whole
expression. -/
def simplifyACStep (e : ACApps) : CCM (Option (ACApps × DelayedExpr)) := do
  if let .apps _ args := e then
    for h : i in [:args.size] do
      if i == 0 || args[i] != (args[i - 1]'(Nat.lt_of_le_of_lt (i.sub_le 1) h.2.1)) then
        let some ae := (← get).acEntries[args[i]]? | failure
        let occs := ae.RLHSOccs
        let mut Rlhs? : Option ACApps := none
        for Rlhs in occs do
          if Rlhs.isSubset e then
            Rlhs? := some Rlhs
            break
        if let some Rlhs := Rlhs? then
          let some (Rrhs, H) := (← get).acR[Rlhs]? | failure
          return (some <| ← simplifyACCore e Rlhs Rrhs H)
  else if let some p := (← get).acR[e]? then
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

end Mathlib.Tactic.CC.CCM
