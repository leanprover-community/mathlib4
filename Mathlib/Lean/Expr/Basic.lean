/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Kim Morrison, Keeley Hoek, Robert Y. Lewis,
Floris van Doorn, Edward Ayers, Arthur Paulino
-/
import Mathlib.Init
import Lean.Expr

/-!
# Additional operations on Expr and related types

This file defines basic operations on the types expr, name, declaration, level, environment.

This file is mostly for non-tactics.
-/

namespace Lean

namespace BinderInfo

/-! ### Declarations about `BinderInfo` -/

/-- The brackets corresponding to a given `BinderInfo`. -/
def brackets : BinderInfo → String × String
  | BinderInfo.implicit => ("{", "}")
  | BinderInfo.strictImplicit => ("{{", "}}")
  | BinderInfo.instImplicit => ("[", "]")
  | _ => ("(", ")")

end BinderInfo

namespace Name

/-! ### Declarations about `name` -/

/-- Find the largest prefix `n` of a `Name` such that `f n != none`, then replace this prefix
with the value of `f n`. -/
@[specialize] def mapPrefix (f : Name → Option Name) (n : Name) : Name := Id.run do
  if let some n' := f n then return n'
  match n with
  | anonymous => anonymous
  | str n' s => mkStr (mapPrefix f n') s
  | num n' i => mkNum (mapPrefix f n') i

/-- Build a name from components.
For example, ``from_components [`foo, `bar]`` becomes ``` `foo.bar```.
It is the inverse of `Name.components` on list of names that have single components. -/
def fromComponents : List Name → Name := go .anonymous where
  /-- Auxiliary for `Name.fromComponents` -/
  go : Name → List Name → Name
  | n, []        => n
  | n, s :: rest => go (s.updatePrefix n) rest

/-- Update the last component of a name. -/
def updateLast (f : String → String) : Name → Name
  | .str n s => .str n (f s)
  | n        => n

/-- Get the last field of a name as a string.
Doesn't raise an error when the last component is a numeric field. -/
def lastComponentAsString : Name → String
  | .str _ s => s
  | .num _ n => toString n
  | .anonymous => ""

/-- `nm.splitAt n` splits a name `nm` in two parts, such that the *second* part has depth `n`,
i.e. `(nm.splitAt n).2.getNumParts = n` (assuming `nm.getNumParts ≥ n`).
Example: ``splitAt `foo.bar.baz.back.bat 1 = (`foo.bar.baz.back, `bat)``. -/
def splitAt (nm : Name) (n : Nat) : Name × Name :=
  let (nm2, nm1) := nm.componentsRev.splitAt n
  (.fromComponents <| nm1.reverse, .fromComponents <| nm2.reverse)

/-- `isPrefixOf? pre nm` returns `some post` if `nm = pre ++ post`.
Note that this includes the case where `nm` has multiple more namespaces.
If `pre` is not a prefix of `nm`, it returns `none`. -/
def isPrefixOf? (pre nm : Name) : Option Name :=
  if pre == nm then
    some anonymous
  else match nm with
  | anonymous => none
  | num p' a => (isPrefixOf? pre p').map (·.num a)
  | str p' s => (isPrefixOf? pre p').map (·.str s)

open Meta

-- from Lean.Server.Completion
def isBlackListed {m} [Monad m] [MonadEnv m] (declName : Name) : m Bool := do
  if declName == ``sorryAx then return true
  if declName matches .str _ "inj" then return true
  if declName matches .str _ "noConfusionType" then return true
  let env ← getEnv
  pure <| declName.isInternalDetail
   || isAuxRecursor env declName
   || isNoConfusion env declName
  <||> isRec declName <||> isMatcher declName

end Name

namespace ConstantInfo

/-- Checks whether this `ConstantInfo` is a definition. -/
def isDef : ConstantInfo → Bool
  | defnInfo _ => true
  | _          => false

/-- Checks whether this `ConstantInfo` is a theorem. -/
def isThm : ConstantInfo → Bool
  | thmInfo _ => true
  | _          => false

/-- Update `ConstantVal` (the data common to all constructors of `ConstantInfo`)
in a `ConstantInfo`. -/
def updateConstantVal : ConstantInfo → ConstantVal → ConstantInfo
  | defnInfo   info, v => defnInfo   {info with toConstantVal := v}
  | axiomInfo  info, v => axiomInfo  {info with toConstantVal := v}
  | thmInfo    info, v => thmInfo    {info with toConstantVal := v}
  | opaqueInfo info, v => opaqueInfo {info with toConstantVal := v}
  | quotInfo   info, v => quotInfo   {info with toConstantVal := v}
  | inductInfo info, v => inductInfo {info with toConstantVal := v}
  | ctorInfo   info, v => ctorInfo   {info with toConstantVal := v}
  | recInfo    info, v => recInfo    {info with toConstantVal := v}

/-- Update the name of a `ConstantInfo`. -/
def updateName (c : ConstantInfo) (name : Name) : ConstantInfo :=
  c.updateConstantVal {c.toConstantVal with name}

/-- Update the type of a `ConstantInfo`. -/
def updateType (c : ConstantInfo) (type : Expr) : ConstantInfo :=
  c.updateConstantVal {c.toConstantVal with type}

/-- Update the level parameters of a `ConstantInfo`. -/
def updateLevelParams (c : ConstantInfo) (levelParams : List Name) :
    ConstantInfo :=
  c.updateConstantVal {c.toConstantVal with levelParams}

/-- Update the value of a `ConstantInfo`, if it has one. -/
def updateValue : ConstantInfo → Expr → ConstantInfo
  | defnInfo   info, v => defnInfo   {info with value := v}
  | thmInfo    info, v => thmInfo    {info with value := v}
  | opaqueInfo info, v => opaqueInfo {info with value := v}
  | d, _ => d

/-- Turn a `ConstantInfo` into a declaration. -/
def toDeclaration! : ConstantInfo → Declaration
  | defnInfo   info => Declaration.defnDecl info
  | thmInfo    info => Declaration.thmDecl     info
  | axiomInfo  info => Declaration.axiomDecl   info
  | opaqueInfo info => Declaration.opaqueDecl  info
  | quotInfo   _ => panic! "toDeclaration for quotInfo not implemented"
  | inductInfo _ => panic! "toDeclaration for inductInfo not implemented"
  | ctorInfo   _ => panic! "toDeclaration for ctorInfo not implemented"
  | recInfo    _ => panic! "toDeclaration for recInfo not implemented"

end ConstantInfo

open Meta

/-- Same as `mkConst`, but with fresh level metavariables. -/
def mkConst' (constName : Name) : MetaM Expr := do
  return mkConst constName (← (← getConstInfo constName).levelParams.mapM fun _ => mkFreshLevelMVar)

namespace Expr

/-! ### Declarations about `Expr` -/

def bvarIdx? : Expr → Option Nat
  | bvar idx => some idx
  | _        => none

/-- Invariant: `i : ℕ` should be less than the size of `as : Array Expr`. -/
private def getAppAppsAux : Expr → Array Expr → Nat → Array Expr
  | .app f a, as, i => getAppAppsAux f (as.set! i (.app f a)) (i-1)
  | _,       as, _ => as

/-- Given `f a b c`, return `#[f a, f a b, f a b c]`.
Each entry in the array is an `Expr.app`,
and this array has the same length as the one returned by `Lean.Expr.getAppArgs`. -/
@[inline]
def getAppApps (e : Expr) : Array Expr :=
  let dummy := mkSort levelZero
  let nargs := e.getAppNumArgs
  getAppAppsAux e (.replicate nargs dummy) (nargs-1)

/-- Erase proofs in an expression by replacing them with `sorry`s.

This function replaces all proofs in the expression
and in the types that appear in the expression
by `sorryAx`s.
The resulting expression has the same type as the old one.

It is useful, e.g., to verify if the proof-irrelevant part of a definition depends on a variable.
-/
def eraseProofs (e : Expr) : MetaM Expr :=
  Meta.transform (skipConstInApp := true) e
    (pre := fun e => do
      if (← Meta.isProof e) then
        return .continue (← mkSorry (← inferType e) true)
      else
        return .continue)

/-- If an `Expr` has the form `Type u`, then return `some u`, otherwise `none`. -/
def type? : Expr → Option Level
  | .sort u => u.dec
  | _ => none

/-- `isConstantApplication e` checks whether `e` is syntactically an application of the form
`(fun x₁ ⋯ xₙ => H) y₁ ⋯ yₙ` where `H` does not contain the variable `xₙ`. In other words,
it does a syntactic check that the expression does not depend on `yₙ`. -/
def isConstantApplication (e : Expr) :=
  e.isApp && aux e.getAppNumArgs'.pred e.getAppFn' e.getAppNumArgs'
where
  /-- `aux depth e n` checks whether the body of the `n`-th lambda of `e` has loose bvar
    `depth - 1`. -/
  aux (depth : Nat) : Expr → Nat → Bool
    | .lam _ _ b _, n + 1  => aux depth b n
    | e, 0  => !e.hasLooseBVar (depth - 1)
    | _, _ => false

/-- Counts the immediate depth of a nested `let` expression. -/
def letDepth : Expr → Nat
  | .letE _ _ _ b _ => b.letDepth + 1
  | _ => 0

open Meta

/-- Check that an expression contains no metavariables (after instantiation). -/
-- There is a `TacticM` level version of this, but it's useful to have in `MetaM`.
def ensureHasNoMVars (e : Expr) : MetaM Unit := do
  let e ← instantiateMVars e
  if e.hasExprMVar then
    throwError "tactic failed, resulting expression contains metavariables{indentExpr e}"

/-- Construct the term of type `α` for a given natural number
(doing typeclass search for the `OfNat` instance required). -/
def ofNat (α : Expr) (n : Nat) : MetaM Expr := do
  mkAppOptM ``OfNat.ofNat #[α, mkRawNatLit n, none]

/-- Construct the term of type `α` for a given integer
(doing typeclass search for the `OfNat` and `Neg` instances required). -/
def ofInt (α : Expr) : Int → MetaM Expr
  | Int.ofNat n => Expr.ofNat α n
  | Int.negSucc n => do mkAppM ``Neg.neg #[← Expr.ofNat α (n + 1)]

section recognizers

/--
Return `some n` if `e` is one of the following
- a nat literal (numeral)
- `Nat.zero`
- `Nat.succ x` where `isNumeral x`
- `OfNat.ofNat _ x _` where `isNumeral x` -/
partial def numeral? (e : Expr) : Option Nat :=
  if let some n := e.rawNatLit? then n
  else
    let e := e.consumeMData -- `OfNat` numerals may have `no_index` around them from `ofNat()`
    let f := e.getAppFn
    if !f.isConst then none
    else
      let fName := f.constName!
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then (numeral? e.appArg!).map Nat.succ
      else if fName == ``OfNat.ofNat && e.getAppNumArgs == 3 then numeral? (e.getArg! 1)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then some 0
      else none

/-- Test if an expression is either `Nat.zero`, or `OfNat.ofNat 0`. -/
def zero? (e : Expr) : Bool :=
  match e.numeral? with
  | some 0 => true
  | _ => false

/-- Tests is if an expression matches either `x ≠ y` or `¬ (x = y)`.
If it matches, returns `some (type, x, y)`. -/
def ne?' (e : Expr) : Option (Expr × Expr × Expr) :=
  e.ne? <|> (e.not? >>= Expr.eq?)

/-- `Lean.Expr.le? e` takes `e : Expr` as input.
If `e` represents `a ≤ b`, then it returns `some (t, a, b)`, where `t` is the Type of `a`,
otherwise, it returns `none`. -/
@[inline] def le? (p : Expr) : Option (Expr × Expr × Expr) := do
  let (type, _, lhs, rhs) ← p.app4? ``LE.le
  return (type, lhs, rhs)

/-- `Lean.Expr.lt? e` takes `e : Expr` as input.
If `e` represents `a < b`, then it returns `some (t, a, b)`, where `t` is the Type of `a`,
otherwise, it returns `none`. -/
@[inline] def lt? (p : Expr) : Option (Expr × Expr × Expr) := do
  let (type, _, lhs, rhs) ← p.app4? ``LT.lt
  return (type, lhs, rhs)

/-- Given a proposition `ty` that is an `Eq`, `Iff`, or `HEq`, returns `(tyLhs, lhs, tyRhs, rhs)`,
where `lhs : tyLhs` and `rhs : tyRhs`,
and where `lhs` is related to `rhs` by the respective relation.

See also `Lean.Expr.iff?`, `Lean.Expr.eq?`, and `Lean.Expr.heq?`. -/
def sides? (ty : Expr) : Option (Expr × Expr × Expr × Expr) :=
  if let some (lhs, rhs) := ty.iff? then
    some (.sort .zero, lhs, .sort .zero, rhs)
  else if let some (ty, lhs, rhs) := ty.eq? then
    some (ty, lhs, ty, rhs)
  else
    ty.heq?

end recognizers

universe u

def modifyAppArgM {M : Type → Type u} [Functor M] [Pure M]
    (modifier : Expr → M Expr) : Expr → M Expr
  | app f a => mkApp f <$> modifier a
  | e => pure e

def modifyRevArg (modifier : Expr → Expr) : Nat → Expr → Expr
  | 0,     (.app f x) => .app f (modifier x)
  | (i+1), (.app f x) => .app (modifyRevArg modifier i f) x
  | _, e => e

/-- Given `f a₀ a₁ ... aₙ₋₁`, runs `modifier` on the `i`th argument or
returns the original expression if out of bounds. -/
def modifyArg (modifier : Expr → Expr) (e : Expr) (i : Nat) (n := e.getAppNumArgs) : Expr :=
  modifyRevArg modifier (n - i - 1) e

/-- Given `f a₀ a₁ ... aₙ₋₁`, sets the argument on the `i`th argument to `x` or
returns the original expression if out of bounds. -/
def setArg (e : Expr) (i : Nat) (x : Expr) (n := e.getAppNumArgs) : Expr :=
  e.modifyArg (fun _ => x) i n

def getRevArg? : Expr → Nat → Option Expr
  | app _ a, 0   => a
  | app f _, i+1 => getRevArg! f i
  | _,       _   => none

/-- Given `f a₀ a₁ ... aₙ₋₁`, returns the `i`th argument or none if out of bounds. -/
def getArg? (e : Expr) (i : Nat) (n := e.getAppNumArgs) : Option Expr :=
  getRevArg? e (n - i - 1)

/-- Given `f a₀ a₁ ... aₙ₋₁`, runs `modifier` on the `i`th argument.
An argument `n` may be provided which says how many arguments we are expecting `e` to have. -/
def modifyArgM {M : Type → Type u} [Monad M] (modifier : Expr → M Expr)
    (e : Expr) (i : Nat) (n := e.getAppNumArgs) : M Expr := do
  let some a := getArg? e i | return e
  let a ← modifier a
  return modifyArg (fun _ ↦ a) e i n

/-- Traverses an expression `e` and renames bound variables named `old` to `new`. -/
def renameBVar (e : Expr) (old new : Name) : Expr :=
  match e with
  | app fn arg => app (fn.renameBVar old new) (arg.renameBVar old new)
  | lam n ty bd bi =>
    lam (if n == old then new else n) (ty.renameBVar old new) (bd.renameBVar old new) bi
  | forallE n ty bd bi =>
    forallE (if n == old then new else n) (ty.renameBVar old new) (bd.renameBVar old new) bi
  | mdata d e' => mdata d (e'.renameBVar old new)
  | e => e

open Lean.Meta in
/-- `getBinderName e` returns `some n` if `e` is an expression of the form `∀ n, ...`
and `none` otherwise. -/
def getBinderName (e : Expr) : MetaM (Option Name) := do
  match ← withReducible (whnf e) with
  | .forallE (binderName := n) .. | .lam (binderName := n) .. => pure (some n)
  | _ => pure none

/-- Map binder names in a nested forall `(a₁ : α₁) → ... → (aₙ : αₙ) → _` -/
def mapForallBinderNames : Expr → (Name → Name) → Expr
  | .forallE n d b bi, f => .forallE (f n) d (mapForallBinderNames b f) bi
  | e, _ => e

open Lean.Elab.Term
/-- Annotates a `binderIdent` with the binder information from an `fvar`. -/
def addLocalVarInfoForBinderIdent (fvar : Expr) (tk : TSyntax ``binderIdent) : MetaM Unit :=
  -- the only TermElabM thing we do in `addLocalVarInfo` is check inPattern,
  -- which we assume is always false for this function
  discard <| TermElabM.run do
    match tk with
    | `(binderIdent| $n:ident) => Elab.Term.addLocalVarInfo n fvar
    | tk => Elab.Term.addLocalVarInfo (Unhygienic.run `(_%$tk)) fvar

/-- If `e` has a structure as type with field `fieldName`, `mkDirectProjection e fieldName` creates
the projection expression `e.fieldName` -/
def mkDirectProjection (e : Expr) (fieldName : Name) : MetaM Expr := do
  let type ← whnf (← inferType e)
  let .const structName us := type.getAppFn | throwError "{e} doesn't have a structure as type"
  let some projName := getProjFnForField? (← getEnv) structName fieldName |
    throwError "{structName} doesn't have field {fieldName}"
  return mkAppN (.const projName us) (type.getAppArgs.push e)

/-- If `e` has a structure as type with field `fieldName` (either directly or in a parent
structure), `mkProjection e fieldName` creates the projection expression `e.fieldName` -/
def mkProjection (e : Expr) (fieldName : Name) : MetaM Expr := do
  let .const structName _ := (← whnf (← inferType e)).getAppFn |
    throwError "{e} doesn't have a structure as type"
  let some baseStruct := findField? (← getEnv) structName fieldName |
    throwError "No parent of {structName} has field {fieldName}"
  let mut e := e
  for projName in (getPathToBaseStructure? (← getEnv) baseStruct structName).get! do
    let type ← whnf (← inferType e)
    let .const _structName us := type.getAppFn | throwError "{e} doesn't have a structure as type"
    e := mkAppN (.const projName us) (type.getAppArgs.push e)
  mkDirectProjection e fieldName

/-- If `e` is a projection of the structure constructor, reduce the projection.
Otherwise returns `none`. If this function detects that expression is ill-typed, throws an error.
For example, given `Prod.fst (x, y)`, returns `some x`. -/
def reduceProjStruct? (e : Expr) : MetaM (Option Expr) := do
  let .const cname _ := e.getAppFn | return none
  let some pinfo ← getProjectionFnInfo? cname | return none
  let args := e.getAppArgs
  if ha : args.size = pinfo.numParams + 1 then
    -- The last argument of a projection is the structure.
    let sarg := args[pinfo.numParams]'(ha ▸ pinfo.numParams.lt_succ_self)
    -- Check that the structure is a constructor expression.
    unless sarg.getAppFn.isConstOf pinfo.ctorName do
      return none
    let sfields := sarg.getAppArgs
    -- The ith projection extracts the ith field of the constructor
    let sidx := pinfo.numParams + pinfo.i
    if hs : sidx < sfields.size then
      return some (sfields[sidx]'hs)
    else
      throwError m!"ill-formed expression, {cname} is the {pinfo.i + 1}-th projection function \
        but {sarg} does not have enough arguments"
  else
    return none

/-- Returns true if `e` contains a name `n` where `p n` is true. -/
@[specialize]
def containsConst (e : Expr) (p : Name → Bool) : Bool :=
  Option.isSome <| e.find? fun | .const n _ => p n | _ => false

/-- Given `(hNotEx : Not ex)` where `ex` is of the form `Exists x, p x`,
return a `forall x, Not (p x)` and a proof for it.

This function handles nested existentials. -/
partial def forallNot_of_notExists (ex hNotEx : Expr) : MetaM (Expr × Expr) := do
  let .app (.app (.const ``Exists [lvl]) A) p := ex | failure
  go lvl A p hNotEx
where
  /-- Given `(hNotEx : Not (@Exists.{lvl} A p))`,
      return a `forall x, Not (p x)` and a proof for it.

      This function handles nested existentials. -/
  go (lvl : Level) (A p hNotEx : Expr) : MetaM (Expr × Expr) := do
    let xn ← mkFreshUserName `x
    withLocalDeclD xn A fun x => do
      let px := p.beta #[x]
      let notPx := mkNot px
      let hAllNotPx := mkApp3 (.const ``forall_not_of_not_exists [lvl]) A p hNotEx
      if let .app (.app (.const ``Exists [lvl']) A') p' := px then
        let hNotPxN ← mkFreshUserName `h
        withLocalDeclD hNotPxN notPx fun hNotPx => do
          let (qx, hQx) ← go lvl' A' p' hNotPx
          let allQx ← mkForallFVars #[x] qx
          let hNotPxImpQx ← mkLambdaFVars #[hNotPx] hQx
          let hAllQx ← mkLambdaFVars #[x] (.app hNotPxImpQx (.app hAllNotPx x))
          return (allQx, hAllQx)
      else
        let allNotPx ← mkForallFVars #[x] notPx
        return (allNotPx, hAllNotPx)

end Expr

/-- Get the projections that are projections to parent structures. Similar to `getParentStructures`,
except that this returns the (last component of the) projection names instead of the parent names.
-/
def getFieldsToParents (env : Environment) (structName : Name) : Array Name :=
  getStructureFields env structName |>.filter fun fieldName =>
    isSubobjectField? env structName fieldName |>.isSome

end Lean
