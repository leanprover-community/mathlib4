/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Scott Morrison, Keeley Hoek, Robert Y. Lewis,
Floris van Doorn, E.W.Ayers, Arthur Paulino
-/
import Lean
import Std.Lean.Expr
import Std.Data.List.Basic

/-!
# Additional operations on Expr and related types

This file defines basic operations on the types expr, name, declaration, level, environment.

This file is mostly for non-tactics.
-/

set_option autoImplicit true

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
def mapPrefix (f : Name → Option Name) (n : Name) : Name := Id.run do
  if let some n' := f n then return n'
  match n with
  | anonymous => anonymous
  | str n' s => mkStr (mapPrefix f n') s
  | num n' i => mkNum (mapPrefix f n') i

/-- Build a name from components. For example ``from_components [`foo, `bar]`` becomes
  ``` `foo.bar```.
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
def getString : Name → String
  | .str _ s => s
  | .num _ n => toString n
  | .anonymous => ""

/-- `nm.splitAt n` splits a name `nm` in two parts, such that the *second* part has depth `n`, i.e.
  `(nm.splitAt n).2.getNumParts = n` (assuming `nm.getNumParts ≥ n`).
  Example: ``splitAt `foo.bar.baz.back.bat 1 = (`foo.bar.baz.back, `bat)``. -/
def splitAt (nm : Name) (n : Nat) : Name × Name :=
  let (nm2, nm1) := (nm.componentsRev.splitAt n)
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

/-- Lean 4 makes declarations which are technically not internal
(that is, head string does not start with `_`) but which sometimes should
be treated as such. For example, the `to_additive` attribute needs to
transform `proof_1` constants generated by `Lean.Meta.mkAuxDefinitionFor`.
This might be better fixed in core, but until then, this method can act
as a polyfill. This method only looks at the name to decide whether it is probably internal.
Note: this declaration also occurs as `shouldIgnore` in the Lean 4 file `test/lean/run/printDecls`.
-/
def isInternal' (declName : Name) : Bool :=
  declName.isInternal ||
  match declName with
  | .str _ s => "match_".isPrefixOf s || "proof_".isPrefixOf s
  | _        => true


open Meta

-- from Lean.Server.Completion
def isBlackListed (declName : Name) : CoreM Bool := do
  if declName == ``sorryAx then return true
  if declName matches .str _ "inj" then return true
  if declName matches .str _ "noConfusionType" then return true
  let env ← getEnv
  pure $ declName.isInternal'
   || isAuxRecursor env declName
   || isNoConfusion env declName
  <||> isRec declName <||> isMatcher declName

end Name

namespace NameSet

/-- The union of two `NameSet`s. -/
def append (s t : NameSet) : NameSet :=
  s.mergeBy (fun _ _ _ => .unit) t

instance : Append NameSet where
  append := NameSet.append

end NameSet

namespace ConstantInfo

/-- Checks whether this `ConstantInfo` is a definition, -/
def isDef : ConstantInfo → Bool
  | defnInfo _ => true
  | _          => false

/-- Checks whether this `ConstantInfo` is a theorem, -/
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

/-- If the expression is a constant, return that name. Otherwise return `Name.anonymous`. -/
def constName (e : Expr) : Name :=
  e.constName?.getD Name.anonymous

def bvarIdx? : Expr → Option Nat
  | bvar idx => some idx
  | _        => none

/-- Return the function (name) and arguments of an application. -/
def getAppFnArgs (e : Expr) : Name × Array Expr :=
  withApp e λ e a => (e.constName, a)

/-- Like `Expr.getUsedConstants`, but produce a `NameSet`. -/
def getUsedConstants' (e : Expr) : NameSet :=
  e.foldConsts {} fun c cs => cs.insert c

/-- Turn an expression that is a natural number literal into a natural number. -/
def natLit! : Expr → Nat
  | lit (Literal.natVal v) => v
  | _                      => panic! "nat literal expected"

/-- If an `Expr` has form `.fvar n`, then returns `some n`, otherwise `none`. -/
def fvarId? : Expr → Option FVarId
  | .fvar n => n
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
  | Int.negSucc n => do mkAppM ``Neg.neg #[← Expr.ofNat α (n+1)]

section recognizers

/--
  Return `some n` if `e` is one of the following
  - A nat literal (numeral)
  - `Nat.zero`
  - `Nat.succ x` where `isNumeral x`
  - `OfNat.ofNat _ x _` where `isNumeral x` -/
partial def numeral? (e : Expr) : Option Nat :=
  if let some n := e.natLit? then n
  else
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

/-- `Lean.Expr.le? p` take `e : Expr` as input.
If `e` represents `a ≤ b`, then it returns `some (t, a, b)`, where `t` is the Type of `a`,
otherwise, it returns `none`. -/
@[inline] def le? (p : Expr) : Option (Expr × Expr × Expr) := do
  let (type, _, lhs, rhs) ← p.app4? ``LE.le
  return (type, lhs, rhs)

end recognizers

def modifyAppArgM [Functor M] [Pure M] (modifier : Expr → M Expr) : Expr → M Expr
  | app f a => mkApp f <$> modifier a
  | e => pure e

def modifyAppArg (modifier : Expr → Expr) : Expr → Expr :=
  modifyAppArgM (M := Id) modifier

def modifyRevArg (modifier : Expr → Expr) : Nat → Expr → Expr
  | 0 => modifyAppArg modifier
  | (i+1) => modifyAppArg (modifyRevArg modifier i)

/-- Given `f a₀ a₁ ... aₙ₋₁`, runs `modifier` on the `i`th argument or
returns the original expression if out of bounds. -/
def modifyArg (modifier : Expr → Expr) (e : Expr) (i : Nat) (n := e.getAppNumArgs) : Expr :=
  modifyRevArg modifier (n - i - 1) e

def getRevArg? : Expr → Nat → Option Expr
  | app _ a, 0   => a
  | app f _, i+1 => getRevArg! f i
  | _,       _   => none

/-- Given `f a₀ a₁ ... aₙ₋₁`, returns the `i`th argument or none if out of bounds. -/
def getArg? (e : Expr) (i : Nat) (n := e.getAppNumArgs) : Option Expr :=
  getRevArg? e (n - i - 1)

/-- Given `f a₀ a₁ ... aₙ₋₁`, runs `modifier` on the `i`th argument.
An argument `n` may be provided which says how many arguments we are expecting `e` to have. -/
def modifyArgM [Monad M] (modifier : Expr → M Expr) (e : Expr) (i : Nat) (n := e.getAppNumArgs) :
    M Expr := do
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
  | e => e

open Lean.Meta in
/-- `getBinderName e` returns `some n` if `e` is an expression of the form `∀ n, ...`
and `none` otherwise. -/
def getBinderName (e : Expr) : MetaM (Option Name) := do
  match ← withReducible (whnf e) with
  | .forallE (binderName := n) .. | .lam (binderName := n) .. => pure (some n)
  | _ => pure none

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
  let .const structName _ := (← whnf (←inferType e)).getAppFn |
    throwError "{e} doesn't have a structure as type"
  let some baseStruct := findField? (← getEnv) structName fieldName |
    throwError "No parent of {structName} has field {fieldName}"
  let mut e := e
  for projName in (getPathToBaseStructure? (← getEnv) baseStruct structName).get! do
    let type ← whnf (← inferType e)
    let .const _structName us := type.getAppFn | throwError "{e} doesn't have a structure as type"
    e := mkAppN (.const projName us) (type.getAppArgs.push e)
  mkDirectProjection e fieldName

/-- Returns true if `e` contains a name `n` where `p n` is true. -/
def containsConst (e : Expr) (p : Name → Bool) : Bool :=
  Option.isSome <| e.find? fun | .const n _ => p n | _ => false

/--
Rewrites `e` via some `eq`, producing a proof `e = e'` for some `e'`.

Rewrites with a fresh metavariable as the ambient goal.
Fails if the rewrite produces any subgoals.
-/
def rewrite (e eq : Expr) : MetaM Expr := do
  let ⟨_, eq', []⟩ ← (← mkFreshExprMVar none).mvarId!.rewrite e eq
    | throwError "Expr.rewrite may not produce subgoals."
  return eq'

/--
Rewrites the type of `e` via some `eq`, then moves `e` into the new type via `Eq.mp`.

Rewrites with a fresh metavariable as the ambient goal.
Fails if the rewrite produces any subgoals.
-/
def rewriteType (e eq : Expr) : MetaM Expr := do
  mkEqMP (← (← inferType e).rewrite eq) e

end Expr

/-- Return all names appearing in the type or value of a `ConstantInfo`. -/
def ConstantInfo.getUsedConstants (c : ConstantInfo) : NameSet :=
  let tc := c.type.getUsedConstants'
  match c.value? with
  | none => tc
  | some v => tc ++ v.getUsedConstants'

/-- Get the projections that are projections to parent structures. Similar to `getParentStructures`,
  except that this returns the (last component of the) projection names instead of the parent names.
-/
def getFieldsToParents (env : Environment) (structName : Name) : Array Name :=
  getStructureFields env structName |>.filter fun fieldName =>
    isSubobjectField? env structName fieldName |>.isSome

/-- Return the name of the module in which a declaration was defined. -/
def Environment.getModuleFor? (env : Environment) (declName : Name) : Option Name :=
  match env.getModuleIdxFor? declName with
  | none =>
    if env.constants.map₂.contains declName then
      env.header.mainModule
    else
      none
  | some idx => env.header.moduleNames[idx.toNat]!

/--
Return the names of the modules in which constants used in the specified declaration were defined.

Note that this will *not* account for tactics and syntax used in the declaration,
so the results may not suffice as imports.
-/
def Name.requiredModules (n : Name) : CoreM NameSet := do
  let env ← getEnv
  let mut requiredModules : NameSet := {}
  let ci ← getConstInfo n
  for n in ci.getUsedConstants do
    match env.getModuleFor? n with
    | some m =>
      if ¬ (`Init).isPrefixOf m then
        requiredModules := requiredModules.insert m
    | none => pure ()
  return requiredModules

/--
Return the names of the modules in which constants used in the current file were defined.

Note that this will *not* account for tactics and syntax used in the file,
so the results may not suffice as imports.
-/
def Environment.requiredModules (env : Environment) : NameSet := Id.run do
  let localConstantInfos := env.constants.map₂
  let mut requiredModules : NameSet := {}
  for (_, ci) in localConstantInfos do
    for n in ci.getUsedConstants do
      match env.getModuleFor? n with
      | some m =>
        if ¬ (`Init).isPrefixOf m then
          requiredModules := requiredModules.insert m
      | none => pure ()
  return requiredModules

end Lean
