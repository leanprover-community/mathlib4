/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public meta import Lean.Meta.Reduce
public meta import Mathlib.Lean.Meta.RefinedDiscrTree.Initialize
public meta import Mathlib.Lean.Meta.RefinedDiscrTree.Lookup
public meta import Mathlib.Tactic.FunProp.Decl
public meta import Mathlib.Tactic.FunProp.FunctionData
public meta import Mathlib.Tactic.FunProp.Types
public import Mathlib.Tactic.FunProp.Decl
public import Mathlib.Tactic.FunProp.Types

import Mathlib.Lean.Meta.RefinedDiscrTree.Lookup

/-!
## `fun_prop` environment extensions storing theorems for `fun_prop`
-/

public meta section

namespace Mathlib
open Lean Meta
open Std (TreeMap)

namespace Meta.FunProp

/-- Tag for one of the 5 basic lambda theorems, that also hold extra data for composition theorem
-/
inductive LambdaTheoremArgs
  /-- Identity theorem e.g. `Continuous fun x ↦ x` -/
  | id
  /-- Constant theorem e.g. `Continuous fun x ↦ y` -/
  | const
  /-- Apply theorem e.g. `Continuous fun (f : (x : X) → Y x ↦ f x)` -/
  | apply
  /-- Composition theorem e.g. `Continuous f → Continuous g → Continuous fun x ↦ f (g x)`

  The numbers `fArgId` and `gArgId` store the argument index for `f` and `g` in the composition
  theorem. -/
  | comp (fArgId gArgId : Nat)
  /-- Pi theorem e.g. `∀ y, Continuous (f · y) → Continuous fun x y ↦ f x y` -/
  | pi
  deriving Inhabited, BEq, Repr, Hashable

/-- Tag for one of the 5 basic lambda theorems -/
inductive LambdaTheoremType
  /-- Identity theorem e.g. `Continuous fun x ↦ x` -/
  | id
  /-- Constant theorem e.g. `Continuous fun x ↦ y` -/
  | const
  /-- Apply theorem e.g. `Continuous fun (f : (x : X) → Y x ↦ f x)` -/
  | apply
  /-- Composition theorem e.g. `Continuous f → Continuous g → Continuous fun x ↦ f (g x)` -/
  | comp
  /-- Pi theorem e.g. `∀ y, Continuous (f · y) → Continuous fun x y ↦ f x y` -/
  | pi
  deriving Inhabited, BEq, Repr, Hashable

/-- Convert `LambdaTheoremArgs` to `LambdaTheoremType`. -/
def LambdaTheoremArgs.type (t : LambdaTheoremArgs) : LambdaTheoremType :=
  match t with
  | .id => .id
  | .const => .const
  | .comp .. => .comp
  | .apply  => .apply
  | .pi => .pi

/-- Decides whether `f` is a function corresponding to one of the lambda theorems. -/
def detectLambdaTheoremArgs (f : Expr) (ctxVars : Array Expr) :
    MetaM (Option LambdaTheoremArgs) := do

  -- eta expand but beta reduce body
  let f ← forallTelescope (← inferType f) fun xs _ =>
    mkLambdaFVars xs (mkAppN f xs).headBeta

  match f with
  | .lam _ _ xBody _ =>
    unless xBody.hasLooseBVars do return some .const
    match xBody with
    | .bvar 0 => return some .id
    | .app (.bvar 0) (.fvar _) =>  return some .apply
    | .app (.fvar fId) (.app (.fvar gId) (.bvar 0)) =>
      -- fun x => f (g x)
      let some argId_f := ctxVars.findIdx? (fun x => x == (.fvar fId)) | return none
      let some argId_g := ctxVars.findIdx? (fun x => x == (.fvar gId)) | return none
      return some <| .comp argId_f argId_g
    | .lam _ _ (.app (.app (.fvar _) (.bvar 1)) (.bvar 0)) _ =>
      return some .pi
    | _ => return none
  | _ => return none


/-- Structure holding information about lambda theorem. -/
structure LambdaTheorem where
  /-- Name of function property -/
  funPropName : Name
  /-- Name of lambda theorem -/
  thmName : Name
  /-- Type and important argument of the theorem. -/
  thmArgs : LambdaTheoremArgs
  deriving Inhabited, BEq

/-- Collection of lambda theorems -/
structure LambdaTheorems where
  /-- map: function property name × theorem type → lambda theorem -/
  theorems : Std.HashMap (Name × LambdaTheoremType) (Array LambdaTheorem) := {}
  deriving Inhabited


/-- Return proof of lambda theorem -/
def LambdaTheorem.getProof (thm : LambdaTheorem) : MetaM Expr := do
  mkConstWithFreshMVarLevels thm.thmName

/-- Environment extension storing lambda theorems. -/
abbrev LambdaTheoremsExt := SimpleScopedEnvExtension LambdaTheorem LambdaTheorems

/-- Environment extension storing all lambda theorems. -/
initialize lambdaTheoremsExt : LambdaTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d e =>
      {d with theorems :=
        let es := d.theorems.getD (e.funPropName, e.thmArgs.type) #[]
        d.theorems.insert (e.funPropName, e.thmArgs.type) (es.push e)}
  }

/-- Get lambda theorems for particular function property `funPropName`. -/
def getLambdaTheorems (funPropName : Name) (type : LambdaTheoremType) :
    CoreM (Array LambdaTheorem) := do
  return (lambdaTheoremsExt.getState (← getEnv)).theorems.getD (funPropName,type) #[]


--------------------------------------------------------------------------------

/-- Function theorems are stated in uncurried or compositional form.

uncurried
```
theorem Continuous_add : Continuous (fun x ↦ x.1 + x.2)
```

compositional
```
theorem Continuous_add (hf : Continuous f) (hg : Continuous g) : Continuous (fun x ↦ (f x) + (g x))
```
-/
inductive TheoremForm where
  | uncurried (args : Nat) | comp
  deriving Inhabited, BEq, Repr

/-- TheoremForm to string -/
instance : ToString TheoremForm :=
  ⟨fun
   | .uncurried 1 => "simple"
   | .uncurried n => s!"simple ({n} arguments)"
   | .comp => "compositional"⟩

/-- theorem about specific function (either declared constant or free variable) -/
structure FunctionTheorem where
  /-- function property name -/
  funPropName : Name
  /-- theorem name -/
  thmOrigin   : Origin
  /-- function name -/
  funOrigin   : Origin
  /-- array of argument indices about which this theorem is about -/
  mainArgs    : Array Nat
  /-- total number of arguments applied to the function -/
  appliedArgs : Nat
  /-- priority -/
  priority    : Nat  := eval_prio default
  /-- form of the theorem, see documentation of TheoremForm -/
  form : TheoremForm
  deriving Inhabited, BEq

set_option linter.style.docString.empty false in
/-- -/
structure FunctionTheorems where
  /-- map: function name → function property → function theorem -/
  theorems :
    TreeMap Name (TreeMap Name (Array FunctionTheorem) Name.quickCmp) Name.quickCmp := {}
  deriving Inhabited


/-- return proof of function theorem -/
def FunctionTheorem.getProof (thm : FunctionTheorem) : MetaM Expr := do
  match thm.thmOrigin with
  | .decl name => mkConstWithFreshMVarLevels name
  | .fvar id => return .fvar id

/-- Given a theorem `thm` in uncurried form, returns a tuple `(xs, p, f, g)`, where `xy` is an array
of metavariables corresponding to the theorem's arguments and `p` is an expression
containing metavariables that should be unified with the goal. If this unification is successful,
then the goal is of the form `f ∘ g`, where `f` is an instantiation of `thm`. -/
def FunctionTheorem.mkPattern (thm : FunctionTheorem) :
    MetaM (Array Expr × Expr × Expr × Expr) := do
  let .uncurried argCount := thm.form
  | throwError "fun_prop bug: mkPattern can only be used with uncurried form"
  let type ← instantiateMVars <| ← inferType <| ← thm.thmOrigin.getValue
  let (xs, _, type) ← withReducible <| forallMetaTelescopeReducing type
  let .some f ← getFunPropFun? type
    | throwError "fun_prop bug: mkPattern called with invalid theorem"
  let .forallE _ xType _ _ ← instantiateMVars (← inferType f)
    | throwError m!"fun_prop bug: function expected, got `{f} : {← inferType f}, \
                    type ctor {(← inferType f).ctorName}"
  let xTypes ← getProdNTypes xType argCount
  let yType ← mkFreshExprMVar none
  withLocalDeclD .anonymous yType fun y => do
  let gBody ← mkProdElem <| ← xTypes.mapM fun t => mkFreshExprMVar <| some t
  let g ← mkLambdaFVars #[y] gBody
  let p ← mkLambdaFVars #[y] <| f.beta #[gBody]
  return (xs, p, f, g)

set_option linter.style.docString.empty false in
/-- -/
abbrev FunctionTheoremsExt := SimpleScopedEnvExtension FunctionTheorem FunctionTheorems

/-- Extension storing all function theorems. -/
initialize functionTheoremsExt : FunctionTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun d e =>
      {d with
        theorems :=
          d.theorems.alter e.funOrigin.name fun funProperties =>
            let funProperties := funProperties.getD {}
            funProperties.alter e.funPropName fun thms =>
              let thms := thms.getD #[]
              thms.push e}
  }

set_option linter.style.docString.empty false in
/-- -/
def getTheoremsForFunction (funName : Name) (funPropName : Name) :
    CoreM (Array FunctionTheorem) := do
  return (functionTheoremsExt.getState (← getEnv)).theorems.getD funName {}
    |>.getD funPropName #[]


--------------------------------------------------------------------------------

/-- Get proof of a theorem. -/
def GeneralTheorem.getProof (thm : GeneralTheorem) : MetaM Expr := do
  mkConstWithFreshMVarLevels thm.thmName

/-- Extensions for transition or morphism theorems -/
abbrev GeneralTheoremsExt := SimpleScopedEnvExtension GeneralTheorem GeneralTheorems

/-- Environment extension for transition theorems. -/
initialize transitionTheoremsExt : GeneralTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun d e =>
      {d with theorems := e.keys.foldl (fun thms (key, entry) =>
        RefinedDiscrTree.insert thms key (entry, e)) d.theorems}
  }

/-- Get transition theorems applicable to `e`.

For example calling on `e` equal to `Continuous f` might return theorems implying continuity
from linearity over finite-dimensional spaces or differentiability. -/
def getTransitionTheorems (e : Expr) : FunPropM (Array GeneralTheorem) := do
  let thms := (← get).transitionTheorems.theorems
  let (candidates, thms) ← withConfig (fun cfg => { cfg with iota := false, zeta := false }) <|
    thms.getMatch e false true
  modify ({ · with transitionTheorems := ⟨thms⟩ })
  return candidates.toArray

/-- Environment extension for morphism theorems. -/
initialize morTheoremsExt : GeneralTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun d e =>
      {d with theorems := e.keys.foldl (fun thms (key, entry) =>
        RefinedDiscrTree.insert thms key (entry, e)) d.theorems}
  }


/-- Get morphism theorems applicable to `e`.

For example calling on `e` equal to `Continuous f` for `f : X→L[ℝ] Y` would return theorem
inferring continuity from the bundled morphism. -/
def getMorphismTheorems (e : Expr) : FunPropM (Array GeneralTheorem) := do
  let thms := (← get).morTheorems.theorems
  let (candidates, thms) ← withConfig (fun cfg => { cfg with iota := false, zeta := false }) <|
    thms.getMatch e false true
  modify ({ · with morTheorems := ⟨thms⟩ })
  return candidates.toArray


--------------------------------------------------------------------------------


/-- There are four types of theorems:
- lam - theorem about basic lambda calculus terms
- function - theorem about a specific function(declared or free variable) in specific arguments
- mor - special theorems talking about bundled morphisms/DFunLike.coe
- transition - theorems inferring one function property from another

Examples:
- lam
  ```
  theorem Continuous_id : Continuous fun x ↦ x
  theorem Continuous_comp (hf : Continuous f) (hg : Continuous g) : Continuous fun x ↦ f (g x)
  ```
- function
  ```
  theorem Continuous_add : Continuous (fun x ↦ x.1 + x.2)
  theorem Continuous_add (hf : Continuous f) (hg : Continuous g) :
      Continuous (fun x ↦ (f x) + (g x))
  ```
- mor - the head of function body has to be `DFunLike.coe`
  ```
  theorem ContDiff.clm_apply {f : E → F →L[𝕜] G} {g : E → F}
      (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
      ContDiff 𝕜 n fun x ↦ (f x) (g x)
  theorem clm_linear {f : E →L[𝕜] F} : IsLinearMap 𝕜 f
  ```
- transition - the conclusion has to be in the form `P f` where `f` is a free variable
  ```
  theorem linear_is_continuous [FiniteDimensional ℝ E] {f : E → F} (hf : IsLinearMap 𝕜 f) :
      Continuous f
  ```
-/
inductive Theorem where
  | lam        (thm : LambdaTheorem)
  | function   (thm : FunctionTheorem)
  | mor        (thm : GeneralTheorem)
  | transition (thm : GeneralTheorem)

/-- Decide whether `f` is in compositional form. This is done by checking whether
there is an application where the head is in the array `fvars`, and at least one argument of
this application contains the function variable. -/
partial def isCompositional (fvars : Array Expr) (f : Expr) : MetaM Bool := do
  -- Reduce everything to handle `Function.comp`, etc.
  let f ← withReducible <| reduce (explicitOnly := false) (skipTypes := false) f
  let .lam xn xt f xbi := f | return false
  withLocalDecl xn xbi xt fun x => do
  let f := f.instantiate1 x
  let fvars : FVarIdSet := .ofArray <| fvars.map (·.fvarId!)
  let rec go fvarApp
  | y@(.fvar _) => fvarApp && y == x
  | e@(.app ..) =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.fvarId?.any fvars.contains then
      args.any (go true)
    else
      go fvarApp fn || args.any (go fvarApp)
  | .lam _ _ f _ => go fvarApp f
  | .letE _ _ e f _ => go fvarApp e || go fvarApp f
  | .forallE _ e f _ => go fvarApp e || go fvarApp f
  | .proj _ _ e => go fvarApp e
  | _ => false
  return go false f

/-- Counts the number of arguments of a theorem in uncurried form. This is the least `n` such that
if `x` is the function variable, then the `n` expressions `x.1`, `x.2.1`, …, `x.2…2.1` and `x.2…2`
all appear in the function. -/
partial def countUncurriedArgs (f : Expr) : MetaM Nat := do
  -- Reduce everything to handle `Function.comp`, etc.
  let f ← withReducible <| reduce (explicitOnly := false) (skipTypes := false) f
  let .lam xn xt f xbi := f | return 1
  withLocalDecl xn xbi xt fun x => do
  let f := f.instantiate1 x
  let ((), fsts, maxSnds) ← f.forEach (go x) |>.run (0, 0)
  let mut count := 0
  while count < maxSnds && fsts.testBit count do
    count := count + 1
  return count + 1
where
  go x e : StateT (Nat × Nat) MetaM Unit := do
    let mut (e, isFst) := (e, false)
    -- We must check for `.proj` because of the call to `reduce`
    if let .proj `Prod 0 e' := e then
      e := e'
      isFst := true
    let mut snds := 0
    while let .proj `Prod 1 e' := e do
      e := e'
      snds := snds + 1
    if e != x then return
    if isFst then
      modify (fun (fsts, maxSnds) => (fsts ||| 1 <<< snds, maxSnds))
    else
      modify (fun (fsts, maxSnds) => (fsts, max maxSnds snds))

/-- Given an array `fvars` obtained from `forallTelescope`, returns the theorem form of `f`. -/
partial def getTheoremForm (fvars : Array Expr) (f : Expr) : MetaM TheoremForm := do
  if ← isCompositional fvars f then
    return .comp
  else
    return .uncurried <| ← countUncurriedArgs f

/-- For a theorem declaration `declName` return `fun_prop` theorem. It correctly detects which
type of theorem it is. -/
def getTheoremFromConst (declName : Name) (prio : Nat := eval_prio default) : MetaM Theorem := do
  let info ← getConstInfo declName
  forallTelescope info.type fun xs b => do
    let some (decl,f) ← getFunProp? b
      | throwError "unrecognized function property `{← ppExpr b}`"
    let funPropName := decl.funPropName
    let fData? ←
      withConfig (fun cfg => { cfg with zeta := false}) <| getFunctionData? f unfoldPred
    if let some thmArgs ← detectLambdaTheoremArgs (← fData?.get) xs then
      return .lam {
        funPropName := funPropName
        thmName := declName
        thmArgs := thmArgs
      }

    let .data fData := fData?
      | throwError s!"function in invalid form {← ppExpr f}"

    match fData.fn with
    | .const funName _ =>
      return .function {
-- funPropName funName fData.mainArgs fData.args.size thmForm
        funPropName := funPropName
        thmOrigin := .decl declName
        funOrigin := .decl funName
        mainArgs := fData.mainArgs
        appliedArgs := fData.args.size
        priority := prio
        form := ← withCanUnfoldPred unfoldPred <| getTheoremForm xs f
      }
    | .fvar .. =>
      let (_,_,b') ← forallMetaTelescope info.type
      let keys ← RefinedDiscrTree.initializeLazyEntryWithEta b'
      let thm : GeneralTheorem := {
        funPropName := funPropName
        thmName := declName
        keys    := keys
        priority  := prio
      }
      -- todo: maybe do a little bit more careful detection of morphism and transition theorems
      match (← fData.isMorApplication) with
      | .exact | .overApplied => return .mor thm
      | .underApplied =>
        throwError "fun_prop theorem about morphism coercion has to be in fully applied form"
      | .none =>
        if fData.fn.isFVar && (fData.args.size == 1) &&
           (fData.args[0]!.expr == fData.mainVar) then
          return .transition thm

        throwError "Not a valid `fun_prop` theorem!"
    | _ =>
      throwError "unrecognized theoremType `{← ppExpr b}`"


/-- Register theorem `declName` with `fun_prop`. -/
def addTheorem (declName : Name) (attrKind : AttributeKind := .global)
    (prio : Nat := eval_prio default) : MetaM Unit := do
  match (← getTheoremFromConst declName prio) with
  | .lam thm =>
    trace[Meta.Tactic.fun_prop.attr] "\
lambda theorem: {thm.thmName}
function property: {thm.funPropName}
type: {repr thm.thmArgs.type}"
    lambdaTheoremsExt.add thm attrKind
  | .function thm =>
    trace[Meta.Tactic.fun_prop.attr] "\
function theorem: {thm.thmOrigin.name}
function property: {thm.funPropName}
function name: {thm.funOrigin.name}
main arguments: {thm.mainArgs}
applied arguments: {thm.appliedArgs}
form: {toString thm.form}"
    functionTheoremsExt.add thm attrKind
  | .mor thm =>
    trace[Meta.Tactic.fun_prop.attr] "\
morphism theorem: {thm.thmName}
function property: {thm.funPropName}"
    morTheoremsExt.add thm attrKind
  | .transition thm =>
    trace[Meta.Tactic.fun_prop.attr] "\
transition theorem: {thm.thmName}
function property: {thm.funPropName}"
    transitionTheoremsExt.add thm attrKind

end Meta.FunProp

end Mathlib
