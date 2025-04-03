/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Control.Traversable.Lemmas

#align_import control.traversable.derive from "leanprover-community/mathlib"@"b01d6eb9d0a308807af54319b264d0994b91774b"

/-!
# Deriving handler for `Traversable` instances

This module gives deriving handlers for `Functor`, `LawfulFunctor`, `Traversable`, and
`LawfulTraversable`. These deriving handlers automatically derive their dependencies, for
example `deriving LawfulTraversable` all by itself gives all four.
-/

namespace Mathlib.Deriving.Traversable

open Lean Meta Elab Term Command Tactic Match List Monad Functor

/-- `nestedMap f α (List (Array (List α)))` synthesizes the expression
`Functor.map (Functor.map (Functor.map f))`. `nestedMap` assumes that `α` appears in
`(List (Array (List α)))`.

(Similar to `nestedTraverse` but for `Functor`.) -/
partial def nestedMap (f v t : Expr) : TermElabM Expr := do
  let t ← instantiateMVars t
  if ← withNewMCtxDepth <| isDefEq t v then
    return f
  else if !v.occurs t.appFn! then
    let cl ← mkAppM ``Functor #[t.appFn!]
    let inst ← synthInstance cl
    let f' ← nestedMap f v t.appArg!
    mkAppOptM ``Functor.map #[t.appFn!, inst, none, none, f']
  else throwError "type {t} is not a functor with respect to variable {v}"

/-- similar to `traverseField` but for `Functor` -/
def mapField (n : Name) (cl f α β e : Expr) : TermElabM Expr := do
  let t ← whnf (← inferType e)
  if t.getAppFn.constName = some n then
    throwError "recursive types not supported"
  else if α.eqv e then
    return β
  else if α.occurs t then
    let f' ← nestedMap f α t
    return f'.app e
  else if ←
      (match t with
        | .app t' _ => withNewMCtxDepth <| isDefEq t' cl
        | _ => return false) then
    mkAppM ``Comp.mk #[e]
  else
    return e

/-- Get the auxiliary local declaration corresponding to the current declaration. If there are
multiple declaraions it will throw. -/
def getAuxDefOfDeclName : TermElabM FVarId := do
  let some declName ← getDeclName? | throwError "no 'declName?'"
  let auxDeclMap := (← read).auxDeclToFullName
  let fvars := auxDeclMap.fold (init := []) fun fvars fvar fullName =>
    if fullName = declName then fvars.concat fvar else fvars
  match fvars with
  | [] => throwError "no auxiliary local declaration corresponding to the current declaration"
  | [fvar] => return fvar
  | _ => throwError "multiple local declarations corresponding to the current declaration"

/-- similar to `traverseConstructor` but for `Functor` -/
def mapConstructor (c n : Name) (f α β : Expr) (args₀ : List Expr)
    (args₁ : List (Bool × Expr)) (m : MVarId) : TermElabM Unit := do
  let ad ← getAuxDefOfDeclName
  let g ← m.getType >>= instantiateMVars
  let args' ← args₁.mapM (fun (y : Bool × Expr) =>
      if y.1 then return mkAppN (.fvar ad) #[α, β, f, y.2]
      else mapField n g.appFn! f α β y.2)
  mkAppOptM c ((args₀ ++ args').map some).toArray >>= m.assign

/-- Makes a `match` expression corresponding to the application of `casesOn` like:
```lean
match (motive := motive) indices₁, indices₂, .., (val : type.{univs} params₁ params₂ ..) with
| _, _, .., ctor₁ fields₁₁ fields₁₂ .. => rhss ctor₁ [fields₁₁, fields₁₂, ..]
| _, _, .., ctor₂ fields₂₁ fields₂₂ .. => rhss ctor₂ [fields₂₁, fields₂₂, ..]
```
This is convenient to make a definition with equation lemmas. -/
def mkCasesOnMatch (type : Name) (levels : List Level) (params : List Expr) (motive : Expr)
    (indices : List Expr) (val : Expr)
    (rhss : (ctor : Name) → (fields : List FVarId) → TermElabM Expr) : TermElabM Expr := do
  let matcherName ← getDeclName? >>= (fun n? => Lean.mkAuxName (.mkStr (n?.getD type) "match") 1)
  let matchType ← generalizeTelescope (indices.concat val).toArray fun iargs =>
    mkForallFVars iargs (motive.beta iargs)
  let iinfo ← getConstInfoInduct type
  let lhss ← iinfo.ctors.mapM fun ctor => do
    let cinfo ← getConstInfoCtor ctor
    let catype ←
      instantiateForall (cinfo.type.instantiateLevelParams cinfo.levelParams levels) params.toArray
    forallBoundedTelescope catype cinfo.numFields fun cargs _ => do
      let fvarDecls ← cargs.toList.mapM fun carg => getFVarLocalDecl carg
      let fieldPats := cargs.toList.map fun carg => Pattern.var carg.fvarId!
      let patterns := [Pattern.ctor cinfo.name levels params fieldPats]
      return { ref := .missing
               fvarDecls
               patterns }
  let mres ← Term.mkMatcher { matcherName
                              matchType
                              discrInfos := mkArray (indices.length + 1) {}
                              lhss }
  mres.addMatcher
  let rhss ← lhss.mapM fun altLHS => do
    let [.ctor ctor _ _ cpats] := altLHS.patterns | unreachable!
    withExistingLocalDecls altLHS.fvarDecls do
      let fields := altLHS.fvarDecls.map LocalDecl.fvarId
      let rhsBody ← rhss ctor fields
      if cpats.isEmpty then
        mkFunUnit rhsBody
      else
        mkLambdaFVars (fields.map Expr.fvar).toArray rhsBody
  return mkAppN mres.matcher (motive :: indices ++ [val] ++ rhss).toArray

/-- Get `FVarId`s which is not implementation details in the current context. -/
def getFVarIdsNotImplementationDetails : MetaM (List FVarId) := do
  let lctx ← getLCtx
  return lctx.decls.foldl (init := []) fun r decl? => match decl? with
    | some decl => if decl.isImplementationDetail then r else r.concat decl.fvarId
    | none      => r

/-- Get `Expr`s of `FVarId`s which is not implementation details in the current context. -/
def getFVarsNotImplementationDetails : MetaM (List Expr) :=
  List.map Expr.fvar <$> getFVarIdsNotImplementationDetails

/-- derive the `map` definition of a `Functor` -/
def mkMap (type : Name) (m : MVarId) : TermElabM Unit := do
  let levels ← getLevelNames
  let vars ← getFVarsNotImplementationDetails
  let (#[α, β, f, x], m) ← m.introN 4 [`α, `β, `f, `x] | failure
  m.withContext do
    let xtype ← x.getType
    let target ← m.getType >>= instantiateMVars
    let motive ← mkLambdaFVars #[.fvar x] target
    let e ←
      mkCasesOnMatch type (levels.map Level.param) (vars.concat (.fvar α)) motive [] (.fvar x)
        fun ctor fields => do
          let m ← mkFreshExprSyntheticOpaqueMVar target
          let args := fields.map Expr.fvar
          let args₀ ← args.mapM fun a => do
            let b := xtype.occurs (← inferType a)
            return (b, a)
          mapConstructor
            ctor type (.fvar f) (.fvar α) (.fvar β) (vars.concat (.fvar β)) args₀ m.mvarId!
          instantiateMVars m
    m.assign e

/-- derive the `map` definition and declare `Functor` using this. -/
def deriveFunctor (m : MVarId) : TermElabM Unit := do
  let levels ← getLevelNames
  let vars ← getFVarsNotImplementationDetails
  let .app (.const ``Functor _) F ← m.getType >>= instantiateMVars | failure
  let some n := F.getAppFn.constName? | failure
  let d ← getConstInfo n
  let [m] ← run m <| evalTactic (← `(tactic| refine { map := @(?_) })) | failure
  let t ← m.getType >>= instantiateMVars
  let n' := .mkStr n "map"
  withDeclName n' <| withAuxDecl (.mkSimple "map") t n' fun ad => do
    let m' := (← mkFreshExprSyntheticOpaqueMVar t).mvarId!
    mkMap n m'
    let e ← instantiateMVars (mkMVar m')
    let e := e.replaceFVar ad (mkAppN (.const n' (levels.map Level.param)) vars.toArray)
    let e' ← mkLambdaFVars vars.toArray e
    let t' ← mkForallFVars vars.toArray t
    addPreDefinitions
      #[{ ref := .missing
          kind := .def
          levelParams := levels
          modifiers :=
            { isUnsafe := d.isUnsafe
              attrs :=
                #[{ kind := .global
                    name := `specialize
                    stx := ← `(attr| specialize) }] }
          declName := n'
          type := t'
          value := e'
          termination := .none }] {}
  m.assign (mkAppN (mkConst n' (levels.map Level.param)) vars.toArray)

/-- Similar to `mkInstanceName`, but for a `Expr` type. -/
def mkInstanceNameForTypeExpr (type : Expr) : TermElabM Name := do
  let result ← do
    let ref ← IO.mkRef ""
    Meta.forEachExpr type fun e => do
      if e.isForall then ref.modify (· ++ "ForAll")
      else if e.isProp then ref.modify (· ++ "Prop")
      else if e.isType then ref.modify (· ++ "Type")
      else if e.isSort then ref.modify (· ++ "Sort")
      else if e.isConst then
        match e.constName!.eraseMacroScopes with
        | .str _ str =>
            if str.front.isLower then
              ref.modify (· ++ str.capitalize)
            else
              ref.modify (· ++ str)
        | _ => pure ()
    ref.get
  liftMacroM <| mkUnusedBaseName <| Name.mkSimple ("inst" ++ result)

/-- Derive the `cls` instance for the inductive type constructor `n` using the `tac` tactic. -/
def mkOneInstance (n cls : Name) (tac : MVarId → TermElabM Unit)
    (mkInst : Name → Expr → TermElabM Expr := fun n arg => mkAppM n #[arg]) : TermElabM Unit := do
  let .inductInfo decl ← getConstInfo n |
    throwError m!"failed to derive '{cls}', '{n}' is not an inductive type"
  let clsDecl ← getConstInfo cls
  let ls := decl.levelParams.map Level.param
  -- incrementally build up target expression `(hp : p) → [cls hp] → ... cls (n.{ls} hp ...)`
  -- where `p ...` are the inductive parameter types of `n`
  let tgt := Lean.mkConst n ls
  let tgt ← forallTelescope decl.type fun params _ => do
    let params := params.pop
    let tgt := mkAppN tgt params
    let tgt ← mkInst cls tgt
    params.zipWithIndex.foldrM (fun (param, i) tgt => do
      -- add typeclass hypothesis for each inductive parameter
      let tgt ← (do
        guard (i < decl.numParams)
        let paramCls ← mkAppM cls #[param]
        return mkForall `a .instImplicit paramCls tgt) <|> return tgt
      mkForallFVars #[param] tgt) tgt
  (discard <| liftM (synthInstance tgt)) <|> do
    let m := (← mkFreshExprSyntheticOpaqueMVar tgt).mvarId!
    let (_, m') ← m.intros
    withLevelNames decl.levelParams <| m'.withContext <| tac m'
    let val ← instantiateMVars (mkMVar m)
    let isUnsafe := decl.isUnsafe || clsDecl.isUnsafe
    let instN ← m'.withContext do
      let type ← m'.getType >>= instantiateMVars
      mkInstanceNameForTypeExpr type
    addPreDefinitions
      #[{ ref := .missing
          kind := .def
          levelParams := decl.levelParams
          modifiers :=
            { isUnsafe
              attrs :=
                #[{ kind := .global
                    name := `instance
                    stx := ← `(attr| instance) }] }
          declName := instN
          type := tgt
          value := val
          termination := .none }] {}

/-- Make the new deriving handler depends on other deriving handlers. -/
def higherOrderDeriveHandler (cls : Name) (tac : MVarId → TermElabM Unit)
    (deps : List DerivingHandlerNoArgs := [])
    (mkInst : Name → Expr → TermElabM Expr := fun n arg => mkAppM n #[arg]) :
    DerivingHandlerNoArgs := fun a => do
  let #[n] := a | return false -- mutually inductive types are not supported yet
  let ok ← deps.mapM fun f => f a
  unless ok.and do return false
  liftTermElabM <| mkOneInstance n cls tac mkInst
  return true

/-- The deriving handler for `Functor`. -/
def functorDeriveHandler : DerivingHandlerNoArgs :=
  higherOrderDeriveHandler ``Functor deriveFunctor []

initialize registerDerivingHandler ``Functor functorDeriveHandler

/-- Prove the functor laws and derive `LawfulFunctor`. -/
def deriveLawfulFunctor (m : MVarId) : TermElabM Unit := do
  let rules (l₁ : List (Name × Bool)) (l₂ : List (Name)) (b : Bool) : MetaM Simp.Context := do
    let mut s : SimpTheorems := {}
    s ← l₁.foldlM (fun s (n, b) => s.addConst n (inv := b)) s
    s ← l₂.foldlM (fun s n => s.addDeclToUnfold n) s
    if b then
      let hs ← getPropHyps
      s ← hs.foldlM (fun s f => f.getDecl >>= fun d => s.add (.fvar f) #[] d.toExpr) s
    return { simpTheorems := #[s] }
  let .app (.app (.const ``LawfulFunctor _) F) _ ← m.getType >>= instantiateMVars | failure
  let some n := F.getAppFn.constName? | failure
  let [mcn, mim, mcm] ← m.applyConst ``LawfulFunctor.mk | failure
  let (_, mcn) ← mcn.introN 2
  mcn.refl
  let (#[_, x], mim) ← mim.introN 2 | failure
  let (some mim, _) ← dsimpGoal mim (← rules [] [``Functor.map] false) | failure
  let xs ← mim.induction x (mkRecName n)
  xs.forM fun ⟨mim, _, _⟩ =>
    mim.withContext do
      if let (some (_, mim), _) ←
          simpGoal mim (← rules [(``Functor.map_id, false)] [.mkStr n "map"] true) then
        mim.refl
  let (#[_, _, _, _, _, x], mcm) ← mcm.introN 6 | failure
  let (some mcm, _) ← dsimpGoal mcm (← rules [] [``Functor.map] false) | failure
  let xs ← mcm.induction x (mkRecName n)
  xs.forM fun ⟨mcm, _, _⟩ =>
    mcm.withContext do
      if let (some (_, mcm), _) ←
          simpGoal mcm (← rules [(``Functor.map_comp_map, true)] [.mkStr n "map"] true) then
        mcm.refl

/-- The deriving handler for `LawfulFunctor`. -/
def lawfulFunctorDeriveHandler : DerivingHandlerNoArgs :=
  higherOrderDeriveHandler ``LawfulFunctor deriveLawfulFunctor [functorDeriveHandler]
    (fun n arg => mkAppOptM n #[arg, none])

initialize registerDerivingHandler ``LawfulFunctor lawfulFunctorDeriveHandler

/-- `nestedTraverse f α (List (Array (List α)))` synthesizes the expression
`traverse (traverse (traverse f))`. `nestedTraverse` assumes that `α` appears in
`(List (Array (List α)))` -/
partial def nestedTraverse (f v t : Expr) : TermElabM Expr := do
  let t ← instantiateMVars t
  if ← withNewMCtxDepth <| isDefEq t v then
    return f
  else if !v.occurs t.appFn! then
    let cl ← mkAppM ``Traversable #[t.appFn!]
    let inst ← synthInstance cl
    let f' ← nestedTraverse f v t.appArg!
    mkAppOptM ``Traversable.traverse #[t.appFn!, inst, none, none, none, none, f']
  else throwError "type {t} is not traversable with respect to variable {v}"

/--
For a sum type `inductive Foo (α : Type) | foo1 : List α → ℕ → Foo α | ...`
``traverseField `Foo f `α `(x : List α)`` synthesizes
`traverse f x` as part of traversing `foo1`. -/
def traverseField (n : Name) (cl f v e : Expr) : TermElabM (Bool × Expr) := do
  let t ← whnf (← inferType e)
  if t.getAppFn.constName = some n then
    throwError "recursive types not supported"
  else if v.occurs t then
    let f' ← nestedTraverse f v t
    return (true, f'.app e)
  else if ←
      (match t with
        | .app t' _ => withNewMCtxDepth <| isDefEq t' cl
        | _ => return false) then
    Prod.mk true <$> mkAppM ``Comp.mk #[e]
  else
    return (false, e)

/--
For a sum type `inductive Foo (α : Type) | foo1 : List α → ℕ → Foo α | ...`
``traverseConstructor `foo1 `Foo applInst f `α `β [`(x : List α), `(y : ℕ)]``
synthesizes `foo1 <$> traverse f x <*> pure y.` -/
def traverseConstructor (c n : Name) (applInst f α β : Expr) (args₀ : List Expr)
    (args₁ : List (Bool × Expr)) (m : MVarId) : TermElabM Unit := do
  let ad ← getAuxDefOfDeclName
  let g ← m.getType >>= instantiateMVars
  let args' ← args₁.mapM (fun (y : Bool × Expr) =>
      if y.1 then return (true, mkAppN (.fvar ad) #[g.appFn!, applInst, α, β, f, y.2])
      else traverseField n g.appFn! f α y.2)
  let gargs := args'.filterMap (fun y => if y.1 then some y.2 else none)
  let v ← mkFunCtor c (args₀.map (fun e => (false, e)) ++ args')
  let pureInst ← mkAppOptM ``Applicative.toPure #[none, applInst]
  let constr' ← mkAppOptM ``Pure.pure #[none, pureInst, none, v]
  let r ← gargs.foldlM
      (fun e garg => mkFunUnit garg >>= fun e' => mkAppM ``Seq.seq #[e, e']) constr'
  m.assign r
where
  /-- `mkFunCtor ctor [(true, (arg₁ : m type₁)), (false, (arg₂ : type₂)), (true, (arg₃ : m type₃)),
  (false, (arg₄ : type₄))]` makes `fun (x₁ : type₁) (x₃ : type₃) => ctor x₁ arg₂ x₃ arg₄`. -/
  mkFunCtor (c : Name) (args : List (Bool × Expr)) (fvars : Array Expr := #[])
      (aargs : Array Expr := #[]) : TermElabM Expr := do
    match args with
    | (true, x) :: xs =>
      let n ← mkFreshUserName `x
      let t ← inferType x
      withLocalDeclD n t.appArg! fun y => mkFunCtor c xs (fvars.push y) (aargs.push y)
    | (false, x) :: xs => mkFunCtor c xs fvars (aargs.push x)
    | [] => liftM <| mkAppOptM c (aargs.map some) >>= mkLambdaFVars fvars

/-- derive the `traverse` definition of a `Traversable` instance -/
def mkTraverse (type : Name) (m : MVarId) : TermElabM Unit := do
  let vars ← getFVarsNotImplementationDetails
  let levels ← getLevelNames
  let (#[_, applInst, α, β, f, x], m) ← m.introN 6 [`m, `applInst, `α, `β, `f, `x] | failure
  m.withContext do
    let xtype ← x.getType
    let target ← m.getType >>= instantiateMVars
    let motive ← mkLambdaFVars #[.fvar x] target
    let e ←
      mkCasesOnMatch type (levels.map Level.param) (vars.concat (.fvar α)) motive [] (.fvar x)
        fun ctor fields => do
          let m ← mkFreshExprSyntheticOpaqueMVar target
          let args := fields.map Expr.fvar
          let args₀ ← args.mapM fun a => do
            let b := xtype.occurs (← inferType a)
            return (b, a)
          traverseConstructor
            ctor type (.fvar applInst) (.fvar f) (.fvar α) (.fvar β)
            (vars.concat (.fvar β)) args₀ m.mvarId!
          instantiateMVars m
    m.assign e

/-- derive the `traverse` definition and declare `Traversable` using this. -/
def deriveTraversable (m : MVarId) : TermElabM Unit := do
  let levels ← getLevelNames
  let vars ← getFVarsNotImplementationDetails
  let .app (.const ``Traversable _) F ← m.getType >>= instantiateMVars | failure
  let some n := F.getAppFn.constName? | failure
  let d ← getConstInfo n
  let [m] ← run m <| evalTactic (← `(tactic| refine { traverse := @(?_) })) | failure
  let t ← m.getType >>= instantiateMVars
  let n' := .mkStr n "traverse"
  withDeclName n' <| withAuxDecl (.mkSimple "traverse") t n' fun ad => do
    let m' := (← mkFreshExprSyntheticOpaqueMVar t).mvarId!
    mkTraverse n m'
    let e ← instantiateMVars (mkMVar m')
    let e := e.replaceFVar ad (mkAppN (.const n' (levels.map Level.param)) vars.toArray)
    let e' ← mkLambdaFVars vars.toArray e
    let t' ← mkForallFVars vars.toArray t
    addPreDefinitions
      #[{ ref := .missing
          kind := .def
          levelParams := levels
          modifiers :=
            { isUnsafe := d.isUnsafe
              visibility := .protected }
          declName := n'
          type := t'
          value := e'
          termination := .none }] {}
  m.assign (mkAppN (mkConst n' (levels.map Level.param)) vars.toArray)

/-- The deriving handler for `Traversable`. -/
def traversableDeriveHandler : DerivingHandlerNoArgs :=
  higherOrderDeriveHandler ``Traversable deriveTraversable [functorDeriveHandler]

initialize registerDerivingHandler ``Traversable traversableDeriveHandler

/-- Simplify the goal `m` using `functor_norm`. -/
def simpFunctorGoal (m : MVarId) (s : Simp.Context) (simprocs : Simp.SimprocsArray := {})
    (discharge? : Option Simp.Discharge := none)
    (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[])
    (stats : Simp.Stats := {}) :
    MetaM (Option (Array FVarId × MVarId) × Simp.Stats) := do
  let some e ← getSimpExtension? `functor_norm | failure
  let s' ← e.getTheorems
  simpGoal m { s with simpTheorems := s.simpTheorems.push s' } simprocs discharge? simplifyTarget
    fvarIdsToSimp stats
/--
Run the following tactic:
```lean
intros _ .. x
dsimp only [Traversable.traverse, Functor.map]
induction x <;> (the simp tactic corresponding to s) <;> (tac)
```
-/
def traversableLawStarter (m : MVarId) (n : Name) (s : MetaM Simp.Context)
    (tac : Array FVarId → InductionSubgoal → MVarId → MetaM Unit) : MetaM Unit := do
  let s' ← [``Traversable.traverse, ``Functor.map].foldlM
      (fun s n => s.addDeclToUnfold n) ({} : SimpTheorems)
  let (fi, m) ← m.intros
  m.withContext do
    if let (some m, _) ← dsimpGoal m { simpTheorems := #[s'] } then
      let ma ← m.induction fi.back (mkRecName n)
      ma.forM fun is =>
        is.mvarId.withContext do
          if let (some (_, m), _) ← simpFunctorGoal is.mvarId (← s) then
            tac fi is m

/-- Prove the traversable laws and derive `LawfulTraversable`. -/
def deriveLawfulTraversable (m : MVarId) : TermElabM Unit := do
  let rules (l₁ : List (Name × Bool)) (l₂ : List (Name)) (b : Bool) : MetaM Simp.Context := do
    let mut s : SimpTheorems := {}
    s ← l₁.foldlM (fun s (n, b) => s.addConst n (inv := b)) s
    s ← l₂.foldlM (fun s n => s.addDeclToUnfold n) s
    if b then
      let hs ← getPropHyps
      s ← hs.foldlM (fun s f => f.getDecl >>= fun d => s.add (.fvar f) #[] d.toExpr) s
    pure <|
    { config := { failIfUnchanged := false, unfoldPartialApp := true },
      simpTheorems := #[s] }
  let .app (.app (.const ``LawfulTraversable _) F) _ ← m.getType >>= instantiateMVars | failure
  let some n := F.getAppFn.constName? | failure
  let [mit, mct, mtmi, mn] ← m.applyConst ``LawfulTraversable.mk | failure
  let defEqns : MetaM Simp.Context := rules [] [.mkStr n "map", .mkStr n "traverse"] true
  traversableLawStarter mit n defEqns fun _ _ m => m.refl
  traversableLawStarter mct n defEqns fun _ _ m => do
    if let (some (_, m), _) ← simpFunctorGoal m
        (← rules [] [.mkStr n "map", .mkStr n "traverse", ``Function.comp] true) then
      m.refl
  traversableLawStarter mtmi n defEqns fun _ _ m => do
    if let (some (_, m), _) ←
        simpGoal m (← rules [(``Traversable.traverse_eq_map_id', false)] [] false) then
    m.refl
  traversableLawStarter mn n defEqns fun _ _ m => do
    if let (some (_, m), _) ←
        simpGoal m (← rules [(``Traversable.naturality_pf, false)] [] false) then
    m.refl

/-- The deriving handler for `LawfulTraversable`. -/
def lawfulTraversableDeriveHandler : DerivingHandlerNoArgs :=
  higherOrderDeriveHandler ``LawfulTraversable deriveLawfulTraversable
    [traversableDeriveHandler, lawfulFunctorDeriveHandler] (fun n arg => mkAppOptM n #[arg, none])

initialize registerDerivingHandler ``LawfulTraversable lawfulTraversableDeriveHandler

end Mathlib.Deriving.Traversable
