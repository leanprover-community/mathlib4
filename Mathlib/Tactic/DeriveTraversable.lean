/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module control.traversable.derive
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Tactic.Basic
import Mathlib.Control.Traversable.Lemmas

/-!
## Automation to construct `traversable` instances
-/

namespace Mathlib.Deriving.Traversable

open Lean Meta Elab Term Command Tactic Match List Monad Functor

/-- similar to `nestedTraverse` but for `Functor` -/
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

/-- similar to `traverseConstructor` but for `Functor` -/
def mapConstructor (c n : Name) (ad : Expr) (f α β : Expr) (args₀ : List Expr)
    (args₁ : List (Bool × Expr)) (m : MVarId) : TermElabM Unit := do
  let g ← m.getType >>= instantiateMVars
  let args' ← args₁.mapM (fun (y : Bool × Expr) =>
      if y.1 then return mkAppN ad #[α, β, f, y.2]
      else mapField n g.appFn! f α β y.2)
  mkAppOptM c ((args₀ ++ args').map some).toArray >>= m.assign

/-- derive the `map` definition of a `Functor` -/
def mkMap (type : Name) (ad : Expr) (levels : List Name) (vars : List Expr) (m : MVarId) :
    TermElabM Unit := do
  let (#[α, β, f, x], m') ← m.introN 4 [`α, `β, `f, `x] | unreachable!
  m'.withContext do
    let et ← x.getType
    let .inductInfo cinfo ← getConstInfo type | failure
    let cinfos ← cinfo.ctors.mapM fun ctor => do
      let .ctorInfo cinfo ← getConstInfo ctor | failure
      return cinfo
    let mn ← Lean.mkAuxName (type ++ "map" ++ "match") 1
    let matchType ← mkArrow et (← m'.getType)
    let motive ← forallBoundedTelescope matchType (some 1) fun xs body => mkLambdaFVars xs body
    let lhss ← cinfos.mapM fun cinfo => do
      let .ctorInfo cinfo ← getConstInfo cinfo.name | failure
      let ls := levels.map Level.param
      let vars' := vars.concat (.fvar α)
      let ce := mkAppN (.const cinfo.name ls) vars'.toArray
      let ct ← inferType ce
      forallBoundedTelescope ct cinfo.numFields fun args _ => do
        let fvarDecls ← args.toList.mapM fun arg => getFVarLocalDecl arg
        let fields := args.toList.map fun arg => Pattern.var arg.fvarId!
        let patterns := [Pattern.ctor cinfo.name ls vars' fields]
        return { ref := .missing
                 fvarDecls
                 patterns }
    let mres ← Term.mkMatcher
      { matcherName := mn
        matchType
        discrInfos := #[{}]
        lhss }
    mres.addMatcher
    let r := mkApp2 mres.matcher motive (.fvar x)
    let ms' ← m'.apply r
    let ms' := ms'.zip cinfos
    ms'.forM fun (m', cinfo) => do
      if cinfo.numFields = 0 then
        let (_, m') ← m'.intro1
        m'.withContext do
          mapConstructor
            cinfo.name type ad (.fvar f) (.fvar α) (.fvar β) (vars.concat (.fvar β)) [] m'
      else
        let (args, m') ← m'.introN cinfo.numFields
        m'.withContext do
          let args := args.toList.map Expr.fvar
          let args₀ ← args.mapM fun a => do
            let b ← et.occurs <$> inferType a
            return (b, a)
          mapConstructor
            cinfo.name type ad (.fvar f) (.fvar α) (.fvar β) (vars.concat (.fvar β)) args₀ m'

def deriveFunctor (levels : List Name) (vars : List Expr) (m : MVarId) : TermElabM Unit := do
  let .app (.const ``Functor _) F ← m.getType >>= instantiateMVars | failure
  let some n := F.getAppFn.constName? | failure
  let d ← getConstInfo n
  let [m] ← run m <| evalTactic (← `(tactic| refine { map := @(?_) })) | failure
  let t ← m.getType >>= instantiateMVars
  let n' := n ++ "map"
  withAuxDecl "map" t n' fun ad => do
    let m' := (← mkFreshExprSyntheticOpaqueMVar t).mvarId!
    mkMap n ad levels vars m'
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
          value := e' }] {}
  m.assign (mkAppN (mkConst n' (levels.map Level.param)) vars.toArray)

def mkOneInstance (n cls : Name) (tac : List Name → List Expr → MVarId → TermElabM Unit)
    (mkInst : Name → Expr → TermElabM Expr := fun n arg => mkAppM n #[arg]) : TermElabM Unit := do
  let .inductInfo decl ← getConstInfo n |
    throwError m!"failed to derive '{cls}', '{n}' is not an inductive type"
  let clsDecl ← getConstInfo cls
  let ls := decl.levelParams.map Level.param
  -- incrementally build up target expression `(hp : p) → [cls hp] → ... cls (n.{ls} hp ...)`
  -- where `p ...` are the inductive parameter types of `n`
  let tgt := Lean.mkConst n ls
  forallTelescope decl.type fun params _ => do
    let params := params.pop
    let tgt := mkAppN tgt params
    let tgt ← mkInst cls tgt
    let tgt ← params.zipWithIndex.foldrM (fun (param, i) tgt => do
      -- add typeclass hypothesis for each inductive parameter
      let tgt ← (do
        guard (i < decl.numParams)
        let paramCls ← mkAppM cls #[param]
        return mkForall `a .instImplicit paramCls tgt) <|> return tgt
      mkForallFVars #[param] tgt) tgt
    (discard <| liftM (synthInstance tgt)) <|> do
      let m := (← mkFreshExprSyntheticOpaqueMVar tgt).mvarId!
      let (fvars, m') ← m.intros
      tac decl.levelParams (fvars.toList.map Expr.fvar) m'
      let val ← instantiateMVars (mkMVar m)
      let isUnsafe := decl.isUnsafe || clsDecl.isUnsafe
      let result ← m'.withContext <| do
        let type ← m'.getType >>= instantiateMVars
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
      let instN ← liftMacroM <| mkUnusedBaseName <| Name.mkSimple ("inst" ++ result)
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
            value := val }] {}

def higherOrderDeriveHandler (cls : Name) (tac : List Name → List Expr → MVarId → TermElabM Unit)
    (deps : List DerivingHandlerNoArgs := [])
    (mkInst : Name → Expr → TermElabM Expr := fun n arg => mkAppM n #[arg]) :
    DerivingHandlerNoArgs := fun a => do
  let #[n] := a | return false -- mutually inductive types are not supported yet
  deps.forM fun f : DerivingHandlerNoArgs => discard <| f a
  liftTermElabM <| mkOneInstance n cls tac mkInst
  return true

def functorDeriveHandler : DerivingHandlerNoArgs :=
  higherOrderDeriveHandler ``Functor deriveFunctor []

initialize registerDerivingHandler ``Functor functorDeriveHandler

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
  liftM <| (Prod.snd <$> mcn.introN 2) >>= MVarId.refl
  let (#[_, x], mim) ← mim.introN 2 | failure
  let (some mim, _) ← dsimpGoal mim (← rules [] [``Functor.map] false) | failure
  let xs ← mim.induction x (mkRecName n)
  xs.forM fun ⟨mim, _, _⟩ =>
    mim.withContext do
      if let (some (_, mim), _) ←
          simpGoal mim (← rules [(``Functor.map_id, false)] [n ++ "map"] true) then
        mim.refl
  let (#[_, _, _, _, _, x], mcm) ← mcm.introN 6 | failure
  let (some mcm, _) ← dsimpGoal mcm (← rules [] [``Functor.map] false) | failure
  let xs ← mcm.induction x (mkRecName n)
  xs.forM fun ⟨mcm, _, _⟩ =>
    mcm.withContext do
      if let (some (_, mcm), _) ←
          simpGoal mcm (← rules [(``Functor.map_comp_map, true)] [n ++ "map"] true) then
        mcm.refl

def lawfulFunctorDeriveHandler : DerivingHandlerNoArgs :=
  higherOrderDeriveHandler ``LawfulFunctor (fun _ _ => deriveLawfulFunctor) [functorDeriveHandler]
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
``traverseField `foo f `α `(x : List α)`` synthesizes
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
``traverseConstructor `foo1 `foo ad applInst f `α `β [`(x : List α), `(y : ℕ)]``
synthesizes `foo1 <$> traverse f x <*> pure y.` -/
def traverseConstructor (c n : Name) (ad : Expr) (applInst f α β : Expr) (args₀ : List Expr)
    (args₁ : List (Bool × Expr)) (m : MVarId) : TermElabM Unit := do
  let g ← m.getType >>= instantiateMVars
  let args' ← args₁.mapM (fun (y : Bool × Expr) =>
      if y.1 then return (true, mkAppN ad #[g.appFn!, applInst, α, β, f, y.2])
      else traverseField n g.appFn! f α y.2)
  let gargs := args'.filterMap (fun y => if y.1 then some y.2 else none)
  let v ← mkFunCtor c (args₀.map (fun e => (false, e)) ++ args') #[] #[]
  let pureInst ← mkAppOptM ``Applicative.toPure #[none, applInst]
  let constr' ← mkAppOptM ``Pure.pure #[none, pureInst, none, v]
  let r ← gargs.foldlM
      (fun e garg => mkAppM ``Seq.seq #[e, .lam `_ (.const ``Unit []) garg .default]) constr'
  m.assign r
where
  mkFunCtor (c : Name) (args : List (Bool × Expr)) (fvars : Array Expr) (aargs : Array Expr) :
      TermElabM Expr := do
    match args with
    | (true, x) :: xs =>
      let n ← mkFreshUserName `x
      let t ← inferType x
      withLocalDecl n .default t.appArg! fun y => mkFunCtor c xs (fvars.push y) (aargs.push y)
    | (false, x) :: xs => mkFunCtor c xs fvars (aargs.push x)
    | [] => liftM <| mkAppOptM c (aargs.map some) >>= mkLambdaFVars fvars

/-- derive the `traverse` definition of a `Traversable` instance -/
def mkTraverse (type : Name) (ad : Expr) (levels : List Name) (vars : List Expr) (m : MVarId) :
    TermElabM Unit := do
  let (#[_, applInst, α, β, f, x], m') ← m.introN 6 [`m, `applInst, `α, `β, `f, `x] | unreachable!
  m'.withContext do
    let et ← x.getType
    let .inductInfo cinfo ← getConstInfo type | failure
    let cinfos ← cinfo.ctors.mapM fun ctor => do
      let .ctorInfo cinfo ← getConstInfo ctor | failure
      return cinfo
    let mn ← Lean.mkAuxName (type ++ "traverse" ++ "match") 1
    let matchType ← mkArrow et (← m'.getType)
    let motive ← forallBoundedTelescope matchType (some 1) fun xs body => mkLambdaFVars xs body
    let lhss ← cinfos.mapM fun cinfo => do
      let .ctorInfo cinfo ← getConstInfo cinfo.name | failure
      let ls := levels.map Level.param
      let vars' := vars.concat (.fvar α)
      let ce := mkAppN (.const cinfo.name ls) vars'.toArray
      let ct ← inferType ce
      forallBoundedTelescope ct cinfo.numFields fun args _ => do
        let fvarDecls ← args.toList.mapM fun arg => getFVarLocalDecl arg
        let fields := args.toList.map fun arg => Pattern.var arg.fvarId!
        let patterns := [Pattern.ctor cinfo.name ls vars' fields]
        return { ref := .missing
                 fvarDecls
                 patterns }
    let mres ← Term.mkMatcher
      { matcherName := mn
        matchType
        discrInfos := #[{}]
        lhss }
    mres.addMatcher
    let r := mkApp2 mres.matcher motive (.fvar x)
    let ms' ← m'.apply r
    let ms' := ms'.zip cinfos
    ms'.forM fun (m', cinfo) => do
      if cinfo.numFields = 0 then
        let (_, m') ← m'.intro1
        m'.withContext do
          traverseConstructor
            cinfo.name type ad (.fvar applInst) (.fvar f) (.fvar α) (.fvar β)
            (vars.concat (.fvar β)) [] m'
      else
        let (args, m') ← m'.introN cinfo.numFields
        m'.withContext do
          let args := args.toList.map Expr.fvar
          let args₀ ← args.mapM fun a => do
            let b ← et.occurs <$> inferType a
            return (b, a)
          traverseConstructor
            cinfo.name type ad (.fvar applInst) (.fvar f) (.fvar α) (.fvar β)
            (vars.concat (.fvar β)) args₀ m'

def deriveTraversable (levels : List Name) (vars : List Expr) (m : MVarId) : TermElabM Unit := do
  let .app (.const ``Traversable _) F ← m.getType >>= instantiateMVars | failure
  let some n := F.getAppFn.constName? | failure
  let d ← getConstInfo n
  let [m] ← run m <| evalTactic (← `(tactic| refine { traverse := @(?_) })) | failure
  let t ← m.getType >>= instantiateMVars
  let n' := n ++ "traverse"
  withAuxDecl "traverse" t n' fun ad => do
    let m' := (← mkFreshExprSyntheticOpaqueMVar t).mvarId!
    mkTraverse n ad levels vars m'
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
          value := e' }] {}
  m.assign (mkAppN (mkConst n' (levels.map Level.param)) vars.toArray)

def traversableDeriveHandler : DerivingHandlerNoArgs :=
  higherOrderDeriveHandler ``Traversable deriveTraversable [functorDeriveHandler]

initialize registerDerivingHandler ``Traversable traversableDeriveHandler

def simpFunctorGoal (m : MVarId) (s : Simp.Context) :
    MetaM (Option (Array FVarId × MVarId) × Simp.UsedSimps) := do
  let some e ← getSimpExtension? `functor_norm | failure
  let s' ← e.getTheorems
  simpGoal m { s with simpTheorems := s.simpTheorems.push s' }

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

def deriveLawfulTraversable (m : MVarId) : TermElabM Unit := do
  let rules (l₁ : List (Name × Bool)) (l₂ : List (Name)) (b : Bool) : MetaM Simp.Context := do
    let mut s : SimpTheorems := {}
    s ← l₁.foldlM (fun s (n, b) => s.addConst n (inv := b)) s
    s ← l₂.foldlM (fun s n => s.addDeclToUnfold n) s
    if b then
      let hs ← getPropHyps
      s ← hs.foldlM (fun s f => f.getDecl >>= fun d => s.add (.fvar f) #[] d.toExpr) s
    return { simpTheorems := #[s] }
  let .app (.app (.const ``LawfulTraversable _) F) _ ← m.getType >>= instantiateMVars | failure
  let some n := F.getAppFn.constName? | failure
  let [mit, mct, mtmi, mn] ← m.applyConst ``LawfulTraversable.mk | failure
  let defEqns : MetaM Simp.Context := rules [] [n ++ "map", n ++ "traverse"] true
  traversableLawStarter mit n defEqns fun _ _ m => m.refl
  traversableLawStarter mct n defEqns fun _ _ m => do
    if let (some (_, m), _) ←
        simpFunctorGoal m (← rules [] [n ++ "map", n ++ "traverse", ``Function.comp] true) then
    m.refl
  traversableLawStarter mtmi n defEqns fun _ _ m => do
    if let (some (_, m), _) ←
        simpGoal m (← rules [(``Traversable.traverse_eq_map_id', false)] [] false) then
    m.refl
  traversableLawStarter mn n defEqns fun _ _ m => do
    if let (some (_, m), _) ←
        simpGoal m (← rules [(``Traversable.naturality_pf, false)] [] false) then
    m.refl

def lawfulTraversableDeriveHandler : DerivingHandlerNoArgs :=
  higherOrderDeriveHandler ``LawfulTraversable (fun _ _ => deriveLawfulTraversable)
    [traversableDeriveHandler, lawfulFunctorDeriveHandler] (fun n arg => mkAppOptM n #[arg, none])

initialize registerDerivingHandler ``LawfulTraversable lawfulTraversableDeriveHandler

end Mathlib.Deriving.Traversable
