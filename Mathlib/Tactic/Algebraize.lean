import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.Util.AddRelatedDecl
import Mathlib.Lean.Meta.Simp
import Mathlib.Tactic.AlgebraizeAttr
import Lean

import Mathlib.RingTheory.IntegralClosure

open Lean Elab Tactic Term Qq

#check Attr.algebraizeAttr.getDecls

alias RingHom.Algebraize := RingHom.toAlgebra

@[algebraize]
lemma RingHom.Finite.Algebraize {A B : Type*} [CommRing A] [CommRing B] {f : A →+* B}
    (hf : f.Finite) : letI : Algebra A B := f.toAlgebra; Module.Finite A B :=
  hf

@[algebraize]
lemma RingHom.FiniteType.Algebraize {A B : Type*} [CommRing A] [CommRing B] {f : A →+* B}
    (hf : f.FiniteType) : letI : Algebra A B := f.toAlgebra; Algebra.FiniteType A B :=
  hf

@[algebraize]
lemma RingHom.IsIntegral.Algebraize {A B : Type*} [CommRing A] [CommRing B] {f : A →+* B}
    (hf : f.IsIntegral) : letI : Algebra A B := f.toAlgebra; Algebra.IsIntegral A B :=
      letI : Algebra A B := f.toAlgebra
      {isIntegral := hf}


namespace Mathlib.Tactic


def addAlgebraInstanceFromRingHom (t : Expr) : TacticM Unit := withMainContext do
  let u ← Meta.mkFreshLevelMVar
  let v ← Meta.mkFreshLevelMVar
  let A ← mkFreshExprMVarQ q(Type u)
  let B ← mkFreshExprMVarQ q(Type v)
  let _instA ← mkFreshExprMVarQ q(CommRing $A)
  let _instB ← mkFreshExprMVarQ q(CommRing $B)
  let f ← mkFreshExprMVarQ q($A →+* $B)
  let _ ←
    try let _pf ← assertDefEqQ t f
    catch e => throwError e.toMessageData
  try
    let _ ← synthInstanceQ q(Algebra $A $B)
  catch _ => liftMetaTactic fun mvarid => do
    let nm ← mkFreshUserName `algInst
    let mvar ← mvarid.define nm q(Algebra $A $B) q(RingHom.toAlgebra $f)
    let (_, mvar) ← mvar.intro1P
    return [mvar]

def addIsScalarTowerInstanceFromRingHomComp (t : Expr) : TacticM Unit := withMainContext do
  let u ← Meta.mkFreshLevelMVar
  let v ← Meta.mkFreshLevelMVar
  let w ← Meta.mkFreshLevelMVar
  let A : Q(Type u) ← mkFreshExprMVarQ q(Type u)
  let B : Q(Type v) ← mkFreshExprMVarQ q(Type v)
  let C : Q(Type w) ← mkFreshExprMVarQ q(Type w)
  let _instA : Q(CommRing $A) ← mkFreshExprMVarQ q(CommRing $A)
  let _instB : Q(CommRing $B) ← mkFreshExprMVarQ q(CommRing $B)
  let _instC : Q(CommRing $C) ← mkFreshExprMVarQ q(CommRing $C)
  let fst : Q($A →+* $B) ← mkFreshExprMVarQ q($A →+* $B)
  let snd : Q($B →+* $C) ← mkFreshExprMVarQ q($B →+* $C)
  let _ ←
    try let _pf ← assertDefEqQ t q(RingHom.comp $snd $fst)
    catch e => throwError e.toMessageData
  let _algInstAB ← synthInstanceQ q(Algebra $A $B)
  let _algInstBC ← synthInstanceQ q(Algebra $B $C)
  let _algInstAC ← synthInstanceQ q(Algebra $A $C)
  let h ← mkFreshExprMVarQ q(algebraMap $A $C = RingHom.comp (algebraMap $B $C) (algebraMap $A $B))
  h.mvarId!.refl
  try
    let _ ← synthInstanceQ q(IsScalarTower $A $B $C)
  catch _ => liftMetaTactic fun mvarid => do
    let nm ← mkFreshUserName `scalarTowerInst
    let mvar ← mvarid.define nm q(IsScalarTower $A $B $C) q(IsScalarTower.of_algebraMap_eq' $h)
    let (_, mvar) ← mvar.intro1P
    return [mvar]

-- def addFiniteTypeInstance (t : Expr) : TacticM Unit := withMainContext do
--   let u ← Meta.mkFreshLevelMVar
--   let v ← Meta.mkFreshLevelMVar
--   let A ← mkFreshExprMVarQ q(Type u)
--   let B ← mkFreshExprMVarQ q(Type v)
--   let _instA ← mkFreshExprMVarQ q(CommRing $A)
--   let _instB ← mkFreshExprMVarQ q(CommRing $B)
--   let f ← mkFreshExprMVarQ q($A →+* $B)
--   let _ ←
--     try let _pf ← assertDefEqQ t f
--     catch e => throwError e.toMessageData
--   let ft ← mkFreshExprMVarQ q(RingHom.FiniteType $f)
--   ft.mvarId!.assumption
--   let _algInstAB ← synthInstanceQ q(Algebra $A $B)
--   let _ ←
--     try let _ ← assertDefEqQ f q(algebraMap $A $B)
--     catch e => throwError e.toMessageData
--   try
--     let _ ← synthInstanceQ q(Algebra.FiniteType $A $B)
--   catch _ => liftMetaTactic fun mvarid => do
--     let nm ← mkFreshUserName `ftInst
--     let mvar ← mvarid.define nm q(Algebra.FiniteType $A $B) q($ft)
--     let (_, mvar) ← mvar.intro1P
--     return [mvar]

-- #check matchExpr :(

-- def addInstance (oldname : Name) (args : Array Expr) (decl : LocalDecl) : TacticM Unit :=
--   withMainContext do
--     logInfo "hi"
--     liftMetaTactic fun mvarid => do
--       let nm ← mkFreshUserName `ftInst
--       -- let env ← getEnv
--       -- let some c := env.find? newname | throwError "Error"
--       -- let u ← Meta.mkFreshLevelMVarsFor c
--       let .const _ us := decl.type.getAppFn | throwError "Error"
--       let f := Meta.mkAppM (.const () us) args
--       let mvar ← mvarid.define nm f decl.toExpr
--       let (_, mvar) ← mvar.intro1P
--       return [mvar]

-- #check

-- -- WIP on searching through local context for types in a given array
def searchContext (t : Array (TSyntax `term)) : TacticM Unit := withMainContext do
  let t' ← t.mapM fun i => Term.elabTerm i none
  let ctx ← MonadLCtx.getLCtx
  ctx.forM fun decl => do
    if decl.isImplementationDetail then
      return
    let declType := decl.type
    -- let declType ← Lean.Meta.inferType declExpr
    let env ← getEnv

    for i in Attr.algebraizeAttr.getDecls env do
      let (nm, args) := declType.getAppFnArgs
      let some i' := i.eraseSuffix? `Algebraize | throwError "Error"
      if nm != i' then
        continue
      let f := args[args.size - 1]!
      let mut happy := false
      for j in t' do
        if (← Meta.isDefEq j f) then
          happy := true
          break
      if ¬happy then
        continue
      let h : Ident := mkIdent i
      let hf := mkIdent decl.userName
      let sn ← `(term| $h:ident $hf:ident)
      let m ← Term.elabTerm sn none

      liftMetaTactic fun mvarid => do
        let nm ← mkFreshUserName `ftInst
        -- let env ← getEnv
        -- let some c := env.find? newname | throwError "Error"
        -- let u ← Meta.mkFreshLevelMVarsFor c
        let .const _ us := decl.type.getAppFn | throwError "Error"
        --let f := Meta.mkAppM (.const () us) args
        let h ← mkFreshUserName `AlgebraizeInst
        let (_, mvar) ← mvarid.note h m
        -- let (_, mvar) ← mvar.2.intro1P
        return [mvar]

    -- return

syntax "algebraize" (ppSpace colGt term:max)* : tactic

elab_rules : tactic
  | `(tactic| algebraize $[$t:term]*) => do
    for f in t do
      let f ← Term.elabTerm f none
      addAlgebraInstanceFromRingHom f

    for f in t do
      let f ← Term.elabTerm f none
      try addIsScalarTowerInstanceFromRingHomComp f
      catch _ => continue

    searchContext t


    -- for f in t do
    --   let f ← Term.elabTerm f none
    --   try addFiniteTypeInstance f
    --   catch _ => continue

example {A B C D : Type*}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B)
    (g : B →+* C) (h : C →+* D)
    (hf : f.FiniteType) (hf' : f.Finite) (hhg : (h.comp g).FiniteType)
    (hh : (h.comp g).comp f |>.FiniteType)
    (hg : g.IsIntegral) :
    True := by
  algebraize f g (h.comp g) (h.comp (g.comp f))


  --g h (g.comp f) (h.comp g) (h.comp (g.comp f))
  trivial

/-
Ideas to do:
- Search through local context to match types in given array toRingHomiveTypes
-- (I've started on this as addInstanceFromContext)
- Define toRingHomiveTypes through some attribute thing
- Try to add alghoms

-/
