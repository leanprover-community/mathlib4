import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.Util.AddRelatedDecl
import Mathlib.Lean.Meta.Simp
import Lean

open Lean Elab Tactic Term Qq

lemma RingHom.Finite.Algebraize (A B : Type*) [CommRing A] [CommRing B] {f : A →+* B}
    (hf : f.Finite) : letI : Algebra A B := f.toAlgebra; Module.Finite A B :=
  hf

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

def addFiniteTypeInstance (t : Expr) : TacticM Unit := withMainContext do
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
  let ft ← mkFreshExprMVarQ q(RingHom.FiniteType $f)
  ft.mvarId!.assumption
  let _algInstAB ← synthInstanceQ q(Algebra $A $B)
  let _ ←
    try let _ ← assertDefEqQ f q(algebraMap $A $B)
    catch e => throwError e.toMessageData
  try
    let _ ← synthInstanceQ q(Algebra.FiniteType $A $B)
  catch _ => liftMetaTactic fun mvarid => do
    let nm ← mkFreshUserName `ftInst
    let mvar ← mvarid.define nm q(Algebra.FiniteType $A $B) q($ft)
    let (_, mvar) ← mvar.intro1P
    return [mvar]

-- q(.app nm _)
-- name -> ident

def toRingHomiveTypes : Array Expr := #[q(RingHom.Finite), q(RingHom.FiniteType)]
  -- #[(``RingHom.Finite, ``Module.Finite), (``RingHom.FiniteType, ``Algebra.FiniteType)]

def addInstances (t : Expr) : TacticM Unit := withMainContext do
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
  let ft ← mkFreshExprMVarQ q(RingHom.FiniteType $f)
  ft.mvarId!.assumption
  let _algInstAB ← synthInstanceQ q(Algebra $A $B)
  let _ ←
    try let _ ← assertDefEqQ f q(algebraMap $A $B)
    catch e => throwError e.toMessageData
  try
    let _ ← synthInstanceQ q(Algebra.FiniteType $A $B)
  catch _ => liftMetaTactic fun mvarid => do
    let nm ← mkFreshUserName `ftInst
    let mvar ← mvarid.define nm q(Algebra.FiniteType $A $B) q($ft)
    let (_, mvar) ← mvar.intro1P
    return [mvar]

def addInstance (oldname : Name) (args : Array Expr) (decl : LocalDecl) : TacticM Unit :=
  withMainContext do
    logInfo "hi"
    liftMetaTactic fun mvarid => do
      let nm ← mkFreshUserName `ftInst
      -- let env ← getEnv
      -- let some c := env.find? newname | throwError "Error"
      -- let u ← Meta.mkFreshLevelMVarsFor c
      let .const _ us := decl.type.getAppFn | throwError "Error"
      let f := Meta.mkAppM (.const () us) args
      let mvar ← mvarid.define nm f decl.toExpr
      let (_, mvar) ← mvar.intro1P
      return [mvar]

#check mkAppN

-- -- WIP on searching through local context for types in a given array
def searchContext : TacticM Unit := withMainContext do
  let ctx ← MonadLCtx.getLCtx
  ctx.forM fun decl => do
    if decl.isImplementationDetail then
      return
    let declType := decl.type
    -- let declType ← Lean.Meta.inferType declExpr
    for i in toRingHomiveTypes do
      let (nm, args) := declType.getAppFnArgs
      if nm == i then
        logInfo m!"declType: {declType}"
        addInstance i args decl

      -- if ← Meta.isDefEq i declType then
      --   -- do something
      --   return
    return

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

    for f in t do
      let f ← Term.elabTerm f none
      try addFiniteTypeInstance f
      catch _ => continue

example {A B C D : Type*}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B)
    --(g : B →+* C) (h : C →+* D)
    (hf : f.FiniteType) : --(hhg : (h.comp g).FiniteType)
    --(hh : (h.comp g).comp f |>.FiniteType) :
    True := by
  algebraize f

  --g h (g.comp f) (h.comp g) (h.comp (g.comp f))
  trivial

/-
Ideas to do:
- Search through local context to match types in given array toRingHomiveTypes
-- (I've started on this as addInstanceFromContext)
- Define toRingHomiveTypes through some attribute thing
- Try to add alghoms

-/
