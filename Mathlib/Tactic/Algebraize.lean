import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.Util.AddRelatedDecl
import Mathlib.Lean.Meta.Simp
import Lean

open Lean Elab Tactic Term Qq

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

def toRingHomiveTypes : Array Expr := sorry

-- WIP on searching through local context for types in a given array
def addInstanceFromContext : TacticM Unit := withMainContext do
  let ctx ← MonadLCtx.getLCtx
  ctx.forM fun decl => do
    if decl.isImplementationDetail then
      return
    let declExpr := decl.toExpr
    let declType ← Lean.Meta.inferType declExpr
    for i in toRingHomiveTypes do
      if ← Meta.isDefEq i declType then
        return
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
    (f : A →+* B) (g : B →+* C) (h : C →+* D) (hf : f.FiniteType) (hhg : (h.comp g).FiniteType)
    (hh : (h.comp g).comp f |>.FiniteType) :
    True := by
  algebraize f g h (g.comp f) (h.comp g) (h.comp (g.comp f))
  trivial

/-
Ideas to do:
- Search through local context to match types in given array toRingHomiveTypes
-- (I've started on this as addInstanceFromContext)
- Define toRingHomiveTypes through some attribute thing
- Try to add alghoms

-/
