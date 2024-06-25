import Mathlib.RingTheory.RingHom.FiniteType
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
  let _algInstAB : Q(Algebra $A $B) ← synthInstanceQ q(Algebra $A $B)
  let _algInstBC : Q(Algebra $B $C) ← synthInstanceQ q(Algebra $B $C)
  let _algInstAC : Q(Algebra $A $C) ← synthInstanceQ q(Algebra $A $C)
  let h ← mkFreshExprMVarQ q(algebraMap $A $C = RingHom.comp (algebraMap $B $C) (algebraMap $A $B))
  h.mvarId!.refl
  try
    let _ ← synthInstanceQ q(IsScalarTower $A $B $C)
  catch _ => liftMetaTactic fun mvarid => do
    let nm ← mkFreshUserName `scalarTowerInst
    let mvar ← mvarid.define nm q(IsScalarTower $A $B $C) q(IsScalarTower.of_algebraMap_eq' $h)
    let (_, mvar) ← mvar.intro1P
    return [mvar]

syntax "algebraize" (ppSpace colGt term:max)* : tactic

elab_rules : tactic
  | `(tactic| algebraize $[$t:term]*) => do
    for f in t do
      let f ← Term.elabTerm f none
      try withMainContext <| addAlgebraInstanceFromRingHom f
      catch _ => continue

    for f in t do
      let f ← Term.elabTerm f none
      try withMainContext <| addIsScalarTowerInstanceFromRingHomComp f
      catch _ => continue

example {A B C D : Type*}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* C) (h : C →+* D) :
    True := by
  algebraize f g h (g.comp f) (h.comp g) (h.comp (g.comp f)) ((h.comp g).comp f)
  trivial
