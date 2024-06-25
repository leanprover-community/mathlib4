import Mathlib.RingTheory.RingHom.FiniteType
import Lean

open Lean Elab Tactic Term

syntax "algebraize" (ppSpace colGt term:max)* : tactic

example {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra B C := g.toAlgebra
    letI : Algebra A C := (g.comp f).toAlgebra
    IsScalarTower A B C := by
    letI : Algebra A B := f.toAlgebra
    letI : Algebra B C := g.toAlgebra
    letI : Algebra A C := (g.comp f).toAlgebra
    exact IsScalarTower.of_algebraMap_eq (congrFun rfl)

open Qq
elab_rules : tactic
  | `(tactic| algebraize $[$t:term]*) => do
    for f in t do
      let u ← Meta.mkFreshLevelMVar
      let v ← Meta.mkFreshLevelMVar
      let A : Q(Type u) ← mkFreshExprMVarQ q(Type u)
      let B : Q(Type v) ← mkFreshExprMVarQ q(Type v)
      let instA : Q(CommRing $A) ← mkFreshExprMVarQ q(CommRing $A)
      let instB : Q(CommRing $B) ← mkFreshExprMVarQ q(CommRing $B)
      let t ← elabTermEnsuringTypeQ f q($A →+* $B)
      let algTp : Q(Type (max u v)) := q(Algebra $A $B)
      let algVal : Q(Algebra $A $B) := q(RingHom.toAlgebra $t)
      liftMetaTactic fun mvarid => do
        let newMVar ← mvarid.define .anonymous algTp algVal
        let (_, newMVar) ← newMVar.intro1P
        return [newMVar]

example {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    True := by
  algebraize f g
  trivial
