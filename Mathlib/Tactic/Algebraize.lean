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
    exact IsScalarTower.of_algebraMap_eq' rfl

#check rfl
#check RingHom.comp
open Qq
elab_rules : tactic
  | `(tactic| algebraize $[$t:term]*) => withMainContext do
    for f in t do
      let u ← Meta.mkFreshLevelMVar
      let v ← Meta.mkFreshLevelMVar
      let A : Q(Type u) ← mkFreshExprMVarQ q(Type u)
      let B : Q(Type v) ← mkFreshExprMVarQ q(Type v)
      let _instA : Q(CommRing $A) ← mkFreshExprMVarQ q(CommRing $A)
      let _instB : Q(CommRing $B) ← mkFreshExprMVarQ q(CommRing $B)
      let t ← elabTermEnsuringTypeQ f q($A →+* $B)

      let algTp : Q(Type (max u v)) := q(Algebra $A $B)
      let algVal : Q(Algebra $A $B) := q(RingHom.toAlgebra $t)
      --let proofTp : Q(Prop) := q(algebraMap $A $B = $t)
      --let s : Q($A →+* $B) := q(algebraMap $A $B)
      --let e : Q($A →+* $B) := q($t)
      --let proofVal : Q($s = $e) := q(rfl)
      liftMetaTactic fun mvarid => do
        let nm ← mkFreshUserName `algInst
        let newMVar ← mvarid.define nm algTp algVal
        let (_fvarid, newMVar) ← newMVar.intro1P
        return [newMVar]

    withMainContext do
    for f in t do
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
      let t ← elabTermEnsuringTypeQ f q($A →+* $C)
      try let _h ← assertDefEqQ t q(RingHom.comp $snd $fst)
      catch _ => continue
      let _algInstAB : Q(Algebra $A $B) ← synthInstanceQ q(Algebra $A $B)
      let _algInstBC : Q(Algebra $B $C) ← synthInstanceQ q(Algebra $B $C)
      let _algInstAC : Q(Algebra $A $C) ← synthInstanceQ q(Algebra $A $C)
      let h ← mkFreshExprMVarQ q(algebraMap $A $C = RingHom.comp (algebraMap $B $C) (algebraMap $A $B))
      let scalarVal : Q(IsScalarTower $A $B $C) := q(IsScalarTower.of_algebraMap_eq' $h)
      let scalarTp := q(IsScalarTower $A $B $C)
      Expr.mvarId! h |>.refl
      liftMetaTactic fun mvarid => do
        let nm ← mkFreshUserName `scalarTowerInst
        let newMVar ← mvarid.define nm scalarTp scalarVal
        let (_, newMVar) ← newMVar.intro1P
        return [newMVar]

      /-
      for a in rings do
        logInfo a
      for A in rings do for B in rings do for C in rings do
        try
          let u ← Meta.mkFreshLevelMVar
          let v ← Meta.mkFreshLevelMVar
          let w ← Meta.mkFreshLevelMVar
          have AA : Q(Type u) := A
          have BB : Q(Type v) := B
          have CC : Q(Type w) := C
          let instA : Q(CommRing $AA) ← synthInstanceQ q(CommRing $AA)
          let instB : Q(CommRing $BB) ← synthInstanceQ q(CommRing $BB)
          let instC : Q(CommRing $CC) ← synthInstanceQ q(CommRing $CC)
          let algAB : Q(Algebra $AA $BB) ← synthInstanceQ q(Algebra $AA $BB)
          let algBC : Q(Algebra $BB $CC) ← synthInstanceQ q(Algebra $BB $CC)
          let algAC : Q(Algebra $AA $CC) ← synthInstanceQ q(Algebra $AA $CC)
          let towerTp := q(IsScalarTower $AA $BB $CC)
          let h := (← assertDefEqQ q(algebraMap $AA $CC) q((algebraMap $BB $CC).comp (algebraMap $AA $BB))).down
          let towerVal : Q(IsScalarTower $AA $BB $CC) := q(IsScalarTower.of_algebraMap_eq' $h)
          liftMetaTactic fun mvarid => do
            let nm ← mkFreshUserName `scalarTowerInst
            let newMVar ← mvarid.define nm towerTp towerVal

            let (_, newMVar) ← newMVar.intro1P
            return [newMVar]

        catch _ => continue
      -/
      --liftMetaTactic fun mvarid => do
      --  let nm ← mkFreshUserName `algProof
      --  let newMVar ← mvarid.define nm proofTp proofVal
      --  let (_, newMVar) ← newMVar.intro1P
      --  return [newMVar]


variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
def ff : ℚ →+* ℚ := sorry

example {A B C D : Type*}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* C) (h : C →+* D) :
    True := by
  algebraize f g h (g.comp f) (h.comp g) (h.comp (g.comp f)) ((h.comp g).comp f)
  trivial
