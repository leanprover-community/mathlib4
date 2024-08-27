import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.Util.AddRelatedDecl
import Mathlib.Lean.Meta.Simp
import Mathlib.Tactic.AlgebraizeAttr
import Lean

import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open Lean Elab Tactic Term Qq Meta

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

/-- TODO

The reason we demand both `f` and `ft` as arguments (even though `f` can be inferred from `ft`) is
because before calling this function in `algebraize`, we have already computed `ft`

-/
def addAlgebraInstanceFromRingHom (f ft : Expr) : TacticM Unit := withMainContext do
  let (_, l) := ft.getAppFnArgs
  let alg ← mkAppOptM `Algebra #[l[0]!, l[1]!, none, none]
  try let _ ← synthInstance alg
  catch _ => liftMetaTactic fun mvarid => do
    let nm ← mkFreshUserName `algInst
    let mvar ← mvarid.define nm alg (← mkAppM `RingHom.toAlgebra #[f])
    let (_, mvar) ← mvar.intro1P
    return [mvar]

-- OLD Qq VERSION:
-- def addAlgebraInstanceFromRingHom (t : Expr) : TacticM Unit := withMainContext do
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
--   try
--     let _ ← synthInstanceQ q(Algebra $A $B)
--   catch _ => liftMetaTactic fun mvarid => do
--     let nm ← mkFreshUserName `algInst
--     let mvar ← mvarid.define nm q(Algebra $A $B) q(RingHom.toAlgebra $f)
--     let (_, mvar) ← mvar.intro1P
--     return [mvar]

/-- TODO


-/
def addIsScalarTowerInstanceFromRingHomComp (f : Expr) : TacticM Unit := withMainContext do
  let (_, l) := f.getAppFnArgs
  let tower ← mkAppOptM `IsScalarTower #[l[0]!, l[1]!, l[2]!, none, none, none]
  try let _ ← synthInstance tower
  catch _ => liftMetaTactic fun mvarid => do
    let nm ← mkFreshUserName `scalarTowerInst
    -- This is quite ugly, so I might prefer Qq reason for this reason
    let h ← mkFreshExprMVar (← mkAppM `Eq #[
      ← mkAppOptM `algebraMap #[l[0]!, l[2]!, none, none, none],
      ← mkAppM `RingHom.comp #[
        ← mkAppOptM `algebraMap #[l[1]!, l[2]!, none, none, none],
        ← mkAppOptM `algebraMap #[l[0]!, l[1]!, none, none, none]
    ]])
    h.mvarId!.refl
    let mvar ← mvarid.define nm tower
      (← mkAppOptM `IsScalarTower.of_algebraMap_eq'
        #[l[0]!, l[1]!, l[2]!, none, none, none, none, none, none, h])
    let (_, mvar) ← mvar.intro1P
    return [mvar]

  -- OLD Qq VERSION: (which might be better)
  -- def addIsScalarTowerInstanceFromRingHomComp (t : Expr) : TacticM Unit := withMainContext do
  -- let u ← Meta.mkFreshLevelMVar
  -- let v ← Meta.mkFreshLevelMVar
  -- let w ← Meta.mkFreshLevelMVar
  -- let A : Q(Type u) ← mkFreshExprMVarQ q(Type u)
  -- let B : Q(Type v) ← mkFreshExprMVarQ q(Type v)
  -- let C : Q(Type w) ← mkFreshExprMVarQ q(Type w)
  -- let _instA : Q(CommRing $A) ← mkFreshExprMVarQ q(CommRing $A)
  -- let _instB : Q(CommRing $B) ← mkFreshExprMVarQ q(CommRing $B)
  -- let _instC : Q(CommRing $C) ← mkFreshExprMVarQ q(CommRing $C)
  -- let fst : Q($A →+* $B) ← mkFreshExprMVarQ q($A →+* $B)
  -- let snd : Q($B →+* $C) ← mkFreshExprMVarQ q($B →+* $C)
  -- let _ ←
  --   try let _pf ← assertDefEqQ f q(RingHom.comp $snd $fst)
  --   catch e => throwError e.toMessageData
  -- let _algInstAB ← synthInstanceQ q(Algebra $A $B)
  -- let _algInstBC ← synthInstanceQ q(Algebra $B $C)
  -- let _algInstAC ← synthInstanceQ q(Algebra $A $C)
  -- let h ← mkFreshExprMVarQ q(algebraMap $A $C = RingHom.comp (algebraMap $B $C)
  --    (algebraMap $A $B))
  -- h.mvarId!.refl
  -- try
  --   let _ ← synthInstanceQ q(IsScalarTower $A $B $C)
  -- catch _ => liftMetaTactic fun mvarid => do
  --   let nm ← mkFreshUserName `scalarTowerInst
  --   let mvar ← mvarid.define nm q(IsScalarTower $A $B $C) q(IsScalarTower.of_algebraMap_eq' $h)
  --   let (_, mvar) ← mvar.intro1P
  --   return [mvar]

/-- TODO

-/
-- -- WIP on searching through local context for types in a given array
def searchContext (t : Array Expr) : TacticM Unit := withMainContext do
  -- let t' ← t.mapM fun i => Term.elabTerm i none
  let ctx ← MonadLCtx.getLCtx
  ctx.forM fun decl => do
    if decl.isImplementationDetail then
      return
    let declType := decl.type
    let env ← getEnv

    for i in Attr.algebraizeAttr.getDecls env do
      let (nm, args) := declType.getAppFnArgs
      let some i' := i.eraseSuffix? `Algebraize | throwError "Error"
      if nm != i' then
        continue
      let f := args[args.size - 1]!
      if ¬ (← t.anyM (fun j => Meta.isDefEq j f)) then
        continue
      let h : Ident := mkIdent i
      let hf := mkIdent decl.userName
      let sn ← `(term| $h:ident $hf:ident)
      let m ← Term.elabTerm sn none

      liftMetaTactic fun mvarid => do
        let h ← mkFreshUserName `AlgebraizeInst
        let (_, mvar) ← mvarid.note h m
        return [mvar]

syntax "algebraize" (ppSpace colGt term:max)* : tactic

elab_rules : tactic
  | `(tactic| algebraize $[$t:term]*) => do
    let t ← t.mapM fun i => Term.elabTerm i none
    -- We loop through the given terms and try to add algebra and scalar tower instances
    for f in t do
      let ft ← inferType f
      match ft.getAppFn with
      | Expr.const `RingHom _ => addAlgebraInstanceFromRingHom f ft
      | _ => throwError "Expected a `RingHom`" -- TODO: improve message

    for f in t do
      match f.getAppFn with
      | Expr.const `RingHom.comp _ =>
        try addIsScalarTowerInstanceFromRingHomComp f
        catch _ => continue
      | _ => continue

    -- We then search through the local context to find other instances of algebraize
    searchContext t

example {A B C D : Type*}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B)
    (g : B →+* C) (h : C →+* D)
    (hf : f.FiniteType) (hf' : f.Finite) (hhg : (h.comp g).FiniteType)
    (hh : (h.comp g).comp f |>.FiniteType)
    (hg : g.IsIntegral) :
    True := by
  algebraize f g (g.comp f)


  --g h (g.comp f) (h.comp g) (h.comp (g.comp f))
  trivial

end Mathlib.Tactic
