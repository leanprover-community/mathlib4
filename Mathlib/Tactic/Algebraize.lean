import Mathlib.Algebra.Algebra.Tower
import Lean.Attributes
import Mathlib.Util.AddRelatedDecl

open Lean Elab Tactic Term Meta

namespace Lean.Attr

def algebraizeGetParam (thm : Name) (stx : Syntax) : AttrM Name := do
  match stx with
  | `(attr| algebraize2 $name:ident) => return name.getId
  -- TODO: deal with this case! Then if name is "RingHom.FiniteType" ---> "Algebra.FiniteType.mk"
  | `(attr| algebraize2) => throwError "algebraize requires an argument"
  | _ => throwError "unexpected algebraize argument"

initialize algebraize2Attr : ParametricAttribute Name ←
  registerParametricAttribute {
    name := `algebraize2,
    descr := "TODO",
    getParam := algebraizeGetParam }

end Lean.Attr

-- alias RingHom.Algebraize := RingHom.toAlgebra

-- @[algebraize]
-- lemma RingHom.Finite.Algebraize {A B : Type*} [CommRing A] [CommRing B] {f : A →+* B}
--     (hf : f.Finite) : letI : Algebra A B := f.toAlgebra; Module.Finite A B :=
--   hf

-- @[algebraize]
-- lemma RingHom.Finite.Algebraize {A B : Type*} [CommRing A] [CommRing B] {f : A →+* B}
--     (hf : f.Finite) : letI : Algebra A B := f.toAlgebra; Module.Finite A B :=
--   hf

-- @[algebraize]
-- lemma RingHom.FiniteType.Algebraize {A B : Type*} [CommRing A] [CommRing B] {f : A →+* B}
--     (hf : f.FiniteType) : letI : Algebra A B := f.toAlgebra; Algebra.FiniteType A B :=
--   hf

-- @[algebraize]
-- lemma RingHom.IsIntegral.Algebraize {A B : Type*} [CommRing A] [CommRing B] {f : A →+* B}
--     (hf : f.IsIntegral) : letI : Algebra A B := f.toAlgebra; Algebra.IsIntegral A B :=
--       letI : Algebra A B := f.toAlgebra
--       {isIntegral := hf}
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
  try
    let _ ← synthInstance tower
  catch _ => liftMetaTactic fun mvarid => do
    let nm ← mkFreshUserName `scalarTowerInst
    -- This is quite ugly, so I might prefer Qq reason for this reason
    -- Maybe I can use forallTelescope on `IsScalarTower.of_algebraMap_eq' somehow here?
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
def searchContext' (t : Array Expr) : TacticM Unit := withMainContext do
  let ctx ← MonadLCtx.getLCtx
  ctx.forM fun decl => do
    if decl.isImplementationDetail then return
    let (nm, args) := decl.type.getAppFnArgs
    match Attr.algebraize2Attr.getParam? (← getEnv) nm with
    | some p =>
      let f := args[args.size - 1]!
      -- Check if `f` appears in the list of functions we have algebraized
      if ¬ (← t.anyM (fun j => Meta.isDefEq j f)) then return

      let cinfo ← getConstInfo p
      let n ← getExpectedNumArgs cinfo.type
      let pargs := Array.mkArray n (none : Option Expr)
      let pargs := pargs.set! 0 args[0]!
      let pargs := pargs.set! 1 args[1]!
      let tp ← mkAppOptM p pargs

      liftMetaTactic fun mvarid => do
        let h ← mkFreshUserName `AlgebraizeInst
        -- TODO: should make this with let somehow? Data is forgotten...!
        let (_, mvar) ← mvarid.note h decl.value tp
        return [mvar]
      -- Otherwise, ...
      -- else
      --   logInfo m!"hello outside"
      --   -- Otherwise, `p` is a lemma for creating the algebra instance
      --   let h := mkIdent p
      --   let hf := mkIdent decl.userName
      --   let sn ← `(term| $h:ident $hf:ident)
      --   let m ← Term.elabTerm sn none

      --   liftMetaTactic fun mvarid => do
      --     let h ← mkFreshUserName `AlgebraizeInst
      --     let (_, mvar) ← mvarid.note h m
      --     return [mvar]
    | none => return

-- -- WIP on searching through local context for types in a given array
-- def searchContext (t : Array Expr) : TacticM Unit := withMainContext do
--   let ctx ← MonadLCtx.getLCtx
--   ctx.forM fun decl => do
--     if decl.isImplementationDetail then
--       return
--     let (nm, args) := decl.type.getAppFnArgs
--     logInfo m!"{nm} {args}"
--     for i in Attr.algebraizeAttr.getDecls (← getEnv) do
--       -- TODO: figure out how to get one lemma to point to another via attributes
--       -- (maybe just include the other lemma name as a parameter?)
--       let some i' := i.eraseSuffix? `Algebraize | throwError "Error"
--       if i' != nm then
--         continue
--       let f := args[args.size - 1]!
--       logInfo m!"f : {f}"
--       if ¬ (← t.anyM (fun j => Meta.isDefEq j f)) then
--         continue
--       let h : Ident := mkIdent i
--       let hf := mkIdent decl.userName
--       let sn ← `(term| $h:ident $hf:ident)
--       let m ← Term.elabTerm sn none

--       liftMetaTactic fun mvarid => do
--         let h ← mkFreshUserName `AlgebraizeInst
--         let (_, mvar) ← mvarid.note h m
--         return [mvar]

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
    searchContext' t

end Mathlib.Tactic
