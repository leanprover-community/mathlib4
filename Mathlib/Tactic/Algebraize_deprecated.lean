import Lean.Attributes

namespace Lean.Attr

-- TODO: should be ParametricAttribute + should write a function that gets the name
initialize algebraizeAttr : TagAttribute ← registerTagAttribute `algebraize "algebraize"

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
