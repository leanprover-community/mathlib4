import Lean

open Lean Meta

partial def normalizeCore (cache : IO.Ref (Std.HashMap ExprStructEq Expr)) (e : Expr) :
    CoreM Expr :=
  (fun f => f cache) <| show MonadCacheT ExprStructEq Expr CoreM Expr from do
  checkCache { val := e : ExprStructEq } fun _ => Core.withIncRecDepth do
    match e.headBeta with
    | .letE n t v b ndep =>

      match v.headBeta with
      | .letE n' t' v' v ndep' =>
        let b := b.liftLooseBVars 1 1
        normalizeCore cache <| .letE n' t' v' (.letE n t v b ndep) ndep'

      | (mkApp4 (.const ``Prod.mk [u,v]) X Y x y) =>

        let b := b.liftLooseBVars 1 2
        let b := b.instantiate1 (mkApp4 (.const ``Prod.mk [u,v]) X Y (.bvar 1) (.bvar 0))

        normalizeCore cache <|
          .letE (n.appendAfter "₁") X x (nondep:=ndep) <|
          .letE (n.appendAfter "₂") Y (y.liftLooseBVars 0 1) (nondep:=ndep) b

      | (.bvar ..) | (.fvar ..) | (.lam ..) =>
        normalizeCore cache <| b.instantiate1 v

      | (.app (.lam _ _ b' _) x) =>
        normalizeCore cache <| .letE n t (b'.instantiate1 x) b ndep

      | v => do
        let v' ← normalizeCore cache v
        if v==v' then
          let b' ← normalizeCore cache b
          if ¬b'.hasLooseBVar 0 then
            return b'.lowerLooseBVars 1 1
          else
            return (.letE n t v' b' ndep)
        else
          normalizeCore cache (.letE n t v' b ndep)

    | .proj ``Prod 0 xy =>
      match (← normalizeCore cache xy) with
      | mkApp4 (.const ``Prod.mk _) _ _ x _ => return x
      | .letE n t v b nonDep => normalizeCore cache (.letE n t v (.proj ``Prod 0 b) nonDep)
      | xy => return .proj ``Prod 0 xy
    | .proj ``Prod 1 xy =>
      match (← normalizeCore cache xy) with
      | mkApp4 (.const ``Prod.mk _) _ _ _ y => return y
      | .letE n t v b nonDep => normalizeCore cache (.letE n t v (.proj ``Prod 1 b) nonDep)
      | xy => return .proj ``Prod 1 xy
    | (mkApp3 (.const ``Prod.fst lvl) X Y xy) =>
      match (← normalizeCore cache xy) with
      | mkApp4 (.const ``Prod.mk _) _ _ x _ => return x
      | .letE n t v b nonDep =>
        normalizeCore cache (.letE n t v (mkApp3 (.const ``Prod.fst lvl) X Y b) nonDep)
      | xy => return (mkApp3 (.const ``Prod.fst lvl) X Y xy)
    | (mkApp3 (.const ``Prod.snd lvl) X Y xy) =>
      match (← normalizeCore cache xy) with
      | mkApp4 (.const ``Prod.mk _) _ _ _ y => return y
      | .letE n t v b nonDep =>
        normalizeCore cache (.letE n t v (mkApp3 (.const ``Prod.snd lvl) X Y b) nonDep)
      | xy => return (mkApp3 (.const ``Prod.snd lvl) X Y xy)
    | .app f x => do
      let f' ← normalizeCore cache f
      let x' ← normalizeCore cache x
      if f==f' ∧ x==x' then
        return .app f x
      else
        match f', x' with
        | .letE n t v b nonDep, x =>
          normalizeCore cache (.letE n t v (.app b (x.liftLooseBVars 0 1)) nonDep)
        | f, .letE n t v b nonDep =>
          normalizeCore cache (.letE n t v (.app (f.liftLooseBVars 0 1) b) nonDep)
        | f, x => normalizeCore cache (.app f x)
    | .lam n t b bi =>
      return .lam n t (← normalizeCore cache b) bi
    | .mdata d e =>
      return .mdata d (← normalizeCore cache e)
    | e => return e


initialize normalizeCache : IO.Ref (Std.HashMap ExprStructEq Expr) ← IO.mkRef {}
