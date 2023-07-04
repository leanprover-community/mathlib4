/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module control.traversable.derive
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Tactic.Basic
import Mathlib.Control.Traversable.Lemmas

/-!
## Automation to construct `traversable` instances
-/

namespace Mathlib.Deriving.Traversable

open Lean Meta Elab Term Command Tactic Match List Monad Functor

/-- similar to `nestedTraverse` but for `Functor` -/
partial def nestedMap (f v t : Expr) : TermElabM Expr := do
  let t ← instantiateMVars t
  if ← withNewMCtxDepth <| isDefEq t v then
    return f
  else if !v.occurs t.appFn! then
    let cl ← mkAppM ``Functor #[t.appFn!]
    let inst ← synthInstance cl
    let f' ← nestedMap f v t.appArg!
    mkAppOptM ``Functor.map #[t.appFn!, inst, none, none, f']
  else throwError "type {t} is not a functor with respect to variable {v}"

/-- similar to `traverseField` but for `Functor` -/
def mapField (n : Name) (cl f α β e : Expr) : TermElabM Expr := do
  let t ← whnf (← inferType e)
  if t.getAppFn.constName = some n then
    throwError "recursive types not supported"
  else if α.eqv e then
    return β
  else if α.occurs t then
    let f' ← nestedMap f α t
    return f'.app e
  else if ←
      (match t with
        | .app t' _ => withNewMCtxDepth <| isDefEq t' cl
        | _ => return false) then
    mkAppM ``Comp.mk #[e]
  else
    return e

/-- similar to `traverseConstructor` but for `Functor` -/
def mapConstructor (c n : Name) (ad : Expr) (f α β : Expr) (args₀ : List Expr)
    (args₁ : List (Bool × Expr)) (m : MVarId) : TermElabM Unit := do
  let g ← m.getType >>= instantiateMVars
  let args' ← args₁.mapM (fun (y : Bool × Expr) =>
      if y.1 then return mkAppN ad #[α, β, f, y.2]
      else mapField n g.appFn! f α β y.2)
  mkAppOptM c ((args₀ ++ args').map some).toArray >>= m.assign

/-- derive the `map` definition of a `Functor` -/
def mkMap (type : Name) (ad : Expr) (levels : List Name) (vars : List Expr) (m : MVarId) :
    TermElabM Unit := do
  let (#[α, β, f, x], m') ← m.introN 4 [`α, `β, `f, `x] | unreachable!
  m'.withContext do
    let et ← x.getType
    let .inductInfo cinfo ← getConstInfo type | failure
    let cinfos ← cinfo.ctors.mapM fun ctor => do
      let .ctorInfo cinfo ← getConstInfo ctor | failure
      return cinfo
    let mn ← Lean.mkAuxName (type ++ "map" ++ "match") 1
    let matchType ← mkArrow et (← m'.getType)
    let motive ← forallBoundedTelescope matchType (some 1) fun xs body => mkLambdaFVars xs body
    let lhss ← cinfos.mapM fun cinfo => do
      let .ctorInfo cinfo ← getConstInfo cinfo.name | failure
      let ls := levels.map Level.param
      let vars' := vars.concat (.fvar α)
      let ce := mkAppN (.const cinfo.name ls) vars'.toArray
      let ct ← inferType ce
      forallBoundedTelescope ct cinfo.numFields fun args _ => do
        let fvarDecls ← args.toList.mapM fun arg => getFVarLocalDecl arg
        let fields := args.toList.map fun arg => Pattern.var arg.fvarId!
        let patterns := [Pattern.ctor cinfo.name ls vars' fields]
        return { ref := .missing
                 fvarDecls
                 patterns }
    let mres ← Term.mkMatcher
      { matcherName := mn
        matchType
        discrInfos := #[{}]
        lhss }
    mres.addMatcher
    let r := mkApp2 mres.matcher motive (.fvar x)
    let ms' ← m'.apply r
    let ms' := ms'.zip cinfos
    ms'.forM fun (m', cinfo) => do
      if cinfo.numFields = 0 then
        let (_, m') ← m'.intro1
        m'.withContext do
          mapConstructor
            cinfo.name type ad (mkFVar f) (mkFVar α) (mkFVar β) (vars.concat (mkFVar β)) [] m'
      else
        let (args, m') ← m'.introN cinfo.numFields
        m'.withContext do
          let args := args.toList.map Expr.fvar
          let args₀ ← args.mapM fun a => do
            let b ← et.occurs <$> inferType a
            return (b, a)
          mapConstructor
            cinfo.name type ad (mkFVar f) (mkFVar α) (mkFVar β) (vars.concat (mkFVar β)) args₀ m'

def deriveFunctor (levels : List Name) (vars : List Expr) (m : MVarId) : TermElabM Unit := do
  let .app (.const ``Functor _) F ← m.getType >>= instantiateMVars | failure
  let some n := F.getAppFn.constName? | failure
  let d ← getConstInfo n
  let [m] ← run m <| evalTactic (← `(tactic| refine { map := @(?_) })) | failure
  let t ← m.getType >>= instantiateMVars
  let n' := n ++ "map"
  withAuxDecl "map" t n' fun ad => do
    let m' := (← mkFreshExprSyntheticOpaqueMVar t).mvarId!
    mkMap n ad levels vars m'
    let e ← instantiateMVars (mkMVar m')
    let e := e.replaceFVar ad (mkAppN (.const n' (levels.map Level.param)) vars.toArray)
    let e' ← mkLambdaFVars vars.toArray e
    let t' ← mkForallFVars vars.toArray t
    addPreDefinitions
      #[{ ref := .missing
          kind := .def
          levelParams := levels
          modifiers :=
            { isUnsafe := d.isUnsafe
              attrs :=
                #[{ kind := .global
                    name := `specialize
                    stx := ← `(attr| specialize) }] }
          declName := n'
          type := t'
          value := e' }] {}
  m.assign (mkAppN (mkConst n' (levels.map Level.param)) vars.toArray)

def mkOneInstance (n cls : Name) (tac : List Name → List Expr → MVarId → TermElabM Unit)
    (mkInst : Name → Expr → TermElabM Expr := fun n arg => mkAppM n #[arg]) : TermElabM Unit := do
  let .inductInfo decl ← getConstInfo n |
    throwError m!"failed to derive '{cls}', '{n}' is not an inductive type"
  let clsDecl ← getConstInfo cls
  let ls := decl.levelParams.map Level.param
  -- incrementally build up target expression `(hp : p) → [cls hp] → ... cls (n.{ls} hp ...)`
  -- where `p ...` are the inductive parameter types of `n`
  let tgt := Lean.mkConst n ls
  forallTelescope decl.type fun params _ => do
    let params := params.pop
    let tgt := mkAppN tgt params
    let tgt ← mkInst cls tgt
    let tgt ← params.zipWithIndex.foldrM (fun (param, i) tgt => do
      -- add typeclass hypothesis for each inductive parameter
      let tgt ← (do
        guard (i < decl.numParams)
        let paramCls ← mkAppM cls #[param]
        return mkForall `a .instImplicit paramCls tgt) <|> return tgt
      mkForallFVars #[param] tgt) tgt
    (discard <| liftM (synthInstance tgt)) <|> do
      let m := (← mkFreshExprSyntheticOpaqueMVar tgt).mvarId!
      let (fvars, m') ← m.intros
      tac decl.levelParams (fvars.toList.map mkFVar) m'
      let val ← instantiateMVars (mkMVar m)
      let isUnsafe := decl.isUnsafe && clsDecl.isUnsafe
      let result ← m'.withContext <| do
        let type ← m'.getType >>= instantiateMVars
        let ref ← IO.mkRef ""
        Meta.forEachExpr type fun e => do
          if e.isForall then ref.modify (· ++ "ForAll")
          else if e.isProp then ref.modify (· ++ "Prop")
          else if e.isType then ref.modify (· ++ "Type")
          else if e.isSort then ref.modify (· ++ "Sort")
          else if e.isConst then
            match e.constName!.eraseMacroScopes with
            | .str _ str =>
                if str.front.isLower then
                  ref.modify (· ++ str.capitalize)
                else
                  ref.modify (· ++ str)
            | _ => pure ()
        ref.get
      let instN ← liftMacroM <| mkUnusedBaseName <| Name.mkSimple ("inst" ++ result)
      addPreDefinitions
        #[{ ref := .missing
            kind := .def
            levelParams := decl.levelParams
            modifiers :=
              { isUnsafe
                attrs :=
                  #[{ kind := .global
                      name := `instance
                      stx := ← `(attr| instance) }] }
            declName := instN
            type := tgt
            value := val }] {}

def higherOrderDeriveHandler (cls : Name) (tac : List Name → List Expr → MVarId → TermElabM Unit)
    (deps : List DerivingHandlerNoArgs := [])
    (mkInst : Name → Expr → TermElabM Expr := fun n arg => mkAppM n #[arg]) :
    DerivingHandlerNoArgs := fun a => do
  let #[n] := a | return false -- mutually inductive types are not supported yet
  deps.forM fun f : DerivingHandlerNoArgs => discard <| f a
  liftTermElabM <| mkOneInstance n cls tac mkInst
  return true

def functorDeriveHandler : DerivingHandlerNoArgs :=
  higherOrderDeriveHandler ``Functor deriveFunctor []

initialize registerDerivingHandler ``Functor functorDeriveHandler

def deriveLawfulFunctor (_ : List Name) (_ : List Expr) (m : MVarId) : TermElabM Unit := do
  let rules (l₁ : List (Name × Bool)) (l₂ : List (Name)) (b : Bool) : MetaM Simp.Context := do
    let mut s : SimpTheorems := {}
    s ← l₁.foldlM (fun s (n, b) => s.addConst n (inv := b)) s
    s ← l₂.foldlM (fun s n => s.addDeclToUnfold n) s
    if b then
      let hs ← getPropHyps
      s ← hs.foldlM (fun s f => f.getDecl >>= fun d => s.add (.fvar f) #[] d.toExpr) s
    return { simpTheorems := #[s] }
  let .app (.app (.const ``LawfulFunctor _) F) _ ← m.getType >>= instantiateMVars | failure
  let some n := F.getAppFn.constName? | failure
  let [mcn, mim, mcm] ← m.applyConst ``LawfulFunctor.mk | failure
  liftM <| (Prod.snd <$> mcn.introN 2) >>= MVarId.refl
  let (#[_, x], mim) ← mim.introN 2 | failure
  let (some mim, _) ← dsimpGoal mim (← rules [] [``Functor.map] false) | failure
  let xs ← mim.induction x (mkRecName n)
  xs.forM fun ⟨mim, _, _⟩ =>
    mim.withContext do
      let (some (_, mim), _) ←
        simpGoal mim (← rules [(``Functor.map_id, false)] [n ++ "map"] true) | failure
      mim.refl
  let (#[_, _, _, _, _, x], mcm) ← mcm.introN 6 | failure
  let (some mcm, _) ← dsimpGoal mcm (← rules [] [``Functor.map] false) | failure
  let xs ← mcm.induction x (mkRecName n)
  xs.forM fun ⟨mcm, _, _⟩ =>
    mcm.withContext do
      let (some (_, mcm), _) ←
        simpGoal mcm (← rules [(``Functor.map_comp_map, true)] [n ++ "map"] true) | failure
      mcm.refl

def lawfulFunctorDeriveHandler : DerivingHandlerNoArgs :=
  higherOrderDeriveHandler ``LawfulFunctor deriveLawfulFunctor [functorDeriveHandler]
    (fun n arg => mkAppOptM n #[arg, none])

initialize registerDerivingHandler ``LawfulFunctor lawfulFunctorDeriveHandler

/-
/-- `seq_apply_constructor f [x,y,z]` synthesizes `f <*> x <*> y <*> z` -/
private meta def seq_apply_constructor :
  expr → list (expr ⊕ expr) → tactic (list (tactic expr) × expr)
| e (sum.inr x :: xs) :=
    prod.map (cons intro1)   id <$> (to_expr ``(%%e <*> %%x) >>= flip seq_apply_constructor xs)
| e (sum.inl x :: xs) := prod.map (cons $ pure x) id <$> seq_apply_constructor e xs
| e [] := return ([],e)

/-- ``nested_traverse f α (list (array n (list α)))`` synthesizes the expression
`traverse (traverse (traverse f))`. `nested_traverse` assumes that `α` appears in
`(list (array n (list α)))` -/
meta def nested_traverse (f v : expr) : expr → tactic expr
| t :=
do t ← instantiate_mvars t,
   mcond (succeeds $ is_def_eq t v)
      (pure f)
      (if ¬ v.occurs (t.app_fn)
          then do
            cl ← mk_app ``traversable [t.app_fn],
            _inst ← mk_instance cl,
            f' ← nested_traverse t.app_arg,
            mk_mapp ``traversable.traverse [t.app_fn,_inst,none,none,none,none,f']
          else fail format!"type {t} is not traversable with respect to variable {v}")

/--
For a sum type `inductive foo (α : Type) | foo1 : list α → ℕ → foo | ...`
``traverse_field `foo appl_inst f `α `(x : list α)`` synthesizes
`traverse f x` as part of traversing `foo1`. -/
meta def traverse_field (n : name) (appl_inst cl f v e : expr) : tactic (expr ⊕ expr) :=
do t ← infer_type e >>= whnf,
   if t.get_app_fn.const_name = n
   then fail "recursive types not supported"
   else if v.occurs t
   then do f' ← nested_traverse f v t,
           pure $ sum.inr $ f' e
   else
         (is_def_eq t.app_fn cl >> sum.inr <$> mk_app ``comp.mk [e])
     <|> pure (sum.inl e)

/--
For a sum type `inductive foo (α : Type) | foo1 : list α → ℕ → foo | ...`
``traverse_constructor `foo1 `foo appl_inst f `α `β [`(x : list α), `(y : ℕ)]``
synthesizes `foo1 <$> traverse f x <*> pure y.` -/
meta def traverse_constructor (c n : name) (appl_inst f α β : expr)
  (args₀ : list expr)
  (args₁ : list (bool × expr)) (rec_call : list expr) : tactic expr :=
do g ← target,
   args' ← mmap (traverse_field n appl_inst g.app_fn f α) args₀,
   (_, args') ← mmap_accuml (λ (x : list expr) (y : bool × _),
     if y.1 then pure (x.tail, sum.inr x.head)
     else prod.mk x <$> traverse_field n appl_inst g.app_fn f α y.2) rec_call args₁,
   constr ← mk_const c,
   v ← mk_mvar,
   constr' ← to_expr ``(@pure _ (%%appl_inst).to_has_pure _ %%v),
   (vars_intro,r) ← seq_apply_constructor constr' (args₀.map sum.inl ++ args'),
   gs ← get_goals,
   set_goals [v],
   vs ← vars_intro.mmap id,
   tactic.exact (constr.mk_app vs),
   done,
   set_goals gs,
   return r

/-- derive the `traverse` definition of a `traversable` instance -/
meta def mk_traverse (type : name) := do
do ls ← local_context,
   [m,appl_inst,α,β,f,x] ← tactic.intro_lst [`m,`appl_inst,`α,`β,`f,`x],
   et ← infer_type x,
   reset_instance_cache,
   xs ← tactic.induction x,
   xs.mmap'
      (λ (x : name × list expr × list (name × expr)),
      do let (c,args,_) := x,
         (args,rec_call) ← args.mpartition $ λ e, (bnot ∘ β.occurs) <$> infer_type e,
         args₀ ← args.mmap $ λ a, do { b ← et.occurs <$> infer_type a, pure (b,a) },
         traverse_constructor c type appl_inst f α β (ls ++ [β]) args₀ rec_call >>= tactic.exact)

open applicative

meta def derive_traverse (pre : option name) : tactic unit :=
do vs ← local_context,
   `(traversable %%f) ← target,
   env ← get_env,
   let n := f.get_app_fn.const_name,
   d ← get_decl n,
   constructor,
   tgt ← target,
   extract_def (with_prefix pre n <.> "traverse") d.is_trusted $ mk_traverse n,
   when (d.is_trusted) $ do
      tgt ← pis vs tgt,
      derive_traverse_equations pre n vs tgt

open interactive


meta def simp_functor (rs : list simp_arg_type := []) : tactic unit :=
simp none none ff rs [`functor_norm] (loc.ns [none])

meta def traversable_law_starter (rs : list simp_arg_type) :=
do vs ← tactic.intros,
   resetI,
   dunfold [``traversable.traverse,``functor.map] (loc.ns [none]),
   () <$ tactic.induction vs.ilast;
     simp_functor rs

meta def derive_lawful_traversable (pre : option name) : tactic unit :=
do `(@is_lawful_traversable %%f %%d) ← target,
   let n := f.get_app_fn.const_name,
   eqns  ← get_equations_of (with_prefix pre n <.> "traverse"),
   eqns' ← get_equations_of (with_prefix pre n <.> "map"),
   let def_eqns := eqns.map simp_arg_type.expr ++
                   eqns'.map simp_arg_type.expr ++
                  [simp_arg_type.all_hyps],
   let comp_def := [ simp_arg_type.expr ``(function.comp) ],
   let tr_map := list.map simp_arg_type.expr [``(traversable.traverse_eq_map_id')],
   let natur  := λ (η : expr), [simp_arg_type.expr ``(traversable.naturality_pf %%η)],
   let goal := loc.ns [none],
   constructor;
     [ traversable_law_starter def_eqns; refl,
       traversable_law_starter def_eqns; (refl <|> simp_functor (def_eqns ++ comp_def)),
       traversable_law_starter def_eqns; (refl <|> simp none none tt tr_map [] goal ),
       traversable_law_starter def_eqns; (refl <|> do
         η ← get_local `η <|> do
         { t ← mk_const ``is_lawful_traversable.naturality >>= infer_type >>= pp,
           fail format!"expecting an `applicative_transformation` called `η` in\nnaturality : {t}"},
         simp none none tt (natur η) [] goal) ];
   refl,
   return ()

open function

meta def traversable_derive_handler' (nspace : option name := none) : derive_handler :=
higher_order_derive_handler ``traversable (derive_traverse nspace)
  [functor_derive_handler' nspace] nspace

@[derive_handler]
meta def traversable_derive_handler : derive_handler :=
guard_class  ``traversable traversable_derive_handler'

meta def lawful_traversable_derive_handler' (nspace : option name := none) : derive_handler :=
higher_order_derive_handler
  ``is_lawful_traversable (derive_lawful_traversable nspace)
  [traversable_derive_handler' nspace,
   lawful_functor_derive_handler' nspace]
  nspace
  (λ n arg, mk_mapp n [arg,none])

@[derive_handler]
meta def lawful_traversable_derive_handler : derive_handler :=
guard_class ``is_lawful_traversable lawful_traversable_derive_handler'
-/

end Mathlib.Deriving.Traversable
