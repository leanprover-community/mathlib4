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

open Lean Meta Elab Tactic List Monad Functor

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
  else if ← withNewMCtxDepth <| isDefEq t cl then
    mkAppM ``Comp.mk #[e]
  else
    return e

/-- similar to `traverseConstructor` but for `Functor` -/
def mapConstructor (c n : Name) (f α β : Expr) (args₀ : List Expr) (args₁ : List (Bool × Expr))
    (recCall : List Expr) (g : Expr) : TermElabM Expr := do
  let (_, args') ←
    mapAccumLM (fun (x : List Expr) (y : Bool × Expr) =>
      if y.1 then return (x.tail, x.head!)
      else Prod.mk recCall <$> mapField n g.appFn! f α β y.2) recCall args₁
  let r ← mkAppOptM c ((args₀ ++ args').map some).toArray
  return r

/-- derive the `map` definition of a `Functor` -/
def mkMap (type : Name) (ls : List Expr) (g : Expr) : TermElabM Expr := do
  let m := (← mkFreshExprSyntheticOpaqueMVar g).mvarId!
  let (#[α, β, f, x], m') ← m.introN 4 [`α, `β, `f, `x] | unreachable!
  m'.withContext do
    let et ← x.getType
    let xs ← m'.induction x (mkRecName type)
    xs.forM fun ⟨m', args, _⟩ => do
      let c := Name.mkStr type (← m'.getTag).getString!
      m'.withContext do
        let (args, recCall) ←
          args.toList.partitionM fun e => (!(mkFVar β).occurs ·) <$> inferType e
        let args₀ ← args.mapM fun a => do
          let b ← et.occurs <$> inferType a
          return (b, a)
        let g ← m'.getType
        mapConstructor
            c type (mkFVar f) (mkFVar α) (mkFVar β) (ls.concat (mkFVar β)) args₀ recCall g
          >>= m'.assign
  instantiateMVars (mkMVar m)

/-
meta def with_prefix : option name → name → name
| none n := n
| (some p) n := p ++ n

/-- derive the equations for a specific `map` definition -/
meta def derive_map_equations (pre : option name) (n : name) (vs : list expr) (tgt : expr) :
  tactic unit :=
do e ← get_env,
   ((e.constructors_of n).enum_from 1).mmap' $ λ ⟨i,c⟩,
   do { mk_meta_var tgt >>= set_goals ∘ pure,
        vs ← intro_lst $ vs.map expr.local_pp_name,
        [α,β,f] ← tactic.intro_lst [`α,`β,`f] >>= mmap instantiate_mvars,
        c' ← mk_mapp c $ vs.map some ++ [α],
        tgt' ← infer_type c' >>= pis vs,
        mk_meta_var tgt' >>= set_goals ∘ pure,
        vs ← tactic.intro_lst $ vs.map expr.local_pp_name,
        vs' ← tactic.intros,
        c' ← mk_mapp c $ vs.map some ++ [α],
        arg ← mk_mapp' c' vs',
        n_map ← mk_const (with_prefix pre n <.> "map"),
        let call_map := λ x, mk_mapp' n_map (vs ++ [α,β,f,x]),
        lhs ← call_map arg,
        args ← vs'.mmap $ λ a,
        do { t ← infer_type a,
             pure ((expr.const_name (expr.get_app_fn t) = n : bool),a) },
        let rec_call := args.filter_map $
          λ ⟨b, e⟩, guard b >> pure e,
        rec_call ← rec_call.mmap call_map,
        rhs ← map_constructor c n f α β (vs ++ [β]) args rec_call,
        monad.join $ unify <$> infer_type lhs <*> infer_type rhs,
        eqn ← mk_app ``eq [lhs,rhs],
        let ws := eqn.list_local_consts,
        eqn ← pis ws.reverse eqn,
        eqn ← instantiate_mvars eqn,
        (_,pr) ← solve_aux eqn (tactic.intros >> refine ``(rfl)),
        let eqn_n := (with_prefix pre n <.> "map" <.> "equations" <.> "_eqn").append_after i,
        pr ← instantiate_mvars pr,
        add_decl $ declaration.thm eqn_n eqn.collect_univ_params eqn (pure pr),
        return () },
   set_goals [],
   return ()

meta def derive_functor (pre : option name) : tactic unit :=
do vs ← local_context,
   `(functor %%f) ← target,
   env ← get_env,
   let n := f.get_app_fn.const_name,
   d ← get_decl n,
   refine ``( { functor . map := _ , .. } ),
   tgt ← target,
   extract_def (with_prefix pre n <.> "map") d.is_trusted $ mk_map n,
   when (d.is_trusted) $ do
     tgt ← pis vs tgt,
     derive_map_equations pre n vs tgt

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

/-- derive the equations for a specific `traverse` definition -/
meta def derive_traverse_equations (pre : option name) (n : name) (vs : list expr) (tgt : expr) :
  tactic unit :=
do e ← get_env,
   ((e.constructors_of n).enum_from 1).mmap' $ λ ⟨i,c⟩,
   do { mk_meta_var tgt >>= set_goals ∘ pure,
        vs ← intro_lst $ vs.map expr.local_pp_name,
        [m,appl_inst,α,β,f] ← tactic.intro_lst [`m,`appl_inst,`α,`β,`f] >>= mmap instantiate_mvars,
        c' ← mk_mapp c $ vs.map some ++ [α],
        tgt' ← infer_type c' >>= pis vs,
        mk_meta_var tgt' >>= set_goals ∘ pure,
        vs ← tactic.intro_lst $ vs.map expr.local_pp_name,
        c' ← mk_mapp c $ vs.map some ++ [α],
        vs' ← tactic.intros,
        arg ← mk_mapp' c' vs',
        n_map ← mk_const (with_prefix pre n <.> "traverse"),
        let call_traverse := λ x, mk_mapp' n_map (vs ++ [m,appl_inst,α,β,f,x]),
        lhs ← call_traverse arg,
        args ← vs'.mmap $ λ a,
        do { t ← infer_type a,
             pure ((expr.const_name (expr.get_app_fn t) = n : bool),a) },
        let rec_call := args.filter_map $
          λ ⟨b, e⟩, guard b >> pure e,
        rec_call ← rec_call.mmap call_traverse,
        rhs ← traverse_constructor c n appl_inst f α β (vs ++ [β]) args rec_call,
        monad.join $ unify <$> infer_type lhs <*> infer_type rhs,
        eqn ← mk_app ``eq [lhs,rhs],
        let ws := eqn.list_local_consts,
        eqn ← pis ws.reverse eqn,
        eqn ← instantiate_mvars eqn,
        (_,pr) ← solve_aux eqn (tactic.intros >> refine ``(rfl)),
        let eqn_n := (with_prefix pre n <.> "traverse" <.> "equations" <.> "_eqn").append_after i,
        pr ← instantiate_mvars pr,
        add_decl $ declaration.thm eqn_n eqn.collect_univ_params eqn (pure pr),
        return () },
   set_goals [],
   return ()

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

meta def mk_one_instance
  (n : name)
  (cls : name)
  (tac : tactic unit)
  (namesp : option name)
  (mk_inst : name → expr → tactic expr := λ n arg, mk_app n [arg]) :
  tactic unit :=
do decl ← get_decl n,
   cls_decl ← get_decl cls,
   env ← get_env,
   guard (env.is_inductive n) <|>
     fail format!"failed to derive '{cls}', '{n}' is not an inductive type",
   let ls := decl.univ_params.map $ λ n, level.param n,
   -- incrementally build up target expression `Π (hp : p) [cls hp] ..., cls (n.{ls} hp ...)`
   -- where `p ...` are the inductive parameter types of `n`
   let tgt : expr := expr.const n ls,
   ⟨params, _⟩ ← open_pis (decl.type.instantiate_univ_params (decl.univ_params.zip ls)),
   let params := params.init,
   let tgt := tgt.mk_app params,
   tgt ← mk_inst cls tgt,
   tgt ← params.enum.mfoldr (λ ⟨i, param⟩ tgt,
   do -- add typeclass hypothesis for each inductive parameter
      tgt ← do
      { guard $ i < env.inductive_num_params n,
        param_cls ← mk_app cls [param],
        pure $ expr.pi `a binder_info.inst_implicit param_cls tgt }
      <|> pure tgt,
      pure $ tgt.bind_pi param
   ) tgt,
   () <$ mk_instance tgt <|> do
     (_, val) ← tactic.solve_aux tgt (do
       tactic.intros >> tac),
     val ← instantiate_mvars val,
     let trusted := decl.is_trusted ∧ cls_decl.is_trusted,
     let inst_n := with_prefix namesp n ++ cls,
     add_decl (declaration.defn inst_n
               decl.univ_params
               tgt val reducibility_hints.abbrev trusted),
     set_basic_attribute `instance inst_n namesp.is_none

open interactive


meta def get_equations_of (n : name) : tactic (list pexpr) :=
do e ← get_env,
   let pre := n <.> "equations",
   let x := e.fold [] $ λ d xs, if pre.is_prefix_of d.to_name then d.to_name :: xs else xs,
   x.mmap resolve_name

meta def derive_lawful_functor (pre : option name) : tactic unit :=
do `(@is_lawful_functor %%f %%d) ← target,
   refine ``( { .. } ),
   let n := f.get_app_fn.const_name,
   let rules := λ r, [simp_arg_type.expr r, simp_arg_type.all_hyps],
   let goal := loc.ns [none],
   solve1 (do
     vs ← tactic.intros,
     try $ dunfold [``functor.map] (loc.ns [none]),
     dunfold [with_prefix pre n <.> "map",``id] (loc.ns [none]),
     () <$ tactic.induction vs.ilast;
       simp none none ff (rules ``(functor.map_id)) [] goal),
   focus1 (do
     vs ← tactic.intros,
     try $ dunfold [``functor.map] (loc.ns [none]),
     dunfold [with_prefix pre n <.> "map",``id] (loc.ns [none]),
     () <$ tactic.induction vs.ilast;
       simp none none ff (rules ``(functor.map_comp_map)) [] goal),
   return ()

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

meta def guard_class (cls : name) (hdl : derive_handler) : derive_handler :=
λ p n,
if p.is_constant_of cls then
  hdl p n
else
  pure ff

meta def higher_order_derive_handler
  (cls : name)
  (tac : tactic unit)
  (deps : list derive_handler := [])
  (namesp : option name)
  (mk_inst : name → expr → tactic expr := λ n arg, mk_app n [arg]) :
  derive_handler :=
λ p n,
do mmap' (λ f : derive_handler, f p n) deps,
   mk_one_instance n cls tac namesp mk_inst,
   pure tt

meta def functor_derive_handler' (nspace : option name := none) : derive_handler :=
higher_order_derive_handler ``functor (derive_functor nspace) [] nspace

@[derive_handler]
meta def functor_derive_handler : derive_handler :=
guard_class ``functor functor_derive_handler'

meta def traversable_derive_handler' (nspace : option name := none) : derive_handler :=
higher_order_derive_handler ``traversable (derive_traverse nspace)
  [functor_derive_handler' nspace] nspace

@[derive_handler]
meta def traversable_derive_handler : derive_handler :=
guard_class  ``traversable traversable_derive_handler'

meta def lawful_functor_derive_handler'  (nspace : option name := none) : derive_handler :=
higher_order_derive_handler
  ``is_lawful_functor (derive_lawful_functor nspace)
  [traversable_derive_handler' nspace]
  nspace
  (λ n arg, mk_mapp n [arg,none])

@[derive_handler]
meta def lawful_functor_derive_handler : derive_handler :=
guard_class  ``is_lawful_functor lawful_functor_derive_handler'

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
