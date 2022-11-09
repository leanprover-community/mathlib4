import Lean

namespace Mathlib.Tactic

open Lean Meta

/-- `compactRelation bs as_ps`: Produce a relation of the form:
```lean
R := λ as ∃ bs, Λ_i a_i = p_i[bs]
```
This relation is user-visible, so we compact it by removing each `b_j` where a `p_i = b_j`, and
hence `a_i = b_j`. We need to take care when there are `p_i` and `p_j` with `p_i = p_j = b_k`.
-/
partial def compactRelation :
  List Expr → List (Expr × Expr) → List (Option Expr) × List (Expr × Expr) × (Expr → Expr)
| [],    as_ps => ([], as_ps, id)
| b::bs, as_ps =>
  match as_ps.span (λ⟨_,p⟩ => ¬ p == b) with
    | (_, []) => -- found nothing in ps equal to b
        let (bs, as_ps', subst) := compactRelation bs as_ps
        (b::bs, as_ps', subst)
    | (ps₁, (a, _) :: ps₂) => -- found one that matches b. Remove it.
      let i := fun e => e.replaceFVar b a
      let (bs, as_ps', subst) := compactRelation (bs.map i) ((ps₁ ++ ps₂).map (λ⟨a, p⟩ => (a, i p)))
      (none :: bs, as_ps', i ∘ subst)

def getAppArgsAux : List Expr → Expr → List Expr
| r, .app f a => getAppArgsAux (a::r) f
| r, _       => r

def getAppArgs : Expr → List Expr :=
getAppArgsAux []

/-- Generates an expression of the form `∃(args), inner`. `args` is assumed to be a list of fvars.
When possible, `p ∧ q` is used instead of `∃(_ : p), q`. -/
def mkExistsLst (args : List Expr) (inner : Expr) : MetaM Expr :=
args.foldrM (λarg i:Expr => do
    let t ← inferType arg
    let l := (← inferType t).sortLevel!
    pure $ if arg.occurs i || l != Level.zero
      then mkApp2 (mkConst `Exists [l] : Expr) t (←(mkLambdaFVars #[arg] i))
      else mkApp2 (mkConst `And [] : Expr) t i)
  inner

/-- `mkOpLst op empty [x1, x2, ...]` is defined as `op x1 (op x2 ...)`.
  Returns `empty` if the list is empty. -/
def mkOpLst (op : Expr) (empty : Expr) : List Expr → Expr
| []        => empty
| [e]       => e
| (e :: es) => mkApp2 op e $ mkOpLst op empty es

/-- `mkAndLst [x1, x2, ...]` is defined as `x1 ∧ (x2 ∧ ...)`, or `True` if the list is empty. -/
def mkAndLst : List Expr → Expr := mkOpLst (mkConst `And) (mkConst `True)

/-- `mkOrLst [x1, x2, ...]` is defined as `x1 ∨ (x2 ∨ ...)`, or `False` if the list is empty. -/
def mkOrLst : List Expr → Expr := mkOpLst (mkConst `Or) (mkConst `False)

def init : List α → List α
| []     => []
| [_]    => []
| a::l => a::init l

/--
`params` is the leading params
`idxs` is the remaining params, i.e. the "indices"
-/
def constrToProp (univs : List Level) (params : List Expr) (idxs : List Expr) (c : Name) :
  MetaM ((List (Option Expr) × (Expr ⊕ Nat)) × Expr)  :=
do let type := (← getConstInfo c).instantiateTypeLevelParams univs
   dbg_trace f!"type: {type}"
   let type' ← Meta.forallBoundedTelescope type (params.length) fun fvars ty => do
     pure $ ty.replaceFVars fvars params.toArray

   dbg_trace f!"univs: {univs}"
   dbg_trace f!"type': {type'}"
   dbg_trace f!"params: {params}"
   dbg_trace f!"idxs: {idxs}"

   Meta.forallTelescope type' fun fvars ty => do
     dbg_trace f!"inner fvars: {fvars}"
     dbg_trace f!"inner ty: {ty}"
     let idxs_inst := ty.getAppArgs.toList.drop params.length
     dbg_trace f!"idxs_inst: {idxs_inst}"
     let (bs, eqs, subst) := compactRelation fvars.toList (idxs.zip idxs_inst)
     let bs' := bs.filterMap id
     let eqs ← eqs.mapM (λ⟨idx, inst⟩ => do
          let ty ← idx.fvarId!.getType
          let instTy ← inferType inst
          let u := (←inferType ty).sortLevel!
          if ←isDefEq ty instTy
          then pure (mkApp3 (mkConst `Eq [u]) ty idx inst)
          else pure (mkApp4 (mkConst `HEq [u]) ty idx instTy inst))
     let (n, r) ← match bs', eqs with
     | [], [] => do
           pure (Sum.inr 0, (mkConst `True))
     | _, []  => do
          let t : Expr ← bs'.getLast!.fvarId!.getType
          let t := subst t
          let l := (←inferType t).sortLevel!
          if l == Level.zero then do
            let r ← mkExistsLst (init bs') t
            pure (Sum.inl bs'.getLast!, r)
          else do
            let r ← mkExistsLst bs' (mkConst `True)
            pure (Sum.inr 0, r)
     | _, _ => do
       let r ← mkExistsLst bs' (mkAndLst eqs)
       pure (Sum.inr eqs.length, subst r)
     pure ((bs, n), r)

/--
  Proves the left to right direction.
-/
def toCases (mvar : MVarId) (shape : List $ List (Option Expr) × (Expr ⊕ ℕ)) : MetaM Unit :=
do
  let ty ← instantiateMVars (←mvar.getType)
  dbg_trace f!"mvar type = {ty}"
  let ⟨h, mvar'⟩ ← mvar.intro1
  let _ ← Elab.Term.TermElabM.run $ Elab.Tactic.run mvar' do
      Elab.Tactic.evalTactic (←`(tactic| admit))
      pure ()
  pure ()

/- 
  i ← induction h,
  focus ((s.zip i).enum.map $ λ⟨p, (shape, t), _, vars, _⟩, do
    let si := (shape.zip vars).filter_map (λ⟨c, v⟩, c >>= λ _, some v),
    select p (s.length - 1),
    match t with
    | sum.inl e := do
      si.init.mmap' existsi,
      some v ← return $ vars.nth (shape.length - 1),
      exact v
    | sum.inr n := do
      si.mmap' existsi,
      iterate_exactly (n - 1) (split >> constructor >> skip) >> constructor >> skip
    end,
    done),
  done -/

def mkIffOfInductivePropImpl (ind : Name) (rel : Name) : MetaM Unit := do
  let constInfo ← getConstInfo ind
  let inductVal ← match constInfo with
                  | .inductInfo info => pure info
                  | _ => throwError "mk_iff only applies to inductive declarations"
  let constrs := inductVal.ctors
  let params := inductVal.numParams
  let type := inductVal.type

  let univNames := inductVal.levelParams
  let univs := univNames.map mkLevelParam
  /- we use these names for our universe parameters, maybe we should construct a copy of them
  using `uniq_name` -/

  let (thmTy,shape) ← Meta.forallTelescope type fun fvars ty => do
    if !ty.isProp then throwError "mk_iff only applies to prop-valued declarations"
    let lhs := mkAppN (mkConst ind univs) fvars
    let fvars' := fvars.toList
    let shape_rhss ← constrs.mapM (constrToProp univs (fvars'.take params) (fvars'.drop params))
    let (shape, rhss) := shape_rhss.unzip
    pure (←mkForallFVars fvars (mkApp2 (mkConst `Iff) lhs (mkOrLst rhss)),
          shape)

  dbg_trace f!"thmTy = {thmTy}"

  let mvar ← mkFreshExprMVar (some thmTy)
  let mvarId := mvar.mvarId!
  let (fvars, mvarId') ← mvarId.intros
  let [mp, mpr] ← mvarId'.apply (mkConst `Iff.intro) | throwError "failed to split goal"

  let () ← toCases mp shape

  let _ ← Elab.Term.TermElabM.run $ Elab.Tactic.run mpr do
      Elab.Tactic.evalTactic (←`(tactic| admit))
      pure ()


  let decl : Declaration := .thmDecl {
        name := rel
        levelParams := univNames
        type := thmTy
        value := ← instantiateMVars mvar
      }

  addDecl decl
  pure ()

#check Expr.mvarId!
#check mkFreshExprMVar
#check Elab.Term.TermElabM
#check Elab.Tactic.TacticM
#check Elab.Tactic.evalTactic

syntax (name := mkIff) "mk_iff" (ppSpace ident)? : attr
syntax (name := mkIffOfInductiveProp) "mk_iff_of_inductive_prop" ident ident : command

elab_rules : command
| `(command| mk_iff_of_inductive_prop $i:ident $r:ident) =>
    Elab.Command.liftCoreM do
      Lean.Meta.MetaM.run' do
        mkIffOfInductivePropImpl i.getId r.getId

initialize Lean.registerBuiltinAttribute {
  name := `mkIff
  descr := "Generate an `iff` lemma for an inductive `Prop`."
  add := fun decl stx _ => Lean.Meta.MetaM.run' do
    let tgt ← (match stx with
               | `(attr| mk_iff $tgt:ident) => pure tgt.getId
               | `(attr| mk_iff) => match decl with
                                    | .str parent base => pure (Name.mkStr parent (base ++ "_iff"))
                                    | _ => throwError "mk_iff only works with string names"
               | _ => throwError "unrecognized syntax")
    mkIffOfInductivePropImpl decl tgt
}
