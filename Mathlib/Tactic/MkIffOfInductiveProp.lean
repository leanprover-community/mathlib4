import Lean
import Mathlib.Tactic.Existsi
import Mathlib.Tactic.LeftRight

namespace Mathlib.Tactic

open Lean Meta

/-- `select m n` runs `tactic.right` `m` times, and then `tactic.left` `(n-m)` times.
Fails if `n < m`. -/
private def select (m n : Nat) (goal : MVarId) : MetaM MVarId :=
  match m,n with
  | 0, 0             => pure goal
  | 0, (_ + 1)       => do let [new_goal] ← Mathlib.Tactic.LeftRight.leftRightMeta `left 0 2 goal
                                | throwError "expected only one new goal"
                           pure new_goal
  | (m + 1), (n + 1) => do let [new_goal] ← Mathlib.Tactic.LeftRight.leftRightMeta `right 1 2 goal
                                | throwError "expected only one new goal"
                           select m n new_goal
  | _, _             => failure

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
   let type' ← Meta.forallBoundedTelescope type (params.length) fun fvars ty => do
     pure $ ty.replaceFVars fvars params.toArray

   dbg_trace f!"type': {type'}"

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
          let l := (←inferType t).sortLevel!
          if l == Level.zero then do
            let r ← mkExistsLst (init bs') t
            pure (Sum.inl bs'.getLast!, subst r)
          else do
            let r ← mkExistsLst bs' (mkConst `True)
            pure (Sum.inr 0, subst r)
     | _, _ => do
       let r ← mkExistsLst bs' (mkAndLst eqs)
       pure (Sum.inr eqs.length, subst r)
     pure ((bs, n), r)

def existsi (mvar : MVarId) (e : Expr) : MetaM MVarId := do
  let (subgoals,_) ← Elab.Term.TermElabM.run $ Elab.Tactic.run mvar do
    Elab.Tactic.evalTactic (←`(tactic| refine ⟨?_,?_⟩))
  let [sg1, sg2] := subgoals | throwError "expected two subgoals"
  sg1.assign e
  pure sg2

def splitThenConstructor (mvar : MVarId) (n : Nat) : MetaM Unit :=
match n with
| 0   => do
  let (subgoals',_) ← Elab.Term.TermElabM.run $ Elab.Tactic.run mvar do
    Elab.Tactic.evalTactic (←`(tactic| constructor))
  let [] := subgoals' | throwError "expected no subgoals"
  pure ()
| n  + 1 => do
  let (subgoals,_) ← Elab.Term.TermElabM.run $ Elab.Tactic.run mvar do
    Elab.Tactic.evalTactic (←`(tactic| refine ⟨?_,?_⟩))
  let [sg1, sg2] := subgoals | throwError "expected two subgoals"
  let (subgoals',_) ← Elab.Term.TermElabM.run $ Elab.Tactic.run sg1 do
    Elab.Tactic.evalTactic (←`(tactic| constructor))
  let [] := subgoals' | throwError "expected no subgoals"
  splitThenConstructor sg2 n

/--
  Proves the left to right direction.
-/
def toCases (mvar : MVarId) (shape : List $ List (Option Expr) × (Expr ⊕ Nat)) : MetaM Unit :=
do
  let ⟨h, mvar'⟩ ← mvar.intro1
  let subgoals ← mvar'.cases h
  let _ ← (shape.zip subgoals.toList).enum.mapM fun ⟨p, ⟨⟨shape, t⟩, subgoal⟩⟩ => do
    let vars := subgoal.fields
    let si := (shape.zip vars.toList).filterMap (λ ⟨c,v⟩ => c >>= λ _ => some v)
    let mvar'' ← select p (subgoals.size - 1) subgoal.mvarId
    match t with
    | Sum.inl _ => do
      let v := vars.get! (shape.length - 1)
      let mv ← (init si).foldlM existsi mvar''
      mv.assign v
    | Sum.inr n => do
      let mv ← si.foldlM existsi mvar''
      splitThenConstructor mv (n - 1)
  pure ()

def toInductive (mvar : MVarId) (cs : List Name)
  (gs : List Expr) (s : List (List (Option Expr) × (Expr ⊕ Nat))) (h : FVarId) :
  MetaM Unit := do
  match s.length with
  | 0       => do let _ ← mvar.cases h
                  pure ()
  | (n + 1) => do
      let _ ← Elab.Term.TermElabM.run $ Elab.Tactic.run mvar do
        Elab.Tactic.evalTactic (←`(tactic| admit))
        pure ()
      pure ()

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

  let ⟨mprFvar, mpr'⟩ ← mpr.intro1
  let () ← toInductive mpr' constrs
            ((fvars.toList.take params).map .fvar) shape mprFvar

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
