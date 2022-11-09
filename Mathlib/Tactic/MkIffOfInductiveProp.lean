/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, David Renshaw
-/
import Lean
import Mathlib.Tactic.Existsi
import Mathlib.Tactic.LeftRight

/-!
# mk_iff_of_inductive_prop

This file defines a tactic `tactic.mk_iff_of_inductive_prop` that generates `iff` rules for
inductive `Prop`s. For example, when applied to `List.Chain`, it creates a declaration with
the following type:

```lean
∀{α : Type _} (R : α → α → Prop) (a : α) (l : List α),
  Chain R a l ↔ l = [] ∨ ∃(b : α) (l' : list α), R a b ∧ Chain R b l ∧ l = b :: l'
```

This tactic can be called using either the `mk_iff_of_inductive_prop` user command or
the `mk_iff` attribute.
-/

namespace Mathlib.Tactic.MkIff

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

/-- Drops the final element of a list. -/
def List.init : List α → List α
| []     => []
| [_]    => []
| a::l => a::init l

/-- Converts an inductive constructor `c` into an intermediate representation that
will later be mapped into a proposition.
-/
def constrToProp (univs : List Level) (params : List Expr) (idxs : List Expr) (c : Name) :
  MetaM ((List (Option Expr) × (Expr ⊕ Nat)) × Expr)  :=
do let type := (← getConstInfo c).instantiateTypeLevelParams univs
   let type' ← Meta.forallBoundedTelescope type (params.length) fun fvars ty => do
     pure $ ty.replaceFVars fvars params.toArray

   Meta.forallTelescope type' fun fvars ty => do
     let idxs_inst := ty.getAppArgs.toList.drop params.length
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
            let r ← mkExistsLst (List.init bs') t
            pure (Sum.inl bs'.getLast!, subst r)
          else do
            let r ← mkExistsLst bs' (mkConst `True)
            pure (Sum.inr 0, subst r)
     | _, _ => do
       let r ← mkExistsLst bs' (mkAndLst eqs)
       pure (Sum.inr eqs.length, subst r)
     pure ((bs, n), r)

/-- Has the effect of `refine ⟨e, ?_⟩`.
-/
def existsi (mvar : MVarId) (e : Expr) : MetaM MVarId := do
  let (subgoals,_) ← Elab.Term.TermElabM.run $ Elab.Tactic.run mvar do
    Elab.Tactic.evalTactic (←`(tactic| refine ⟨?_,?_⟩))
  let [sg1, sg2] := subgoals | throwError "expected two subgoals"
  sg1.assign e
  pure sg2

/-- Splits the goal `n` times via `refine ⟨?_,?_⟩, and then applies `constructor` to
close the resulting subgoals.
-/
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

/-- Proves the left to right direction of a generated iff theorem.
`shape` is the output of a call to `constrToProp`.
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
      let mv ← (List.init si).foldlM existsi mvar''
      mv.assign v
    | Sum.inr n => do
      let mv ← si.foldlM existsi mvar''
      splitThenConstructor mv (n - 1)
  pure ()

/-- Calls `cases` on `h` (assumed to be a binary sum) `n` times, and returns
the resulting subgoals and their corresponding new hypotheses.
-/
def nCasesSum (n : Nat) (mvar : MVarId) (h : FVarId) : MetaM (List (FVarId × MVarId)) :=
match n with
| 0 => pure [(h, mvar)]
| n' + 1 => do
  let #[sg1, sg2] ← mvar.cases h | throwError "expected two case subgoals"
  let #[Expr.fvar fvar1] ← pure sg1.fields | throwError "expected fvar"
  let #[Expr.fvar fvar2] ← pure sg2.fields | throwError "expected fvar"
  let rest ← nCasesSum n' sg2.mvarId fvar2
  pure ((fvar1, sg1.mvarId)::rest)

/-- Calls `cases` on `h` (assumed to be a binary product) `n` times, and returns
the resulting subgoal and the new hypotheses.
-/
def nCasesProd (n : Nat) (mvar : MVarId) (h : FVarId) : MetaM (MVarId × List FVarId) :=
match n with
| 0 => pure (mvar, [h])
| n' + 1 => do
  let #[sg] ← mvar.cases h | throwError "expected one case subgoals"
  let #[Expr.fvar fvar1, Expr.fvar fvar2] ← pure sg.fields | throwError "expected fvar"
  let (mvar', rest) ← nCasesProd n' sg.mvarId fvar2
  pure (mvar', fvar1::rest)

/--
Iterate over two lists, if the first element of the first list is `none`, insert `none` into the
result and continue with the tail of first list. Otherwise, wrap the first element of the second
list with `some` and continue with the tails of both lists. Return when either list is empty.

Example:
```
listOptionMerge [none, some (), none, some ()] [0, 1, 2, 3, 4] = [none, (some 0), none, (some 1)]
```
-/
def listOptionMerge {α : Type _} {β : Type _} : List (Option α) → List β → List (Option β)
| [], _ => []
| none :: xs, ys => none :: listOptionMerge xs ys
| some _ :: xs, y :: ys => some y :: listOptionMerge xs ys
| some _ :: _, [] => []

/-- Finds a proof for the the right-to-left subgoal `mvar`.
-/
def toInductive (mvar : MVarId) (cs : List Name)
  (gs : List Expr) (s : List (List (Option Expr) × (Expr ⊕ Nat))) (h : FVarId) :
  MetaM Unit := do
  match s.length with
  | 0       => do let _ ← mvar.cases h
                  pure ()
  | (n + 1) => do
      let subgoals ← nCasesSum n mvar h
      let _ ← (cs.zip (subgoals.zip s)).mapM $ λ⟨constr_name, ⟨h, mv⟩, bs, e⟩ => do
        let n := (bs.filterMap id).length
        let (mvar', _fvars) ← match e with
        | Sum.inl _ => nCasesProd (n-1) mv h
        | Sum.inr 0 => do let ⟨mvar', fvars⟩ ← nCasesProd n mv h
                          let mvar'' ← mvar'.tryClear fvars.getLast!
                          pure ⟨mvar'', fvars⟩
        | Sum.inr (e + 1) => do
           let (mv', fvars) ← nCasesProd n mv h
           let lastfv := fvars.getLast!
           let (mv2, fvars') ← nCasesProd e mv' lastfv
           let (_, mv3) ← mv2.revert fvars'.toArray
           let mv4 ← fvars'.foldlM (λ mv _ => do let ⟨fv, mv'⟩ ← mv.intro1
                                                 subst mv' fv
                                   ) mv3
           pure (mv4, fvars ++ fvars')
        mvar'.withContext do
          let ctxt ← getLCtx
          let fvarIds := ctxt.getFVarIds.toList
          let gs := fvarIds.take gs.length
          let hs := (fvarIds.reverse.take n).reverse
          let m := gs.map some ++ listOptionMerge bs hs
          let args ← m.mapM (λa => match a with
                                   | some v => pure $ mkFVar v
                                   | none => mkFreshExprMVar none)
          let c ← mkConstWithFreshMVarLevels constr_name
          let e := mkAppN c args.toArray
          let t ← inferType e
          let mt ← mvar'.getType
          let _ ← isDefEq t mt -- infer values for those mvars we just made
          mvar'.assign e

/-- Implementation for both `mk_iff` and `mk_iff_of_inductive_prop`.
-/
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

  let mvar ← mkFreshExprMVar (some thmTy)
  let mvarId := mvar.mvarId!
  let (fvars, mvarId') ← mvarId.intros
  let [mp, mpr] ← mvarId'.apply (mkConst `Iff.intro) | throwError "failed to split goal"

  toCases mp shape

  let ⟨mprFvar, mpr'⟩ ← mpr.intro1
  toInductive mpr' constrs ((fvars.toList.take params).map .fvar) shape mprFvar

  addDecl $ .thmDecl {
    name := rel
    levelParams := univNames
    type := thmTy
    value := ← instantiateMVars mvar
  }

/--
Applying the `mk_iff` attribute to an inductively-defined proposition `mk_iff` makes an `iff` rule
`r` with the shape `∀ps is, i as ↔ ⋁_j, ∃cs, is = cs`, where `ps` are the type parameters, `is` are
the indices, `j` ranges over all possible constructors, the `cs` are the parameters for each of the
constructors, and the equalities `is = cs` are the instantiations for each constructor for each of
the indices to the inductive type `i`.

In each case, we remove constructor parameters (i.e. `cs`) when the corresponding equality would
be just `c = i` for some index `i`.

For example, if we try the following:
```lean
@[mk_iff]
structure foo (m n : Nat) : Prop where
  equal : m = n
  sum_eq_two : m + n = 2
```

Then `#check foo_iff` returns:
```lean
foo_iff : ∀ (m n : Nat), foo m n ↔ m = n ∧ m + n = 2
```

You can add an optional string after `mk_iff` to change the name of the generated lemma.
For example, if we try the following:
```lean
@[mk_iff bar]
structure foo (m n : Nat) : Prop where
  equal : m = n
  sum_eq_two : m + n = 2
```

Then `#check bar` returns:
```lean
bar : ∀ (m n : ℕ), foo m n ↔ m = n ∧ m + n = 2
```

See also the user command `mk_iff_of_inductive_prop`.
-/
syntax (name := mkIff) "mk_iff" (ppSpace ident)? : attr

/--
`mk_iff_of_inductive_prop i r` makes an `iff` rule for the inductively-defined proposition `i`.
The new rule `r` has the shape `∀ps is, i as ↔ ⋁_j, ∃cs, is = cs`, where `ps` are the type
parameters, `is` are the indices, `j` ranges over all possible constructors, the `cs` are the
parameters for each of the constructors, and the equalities `is = cs` are the instantiations for
each constructor for each of the indices to the inductive type `i`.

In each case, we remove constructor parameters (i.e. `cs`) when the corresponding equality would
be just `c = i` for some index `i`.

For example, `mk_iff_of_inductive_prop` on `List.Chain` produces:

```lean
∀ {α : Type _} (R : α → α → Prop) (a : α) (l : List α),
  Chain R a l ↔ l = [] ∨ ∃(b : α) (l' : list α), R a b ∧ Chain R b l ∧ l = b :: l'
```

See also the `mk_iff` user attribute.
-/
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
