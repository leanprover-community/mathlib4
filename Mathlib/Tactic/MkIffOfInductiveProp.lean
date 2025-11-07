/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, David Renshaw
-/
import Lean.Elab.DeclarationRange
import Lean.Meta.Tactic.Cases
import Mathlib.Lean.Meta
import Mathlib.Lean.Name
import Mathlib.Tactic.TypeStar

/-!
# mk_iff_of_inductive_prop

This file defines a command `mk_iff_of_inductive_prop` that generates `iff` rules for
inductive `Prop`s. For example, when applied to `List.Chain`, it creates a declaration with
the following type:

```lean
∀ {α : Type*} (R : α → α → Prop) (a : α) (l : List α),
  Chain R a l ↔ l = [] ∨ ∃ (b : α) (l' : List α), R a b ∧ Chain R b l ∧ l = b :: l'
```

This tactic can be called using either the `mk_iff_of_inductive_prop` user command or
the `mk_iff` attribute.
-/

namespace Mathlib.Tactic.MkIff

open Lean Meta Elab

/-- `select m n` runs `right` `m` times; if `m < n`, then it also runs `left` once.
Fails if `n < m`. -/
private def select (m n : Nat) (goal : MVarId) : MetaM MVarId :=
  match m,n with
  | 0, 0             => pure goal
  | 0, (_ + 1)       => do
    let [new_goal] ← goal.nthConstructor `left 0 (some 2)
      | throwError "expected only one new goal"
    pure new_goal
  | (m + 1), (n + 1) => do
    let [new_goal] ← goal.nthConstructor `right 1 (some 2)
      | throwError "expected only one new goal"
    select m n new_goal
  | _, _             => failure

/-- `compactRelation bs as_ps`: Produce a relation of the form:
```lean
R := fun as ↦ ∃ bs, ⋀_i a_i = p_i[bs]
```
This relation is user-visible, so we compact it by removing each `b_j` where a `p_i = b_j`, and
hence `a_i = b_j`. We need to take care when there are `p_i` and `p_j` with `p_i = p_j = b_k`.
-/
partial def compactRelation :
    List Expr → List (Expr × Expr) → List (Option Expr) × List (Expr × Expr) × (Expr → Expr)
| [],    as_ps => ([], as_ps, id)
| b::bs, as_ps =>
  match as_ps.span (fun ⟨_, p⟩ ↦ p != b) with
    | (_, []) => -- found nothing in ps equal to b
      let (bs, as_ps', subst) := compactRelation bs as_ps
      (b::bs, as_ps', subst)
    | (ps₁, (a, _) :: ps₂) => -- found one that matches b. Remove it.
      let i := fun e ↦ e.replaceFVar b a
      let (bs, as_ps', subst) :=
        compactRelation (bs.map i) ((ps₁ ++ ps₂).map (fun ⟨a, p⟩ ↦ (a, i p)))
      (none :: bs, as_ps', i ∘ subst)

private def updateLambdaBinderInfoD! (e : Expr) : Expr :=
  match e with
  | .lam n domain body _ => .lam n domain body .default
  | _           => panic! "lambda expected"

/-- Generates an expression of the form `∃ (args), inner`. `args` is assumed to be a list of fvars.
When possible, `p ∧ q` is used instead of `∃ (_ : p), q`. -/
def mkExistsList (args : List Expr) (inner : Expr) : MetaM Expr :=
  args.foldrM
    (fun arg i:Expr => do
      let t ← inferType arg
      let l := (← inferType t).sortLevel!
      if arg.occurs i || l != Level.zero
        then pure (mkApp2 (.const `Exists [l]) t
          (updateLambdaBinderInfoD! <| ← mkLambdaFVars #[arg] i))
        else pure <| mkApp2 (mkConst `And) t i)
    inner

/-- `mkOpList op empty [x1, x2, ...]` is defined as `op x1 (op x2 ...)`.
  Returns `empty` if the list is empty. -/
def mkOpList (op : Expr) (empty : Expr) : List Expr → Expr
  | []        => empty
  | [e]       => e
  | (e :: es) => mkApp2 op e <| mkOpList op empty es

/-- `mkAndList [x1, x2, ...]` is defined as `x1 ∧ (x2 ∧ ...)`, or `True` if the list is empty. -/
def mkAndList : List Expr → Expr := mkOpList (mkConst `And) (mkConst `True)

/-- `mkOrList [x1, x2, ...]` is defined as `x1 ∨ (x2 ∨ ...)`, or `False` if the list is empty. -/
def mkOrList : List Expr → Expr := mkOpList (mkConst `Or) (mkConst `False)

/-- Drops the final element of a list. -/
def List.init {α : Type*} : List α → List α
  | []     => []
  | [_]    => []
  | a::l => a::init l

/-- Auxiliary data associated with a single constructor of an inductive declaration.
-/
structure Shape : Type where
  /-- For each forall-bound variable in the type of the constructor, minus
  the "params" that apply to the entire inductive type, this list contains `true`
  if that variable has been kept after `compactRelation`.

  For example, `List.Chain.nil` has type
  ```lean
    ∀ {α : Type u_1} {R : α → α → Prop} {a : α}, List.Chain R a []
  ```
  and the first two variables `α` and `R` are "params", while the `a : α` gets
  eliminated in a `compactRelation`, so `variablesKept = [false]`.

  `List.Chain.cons` has type
  ```lean
    ∀ {α : Type u_1} {R : α → α → Prop} {a b : α} {l : List α},
       R a b → List.Chain R b l → List.Chain R a (b :: l)
  ```
  and the `a : α` gets eliminated, so `variablesKept = [false,true,true,true,true]`.
  -/
  variablesKept : List Bool

  /-- The number of equalities, or `none` in the case when we've reduced something
  of the form `p ∧ True` to just `p`.
  -/
  neqs : Option Nat

/-- Converts an inductive constructor `c` into a `Shape` that will be used later in
while proving the iff theorem, and a proposition representing the constructor.
-/
def constrToProp (univs : List Level) (params : List Expr) (idxs : List Expr) (c : Name) :
    MetaM (Shape × Expr) := do
  let type := (← getConstInfo c).instantiateTypeLevelParams univs
  let type' ← Meta.forallBoundedTelescope type (params.length) fun fvars ty ↦ do
    pure <| ty.replaceFVars fvars params.toArray
  Meta.forallTelescope type' fun fvars ty ↦ do
    let idxs_inst := ty.getAppArgs.toList.drop params.length
    let (bs, eqs, subst) := compactRelation fvars.toList (idxs.zip idxs_inst)
    let eqs ← eqs.mapM (fun ⟨idx, inst⟩ ↦ do
      let ty ← idx.fvarId!.getType
      let instTy ← inferType inst
      let u := (← inferType ty).sortLevel!
      if ← isDefEq ty instTy
      then pure (mkApp3 (.const `Eq [u]) ty idx inst)
      else pure (mkApp4 (.const `HEq [u]) ty idx instTy inst))
    let (n, r) ← match bs.filterMap id, eqs with
    | [], [] => do
      pure (some 0, (mkConst `True))
    | bs', [] => do
      let t : Expr ← bs'.getLast!.fvarId!.getType
      let l := (← inferType t).sortLevel!
      if l == Level.zero then do
        let r ← mkExistsList (List.init bs') t
        pure (none, subst r)
      else do
        let r ← mkExistsList bs' (mkConst `True)
        pure (some 0, subst r)
    | bs', _ => do
      let r ← mkExistsList bs' (mkAndList eqs)
      pure (some eqs.length, subst r)
    pure (⟨bs.map Option.isSome, n⟩, r)

/-- Splits the goal `n` times via `refine ⟨?_,?_⟩`, and then applies `constructor` to
close the resulting subgoals.
-/
def splitThenConstructor (mvar : MVarId) (n : Nat) : MetaM Unit :=
match n with
| 0   => do
  let (subgoals',_) ← Term.TermElabM.run <| Tactic.run mvar do
    Tactic.evalTactic (← `(tactic| constructor))
  let [] := subgoals' | throwError "expected no subgoals"
  pure ()
| n + 1 => do
  let (subgoals,_) ← Term.TermElabM.run <| Tactic.run mvar do
    Tactic.evalTactic (← `(tactic| refine ⟨?_,?_⟩))
  let [sg1, sg2] := subgoals | throwError "expected two subgoals"
  let (subgoals',_) ← Term.TermElabM.run <| Tactic.run sg1 do
    Tactic.evalTactic (← `(tactic| constructor))
  let [] := subgoals' | throwError "expected no subgoals"
  splitThenConstructor sg2 n

/-- Proves the left to right direction of a generated iff theorem.
`shape` is the output of a call to `constrToProp`.
-/
def toCases (mvar : MVarId) (shape : List Shape) : MetaM Unit :=
do
  let ⟨h, mvar'⟩ ← mvar.intro1
  let subgoals ← mvar'.cases h
  let _ ← (shape.zip subgoals.toList).zipIdx.mapM fun ⟨⟨⟨shape, t⟩, subgoal⟩, p⟩ ↦ do
    let vars := subgoal.fields
    let si := (shape.zip vars.toList).filterMap (fun ⟨c,v⟩ ↦ if c then some v else none)
    let mvar'' ← select p (subgoals.size - 1) subgoal.mvarId
    match t with
    | none => do
      let v := vars[shape.length - 1]!
      let mv ← mvar''.existsi (List.init si)
      mv.assign v
    | some n => do
      let mv ← mvar''.existsi si
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
Iterate over two lists, if the first element of the first list is `false`, insert `none` into the
result and continue with the tail of first list. Otherwise, wrap the first element of the second
list with `some` and continue with the tails of both lists. Return when either list is empty.

Example:
```
listBoolMerge [false, true, false, true] [0, 1, 2, 3, 4] = [none, (some 0), none, (some 1)]
```
-/
def listBoolMerge {α : Type*} : List Bool → List α → List (Option α)
  | [], _ => []
  | false :: xs, ys => none :: listBoolMerge xs ys
  | true :: xs, y :: ys => some y :: listBoolMerge xs ys
  | true :: _, [] => []

/-- Proves the right to left direction of a generated iff theorem.
-/
def toInductive (mvar : MVarId) (cs : List Name)
    (gs : List Expr) (s : List Shape) (h : FVarId) :
    MetaM Unit := do
  match s.length with
  | 0       => do let _ ← mvar.cases h
                  pure ()
  | (n + 1) => do
      let subgoals ← nCasesSum n mvar h
      let _ ← (cs.zip (subgoals.zip s)).mapM fun ⟨constr_name, ⟨h, mv⟩, bs, e⟩ ↦ do
        let n := (bs.filter id).length
        let (mvar', _fvars) ← match e with
        | none => nCasesProd (n-1) mv h
        | some 0 => do let ⟨mvar', fvars⟩ ← nCasesProd n mv h
                          let mvar'' ← mvar'.tryClear fvars.getLast!
                          pure ⟨mvar'', fvars⟩
        | some (e + 1) => do
           let (mv', fvars) ← nCasesProd n mv h
           let lastfv := fvars.getLast!
           let (mv2, fvars') ← nCasesProd e mv' lastfv

           /- `fvars'.foldlM subst mv2` fails when we have dependent equalities (`HEq`).
           `subst` will change the dependent hypotheses, so that the `uniq` local names
           are wrong afterwards. Instead we revert them and pull them out one-by-one. -/
           let (_, mv3) ← mv2.revert fvars'.toArray
           let mv4 ← fvars'.foldlM (fun mv _ ↦ do let ⟨fv, mv'⟩ ← mv.intro1; subst mv' fv) mv3
           pure (mv4, fvars)
        mvar'.withContext do
          let fvarIds := (← getLCtx).getFVarIds.toList
          let gs := fvarIds.take gs.length
          let hs := (fvarIds.reverse.take n).reverse
          let m := gs.map some ++ listBoolMerge bs hs
          let args ← m.mapM fun a ↦
            match a with
            | some v => pure (mkFVar v)
            | none => mkFreshExprMVar none
          let c ← mkConstWithFreshMVarLevels constr_name
          let e := mkAppN c args.toArray
          let t ← inferType e
          let mt ← mvar'.getType
          let _ ← isDefEq t mt -- infer values for those mvars we just made
          mvar'.assign e

/-- Implementation for both `mk_iff` and `mk_iff_of_inductive_prop`.
-/
def mkIffOfInductivePropImpl (ind : Name) (rel : Name) (relStx : Syntax) : MetaM Unit := do
  let .inductInfo inductVal ← getConstInfo ind |
    throwError "mk_iff only applies to inductive declarations"
  let constrs := inductVal.ctors
  let params := inductVal.numParams
  let type := inductVal.type

  let univNames := inductVal.levelParams
  let univs := univNames.map mkLevelParam
  /- we use these names for our universe parameters, maybe we should construct a copy of them
  using `uniq_name` -/

  let (thmTy, shape) ← Meta.forallTelescope type fun fvars ty ↦ do
    if !ty.isProp then throwError "mk_iff only applies to prop-valued declarations"
    let lhs := mkAppN (mkConst ind univs) fvars
    let fvars' := fvars.toList
    let shape_rhss ← constrs.mapM (constrToProp univs (fvars'.take params) (fvars'.drop params))
    let (shape, rhss) := shape_rhss.unzip
    pure (← mkForallFVars fvars (mkApp2 (mkConst `Iff) lhs (mkOrList rhss)), shape)

  let mvar ← mkFreshExprMVar (some thmTy)
  let mvarId := mvar.mvarId!
  let (fvars, mvarId') ← mvarId.intros
  let [mp, mpr] ← mvarId'.apply (mkConst `Iff.intro) | throwError "failed to split goal"

  toCases mp shape

  let ⟨mprFvar, mpr'⟩ ← mpr.intro1
  toInductive mpr' constrs ((fvars.toList.take params).map .fvar) shape mprFvar

  addDecl <| .thmDecl {
    name := rel
    levelParams := univNames
    type := thmTy
    value := ← instantiateMVars mvar
  }
  addDeclarationRangesFromSyntax rel (← getRef) relStx
  addConstInfo relStx rel

/--
Applying the `mk_iff` attribute to an inductively-defined proposition `mk_iff` makes an `iff` rule
`r` with the shape `∀ ps is, i as ↔ ⋁_j, ∃ cs, is = cs`, where
* `ps` are the type parameters,
* `is` are the indices,
* `j` ranges over all possible constructors,
* the `cs` are the parameters for each of the constructors, and
* the equalities `is = cs` are the instantiations for each constructor for each of
  the indices to the inductive type `i`.

In each case, we remove constructor parameters (i.e. `cs`) when the corresponding equality would
be just `c = i` for some index `i`.

For example, if we try the following:
```lean
@[mk_iff]
structure Foo (m n : Nat) : Prop where
  equal : m = n
  sum_eq_two : m + n = 2
```

Then `#check foo_iff` returns:
```lean
foo_iff : ∀ (m n : Nat), Foo m n ↔ m = n ∧ m + n = 2
```

You can add an optional string after `mk_iff` to change the name of the generated lemma.
For example, if we try the following:
```lean
@[mk_iff bar]
structure Foo (m n : Nat) : Prop where
  equal : m = n
  sum_eq_two : m + n = 2
```

Then `#check bar` returns:
```lean
bar : ∀ (m n : ℕ), Foo m n ↔ m = n ∧ m + n = 2
```

See also the user command `mk_iff_of_inductive_prop`.
-/
syntax (name := mkIff) "mk_iff" (ppSpace ident)? : attr

/--
`mk_iff_of_inductive_prop i r` makes an `iff` rule for the inductively-defined proposition `i`.
The new rule `r` has the shape `∀ ps is, i as ↔ ⋁_j, ∃ cs, is = cs`, where
* `ps` are the type parameters,
* `is` are the indices,
* `j` ranges over all possible constructors,
* the `cs` are the parameters for each of the constructors, and
* the equalities `is = cs` are the instantiations for
  each constructor for each of the indices to the inductive type `i`.

In each case, we remove constructor parameters (i.e. `cs`) when the corresponding equality would
be just `c = i` for some index `i`.

For example, `mk_iff_of_inductive_prop` on `List.Chain` produces:

```lean
∀ { α : Type*} (R : α → α → Prop) (a : α) (l : List α),
  Chain R a l ↔ l = [] ∨ ∃ (b : α) (l' : List α), R a b ∧ Chain R b l ∧ l = b :: l'
```

See also the `mk_iff` user attribute.
-/
syntax (name := mkIffOfInductiveProp) "mk_iff_of_inductive_prop " ident ppSpace ident : command

elab_rules : command
| `(command| mk_iff_of_inductive_prop $i:ident $r:ident) =>
    Command.liftCoreM <| MetaM.run' do
      mkIffOfInductivePropImpl i.getId r.getId r

initialize Lean.registerBuiltinAttribute {
  name := `mkIff
  descr := "Generate an `iff` lemma for an inductive `Prop`."
  add := fun decl stx _ => Lean.Meta.MetaM.run' do
    let (tgt, idStx) ← match stx with
      | `(attr| mk_iff $tgt:ident) =>
        pure ((← mkDeclName (← getCurrNamespace) {} tgt.getId).1, tgt.raw)
      | `(attr| mk_iff) => pure (decl.decapitalize.appendAfter "_iff", stx)
      | _ => throwError "unrecognized syntax"
    mkIffOfInductivePropImpl decl tgt idStx
}

end Mathlib.Tactic.MkIff
