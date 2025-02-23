/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.Adjoin.FG

/-!
# Adjoining elements and being finitely generated in an algebra tower

## Main results

 * `Algebra.fg_trans'`: if `S` is finitely generated as `R`-algebra and `A` as `S`-algebra,
   then `A` is finitely generated as `R`-algebra
 * `fg_of_fg_of_fg`: **Artin--Tate lemma**: if C/B/A is a tower of rings, and A is noetherian, and
   C is algebra-finite over A, and C is module-finite over B, then B is algebra-finite over A.
-/

section drw

private theorem dcongrArg.{u, v} {α : Sort u} {a a' : α}
    {β : (a' : α) → @Eq α a a' → Sort v} (h : @Eq α a a')
    (f : (a' : α) → (h : @Eq α a a') → β a' h) :
    f a (@Eq.refl α a) =
    @Eq.rec α a' (fun x h' ↦ β x (@Eq.trans α a a' x h h')) (f a' h) a (@Eq.symm α a a' h) :=
  Eq.rec (Eq.refl (f a (Eq.refl a))) h

private theorem nddcongrArg.{u, v} {α : Sort u} {a a' : α}
    {β : Sort v} (h : @Eq α a a') (f : (a' : α) → (h : @Eq α a a') → β) :
    f a (@Eq.refl α a) = f a' h :=
  Eq.rec (Eq.refl (f a (Eq.refl a))) h

private theorem heqL.{u} {α β : Sort u} {a : α} {b : β} (h : @HEq α a β b) :
    @Eq α a (@cast β α (@Eq.symm (Sort u) α β (@type_eq_of_heq α β a b h)) b) :=
  HEq.rec (Eq.refl a) h

private theorem heqR.{u} {α β : Sort u} {a : α} {b : β} (h : @HEq α a β b) :
    @Eq β (@cast α β (@type_eq_of_heq α β a b h) a) b :=
  HEq.rec (Eq.refl a) h

namespace Lean.Meta

-- copied from Lean.Meta.kabstract
private partial def dabstract (e : Expr) (p : Expr) (occs : Occurrences := .all) : MetaM Expr := do
let e ← instantiateMVars e
let pHeadIdx := p.toHeadIndex
let pNumArgs := p.headNumArgs
let tp ← inferType p
withLocalDeclD `x tp fun x ↦ do withLocalDeclD `h (← mkEq p x) fun h ↦ do
  let rec visit (e : Expr) : StateRefT Nat MetaM Expr := do
    let visitChildren : Unit → StateRefT Nat MetaM Expr := fun _ => do
      match e with
      | .app f a =>
        let fup ← visit f
        let tfup ← inferType fup
        forallBoundedTelescope (← whnfD tfup) (some 1) fun xs _ ↦ do
          if let #[r] := xs then
            let tr ← inferType r
            let aup ← visit a
            let taup ← inferType aup
            if ← (withNewMCtxDepth <| isDefEq tr taup) then
              return e.updateApp! fup aup
            let motive ← withLocalDeclD `x' tp fun x' ↦ do
              withLocalDeclD `h' (← mkEq x x') fun h' ↦ do
              mkLambdaFVars #[x', h'] <| taup.replaceFVars #[x, h] #[x', ← mkEqTrans h h']
            let aup ← mkEqRec motive aup (← mkEqSymm h)
            let taup ← inferType aup
            if ← (withNewMCtxDepth <| isDefEq tr taup) then
              return e.updateApp! fup aup
            let motive ← mkLambdaFVars #[x, h] tr
            let aup ← mkEqRec motive aup h
            return e.updateApp! fup aup
          else throwFunctionExpected fup
      | .mdata _ b => return e.updateMData! (← visit b)
      | .proj _ _ b =>
        let tb ← inferType b
        let bup ← visit b
        let tbup ← inferType bup
        if ← (withNewMCtxDepth <| isDefEq tb tbup) then
          return e.updateProj! bup
        let motive ← withLocalDeclD `x' tp fun x' ↦ do withLocalDeclD `h' (← mkEq x x') fun h' ↦ do
          mkLambdaFVars #[x', h'] <| tbup.replaceFVars #[x, h] #[x', ← mkEqTrans h h']
        let bup ← mkEqRec motive bup (← mkEqSymm h)
        return e.updateProj! bup
      | .letE n t v b _ =>
        let tup ← visit t
        let vup ← visit v
        let tvup ← inferType vup
        if ← (withNewMCtxDepth <| isDefEq tup tvup) then
          -- why is there no `lambdaLetBoundedTelescope`
          return ← withLetDecl n tup vup fun l ↦ do
            let bup ← visit (b.instantiate1 l)
            return e.updateLet! tup vup (← mkLetFVars #[l] bup)
        let motive ← withLocalDeclD `x' tp fun x' ↦ do withLocalDeclD `h' (← mkEq x x') fun h' ↦ do
          mkLambdaFVars #[x', h'] <| tvup.replaceFVars #[x, h] #[x', ← mkEqTrans h h']
        let vup ← mkEqRec motive vup (← mkEqSymm h)
        let tvup ← inferType vup
        if ← (withNewMCtxDepth <| isDefEq tup tvup) then
          return ← withLetDecl n tup vup fun l ↦ do
            let motive ← do
              let motive ← withLocalDeclD `x' tp fun x' ↦ do
                withLocalDeclD `h' (← mkEq x x') fun h' ↦ do
                mkLambdaFVars #[x', h'] <| tup.replaceFVars #[x, h] #[x', ← mkEqTrans h h']
              mkEqRec motive l (← mkEqSymm h)
            let bup ← visit (b.instantiate1 motive)
            return e.updateLet! tup vup (← mkLetFVars #[l] bup)
        let motive ← mkLambdaFVars #[x, h] tup
        let vup ← mkEqRec motive vup h
        return ← withLetDecl n tup vup fun l ↦ do
          let motive ← do
            let motive ← withLocalDeclD `x' tp fun x' ↦ do
              withLocalDeclD `h' (← mkEq x x') fun h' ↦ do
              mkLambdaFVars #[x', h'] <| tup.replaceFVars #[x, h] #[x', ← mkEqTrans h h']
            let vf ← mkEqRec motive l (← mkEqSymm h)
            let motive ← mkLambdaFVars #[x, h] tup
            mkEqRec motive vf h
          let bup ← visit (b.instantiate1 motive)
          return e.updateLet! tup vup bup
      | .lam _ d b _ =>
        let dup ← visit d
        if ← (withNewMCtxDepth <| isDefEq d dup) then
          return ← lambdaBoundedTelescope (e.updateLambdaE! dup b) 1 fun xs c ↦ do
            let cup ← visit c
            mkLambdaFVars xs cup
        return ← lambdaBoundedTelescope (e.updateLambdaE! dup b) 1 fun xs c ↦ do
          let #[r] := xs | unreachable!
          let motive ← do
            let motive ← withLocalDeclD `x' tp fun x' ↦ do
              withLocalDeclD `h' (← mkEq x x') fun h' ↦ do
              mkLambdaFVars #[x', h'] <| dup.replaceFVars #[x, h] #[x', ← mkEqTrans h h']
            mkEqRec motive r (← mkEqSymm h)
          let cup ← visit (c.replaceFVar r motive)
          mkLambdaFVars xs cup
      | .forallE _ d b _ =>
        let dup ← visit d
        if ← (withNewMCtxDepth <| isDefEq d dup) then
          return ← forallBoundedTelescope (e.updateForallE! dup b) (some 1) fun xs c ↦ do
            let cup ← visit c
            mkForallFVars xs cup
        return ← forallBoundedTelescope (e.updateForallE! dup b) (some 1) fun xs c ↦ do
          let #[r] := xs | unreachable!
          let motive ← do
            let motive ← withLocalDeclD `x' tp fun x' ↦ do
              withLocalDeclD `h' (← mkEq x x') fun h' ↦ do
              mkLambdaFVars #[x', h'] <| dup.replaceFVars #[x, h] #[x', ← mkEqTrans h h']
            mkEqRec motive r (← mkEqSymm h)
          let cup ← visit (c.replaceFVar r motive)
          mkForallFVars xs cup
      | e => return e
    if ← isProof e then return e
    else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren ()
    else
      -- We save the metavariable context here,
      -- so that it can be rolled back unless `occs.contains i`.
      let mctx ← getMCtx
      if (← isDefEq e p) then
        let i ← get
        set (i + 1)
        if occs.contains i then
          return x
        else
          -- Revert the metavariable context,
          -- so that other matches are still possible.
          setMCtx mctx
          visitChildren ()
      else
        visitChildren ()
  mkLambdaFVars #[x, h] (← visit e |>.run' 1)

-- copied from Lean.MVarId.rewrite
/--
Rewrite goal `mvarId` dependently.
-/
def _root_.Lean.MVarId.depRewrite (mvarId : MVarId) (e : Expr) (heq : Expr)
    (symm : Bool := false) (config := { : Rewrite.Config }) : MetaM RewriteResult :=
mvarId.withContext do
mvarId.checkNotAssigned `drewrite
let heqIn := heq
let heqType ← instantiateMVars (← inferType heq)
let (newMVars, binderInfos, heqType) ← forallMetaTelescopeReducing heqType
let heq := mkAppN heq newMVars
let cont (heq heqType : Expr) : MetaM RewriteResult := do
  match (← matchEq? heqType) with
  | none => throwTacticEx `drewrite mvarId m!"equality or iff proof expected{indentExpr heqType}"
  | some (α, lhs, rhs) =>
    let cont (heq lhs rhs : Expr) : MetaM RewriteResult := do
      if lhs.getAppFn.isMVar then
        throwTacticEx `drewrite mvarId
          m!"pattern is a metavariable{indentExpr lhs}\nfrom equation{indentExpr heqType}"
      let e ← instantiateMVars e
      let eAbst ← withConfig (fun oldConfig => { config, oldConfig with }) <|
        dabstract e lhs config.occs
      let nAbst ← withLocalDeclD .anonymous α fun a ↦ do
        withLocalDeclD .anonymous (← mkEq lhs a) fun h ↦ do
          mkLambdaFVars #[a, h] e
      if ← withReducible (withNewMCtxDepth <| isDefEq eAbst nAbst) then
        throwTacticEx `drewrite mvarId
          m!"did not find instance of the pattern in the target expression{indentExpr lhs}"
      -- construct rewrite proof
      let eType ← inferType e
      let eNew := match (← instantiateMVars eAbst) with
        | .lam _ _ b _ => b.instantiate1 rhs
        | _ => .app eAbst rhs
      let eNew := match (← instantiateMVars eNew) with
        | .lam _ _ b _ => b.instantiate1 heq
        | _ => .app eNew heq
      let (motive, dep) ← withLocalDeclD `_a α fun a ↦ do
        withLocalDeclD `_h (← mkEq lhs a) fun h ↦ do
        let motive ← inferType (.app (.app eAbst a) h)
        return (← mkLambdaFVars #[a, h] motive, not (← withNewMCtxDepth <| isDefEq motive eType))
      unless (← isTypeCorrect eAbst) do
        throwTacticEx `drewrite mvarId m!"motive is not type correct{indentExpr eAbst}"
      let u1 ← getLevel α
      let u2 ← getLevel eType
      let (eNew, eqPrf) ← do
        if dep then
          let eNew ← withLocalDeclD `x α fun x ↦ do withLocalDeclD `h (← mkEq rhs x) fun h ↦ do
            let motive ← mkLambdaFVars #[x, h] (.app (.app motive x) (← mkEqTrans heq h))
            mkEqRec motive eNew (← mkEqSymm heq)
          pure (eNew, mkApp6 (.const ``dcongrArg [u1, u2]) α lhs rhs motive heq eAbst)
        else
          pure (eNew, mkApp6 (.const ``nddcongrArg [u1, u2]) α lhs rhs eType heq eAbst)
      postprocessAppMVars `drewrite mvarId newMVars binderInfos
        (synthAssignedInstances := !tactic.skipAssignedInstances.get (← getOptions))
      let newMVarIds ← newMVars.map Expr.mvarId! |>.filterM fun mvarId => not <$> mvarId.isAssigned
      let otherMVarIds ← getMVarsNoDelayed heqIn
      let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
      let newMVarIds := newMVarIds ++ otherMVarIds
      pure { eNew := eNew, eqProof := eqPrf, mvarIds := newMVarIds.toList }
    match symm with
    | false => cont heq lhs rhs
    | true  => do
      cont (← mkEqSymm heq) rhs lhs
match heqType.iff? with
| some (lhs, rhs) =>
  let heqType ← mkEq lhs rhs
  let heq := mkApp3 (mkConst ``propext) lhs rhs heq
  cont heq heqType
| none => match heqType.heq? with
  | some (α, lhs, β, rhs) =>
    let heq ← mkAppOptM (if symm then ``heqR else ``heqL) #[α, β, lhs, rhs, heq]
    cont heq (← inferType heq)
  | none =>
    cont heq heqType

/--
The configuration used by `rw!` to call `dsimp`.
This configuration uses only iota reduction (recursor application) to simplify terms.
-/
private def depRwContext : MetaM Simp.Context :=
  Simp.mkContext
    {Lean.Meta.Simp.neutralConfig with
     etaStruct := .none
     iota := true
     failIfUnchanged := false}

end Lean.Meta

namespace Lean.Parser.Tactic

-- copied from Init.Tactics
/--
`rewrite!` is like `rewrite`, but can handle terms whose type
correctness depends on the term being rewritten.
It is also available as a `conv` tactic.
-/
syntax (name := depRewriteSeq) "rewrite!" (config)? rwRuleSeq (location)? : tactic

/--
`rw!` is like `rewrite!`, but also calls `dsimp` to simplify the result after every substitution.
It is also available as a `conv` tactic.
-/
syntax (name := depRwSeq) "rw!" (config)? rwRuleSeq (location)? : tactic

end Lean.Parser.Tactic

-- copied from Lean.Elab.Tactic.Rewrite
namespace Lean.Elab.Tactic
open Meta

def depRewriteTarget (stx : Syntax) (symm : Bool) (config : Rewrite.Config := {}) :
    TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let r ← (← getMainGoal).depRewrite (← getMainTarget) e symm (config := config)
    let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (mvarId' :: r.mvarIds)

def depRewriteLocalDecl (stx : Syntax) (symm : Bool) (fvarId : FVarId)
    (config : Rewrite.Config := {}) : TacticM Unit := withMainContext do
  -- Note: we cannot execute `replaceLocalDecl` inside `Term.withSynthesize`.
  -- See issues #2711 and #2727.
  let rwResult ← Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let localDecl ← fvarId.getDecl
    (← getMainGoal).depRewrite localDecl.type e symm (config := config)
  let replaceResult ← (← getMainGoal).replaceLocalDecl fvarId rwResult.eNew rwResult.eqProof
  replaceMainGoal (replaceResult.mvarId :: rwResult.mvarIds)

@[tactic depRewriteSeq] def evalDepRewriteSeq : Tactic := fun stx => do
  let cfg ← elabRewriteConfig stx[1]
  let loc   := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (depRewriteLocalDecl term symm · cfg)
      (depRewriteTarget term symm cfg)
      (throwTacticEx `drewrite · "did not find instance of the pattern in the current goal")

@[tactic depRwSeq] def evalDepRwSeq : Tactic := fun stx => do
  let cfg ← elabRewriteConfig stx[1]
  let loc   := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (depRewriteLocalDecl term symm · cfg)
      (depRewriteTarget term symm cfg)
      (throwTacticEx `drewrite · "did not find instance of the pattern in the current goal")
    -- copied from Lean.Elab.Tactic.evalDSimp
    dsimpLocation (← depRwContext) #[] loc

end Lean.Elab.Tactic

namespace Lean.Parser.Tactic.Conv

-- copied from Init.Conv
/-- `rewrite! [thm]` rewrites the target dependently using `thm`.
See the `rewrite!` tactic for more information. -/
syntax (name := depRewrite) "rewrite!" (config)? rwRuleSeq (location)? : conv

/-- `rw! [thm]` rewrites the target using `thm`. See the `rw!` tactic for more information. -/
syntax (name := depRw) "rw!" (config)? rwRuleSeq (location)? : conv

end Lean.Parser.Tactic.Conv

namespace Lean.Elab.Tactic.Conv
open Meta

-- copied from Lean.Elab.Tactic.Conv.evalRewrite
def depRewriteTarget (stx : Syntax) (symm : Bool) (config : Rewrite.Config := {}) :
    TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let r ←  (← getMainGoal).depRewrite (← getLhs) e symm (config := config)
    updateLhs r.eNew r.eqProof
    replaceMainGoal ((← getMainGoal) :: r.mvarIds)

def depRwTarget (stx : Syntax) (symm : Bool) (config : Rewrite.Config := {}) : TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let r ←  (← getMainGoal).depRewrite (← getLhs) e symm (config := config)
    updateLhs r.eNew r.eqProof
    -- copied from Lean.Elab.Conv.Simp
    changeLhs (← dsimp (← getLhs) (← depRwContext)).1
    replaceMainGoal ((← getMainGoal) :: r.mvarIds)

def depRwLocalDecl (stx : Syntax) (symm : Bool) (fvarId : FVarId) (config : Rewrite.Config := {}) :
    TacticM Unit := withMainContext do
  -- Note: we cannot execute `replaceLocalDecl` inside `Term.withSynthesize`.
  -- See issues #2711 and #2727.
  let rwResult ← Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let localDecl ← fvarId.getDecl
    (← getMainGoal).depRewrite localDecl.type e symm (config := config)
  let replaceResult ← (← getMainGoal).replaceLocalDecl fvarId rwResult.eNew rwResult.eqProof
  let dsimpResult := (← dsimp rwResult.eNew (← depRwContext)).1
  let replaceResult ← replaceResult.mvarId.changeLocalDecl replaceResult.fvarId dsimpResult
  replaceMainGoal (replaceResult :: rwResult.mvarIds)

@[tactic Lean.Parser.Tactic.Conv.depRewrite]
def evalDepRewriteSeq : Tactic := fun stx => do
  let cfg ← elabRewriteConfig stx[1]
  let loc   := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (depRewriteLocalDecl term symm · cfg)
      (depRewriteTarget term symm cfg)
      (throwTacticEx `drewrite · "did not find instance of the pattern in the current goal")

@[tactic Lean.Parser.Tactic.Conv.depRw]
def evalDepRwSeq : Tactic := fun stx => do
  let cfg ← elabRewriteConfig stx[1]
  let loc   := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (depRwLocalDecl term symm · cfg)
      (depRwTarget term symm cfg)
      (throwTacticEx `drewrite · "did not find instance of the pattern in the current goal")
    -- Note: in this version of the tactic, `dsimp` is done inside `withLocation`.
    -- This is done so that `dsimp` will not close the goal automatically.

end Lean.Elab.Tactic.Conv
end drw

open Pointwise

universe u v w u₁

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁)

namespace Algebra

theorem adjoin_restrictScalars (C D E : Type*) [CommSemiring C] [CommSemiring D] [CommSemiring E]
    [Algebra C D] [Algebra C E] [Algebra D E] [IsScalarTower C D E] (S : Set E) :
    (Algebra.adjoin D S).restrictScalars C =
      (Algebra.adjoin ((⊤ : Subalgebra C D).map (IsScalarTower.toAlgHom C D E)) S).restrictScalars
        C := by
  suffices
    Set.range (algebraMap D E) =
      Set.range (algebraMap ((⊤ : Subalgebra C D).map (IsScalarTower.toAlgHom C D E)) E) by
    ext x
    change x ∈ Subsemiring.closure (_ ∪ S) ↔ x ∈ Subsemiring.closure (_ ∪ S)
    rw [this]
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨⟨algebraMap D E y, ⟨y, ⟨Algebra.mem_top, rfl⟩⟩⟩, hy⟩
  · rintro ⟨⟨y, ⟨z, ⟨h0, h1⟩⟩⟩, h2⟩
    exact ⟨z, Eq.trans h1 h2⟩

theorem adjoin_res_eq_adjoin_res (C D E F : Type*) [CommSemiring C] [CommSemiring D]
    [CommSemiring E] [CommSemiring F] [Algebra C D] [Algebra C E] [Algebra C F] [Algebra D F]
    [Algebra E F] [IsScalarTower C D F] [IsScalarTower C E F] {S : Set D} {T : Set E}
    (hS : Algebra.adjoin C S = ⊤) (hT : Algebra.adjoin C T = ⊤) :
    (Algebra.adjoin E (algebraMap D F '' S)).restrictScalars C =
      (Algebra.adjoin D (algebraMap E F '' T)).restrictScalars C := by
  rw [adjoin_restrictScalars C E, adjoin_restrictScalars C D]
  rw! [← hS, ← hT, ← Algebra.adjoin_image,
    ← Algebra.adjoin_image, ← AlgHom.coe_toRingHom, ← AlgHom.coe_toRingHom,
    IsScalarTower.coe_toAlgHom, IsScalarTower.coe_toAlgHom]
  rw[← adjoin_union_eq_adjoin_adjoin, ← adjoin_union_eq_adjoin_adjoin, Set.union_comm]

end Algebra

section

theorem Algebra.fg_trans' {R S A : Type*} [CommSemiring R] [CommSemiring S] [Semiring A]
    [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] (hRS : (⊤ : Subalgebra R S).FG)
    (hSA : (⊤ : Subalgebra S A).FG) : (⊤ : Subalgebra R A).FG := by
  classical
  rcases hRS with ⟨s, hs⟩
  rcases hSA with ⟨t, ht⟩
  exact ⟨s.image (algebraMap S A) ∪ t, by
    rw [Finset.coe_union, Finset.coe_image,
        Algebra.adjoin_algebraMap_image_union_eq_adjoin_adjoin]
    rw! [hs, Algebra.adjoin_top, ht, Subalgebra.restrictScalars_top,
        Subalgebra.restrictScalars_top
       ]
    ⟩
end

section ArtinTate

variable (C : Type*)

section Semiring

variable [CommSemiring A] [CommSemiring B] [Semiring C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

open Finset Submodule

theorem exists_subalgebra_of_fg (hAC : (⊤ : Subalgebra A C).FG) (hBC : (⊤ : Submodule B C).FG) :
    ∃ B₀ : Subalgebra A B, B₀.FG ∧ (⊤ : Submodule B₀ C).FG := by
  obtain ⟨x, hx⟩ := hAC
  obtain ⟨y, hy⟩ := hBC
  have := hy
  simp_rw [eq_top_iff', mem_span_finset] at this
  choose f hf using this
  classical
  let s : Finset B := Finset.image₂ f (x ∪ y * y) y
  have hxy :
    ∀ xi ∈ x, xi ∈ span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) :=
    fun xi hxi =>
    hf xi ▸
      sum_mem fun yj hyj =>
        smul_mem (span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C))
          ⟨f xi yj, Algebra.subset_adjoin <| mem_image₂_of_mem (mem_union_left _ hxi) hyj⟩
          (subset_span <| mem_insert_of_mem hyj)
  have hyy :
    span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) *
        span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) ≤
      span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) := by
    rw [span_mul_span, span_le, coe_insert]
    rintro _ ⟨yi, rfl | hyi, yj, rfl | hyj, rfl⟩ <;> dsimp
    · rw [mul_one]
      exact subset_span (Set.mem_insert _ _)
    · rw [one_mul]
      exact subset_span (Set.mem_insert_of_mem _ hyj)
    · rw [mul_one]
      exact subset_span (Set.mem_insert_of_mem _ hyi)
    · rw [← hf (yi * yj)]
      exact
        SetLike.mem_coe.2
          (sum_mem fun yk hyk =>
            smul_mem (span (Algebra.adjoin A (↑s : Set B)) (insert 1 ↑y : Set C))
              ⟨f (yi * yj) yk,
                Algebra.subset_adjoin <|
                  mem_image₂_of_mem (mem_union_right _ <| mul_mem_mul hyi hyj) hyk⟩
              (subset_span <| Set.mem_insert_of_mem _ hyk : yk ∈ _))
  refine ⟨Algebra.adjoin A (↑s : Set B), Subalgebra.fg_adjoin_finset _, insert 1 y, ?_⟩
  convert restrictScalars_injective A (Algebra.adjoin A (s : Set B)) C _
  rw [restrictScalars_top, eq_top_iff, ← Algebra.top_toSubmodule, ← hx, Algebra.adjoin_eq_span,
    span_le]
  refine fun r hr =>
    Submonoid.closure_induction (fun c hc => hxy c hc) (subset_span <| mem_insert_self _ _)
      (fun p q _ _ hp hq => hyy <| Submodule.mul_mem_mul hp hq) hr

end Semiring

section Ring

variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- **Artin--Tate lemma**: if A ⊆ B ⊆ C is a chain of subrings of commutative rings, and
A is noetherian, and C is algebra-finite over A, and C is module-finite over B,
then B is algebra-finite over A.

References: Atiyah--Macdonald Proposition 7.8; Altman--Kleiman 16.17. -/
@[stacks 00IS]
theorem fg_of_fg_of_fg [IsNoetherianRing A] (hAC : (⊤ : Subalgebra A C).FG)
    (hBC : (⊤ : Submodule B C).FG) (hBCi : Function.Injective (algebraMap B C)) :
    (⊤ : Subalgebra A B).FG :=
  let ⟨B₀, hAB₀, hB₀C⟩ := exists_subalgebra_of_fg A B C hAC hBC
  Algebra.fg_trans' (B₀.fg_top.2 hAB₀) <|
    Subalgebra.fg_of_submodule_fg <|
      have : IsNoetherianRing B₀ := isNoetherianRing_of_fg hAB₀
      have : Module.Finite B₀ C := ⟨hB₀C⟩
      fg_of_injective (IsScalarTower.toAlgHom B₀ B C).toLinearMap hBCi

end Ring

end ArtinTate
