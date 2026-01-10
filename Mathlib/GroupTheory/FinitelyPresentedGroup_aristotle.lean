/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a6838264-eeb6-4f37-9ad7-ec151c125e05

The following was proved by Aristotle:

- theorem Group.fg_iff_exists_freeGroup_hom_surjective_finite {G : Type*} [Group G] :
    Group.FG G ↔ ∃ (α : Type) (_ : Finite α) (φ : FreeGroup α →* G), Function.Surjective φ

- instance instTrivial : IsFinitelyPresented (Unit)

- lemma quotient_of_normalClosureFG (N : Subgroup G) [N.Normal]
    [hG : IsFinitelyPresented G] (hN : IsNormalClosureFG N) :
    IsFinitelyPresented (G ⧸ N)

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

/-
Copyright (c) Hang Lu Su 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Fabrizio Barroero, Stefano Francaviglia,
  Francesco Milizia, Valerio Proietti, Hang Lu Su, Lawrence Wu
-/

import Mathlib


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

/-!
# Finitely Presented Groups

This file defines when a group is finitely presented and proves their basic properties.
The formal definition of when a group is (finitely) presented is when there exists an isomorphism
between G and F_S / << R >> where S is the generating set and R are the relations.
Here, we define a `Is(Finitely)Presented` directly in terms of the existence of F_S / << R >>
for ease, ignoring the isomorphism.

TODO : maybe just define FinitelyPresentedGroup, then IsFinitelyPresented should be in terms of
the isomorphism? And you can define that FinitelyPresentedGroup IsFinitelyPresented!
OR: look at Group.FG and how that package works.

## Main definitions

## Main results

## Tags
finitely presented group, normal closure finitely generated,
-/

universe u

-- Start of suggested additions to #Group.FG
theorem Group.fg_iff_exists_freeGroup_hom_surjective_fintype_ARISTOTLE1 {G : Type*} [Group G] :
    Group.FG G ↔ ∃ (α : Type) (_ : Fintype α) (φ : FreeGroup α →* G), Function.Surjective φ := by
      constructor <;> intro h;
      · obtain ⟨S, hS⟩ : ∃ S : Set G, S.Finite ∧ Subgroup.closure S = ⊤ := by
          obtain ⟨ S, hS ⟩ := h;
          exact ⟨ S, S.finite_toSet, hS ⟩;
        -- Let α be the finite set S.
        obtain ⟨α, hα⟩ : ∃ α : Type, ∃ (x : Fintype α), Nonempty (α ≃ S) := by
          have := hS.1.exists_finset_coe;
          obtain ⟨ s', rfl ⟩ := this; exact ⟨ Fin s'.card, inferInstance, ⟨ Fintype.equivOfCardEq <| by simp +decide ⟩ ⟩ ;
        obtain ⟨ x, ⟨ e ⟩ ⟩ := hα;
        refine' ⟨ α, x, FreeGroup.lift ( fun a => ( e a : G ) ), _ ⟩;
        intro g
        have h_closure : g ∈ Subgroup.closure S := by
          aesop;
        refine' Subgroup.closure_induction ( fun g hg => _ ) _ _ _ h_closure;
        · exact ⟨ FreeGroup.of ( e.symm ⟨ g, hg ⟩ ), by simp +decide ⟩;
        · exact ⟨ 1, map_one _ ⟩;
        · rintro x y hx hy ⟨ a, rfl ⟩ ⟨ b, rfl ⟩ ; exact ⟨ a * b, by simp +decide ⟩;
        · rintro x hx ⟨ a, rfl ⟩ ; exact ⟨ a⁻¹, by simp +decide ⟩ ;
      · obtain ⟨ α, hα, φ, hφ ⟩ := h
        -- Since α is finite, the image of α under φ is also finite. Therefore, the image of α generates G, proving that G is finitely generated.
        have h_image_finite : Set.Finite (Set.range (fun a : α => φ (FreeGroup.of a))) := by
          exact Set.toFinite _;
        refine' ⟨ h_image_finite.toFinset, _ ⟩;
        refine' eq_top_iff.mpr fun g hg => _;
        obtain ⟨ x, rfl ⟩ := hφ g;
        induction x using FreeGroup.induction_on <;> aesop

theorem Group.fg_iff_exists_freeGroup_hom_surjective_fintype_ARISTOTLE2 {G : Type*} [Group G] :
    Group.FG G ↔ ∃ (α : Type*) (_ : Fintype α) (φ : FreeGroup α →* G), Function.Surjective φ := by
      ·
        constructor <;> intro hG
        all_goals generalize_proofs at *;
        · obtain ⟨ S, hS ⟩ := hG;
          -- Let $T$ be the set of elements in $S$.
          set T : Set G := S.toSet;
          -- Let $α$ be the set of elements in $T$.
          obtain ⟨α, hα⟩ : ∃ α : Type, ∃ (x : Fintype α), Nonempty (α ≃ T) := by
            -- Since $T$ is finite, we can use the fact that any finite set is equivalent to a finite type.
            use Fin (Finset.card S);
            -- Since $S$ is a finset, there exists an equivalence between $Fin (Finset.card S)$ and $S$.
            have h_equiv : Nonempty (Fin (Finset.card S) ≃ S) := by
              exact ⟨ Fintype.equivOfCardEq <| by simp +decide ⟩;
            exact ⟨ inferInstance, h_equiv ⟩;
          obtain ⟨ hα, ⟨ e ⟩ ⟩ := hα;
          -- Define the homomorphism φ by mapping each generator in α to the corresponding element in T.
          use ULift α, inferInstance, FreeGroup.lift (fun a => (e (ULift.down a)).val);
          intro g
          have h_mem : g ∈ Subgroup.closure T := by
            aesop
          generalize_proofs at *;
          refine' Subgroup.closure_induction _ _ _ _ h_mem;
          · intro x hx
            obtain ⟨ a, ha ⟩ := e.surjective ⟨ x, hx ⟩
            use FreeGroup.of (ULift.up a)
            simp [ha];
          · exact ⟨ 1, map_one _ ⟩;
          · rintro x y hx hy ⟨ a, rfl ⟩ ⟨ b, rfl ⟩ ; exact ⟨ a * b, by simp +decide ⟩ ;
          · rintro x hx ⟨ a, rfl ⟩ ; exact ⟨ a⁻¹, by simp +decide ⟩ ;
        · -- To prove the forward direction, assume there exists a finite type α and a surjective homomorphism φ from the free group on α to G. We can use the fact that the image of a finite set under a surjective homomorphism is finite.
          obtain ⟨α, hα, φ, hφ⟩ := hG;
          have h_gen : ∃ (S : Set G), S.Finite ∧ Subgroup.closure S = ⊤ := by
            refine' ⟨ Set.range ( fun x : α => φ ( FreeGroup.of x ) ), Set.toFinite _, _ ⟩;
            rw [ eq_top_iff ];
            rintro g -;
            obtain ⟨ x, rfl ⟩ := hφ g;
            induction x using FreeGroup.induction_on <;> aesop;
          obtain ⟨ S, hS_finite, hS_gen ⟩ := h_gen; exact ⟨ hS_finite.toFinset, by simpa [ Subgroup.closure ] using hS_gen ⟩ ;

theorem Group.fg_iff_exists_freeGroup_hom_surjective_finite {G : Type*} [Group G] :
    Group.FG G ↔ ∃ (α : Type) (_ : Finite α) (φ : FreeGroup α →* G), Function.Surjective φ := by
      constructor
      · rw [Group.fg_iff_exists_freeGroup_hom_surjective]
        intro ⟨S, hS, φ⟩
        -- Since S is finite, we can use the fact that there's an equivalence between S and Fin n for some n.
        obtain ⟨n, hn⟩ : ∃ n : ℕ, Nonempty (S ≃ Fin n) := by
          exact?;
        -- Since Fin n is finite, we can use it as our α.
        use Fin n;
        -- Since Fin n is finite, we can use it as our α. The existence of an equivalence between S and Fin n allows us to transfer the surjective homomorphism from S to Fin n.
        obtain ⟨e⟩ := hn;
        use inferInstance;
        use FreeGroup.lift (fun x => φ.choose (FreeGroup.of (e.symm x)));
        intro g;
        obtain ⟨ x, hx ⟩ := φ.choose_spec g;
        refine' ⟨ FreeGroup.map ( fun x => e x ) x, _ ⟩;
        convert hx using 1;
        refine' FreeGroup.induction_on x _ _ _ _ <;> aesop
      ·
        -- Assume there exists a permutation α, a finite type α, and a surjective homomorphism φ from the free group on α to G.
        intro h
        obtain ⟨α, hα_finite, φ, hφ_surjective⟩ := h;
        -- Let $S$ be the image of the generators of the free group under $\phi$.
        set S := Set.range (fun x : α => φ (FreeGroup.of x)) with hS_def;
        -- Since $S$ is the image of the generators of the free group under $\phi$, and $\phi$ is surjective, $S$ generates $G$.
        have hS_gen : Subgroup.closure S = ⊤ := by
          simp +decide [ Subgroup.eq_top_iff', hS_def ];
          intro x; obtain ⟨ y, rfl ⟩ := hφ_surjective x; induction y using FreeGroup.induction_on <;> aesop;
        exact ⟨ Set.Finite.toFinset ( Set.finite_range _ ), by simpa ⟩

-- End of suggested additions to #Group.FG

-- Start of suggestion additions to #PresentedGroup

class IsPresented (G : Type*) [Group G] : Prop where
 out: ∃ (α : Type*) (rels : Set (FreeGroup α)), Nonempty (G ≃* PresentedGroup rels)

namespace IsPresented

/- Aristotle failed to find a proof. -/
lemma iff_hom_surj {G : Type*} [Group G] : IsPresented G ↔
  ∃ (α : Type*) (rels : Set (FreeGroup α)) (f : FreeGroup α →* G),
  Function.Surjective f ∧ f.ker = Subgroup.normalClosure rels := by
    constructor
    · intro ⟨α, rels, ⟨iso⟩⟩
      -- TODO `use α` returns a type mismatch.
      sorry
    · sorry

end IsPresented

-- End of suggested additions to #PresentedGroup

def FinitelyPresentedGroup {α : Type} [Finite α] (rels : Set (FreeGroup α))
(_h : rels.Finite) := PresentedGroup (rels)

namespace FinitelyPresentedGroup

instance (α : Type) [Finite α] (rels : Set (FreeGroup α)) (h : rels.Finite) :
Group (FinitelyPresentedGroup rels h) :=
  QuotientGroup.Quotient.group _

end FinitelyPresentedGroup

open Subgroup

/-- Definition of subgroup that is given by the normal closure of finitely many elements. -/
def IsNormalClosureFG {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∃ S : Set G, S.Finite ∧ Subgroup.normalClosure S = H

/-- `IsNormalClosureFG` is invariant under surjective homomorphism. -/
lemma IsNormalClosureFG.invariant_surj_hom {G H : Type*} [Group G] [Group H]
  (f : G →* H) (hf : Function.Surjective f) (K : Subgroup G) (hK : IsNormalClosureFG K)
  : IsNormalClosureFG (K.map f) := by
  obtain ⟨ S, hSfinite, hSclosure ⟩ := hK
  use f '' S
  constructor
  · exact hSfinite.image _
  · rw [ ← hSclosure, Subgroup.map_normalClosure _ _ hf]

class IsFinitelyPresented (G : Type*) [Group G] : Prop where
  out: ∃ (α : Type) (_: Finite α) (rels : Set (FreeGroup α)) (h : rels.Finite),
  Nonempty (G ≃* (FinitelyPresentedGroup rels h))

-- TODO calls to IsNormalClosureFG.map could be simplified? Like maybe using the iso functions.
  -- seems like we apply a lot of `MonoidHom.ker_comp_mulEquiv + IsNormalClosureFG.map`.

instance isFP_isFG {G : Type*} [Group G] [h : IsFinitelyPresented G] : Group.FG G := by
  rw [Group.fg_iff_exists_freeGroup_hom_surjective_finite]
  obtain ⟨α, hα, rels, hrels, ⟨iso⟩⟩ := h
  unfold FinitelyPresentedGroup at iso
  unfold PresentedGroup at iso
  use α, hα
  -- TODO probably a nicer way to do this.
  let iso' := iso.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.normalClosure rels))
  use iso'
  simpa [iso'] using
    (Function.Surjective.comp iso.symm.surjective (QuotientGroup.mk'_surjective (Subgroup.normalClosure rels)))

instance isFP_isPresented {G : Type*} [Group G] [h : IsFinitelyPresented G] : IsPresented G := by
  obtain ⟨α, hα, rels, hrels, ⟨iso⟩⟩ := h
  use ULift α, Set.image (FreeGroup.map ULift.up) rels
  let e : ULift α ≃ α := Equiv.ulift
  refine ⟨iso.trans (PresentedGroup.equivPresentedGroup rels e.symm)⟩

-- TODO? every group is isomorphic to a `PresentedGroup`!

namespace IsFinitelyPresented

/- Every FP group is FP -/
lemma FPgroup {α : Type} [Finite α] (rels : Set (FreeGroup α)) (h : rels.Finite) :
  IsFinitelyPresented (FinitelyPresentedGroup rels h) := by
  refine ⟨α, inferInstance, rels, h, ?_⟩
  exact ⟨MulEquiv.refl _⟩

/- Every FP group is FP -/
instance instTrivial : IsFinitelyPresented (Unit) := by
/-   let α := Empty
  let rels := (∅ : Set (FreeGroup Empty))
  have hrels : rels.Finite := by
    simp [rels]
  use α, inferInstance, rels, hrels
  let iso := FreeGroup.freeGroupEmptyEquivUnit
  refine ⟨?_⟩
  unfold FinitelyPresentedGroup
  unfold PresentedGroup -/
  refine' ⟨ PEmpty, inferInstance, ∅, Set.finite_empty, _ ⟩;
  refine' ⟨ _ ⟩;
  refine' { Equiv.ofBijective ( fun _ => 1 ) ⟨ fun _ => _, fun _ => _ ⟩ with .. } <;> simp +decide;
  rename_i x;
  induction x using QuotientGroup.induction_on';
  rename_i x; exact Eq.symm ( by rcases x with ⟨ _ | _ | x ⟩ ; trivial ) ;

variable {G H : Type*} [Group G] [Group H]

/- FP groups are closed under isomorphism -/
lemma of_mulEquiv {G H : Type*} [Group G] [Group H]
(iso : G ≃* H) (h : IsFinitelyPresented G) :
    IsFinitelyPresented H := by
    obtain ⟨α, hα, rels, hrels, ⟨iso'⟩⟩ := h
    exact ⟨α, hα, rels, hrels, ⟨ iso.symm.trans iso' ⟩⟩

-- Aristotle skipped at least one sorry in the block below (common reasons: Aristotle does not define data).
-- TODO: it makes more sense to write this for PresentedGroup first and then unfold.
/- Direct products of finitely presented groups are finitely presented -/
instance instProd [hG : IsFinitelyPresented G] [hH : IsFinitelyPresented H] :
  IsFinitelyPresented (G × H) := by
  obtain ⟨α, hα, Grels, hGrels, ⟨Giso⟩⟩ := hG
  obtain ⟨β, hβ, Hrels, hHrels, ⟨Hiso⟩⟩ := hH
  simp [FinitelyPresentedGroup] at Giso Hiso
  use α ⊕ β, inferInstance
  let Grels_prod : Set (FreeGroup (α ⊕ β)) := FreeGroup.map Sum.inl '' Grels
  let Hrels_prod : Set (FreeGroup (α ⊕ β)) := FreeGroup.map Sum.inr '' Hrels
  have hGrels_prod : Grels_prod.Finite := by
    simpa [Grels_prod] using hGrels.image (FreeGroup.map Sum.inl)
  have hHrels_prod : Hrels_prod.Finite := by
    simpa [Hrels_prod] using hHrels.image (FreeGroup.map Sum.inr)
  -- TODO this should be refactored.
  let comms : Set (FreeGroup (α ⊕ β)) :=
  (fun p => ⁅p.1, p.2⁆) '' (Grels_prod ×ˢ Hrels_prod)
  have hcomm : comms.Finite := by
  -- comms = image of commutator on Grels_prod ×ˢ Hrels_prod
    simpa [comms] using (Set.Finite.image (fun p => ⁅p.1, p.2⁆) (hGrels_prod.prod hHrels_prod))
  let rels_prod : Set (FreeGroup (α ⊕ β)) :=
  Grels_prod ∪ Hrels_prod ∪ comms
  have hrels_prod : rels_prod.Finite := by
  -- assuming hGrels_prod : Grels_prod.Finite, hHrels_prod : Hrels_prod.Finite
    simpa [rels_prod] using (hGrels_prod.union hHrels_prod).union hcomm
  refine ⟨rels_prod, hrels_prod, ?_⟩
  refine ⟨?_iso⟩
  have e₁ : G × H ≃* PresentedGroup Grels × PresentedGroup Hrels :=
    MulEquiv.prodCongr Giso Hiso
  sorry

noncomputable section AristotleLemmas

/-
If $f: \alpha \to \beta$ is surjective and $S \subseteq \beta$ is finite, there exists a finite set $T \subseteq \alpha$ such that $f(T) = S$.
-/
lemma exists_finite_lift_of_finite_image {α β : Type*} (f : α → β) (hf : Function.Surjective f) (S : Set β) (hS : S.Finite) : ∃ T : Set α, T.Finite ∧ f '' T = S := by
  choose g hg using hf;
  exact ⟨ g '' S, hS.image _, by aesop ⟩

/-
The preimage of the normal closure of $S$ under a surjective homomorphism $f$ is generated by the normal closure of a lift $T$ of $S$ and the kernel of $f$.
-/
lemma comap_normalClosure_eq_normalClosure_lift_sup_ker {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Surjective f) (S : Set H) (T : Set G) (hT : f '' T = S) : (Subgroup.normalClosure S).comap f = Subgroup.normalClosure T ⊔ f.ker := by
  apply le_antisymm;
  · intro x hx; simp_all +decide [ Subgroup.normalClosure, Subgroup.comap ] ;
    -- Since $f(x) \in \langle \text{conjugatesOfSet } S \rangle$, we can write $f(x)$ as a product of elements from $\text{conjugatesOfSet } S$.
    obtain ⟨y, hy⟩ : ∃ y ∈ Subgroup.closure (Group.conjugatesOfSet T), f x = f y := by
      refine' Subgroup.closure_induction ( fun y hy => _ ) _ _ _ hx;
      · simp_all +decide [ Group.conjugatesOfSet ];
        rcases hy with ⟨ y, hy, hy' ⟩ ; simp_all +decide [ conjugatesOf ] ;
        rcases hy' with ⟨ c, rfl ⟩ ; rcases hf c with ⟨ d, rfl ⟩ ; rcases hT.symm.subset hy with ⟨ a, ha, rfl ⟩ ; use d * a * d⁻¹; simp_all +decide [ Subgroup.mem_closure ] ;
        exact fun K hK => hK a ha ⟨ d, rfl ⟩;
      · exact ⟨ 1, Subgroup.one_mem _, by simp +decide ⟩;
      · rintro x y hx hy ⟨ u, hu, rfl ⟩ ⟨ v, hv, rfl ⟩ ; exact ⟨ u * v, Subgroup.mul_mem _ hu hv, by simp +decide ⟩ ;
      · rintro x hx ⟨ y, hy, rfl ⟩ ; exact ⟨ y⁻¹, Subgroup.inv_mem _ hy, by simp +decide ⟩ ;
    -- Since $f(x) = f(y)$, we have $x = y * k$ for some $k \in \ker(f)$.
    obtain ⟨k, hk⟩ : ∃ k ∈ f.ker, x = y * k := by
      exact ⟨ y⁻¹ * x, by aesop ⟩;
    exact hk.2.symm ▸ Subgroup.mul_mem_sup hy.1 hk.1;
  · refine' sup_le _ _;
    · unfold Subgroup.normalClosure;
      simp +decide [ hT.symm, Group.conjugatesOfSet ];
      simp +decide [ conjugatesOf, Set.subset_def ];
      exact fun i hi a => Subgroup.subset_closure ( Set.mem_iUnion₂.2 ⟨ i, hi, ⟨ f a, rfl ⟩ ⟩ );
    · aesop_cat

/-
The normal closure of the union of two sets is the join of their normal closures.
-/
lemma normalClosure_union {G : Type*} [Group G] (s t : Set G) : Subgroup.normalClosure (s ∪ t) = Subgroup.normalClosure s ⊔ Subgroup.normalClosure t := by
  refine' le_antisymm _ _;
  · refine' Subgroup.normalClosure_le_normal _;
    rintro x ( hx | hx ) <;> [ exact Subgroup.mem_sup_left ( Subgroup.subset_normalClosure hx ) ; exact Subgroup.mem_sup_right ( Subgroup.subset_normalClosure hx ) ];
  · exact sup_le ( Subgroup.normalClosure_mono ( Set.subset_union_left ) ) ( Subgroup.normalClosure_mono ( Set.subset_union_right ) )

end AristotleLemmas

lemma quotient_of_normalClosureFG (N : Subgroup G) [N.Normal]
    [hG : IsFinitelyPresented G] (hN : IsNormalClosureFG N) :
    IsFinitelyPresented (G ⧸ N) := by
    obtain ⟨α, hα, rels, hrels, ⟨iso⟩⟩ := hG
    unfold FinitelyPresentedGroup at iso
    unfold PresentedGroup at iso
    let N' := N.map iso.toMonoidHom
    have hN'normal : N'.Normal :=
     Subgroup.Normal.map (H := N) (h := inferInstance) (f := iso.toMonoidHom) iso.surjective
    have hN'closureFG : IsNormalClosureFG N' := by
      simpa [N'] using
    (IsNormalClosureFG.invariant_surj_hom (f := iso.toMonoidHom)
      (hf := iso.surjective) (K := N) hN)
    have he : Subgroup.map (↑iso) N = N' := by
      rfl
    have qiso : G ⧸ N ≃* (FreeGroup α ⧸ Subgroup.normalClosure rels) ⧸ N' :=
      QuotientGroup.congr N N' iso he
    obtain ⟨S, hS, hSClosure⟩ := hN'closureFG
    -- TODO show isomorphism (FreeGroup α ⧸ normalClosure rels) ⧸ N' with (FreeGroup α ⧸ normalClosure (rels ∪ S))
    obtain ⟨T, hT, hTS⟩ : ∃ T : Set (FreeGroup α), T.Finite ∧ S = T.image (QuotientGroup.mk' (Subgroup.normalClosure rels)) := by
      have := exists_finite_lift_of_finite_image ( QuotientGroup.mk' ( Subgroup.normalClosure rels ) ) ( QuotientGroup.mk'_surjective _ ) S hS;
      grind;
    have hq : (Subgroup.normalClosure S).comap (QuotientGroup.mk' (Subgroup.normalClosure rels)) = Subgroup.normalClosure (T ∪ rels) := by
      have hq : (Subgroup.normalClosure S).comap (QuotientGroup.mk' (Subgroup.normalClosure rels)) = Subgroup.normalClosure T ⊔ (Subgroup.normalClosure rels) := by
        convert comap_normalClosure_eq_normalClosure_lift_sup_ker ( QuotientGroup.mk' ( Subgroup.normalClosure rels ) ) ( QuotientGroup.mk'_surjective _ ) S T _ using 1;
        · simp +decide [ QuotientGroup.ker_mk' ];
        · rw [hTS];
      rw [ hq, normalClosure_union ];
    have hq : Subgroup.normalClosure S = Subgroup.map (QuotientGroup.mk' (Subgroup.normalClosure rels)) (Subgroup.normalClosure (T ∪ rels)) := by
      rw [ ← hq, Subgroup.map_comap_eq_self_of_surjective ( QuotientGroup.mk'_surjective _ ) ];
    have hq : (FreeGroup α ⧸ Subgroup.normalClosure rels) ⧸ N' ≃* (FreeGroup α ⧸ Subgroup.normalClosure (T ∪ rels)) := by
      have hq : (FreeGroup α ⧸ Subgroup.normalClosure rels) ⧸ Subgroup.map (QuotientGroup.mk' (Subgroup.normalClosure rels)) (Subgroup.normalClosure (T ∪ rels)) ≃* (FreeGroup α ⧸ Subgroup.normalClosure (T ∪ rels)) := by
        refine' QuotientGroup.quotientQuotientEquivQuotient _ _ _;
        exact Subgroup.normalClosure_mono ( Set.subset_union_right );
      convert hq using 1;
      grind +ring;
    refine' ⟨ α, hα, T ∪ rels, hT.union hrels, _ ⟩;
    exact ⟨ qiso.trans hq ⟩

end IsFinitelyPresented