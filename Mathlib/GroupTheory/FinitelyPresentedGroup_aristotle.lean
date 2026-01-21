/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ca9e7207-4c3a-46c4-afc9-fec2ff48f6d4

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma FreeGroup.map_surjective {α β : Type*} (f : α → β) (hf : Function.Surjective f) :
    Function.Surjective (FreeGroup.map f)

- theorem Group.fg_iff_exists_freeGroup_hom_surjective_finite {G : Type*} [Group G] :
    Group.FG G ↔ ∃ (α : Type) (_ : Finite α) (φ : FreeGroup α →* G), Function.Surjective φ

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

-- Start of suggested additions to #Monoid.ker

-- TODO not sure if this is the right abstraction / right name for this.
/-- The kernel of a homomorphism composed with an isomorphism is equal to the kernel of
the homomorphism mapped by the inverse isomorphism. -/
@[simp]
lemma MonoidHom.ker_comp_mulEquiv {G H K : Type*} [Group G] [Group H] [Group K]
  (f : H →* K) (iso : G ≃* H) : (f.comp iso).ker = (Subgroup.map (iso.symm.toMonoidHom) f.ker) := by
  rw [← MonoidHom.comap_ker, Subgroup.comap_equiv_eq_map_symm]
  rfl

-- End of suggested additions to #Monoid.ker

-- Start of suggested additions to #FreeGroup
-- TODO review this
def FreeGroup.freeGroupEmptyMulEquivUnit : FreeGroup Empty ≃* Unit :=
{ toEquiv := FreeGroup.freeGroupEmptyEquivUnit
  map_mul' := by intro x y; rfl }

-- TODO review this
def FreeGroup.freeGroupUnitMulEquivInt :
    FreeGroup Unit ≃* Multiplicative ℤ := by
  refine
    { toFun := fun x => Multiplicative.ofAdd (FreeGroup.freeGroupUnitEquivInt x)
      invFun := fun z => FreeGroup.freeGroupUnitEquivInt.symm z.toAdd
      left_inv := by
        intro x
        simp
      right_inv := by
        intro z
        simp
      map_mul' := by
        intro x y
        ext
        simp [FreeGroup.freeGroupUnitEquivInt] }

-- TODO do this.
  lemma FreeGroup.map_surjective {α β : Type*} (f : α → β) (hf : Function.Surjective f) :
    Function.Surjective (FreeGroup.map f) := by
    intro x
    induction' x using FreeGroup.induction_on with x ih;
    · exact ⟨ 1, by simp +decide ⟩;
    · exact Exists.elim ( hf x ) fun a ha => ⟨ FreeGroup.of a, by simp +decide [ ha ] ⟩;
    · -- By the induction hypothesis, there exists an element a in the free group on α such that FreeGroup.map f a = FreeGroup.of ih.
      obtain ⟨a, ha⟩ : ∃ a : FreeGroup α, FreeGroup.map f a = FreeGroup.of ih := by
        assumption;
      exact ⟨ a⁻¹, by simp +decide [ ha ] ⟩;
    · case _ hx hy => obtain ⟨ x, rfl ⟩ := hx; obtain ⟨ y, rfl ⟩ := hy; exact ⟨ x * y, by simp +decide ⟩ ;

-- end of addition to #FreeGroup

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
        obtain ⟨ φ, hφ ⟩ := φ;
        -- Since the free group on S is isomorphic to the free group on a finite type, we can use this isomorphism to construct the required homomorphism.
        obtain ⟨α, hα, e⟩ : ∃ (α : Type) (hα : Fintype α), Nonempty (S ≃ α) := by
          -- Since S is finite, we can use the fact that any finite set is equivalent to a finite type.
          obtain ⟨α, hα⟩ : ∃ α : Type, Nonempty (S ≃ α) ∧ Finite α := by
            -- Since S is finite, we can use the fact that any finite set is equivalent to a finite type. Specifically, we can take α to be Fin (Nat.card S).
            use Fin (Nat.card S);
            exact ⟨ by have := hS.fintype; exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ Nat.card_eq_fintype_card ] ⟩, by infer_instance ⟩;
          cases' hα with hα₁ hα₂;
          exact ⟨ α, Fintype.ofFinite α, hα₁ ⟩;
        refine' ⟨ α, _, _, _ ⟩;
        -- Since α is finite, we can use the fact that it has a Fintype instance.
        apply Finite.of_fintype α;
        exact φ.comp ( FreeGroup.map e.some.symm );
        exact hφ.comp ( FreeGroup.map_surjective _ e.some.symm.surjective )
      ·
        -- If there exists a finite type α and a surjective homomorphism from the free group on α to G, then G is generated by the image of α under the homomorphism.
        intro h
        obtain ⟨α, hα, φ, hφ⟩ := h
        have h_gen : ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ := by
          -- Since φ is surjective, the image of α under φ generates G.
          have h_image_gen : Subgroup.closure (Set.image (fun a => φ (FreeGroup.of a)) (Set.univ : Set α)) = ⊤ := by
            simp +decide [ Subgroup.eq_top_iff', hφ ];
            intro x; obtain ⟨ y, rfl ⟩ := hφ x; induction y using FreeGroup.induction_on <;> aesop;
          -- Since α is finite, the image of α under φ is also finite. We can collect these elements into a finite set S.
          obtain ⟨S, hS⟩ : ∃ S : Finset G, (Set.image (fun a => φ (FreeGroup.of a)) (Set.univ : Set α)) = S := by
            exact ⟨ Set.Finite.toFinset ( Set.toFinite ( Set.image ( fun a => φ ( FreeGroup.of a ) ) Set.univ ) ), by simp +decide ⟩;
          exact ⟨ S, hS ▸ h_image_gen ⟩;
        exact?

-- End of suggested additions to #Group.FG

-- Start of suggestion additions to #PresentedGroup

class IsPresented (G : Type*) [Group G] : Prop where
 out: ∃ (α : Type*) (rels : Set (FreeGroup α)), Nonempty (G ≃* PresentedGroup rels)

namespace IsPresented

/- When a FinitelyPresentedGroup G is defined as a PresentedGroup G, it naturally acquires the type
\α since `G = FreeGroup α / normalClosure rels` where `rels : Set (FreeGroup α)`.
On the other hand, when we write IsFinitelyPresented as `∃ α: Type` and a surjective map
`f: FreeGroup α →* G` such that `f.ker = normalClosure rels,`
since `MonoidHom` allows `FreeGroup α` and `G` to be different types,
we have to specify that `α` and `G` live in the same type universe to get the same result. -/
-- lemma iff_hom_surj {G : Type*} [Group G] : IsPresented G ↔
--   ∃ (α : Type*) (rels : Set (FreeGroup α)) (f : FreeGroup α →* G),
--   Function.Surjective f ∧ f.ker = Subgroup.normalClosure rels := by
--     constructor
--     · intro ⟨α, rels, ⟨iso⟩⟩
--       -- TODO `use α` returns a type mismatch.
--       sorry
--     · sorry

end IsPresented

-- End of suggested additions to #PresentedGroup

-- Start of NormalClosureFG statements
open Subgroup

/- The normal closure of an empty set is the trivial subgroup. -/
lemma normalClosure_empty {G : Type*} [Group G] :
    Subgroup.normalClosure (∅ : Set G) = (⊥ : Subgroup G) := by
  apply le_antisymm
  · exact Subgroup.normalClosure_le_normal (N := (⊥ : Subgroup G)) (by simp)
  · exact bot_le

/-- Definition of subgroup that is given by the normal closure of finitely many elements. -/
def IsNormalClosureFG {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∃ S : Set G, S.Finite ∧ Subgroup.normalClosure S = H

/-- `IsNormalClosureFG` is invariant under surjective homomorphism. -/
@[simp]
lemma IsNormalClosureFG.invariant_surj_hom {G H : Type*} [Group G] [Group H]
  (f : G →* H) (hf : Function.Surjective f) (K : Subgroup G) (hK : IsNormalClosureFG K)
  : IsNormalClosureFG (K.map f) := by
  obtain ⟨ S, hSfinite, hSclosure ⟩ := hK
  use f '' S
  constructor
  · exact hSfinite.image _
  · rw [ ← hSclosure, Subgroup.map_normalClosure _ _ hf]

-- End of NormalClosureFG statements

def FinitelyPresentedGroup {α : Type} [Finite α] (rels : Set (FreeGroup α))
(_h : rels.Finite) := PresentedGroup (rels)

namespace FinitelyPresentedGroup

instance (α : Type) [Finite α] (rels : Set (FreeGroup α)) (h : rels.Finite) :
Group (FinitelyPresentedGroup rels h) :=
  QuotientGroup.Quotient.group _

end FinitelyPresentedGroup

class IsFinitelyPresented (G : Type*) [Group G] : Prop where
  out: ∃ (α : Type) (_: Finite α) (rels : Set (FreeGroup α)) (h : rels.Finite),
  Nonempty (G ≃* (FinitelyPresentedGroup rels h))

class IsOneRelator (G : Type*) [Group G] : Prop where
  out : ∃ (α : Type*) (rels : Set (FreeGroup α)) (hrels : rels.Finite),
      Nonempty (G ≃* PresentedGroup rels) ∧
      hrels.toFinset.card = 1

-- TODO calls to IsNormalClosureFG.map could be simplified? Like maybe using the iso functions.
  -- seems like we apply a lot of `MonoidHom.ker_comp_mulEquiv + IsNormalClosureFG.map`.

/- Every FP group is FG -/
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

-- TODO? every group is isomorphic to a `PresentedGroup`

namespace IsFinitelyPresented

/- Every FP group is FP -/
lemma FPgroup {α : Type} [Finite α] (rels : Set (FreeGroup α)) (h : rels.Finite) :
  IsFinitelyPresented (FinitelyPresentedGroup rels h) := by
  refine ⟨α, inferInstance, rels, h, ?_⟩
  exact ⟨MulEquiv.refl _⟩

theorem iff_hom_surj_finite {G : Type*} [Group G] :
IsFinitelyPresented G ↔ ∃ (α : Type) (_ : Finite α) (f : (FreeGroup α) →* G),
  Function.Surjective f ∧ IsNormalClosureFG (MonoidHom.ker f)  := by
  constructor
  · intro ⟨α, hα, rels, hrels, ⟨iso⟩⟩
    unfold FinitelyPresentedGroup at iso
    unfold PresentedGroup at iso
    let f : FreeGroup α →* G :=
      iso.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.normalClosure rels))
    have hfsurj : Function.Surjective f := by
      simpa [f] using
      (iso.symm.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.normalClosure rels)))
    have hfker : IsNormalClosureFG f.ker := by
      use rels, hrels
      ext x
      simp [f]
    exact ⟨α, hα, f, hfsurj, hfker⟩
  · intro ⟨α, hα, f, hfsurj, hfker⟩
    obtain ⟨S, hSfinite, hSnormalClosure⟩ := hfker
    use α, hα, S, hSfinite
    refine ⟨?_⟩
    unfold FinitelyPresentedGroup
    unfold PresentedGroup
    let iso1 : FreeGroup α ⧸ f.ker ≃* G :=
      QuotientGroup.quotientKerEquivOfSurjective (φ := f) hfsurj
    have iso2 : FreeGroup α ⧸ normalClosure S ≃* FreeGroup α ⧸ f.ker :=
      QuotientGroup.quotientMulEquivOfEq hSnormalClosure
    exact iso1.symm.trans iso2.symm

theorem iff_hom_surj_fintype {G : Type*} [Group G] :
IsFinitelyPresented G ↔ ∃ (α : Type) (_ : Fintype α) (f : (FreeGroup α) →* G),
  Function.Surjective f ∧ IsNormalClosureFG (MonoidHom.ker f)  := by
  rw [iff_hom_surj_finite]
  constructor
  · intro ⟨α, _, f, hfsurj, hfker⟩
    let x : Fintype α := Fintype.ofFinite α
    use α, x, f
  · intro ⟨α, _, f, hfsurj, hfker⟩
    use α, inferInstance, f

theorem iff_hom_surj_fin_n {G : Type*} [Group G] :
IsFinitelyPresented G ↔ ∃ (n : ℕ) (f : (FreeGroup (Fin n)) →* G),
  Function.Surjective f ∧ IsNormalClosureFG f.ker  := by
  rw [iff_hom_surj_finite]
  constructor
  · intro ⟨α, hα, f, hfsurj, hfker⟩
    let n := Nat.card α
    let iso : FreeGroup (Fin n) ≃* FreeGroup α :=
    FreeGroup.freeGroupCongr (Finite.equivFin α).symm
    let f' : FreeGroup (Fin n) →* G := f.comp iso
    let hf'surj := hfsurj.comp iso.surjective
    have hf'ker : IsNormalClosureFG f'.ker := by
      unfold f'
      simp only [MonoidHom.ker_comp_mulEquiv]
      exact
      IsNormalClosureFG.invariant_surj_hom iso.symm.toMonoidHom iso.symm.surjective f.ker hfker
    exact ⟨n, f', hf'surj, hf'ker⟩
  · intro ⟨n, f, hfsurj, hfker⟩
    let α := Fin n
    use α, inferInstance, f

theorem if_hom_surj_finite {G : Type*} [Group G] :
(∃ (α : Type*) (_ : Finite α) (f : (FreeGroup α) →* G),
  Function.Surjective f ∧ IsNormalClosureFG (MonoidHom.ker f)) → IsFinitelyPresented G := by
  rintro ⟨α, hα, f, hfsurj, hfker⟩
  rw [iff_hom_surj_fin_n]
  -- TODO considering refactoring this since it seems used for the second time.
  let n := Nat.card α
  let iso : FreeGroup (Fin n) ≃* FreeGroup α :=
    FreeGroup.freeGroupCongr (Finite.equivFin α).symm
  let f' : FreeGroup (Fin n) →* G := f.comp iso
  let hf'surj := hfsurj.comp iso.surjective
  have hf'ker : IsNormalClosureFG f'.ker := by
    unfold f'
    simp only [MonoidHom.ker_comp_mulEquiv]
    exact
    IsNormalClosureFG.invariant_surj_hom iso.symm.toMonoidHom iso.symm.surjective f.ker hfker
  exact ⟨n, f', hf'surj, hf'ker⟩

theorem iff_hom_surj_set_G {G : Type*} [Group G] :
  IsFinitelyPresented G ↔
    ∃ (S : Set G) (_ : S.Finite),
      Function.Surjective (FreeGroup.lift (fun s : S ↦ (s : G))) ∧
      IsNormalClosureFG (FreeGroup.lift (fun s : S ↦ (s : G))).ker := by
  constructor
  · intro ⟨α, hα, rels, hrels, ⟨iso⟩⟩
    simp [FinitelyPresentedGroup, PresentedGroup] at iso
    let _ : Fintype α := Fintype.ofFinite α
    let h : FreeGroup α →* G :=
      iso.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.normalClosure rels))
    have hhsurj : Function.Surjective h := by
      simpa [h] using
      (Function.Surjective.comp iso.symm.surjective
      (QuotientGroup.mk'_surjective (Subgroup.normalClosure rels)))
    let S : Set G := Set.range (fun a : α ↦ h (FreeGroup.of a))
    have hS : S.Finite := by
      simpa [S] using (Set.finite_range (fun a : α ↦ h (FreeGroup.of a)))
    use S, hS
    set f : FreeGroup S →* G := FreeGroup.lift (fun s ↦ (s : G))
    let g : α → S := fun a => ⟨h (FreeGroup.of a), ⟨a, rfl⟩⟩
    have hgsurj : Function.Surjective g := by
      intro s
      rcases s with ⟨y, ⟨a, rfl⟩⟩
      exact ⟨a, rfl⟩
    have hh_fcompg : f.comp (FreeGroup.map g) = h := by
      ext a
      simp [f, h, g]
    have hfsurj : Function.Surjective f := by
      intro y
      obtain ⟨x, rfl⟩ := hhsurj y
      refine ⟨FreeGroup.map g x, ?_⟩
      simpa [MonoidHom.comp_apply] using congrArg (fun m => m x) hh_fcompg
    use hfsurj
    let g' : FreeGroup α →* FreeGroup S := FreeGroup.map g
    have hg'_surj : Function.Surjective g' := FreeGroup.map_surjective g hgsurj
    have hhker : h.ker = Subgroup.normalClosure rels := by
      ext x
      simp [h]
    have hhker' : IsNormalClosureFG h.ker := by
      rw [hhker]
      use rels
    have hfker : f.ker = Subgroup.map g' (Subgroup.normalClosure rels) := by
      have hhker'' : h.ker = (f.ker).comap g' := by
        simpa [g'] using congrArg MonoidHom.ker hh_fcompg.symm
      have hmap : Subgroup.map g' (h.ker) = f.ker := by
        simpa [hhker''] using
          (Subgroup.map_comap_eq_self_of_surjective (f := g') (H := f.ker) hg'_surj)
      simpa [hhker] using hmap.symm
    convert IsNormalClosureFG.invariant_surj_hom g' hg'_surj h.ker hhker'
    rw [hhker]
    exact hfker
  · intro ⟨S, hS, hfsurj, hfker⟩
    set f : FreeGroup S →* G := FreeGroup.lift (fun s => (s : G))
    let α := S
    let _ : Finite α := hS
    apply if_hom_surj_finite -- this is a good justification for using Type* in general.
    use α, inferInstance, f

theorem iff_hom_surj_finset_G {G : Type*} [Group G] :
  IsFinitelyPresented G ↔
      ∃ (S : Finset G),
      Function.Surjective (FreeGroup.lift (fun s : S => (s : G))) ∧
      IsNormalClosureFG (FreeGroup.lift (fun s : S => (s : G))).ker := by
    rw [iff_hom_surj_set_G]
    constructor
    · intro ⟨S, hS, hfsurj, hfker⟩
      set f : FreeGroup S →* G := FreeGroup.lift (fun s => (s : G))
      let S' : Finset G := hS.toFinset
      let e : S ≃ S'
        := hS.subtypeEquivToFinset
      let iso : FreeGroup S' ≃* FreeGroup S
        := FreeGroup.freeGroupCongr e.symm
      let f' : FreeGroup S' →* G := f.comp iso
      let hf'surj := hfsurj.comp iso.surjective
      have hf'ker : IsNormalClosureFG f'.ker := by
        unfold f'
        simp only [MonoidHom.ker_comp_mulEquiv]
        exact
          IsNormalClosureFG.invariant_surj_hom iso.symm.toMonoidHom iso.symm.surjective f.ker hfker
      use S'
      have hf'canon : f' = FreeGroup.lift (fun s' : S' ↦ (s' : G)) := by
        -- TODO prettify this.
        simp_all only [MonoidHom.ker_comp_mulEquiv, FreeGroup.freeGroupCongr_symm, Equiv.symm_symm,
          MulEquiv.toMonoidHom_eq_coe, f, S', f', iso, e]
        ext a : 1
        simp_all only
        [MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply, FreeGroup.freeGroupCongr_apply,
          FreeGroup.map.of, FreeGroup.lift_apply_of, Set.Finite.subtypeEquivToFinset_symm_apply_coe]
      rw [← hf'canon]
      use hf'surj
    · intro ⟨S, hfsurj, hfker⟩
      refine ⟨(S : Set G), S.finite_toSet, ?_, ?_⟩
      · simpa using hfsurj
      · simpa using hfker

-- TODO I think this needs to work for any presented group.
/- If you FreeGroup α by an empty set, you get the original group -/
def quotient_normalClosure_empty_mulEquiv (α : Type*) :
    FreeGroup α ⧸ Subgroup.normalClosure (∅ : Set (FreeGroup α)) ≃* FreeGroup α := by
  have hbot :
      Subgroup.normalClosure (∅ : Set (FreeGroup α)) = (⊥ : Subgroup (FreeGroup α)) := by
    simpa using (normalClosure_empty (G := FreeGroup α))
  exact (QuotientGroup.quotientMulEquivOfEq hbot).trans
    (QuotientGroup.quotientBot (G := FreeGroup α))

/- FreeGroup on finitely many generators is FP -/
/- instance {α : Type} [Finite α] IsFinitelyPresented (FreeGroup α) := by
  sorry -/

/- Trivial group is FP -/
instance instTrivial : IsFinitelyPresented (Unit) := by
  let α := Empty
  let rels := (∅ : Set (FreeGroup Empty))
  have hrels : rels.Finite := by
    simp [rels]
  use α, inferInstance, rels, hrels
  let iso := FreeGroup.freeGroupEmptyMulEquivUnit
  unfold FinitelyPresentedGroup
  unfold PresentedGroup
  refine ⟨?_⟩
  have qiso : FreeGroup α ⧸ Subgroup.normalClosure rels ≃* FreeGroup α := by
    simpa [rels] using quotient_normalClosure_empty_mulEquiv (α := α)
  unfold α at qiso
  exact iso.symm.trans qiso.symm

/- ℤ is finitely presented -/
instance Int.instFinitelyPresented : IsFinitelyPresented (Multiplicative ℤ) := by
  let α := Unit
  let rels := (∅ : Set (FreeGroup α))
  have hrels : rels.Finite := by
    simp [rels]
  use α, inferInstance, rels, hrels
  unfold FinitelyPresentedGroup
  unfold PresentedGroup
  refine ⟨?_⟩
  have qiso : FreeGroup α ⧸ Subgroup.normalClosure rels ≃* FreeGroup α := by
    simpa [rels] using quotient_normalClosure_empty_mulEquiv (α := α)
  let iso := FreeGroup.freeGroupUnitMulEquivInt
  unfold α at qiso
  exact iso.symm.trans qiso.symm

variable {G H : Type*} [Group G] [Group H]

/- FP groups are closed under isomorphism -/
lemma of_mulEquiv {G H : Type*} [Group G] [Group H]
(iso : G ≃* H) (h : IsFinitelyPresented G) :
    IsFinitelyPresented H := by
    obtain ⟨α, hα, rels, hrels, ⟨iso'⟩⟩ := h
    exact ⟨α, hα, rels, hrels, ⟨ iso.symm.trans iso' ⟩⟩

-- TODO: it makes more sense to write this for PresentedGroup first and then unfold.
/- Direct products of finitely presented groups are finitely presented -/
-- instance instProd [hG : IsFinitelyPresented G] [hH : IsFinitelyPresented H] :
--   IsFinitelyPresented (G × H) := by
--   obtain ⟨α, hα, Grels, hGrels, ⟨Giso⟩⟩ := hG
--   obtain ⟨β, hβ, Hrels, hHrels, ⟨Hiso⟩⟩ := hH
--   simp only [FinitelyPresentedGroup] at Giso Hiso
--   use α ⊕ β, inferInstance
--   let Grels_prod : Set (FreeGroup (α ⊕ β)) := FreeGroup.map Sum.inl '' Grels
--   let Hrels_prod : Set (FreeGroup (α ⊕ β)) := FreeGroup.map Sum.inr '' Hrels
--   have hGrels_prod : Grels_prod.Finite := by
--     simpa [Grels_prod] using hGrels.image (FreeGroup.map Sum.inl)
--   have hHrels_prod : Hrels_prod.Finite := by
--     simpa [Hrels_prod] using hHrels.image (FreeGroup.map Sum.inr)
--   -- TODO this should be refactored.
--   let comms : Set (FreeGroup (α ⊕ β)) :=
--   (fun p => ⁅p.1, p.2⁆) '' (Grels_prod ×ˢ Hrels_prod)
--   have hcomm : comms.Finite := by
--   -- comms = image of commutator on Grels_prod ×ˢ Hrels_prod
--     simpa [comms] using (Set.Finite.image (fun p => ⁅p.1, p.2⁆) (hGrels_prod.prod hHrels_prod))
--   let rels_prod : Set (FreeGroup (α ⊕ β)) :=
--   Grels_prod ∪ Hrels_prod ∪ comms
--   have hrels_prod : rels_prod.Finite := by
--   -- assuming hGrels_prod : Grels_prod.Finite, hHrels_prod : Hrels_prod.Finite
--     simpa [rels_prod] using (hGrels_prod.union hHrels_prod).union hcomm
--   refine ⟨rels_prod, hrels_prod, ?_⟩
--   refine ⟨?_iso⟩
--   have e₁ : G × H ≃* PresentedGroup Grels × PresentedGroup Hrels :=
--     MulEquiv.prodCongr Giso Hiso
--   sorry

-- lemma quotient_of_normalClosureFG (N : Subgroup G) [N.Normal]
--     [hG : IsFinitelyPresented G] (hN : IsNormalClosureFG N) :
--     IsFinitelyPresented (G ⧸ N) := by
--     obtain ⟨α, hα, rels, hrels, ⟨iso⟩⟩ := hG
--     unfold FinitelyPresentedGroup at iso
--     unfold PresentedGroup at iso
--     let N' := N.map iso.toMonoidHom
--     have hN'normal : N'.Normal :=
--      Subgroup.Normal.map (H := N) (h := inferInstance) (f := iso.toMonoidHom) iso.surjective
--     have hN'closureFG : IsNormalClosureFG N' := by
--       simpa [N'] using
--     (IsNormalClosureFG.invariant_surj_hom (f := iso.toMonoidHom)
--       (hf := iso.surjective) (K := N) hN)
--     have he : Subgroup.map (↑iso) N = N' := by
--       rfl
--     have qiso : G ⧸ N ≃* (FreeGroup α ⧸ Subgroup.normalClosure rels) ⧸ N' :=
--       QuotientGroup.congr N N' iso he
--     obtain ⟨S, hS, hSClosure⟩ := hN'closureFG
--     -- TODO show isomorphism (FreeGroup α ⧸ normalClosure rels) ⧸ N' with (FreeGroup α ⧸ normalClosure (rels ∪ S))
--     sorry

end IsFinitelyPresented