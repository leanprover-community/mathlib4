/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.Tactic.CategoryTheory.Bicategory

/-!
# A `coherence` tactic for bicategories

-/

open Lean Elab Meta Tactic
open CategoryTheory

universe w v u

namespace Mathlib.Tactic.Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

open Bicategory

initialize registerTraceClass `bicategory

def mkIsoRefl (f : Expr) : BicategoryM Expr := do
  let ctx ← read
  let instCat ← mkHomCatInst (← srcExpr f) (← tgtExpr f)
  return mkAppN (.const ``Iso.refl [ctx.level₂, ctx.level₁])
    #[← inferType f, instCat, f]

def mkWhiskerRightIso (η : Expr) (h : Expr) : BicategoryM Expr := do
  let ctx ← read
  let f ← srcExprOfIso η
  let g ← tgtExprOfIso η
  let a ← srcExpr f
  let b ← tgtExpr f
  let c ← tgtExpr h
  return mkAppN (.const ``Bicategory.whiskerRightIso (← getLevels))
    #[ctx.B, ctx.instBicategory, a, b, c, f, g, η, h]

def mkIsoTrans (η θ : Expr) : BicategoryM Expr := do
  let ctx ← read
  let f ← srcExprOfIso η
  let g ← tgtExprOfIso η
  let h ← tgtExprOfIso θ
  let instCat ← mkHomCatInst (← srcExpr f) (← tgtExpr f)
  return mkAppN (.const ``Iso.trans [ctx.level₂, ctx.level₁])
    #[← inferType f, instCat, f, g, h, η, θ]

def mkIsoSymm (η : Expr) : BicategoryM Expr := do
  let ctx ← read
  let f ← srcExprOfIso η
  let g ← tgtExprOfIso η
  let instCat ← mkHomCatInst (← srcExpr f) (← tgtExpr f)
  return mkAppN (.const ``Iso.symm [ctx.level₂, ctx.level₁])
    #[← inferType f, instCat, f, g, η]

/-- Type of normalized 1-morphisms, represented by (reversed) list. -/
inductive NormalizedHom : Type
  /-- The identity 1-morphism `𝟙 a`. -/
  | nil (e : Expr) (a : Expr) : NormalizedHom
  /-- The `cons` composes an atomic 1-morphism at the end of a normalized 1-morphism. -/
  | cons (e : Expr) : NormalizedHom → Expr → NormalizedHom

/-- The underlying expression of a normalized 1-morphism. -/
def NormalizedHom.e : NormalizedHom → Expr
  | NormalizedHom.nil e _ => e
  | NormalizedHom.cons e _ _ => e

/-- Construct the `NormalizedHom.nil` term in `BicategoryM`. -/
def normalizedHom.nilM (a : Expr) : BicategoryM NormalizedHom := do
  return NormalizedHom.nil (← mkId₁ a) a

/-- Construct a `NormalizedHom.cons` term in `BicategoryM`. -/
def NormalizedHom.consM (p : NormalizedHom) (f : Expr) : BicategoryM NormalizedHom := do
  return NormalizedHom.cons (← mkComp₁ p.e f) p f

structure Coherence.Result where
  /-- The normalized 1-morphism. -/
  normalizedHom : NormalizedHom
  /-- The 2-morphism to the normalized 1-morphism. -/
  toNormalize : Expr

section

variable {a b c d e : B}

abbrev normalizeIso {p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d}
    (η_f : p ≫ f ≅ pf) (η_g : pf ≫ g ≅ pfg) :=
  (α_ _ _ _).symm ≪≫ whiskerRightIso η_f g ≪≫ η_g

theorem naturality_associator
    {p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh : a ⟶ e}
    (η_f : (p ≫ f) ≅ pf) (η_g : (pf ≫ g) ≅ pfg) (η_h : pfg ≫ h ≅ pfgh) :
    p ◁ (α_ f g h).hom ≫ (normalizeIso η_f (normalizeIso η_g η_h)).hom =
    (normalizeIso (normalizeIso η_f η_g) η_h).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, whiskerRight_comp, Category.assoc,
    Iso.hom_inv_id_assoc, pentagon_hom_inv_inv_inv_inv_assoc, comp_whiskerRight]

def mkNaturalityAssociator (p f g h pf pfg pfgh η_f η_g η_h : Expr) : BicategoryM Expr := do
  let ctx ← read
  let a ← srcExpr p
  let b ← tgtExpr p
  let c ← tgtExpr f
  let d ← tgtExpr g
  let e ← tgtExpr h
  return mkAppN (.const ``naturality_associator (← getLevels))
    #[ctx.B, ctx.instBicategory, a, b, c, d, e, p, f, g, h, pf, pfg, pfgh, η_f, η_g, η_h]

theorem naturality_associator_inv
    {p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh : a ⟶ e}
    (η_f : (p ≫ f) ≅ pf) (η_g : (pf ≫ g) ≅ pfg) (η_h : pfg ≫ h ≅ pfgh) :
    p ◁ (α_ f g h).inv ≫ (normalizeIso (normalizeIso η_f η_g) η_h).hom =
    (normalizeIso η_f (normalizeIso η_g η_h)).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, comp_whiskerRight, Category.assoc,
    pentagon_inv_assoc, whiskerRight_comp, Iso.hom_inv_id_assoc]

def mkNaturalityAssociatorInv (p f g h pf pfg pfgh η_f η_g η_h : Expr) : BicategoryM Expr := do
  let ctx ← read
  let a ← srcExpr p
  let b ← tgtExpr p
  let c ← tgtExpr f
  let d ← tgtExpr g
  let e ← tgtExpr h
  return mkAppN (.const ``naturality_associator_inv (← getLevels))
    #[ctx.B, ctx.instBicategory, a, b, c, d, e, p, f, g, h, pf, pfg, pfgh, η_f, η_g, η_h]

theorem naturality_leftUnitor {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) :
    p ◁ (λ_ f).hom ≫ η_f.hom = (normalizeIso (ρ_ p) η_f).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, triangle_assoc_comp_right_assoc]

def mkNaturalityLeftUnitor (p f pf η_f : Expr) : BicategoryM Expr := do
  let ctx ← read
  let a ← srcExpr p
  let b ← tgtExpr p
  let c ← tgtExpr f
  return mkAppN (.const ``naturality_leftUnitor (← getLevels))
    #[ctx.B, ctx.instBicategory, a, b, c, p, f, pf, η_f]

theorem naturality_leftUnitor_inv {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) :
    p ◁ (λ_ f).inv ≫ (normalizeIso (ρ_ p) η_f).hom = η_f.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, triangle_assoc_comp_right_assoc,
    whiskerLeft_inv_hom_assoc, Iso.refl_hom, Category.comp_id]

def mkNaturalityLeftUnitorInv (p f pf η_f : Expr) : BicategoryM Expr := do
  let ctx ← read
  let a ← srcExpr p
  let b ← tgtExpr p
  let c ← tgtExpr f
  return mkAppN (.const ``naturality_leftUnitor_inv (← getLevels))
    #[ctx.B, ctx.instBicategory, a, b, c, p, f, pf, η_f]

theorem naturality_rightUnitor {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) :
    p ◁ (ρ_ f).hom ≫ η_f.hom = (normalizeIso η_f (ρ_ pf)).hom := by
  simp only [whiskerLeft_rightUnitor, Category.assoc, Iso.trans_hom, Iso.symm_hom,
    whiskerRightIso_hom, whiskerRight_id, Iso.inv_hom_id, Category.comp_id]

def mkNaturalityRightUnitor (p f pf η_f : Expr) : BicategoryM Expr := do
  let ctx ← read
  let a ← srcExpr p
  let b ← tgtExpr p
  let c ← tgtExpr f
  return mkAppN (.const ``naturality_rightUnitor (← getLevels))
    #[ctx.B, ctx.instBicategory, a, b, c, p, f, pf, η_f]

theorem naturality_rightUnitor_inv {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) :
    p ◁ (ρ_ f).inv ≫ (normalizeIso η_f (ρ_ pf)).hom = η_f.hom := by
  simp only [whiskerLeft_rightUnitor_inv, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom,
    whiskerRight_id, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id_assoc]

def mkNaturalityRightUnitorInv (p f pf η_f : Expr) : BicategoryM Expr := do
  let ctx ← read
  let a ← srcExpr p
  let b ← tgtExpr p
  let c ← tgtExpr f
  return mkAppN (.const ``naturality_rightUnitor_inv (← getLevels))
    #[ctx.B, ctx.instBicategory, a, b, c, p, f, pf, η_f]

theorem naturality_id {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) :
    p ◁ (𝟙 f) ≫ η_f.hom = η_f.hom := by
  simp only [whiskerLeft_id, Category.id_comp]

def mkNaturalityId (p f pf η_f : Expr) : BicategoryM Expr := do
  let ctx ← read
  let a ← srcExpr p
  let b ← tgtExpr p
  let c ← tgtExpr f
  return mkAppN (.const ``naturality_id (← getLevels))
    #[ctx.B, ctx.instBicategory, a, b, c, p, f, pf, η_f]

theorem naturality_comp
    {p : a ⟶ b} {f g h : b ⟶ c} {pf : a ⟶ c}
    (η : f ⟶ g) (θ : g ⟶ h) (η_f : (p ≫ f) ≅ pf) (η_g : (p ≫ g) ≅ pf) (η_h : p ≫ h ≅ pf)
    (ih_η : p ◁ η ≫ η_g.hom = η_f.hom) (ih_θ : p ◁ θ ≫ η_h.hom = η_g.hom) :
    p ◁ (η ≫ θ) ≫ η_h.hom = η_f.hom := by
  simp only [whiskerLeft_comp, Category.assoc, ← ih_η, ← ih_θ]

def mkNaturalityComp (p f g h pf η θ η_f η_g η_h ih_η ih_θ : Expr) : BicategoryM Expr := do
  let ctx ← read
  let a ← srcExpr p
  let b ← tgtExpr p
  let c ← tgtExpr f
  return mkAppN (.const ``naturality_comp (← getLevels))
    #[ctx.B, ctx.instBicategory, a, b, c, p, f, g, h, pf, η, θ, η_f, η_g, η_h, ih_η, ih_θ]

theorem naturality_whiskerLeft {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d}
    (η : g ⟶ h) (η_f : (p ≫ f) ≅ pf)
    (η_fg : (pf ≫ g) ≅ pfg)
    (η_fh : (pf ≫ h) ≅ pfg)
    (ih_η : pf ◁ η ≫ η_fh.hom = η_fg.hom) :
    p ◁ (f ◁ η) ≫ (normalizeIso η_f η_fh).hom =
    (normalizeIso η_f η_fg).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, ← ih_η, ← whisker_exchange_assoc,
    comp_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc]

def mkNaturalityWhiskerLeft (p f g h pf pfg η η_f η_fg η_fh ih_η : Expr) : BicategoryM Expr := do
  let ctx ← read
  let a ← srcExpr p
  let b ← tgtExpr p
  let c ← tgtExpr f
  let d ← tgtExpr g
  return mkAppN (.const ``naturality_whiskerLeft (← getLevels))
    #[ctx.B, ctx.instBicategory, a, b, c, d, p, f, g, h, pf, pfg, η, η_f, η_fg, η_fh, ih_η]

theorem naturality_whiskerRight {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d}
    (η : f ⟶ g) (η_f : (p ≫ f) ≅ pf)
    (η_g : (p ≫ g) ≅ pf)
    (η_fh : (pf ≫ h) ≅ pfh)
    (ih_η : p ◁ η ≫ η_g.hom = η_f.hom) :
    p ◁ (η ▷ h) ≫ (normalizeIso η_g η_fh).hom =
    (normalizeIso η_f η_fh).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, ← ih_η, comp_whiskerRight,
    whisker_assoc, Category.assoc, Iso.inv_hom_id_assoc]

def mkNaturalityWhiskerRight (p f g h pf pfh η η_f η_g η_fh ih_η : Expr) : BicategoryM Expr := do
  let ctx ← read
  let a ← srcExpr p
  let b ← tgtExpr p
  let c ← tgtExpr f
  let d ← tgtExpr h
  return mkAppN (.const ``naturality_whiskerRight (← getLevels))
    #[ctx.B, ctx.instBicategory, a, b, c, d, p, f, g, h, pf, pfh, η, η_f, η_g, η_fh, ih_η]

end

partial def normalize (p : NormalizedHom) (f : Expr) : BicategoryM Coherence.Result := do
  if let some _ ← isId? f then
    let α ← mkRightUnitor p.e
    return ⟨p, α⟩
  else if let some (f, g) ← isComp? f then
    let ⟨pf, Hf⟩ ← normalize p f
    let Hf' ← mkWhiskerRightIso Hf g
    let ⟨pfg, Hg⟩ ← normalize pf g
    let η ← mkIsoTrans Hf' Hg
    let alpha ← mkIsoSymm (← mkAssociator p.e f g)
    let η' ← mkIsoTrans alpha η
    return ⟨pfg, η'⟩
  else
    let pf ← p.consM f
    let α ← mkIsoRefl pf.e
    return ⟨pf, α⟩

theorem of_normalize_eq {a b : B} {f g f' : a ⟶ b}
    (η θ : f ⟶ g) (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ f')
  (h_η : 𝟙 a ◁ η ≫ η_g.hom = η_f.hom)
  (h_θ : 𝟙 a ◁ θ ≫ η_g.hom = η_f.hom) : η = θ := by
  simp only [id_whiskerLeft, Category.assoc] at h_η h_θ
  calc
    η = (λ_ f).inv ≫ η_f.hom ≫ η_g.inv ≫ (λ_ g).hom := by
      simp [← reassoc_of% h_η]
    _ = θ := by
      simp [← reassoc_of% h_θ]

partial def naturality (p : NormalizedHom) (η : Expr) : BicategoryM Expr := do
  match η.getAppFnArgs with
  | (``Iso.hom, #[_, _, _, _, η]) =>
    match (← whnfR η).getAppFnArgs with
    | (``Bicategory.associator, #[_, _, _, _, _, _, f, g, h]) =>
      withTraceNode `bicategory (fun _ => return m!"associator") do
        let ⟨pf, η_f⟩ ← normalize p f
        let ⟨pfg, η_g⟩ ← normalize pf g
        let ⟨pfgh, η_h⟩ ← normalize pfg h
        let result ← mkNaturalityAssociator p.e f g h pf.e pfg.e pfgh.e η_f η_g η_h
        trace[bicategory] m!"{checkEmoji} {← inferType result}"
        return result
    | (``Bicategory.leftUnitor, #[_, _, _, _, f]) =>
      withTraceNode `bicategory (fun _ => return m!"leftUnitor") do
        let ⟨pf, η_f⟩ ← normalize p f
        let result ← mkNaturalityLeftUnitor p.e f pf.e η_f
        trace[bicategory] m!"{checkEmoji} {← inferType result}"
        return result
    | (``Bicategory.rightUnitor, #[_, _, _, _, f]) =>
      withTraceNode `bicategory (fun _ => return m!"rightUnitor") do
        let ⟨pf, η_f⟩ ← normalize p f
        let result ← mkNaturalityRightUnitor p.e f pf.e η_f
        trace[bicategory] m!"{checkEmoji} {← inferType result}"
        return result
    | _ => throwError "failed to prove the naturality for {η}"
  | (``Iso.inv, #[_, _, _, _, η]) =>
    match (← whnfR η).getAppFnArgs with
    | (``Bicategory.associator, #[_, _, _, _, _, _, f, g, h]) =>
      withTraceNode `bicategory (fun _ => return m!"associatorInv") do
        let ⟨pf, η_f⟩ ← normalize p f
        let ⟨pfg, η_g⟩ ← normalize pf g
        let ⟨pfgh, η_h⟩ ← normalize pfg h
        let result ← mkNaturalityAssociatorInv p.e f g h pf.e pfg.e pfgh.e η_f η_g η_h
        trace[bicategory] m!"{checkEmoji} {← inferType result}"
        return result
    | (``Bicategory.leftUnitor, #[_, _, _, _, f]) =>
      withTraceNode `bicategory (fun _ => return m!"leftUnitorInv") do
        let ⟨pf, η_f⟩ ← normalize p f
        let result ← mkNaturalityLeftUnitorInv p.e f pf.e η_f
        trace[bicategory] m!"{checkEmoji} {← inferType result}"
        return result
    | (``Bicategory.rightUnitor, #[_, _, _, _, f]) =>
      withTraceNode `bicategory (fun _ => return m!"rightUnitorInv") do
        let ⟨pf, η_f⟩ ← normalize p f
        let result ← mkNaturalityRightUnitorInv p.e f pf.e η_f
        trace[bicategory] m!"{checkEmoji} {← inferType result}"
        return result
    | _ => throwError "failed to prove the naturality for {η}"
  | _ =>  match (← whnfR η).getAppFnArgs with
    | (``CategoryStruct.id, #[_, _, f]) =>
      withTraceNode `bicategory (fun _ => return m!"id") do
        let ⟨pf, η_f⟩ ← normalize p f
        let result ← mkNaturalityId p.e f pf.e η_f
        trace[bicategory] m!"{checkEmoji} {← inferType result}"
        return result
    | (``CategoryStruct.comp, #[_, _, f, g, h, η, θ]) =>
      withTraceNode `bicategory (fun _ => return m!"comp") do
        let ⟨pf, η_f⟩ ← normalize p f
        let ⟨_, η_g⟩ ← normalize p g
        let ⟨_, η_h⟩ ← normalize p h
        let ih_η ← naturality p η
        let ih_θ ← naturality p θ
        let result ← mkNaturalityComp p.e f g h pf.e η θ η_f η_g η_h ih_η ih_θ
        trace[bicategory] m!"{checkEmoji} {← inferType result}"
        return result
    | (``Bicategory.whiskerLeft, #[_, _, _, _, _, f, g, h, η]) =>
      withTraceNode `bicategory (fun _ => return m!"whiskerLeft") do
        let ⟨pf, η_f⟩ ← normalize p f
        let ⟨pfg, η_fg⟩ ← normalize pf g
        let ⟨_, η_fh⟩ ← normalize pf h
        let ih ← naturality pf η
        let result ← mkNaturalityWhiskerLeft p.e f g h pf.e pfg.e η η_f η_fg η_fh ih
        trace[bicategory] m!"{checkEmoji} {← inferType result}"
        return result
    | (``Bicategory.whiskerRight, #[_, _, _, _, _, f, g, η, h]) =>
      withTraceNode `bicategory (fun _ => return m!"whiskerRight") do
        let ⟨pf, η_f⟩ ← normalize p f
        let ⟨_, η_g⟩ ← normalize p g
        let ⟨pfh, η_fh⟩ ← normalize pf h
        let ih ← naturality p η
        let result ← mkNaturalityWhiskerRight p.e f g h pf.e pfh.e η η_f η_g η_fh ih
        trace[bicategory] m!"{checkEmoji} {← inferType result}"
        return result
    | (``bicategoricalComp, #[_, _, _, _, _, _, _, _, inst, η, θ]) =>
      withTraceNode `bicategory (fun _ => return m!"bicategoricalComp") do
        let α ← mkAppOptM ``BicategoricalCoherence.hom #[none, none, none, none, none, none, inst]
        let αθ ← mkComp₂ α θ
        let ηαθ ← mkComp₂ η αθ
        naturality p ηαθ
      | (``BicategoricalCoherence.hom, #[_, _, _, _, _, _, _]) =>
        withTraceNode `bicategory (fun _ => return m!"bicategoricalCoherence.hom") do
          let (η', _) ← dsimp η
            { simpTheorems := #[.addDeclToUnfoldCore {} ``BicategoricalCoherence.hom] }
          naturality p η'
    | _ => throwError "failed to prove the naturality for {η}"

def pureCoherence (mvarId : MVarId) : MetaM (List MVarId) :=
  mvarId.withContext do
    withTraceNode `bicategory (fun ex => match ex with
      | .ok _ => return m!"{checkEmoji} coherence equality: {← mvarId.getType}"
      | .error err => return m!"{crossEmoji} {err.toMessageData}") do
      let e ← instantiateMVars <| ← mvarId.getType
      let some (_, η, θ) := (← whnfR e).eq?
        | throwError "coherence requires an equality goal"
      let f ← srcExpr η
      let g ← tgtExpr η
      let a ← srcExpr f
      let ctx ← mkContext η
      BicategoryM.run ctx do
        trace[bicategory] m!"LHS"
        let id_a ← normalizedHom.nilM a
        let ⟨_, η_f⟩ ← normalize id_a f
        let Hη ← naturality id_a η
        trace[bicategory] m!"RHS"
        let ⟨_, η_g⟩ ← normalize id_a g
        let Hθ ← naturality id_a θ
        let H ← mkAppM ``of_normalize_eq #[η, θ, η_f, η_g, Hη, Hθ]
        mvarId.apply H

elab "bicategory_coherence" : tactic => withMainContext do
  let g ← getMainGoal
  replaceMainGoal <| ← pureCoherence g

theorem mk_eq_of_cons {C : Type u} [CategoryStruct.{v} C]
    {f₁ f₂ f₃ f₄ : C}
    (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs ηs' : f₃ ⟶ f₄)
    (pf_α : α = α') (pf_η : η = η') (pf_ηs : ηs = ηs') :
    α ≫ η ≫ ηs = α' ≫ η' ≫ ηs' := by
  simp [pf_α, pf_η, pf_ηs]

/-- Transform an equality between 2-morphisms into the equality between their normalizations. -/
def mkEqOfHom₂ (mvarId : MVarId) : MetaM Expr := do
  let some (_, e₁, e₂) := (← whnfR <| ← instantiateMVars <| ← mvarId.getType).eq?
    | throwError "bicategory requires an equality goal"
  let ctx ← mkContext e₁
  BicategoryM.run ctx do
    let ⟨e₁', p₁⟩ ← eval e₁
    let ⟨e₂', p₂⟩ ← eval e₂
    mkAppM ``mk_eq #[e₁, e₂, ← e₁'.e, ← e₂'.e, p₁, p₂]

def ofNormalizedEq (mvarId : MVarId) : MetaM (List MVarId) := do
  mvarId.withContext do
    let e ← instantiateMVars <| ← mvarId.getType
    let some (_, e₁, e₂) := (← whnfR e).eq? | throwError "bicategory requires an equality goal"
    match (← whnfR e₁).getAppFnArgs, (← whnfR e₂).getAppFnArgs with
    | (``CategoryStruct.comp, #[_, _, _, _, _, α, η]) ,
      (``CategoryStruct.comp, #[_, _, _, _, _, α', η']) =>
      match (← whnfR η).getAppFnArgs, (← whnfR η').getAppFnArgs with
      | (``CategoryStruct.comp, #[_, _, _, _, _, η, ηs]),
        (``CategoryStruct.comp, #[_, _, _, _, _, η', ηs']) =>
        let pf_α ← mkFreshExprMVar (← Meta.mkEq α α')
        let pf_η  ← mkFreshExprMVar (← Meta.mkEq η η')
        let pf_ηs ← mkFreshExprMVar (← Meta.mkEq ηs ηs')
        let x ← mvarId.apply (← mkAppM ``mk_eq_of_cons #[α, α', η, η', ηs, ηs', pf_α, pf_η, pf_ηs])
        return x
      | _, _ => throwError "failed to make a normalized equality for {e}"
    | _, _ => throwError "failed to make a normalized equality for {e}"

def bicategory (mvarId : MVarId) : MetaM (List MVarId) :=
  mvarId.withContext do
    let mvarIds ← mvarId.apply (← mkEqOfHom₂ mvarId)
    let mvarIds' ← repeat' (fun i ↦ ofNormalizedEq i) mvarIds
    let mvarIds'' ← mvarIds'.mapM fun mvarId => do
      withTraceNode `bicategory (fun _ => do return m!"goal: {← mvarId.getType}") do
        try
          mvarId.refl
          trace[bicategory] m!"{checkEmoji} refl"
          return [mvarId]
        catch _ =>
          try
            pureCoherence mvarId
          catch _ => return [mvarId]
    return mvarIds''.join

/-- Normalize the both sides of an equality. -/
elab "bicategory" : tactic => withMainContext do
  replaceMainGoal (← bicategory (← getMainGoal))

end Bicategory

end Mathlib.Tactic
