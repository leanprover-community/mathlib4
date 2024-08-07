/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.Tactic.CategoryTheory.Monoidal

/-!
# A `coherence` tactic for monoidal categories

-/

open Lean Elab Meta Tactic
open CategoryTheory

universe v u

namespace Mathlib.Tactic.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

open MonoidalCategory

/-- Make a `Iso.refl` expression. -/
def mkIsoRefl (f : Expr) : MonoidalM Expr := do
  let ctx ← read
  return mkAppN (.const ``Iso.refl (← getLevels))
    #[ctx.C, ctx.instCat, f]

/-- Make a `whiskerRightIso` expression. -/
def mkWhiskerRightIso (η : Expr) (h : Expr) : MonoidalM Expr := do
  let ctx ← read
  let f ← srcExprOfIso η
  let g ← tgtExprOfIso η
  return mkAppN (.const ``MonoidalCategory.whiskerRightIso (← getLevels))
    #[ctx.C, ctx.instCat, ctx.instMonoidal, f, g, η, h]

/-- Make a `Iso.trans` expression. -/
def mkIsoTrans (η θ : Expr) : MonoidalM Expr := do
  let ctx ← read
  let f ← srcExprOfIso η
  let g ← tgtExprOfIso η
  let h ← tgtExprOfIso θ
  return mkAppN (.const ``Iso.trans (← getLevels))
    #[ctx.C, ctx.instCat, f, g, h, η, θ]

/-- Make a `Iso.symm` expression. -/
def mkIsoSymm (η : Expr) : MonoidalM Expr := do
  let ctx ← read
  let f ← srcExprOfIso η
  let g ← tgtExprOfIso η
  return mkAppN (.const ``Iso.symm (← getLevels))
    #[ctx.C, ctx.instCat, f, g, η]

inductive NormalizedHom (α : Type u) : Type u
  | nil : NormalizedHom α
  | cons : NormalizedHom α → α → NormalizedHom α

structure Coherence.Result where
  /-- The normalized 1-morphism. -/
  normalizedHom : NormalizedHom Expr
  /-- The 2-morphism from the original 1-morphism to the normalized 1-morphism. -/
  toNormalize : Expr

abbrev normalizeIso {p f g pf pfg : C} (η_f : p ⊗ f ≅ pf) (η_g : pf ⊗ g ≅ pfg) :=
  (α_ _ _ _).symm ≪≫ whiskerRightIso η_f g ≪≫ η_g

theorem naturality_associator {p f g h pf pfg pfgh : C}
    (η_f : (p ⊗ f) ≅ pf) (η_g : (pf ⊗ g) ≅ pfg) (η_h : pfg ⊗ h ≅ pfgh) :
    p ◁ (α_ f g h).hom ≫ (normalizeIso η_f (normalizeIso η_g η_h)).hom =
    (normalizeIso (normalizeIso η_f η_g) η_h).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, whiskerRight_tensor, Category.assoc,
    Iso.hom_inv_id_assoc, pentagon_hom_inv_inv_inv_inv_assoc, whiskerRightIso_trans,
    Iso.trans_assoc, Iso.refl_hom, Category.comp_id]

def mkNaturalityAssociator (p f g h η_f η_g η_h : Expr) : MonoidalM Expr := do
  let ctx ← read
  let pf ← tgtExprOfIso η_f
  let pfg ← tgtExprOfIso η_g
  let pfgh ← tgtExprOfIso η_h
  return mkAppN (.const ``naturality_associator (← getLevels))
    #[ctx.C, ctx.instCat, ctx.instMonoidal, p, f, g, h, pf, pfg, pfgh, η_f, η_g, η_h]

theorem naturality_associator_inv {p f g h pf pfg pfgh : C}
    (η_f : (p ⊗ f) ≅ pf) (η_g : (pf ⊗ g) ≅ pfg) (η_h : pfg ⊗ h ≅ pfgh) :
    p ◁ (α_ f g h).inv ≫ (normalizeIso (normalizeIso η_f η_g) η_h).hom =
    (normalizeIso η_f (normalizeIso η_g η_h)).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_trans, Iso.trans_assoc,
    whiskerRightIso_hom, pentagon_inv_assoc, whiskerRight_tensor, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id]

def mkNaturalityAssociatorInv (p f g h η_f η_g η_h : Expr) : MonoidalM Expr := do
  let ctx ← read
  let pf ← tgtExprOfIso η_f
  let pfg ← tgtExprOfIso η_g
  let pfgh ← tgtExprOfIso η_h
  return mkAppN (.const ``naturality_associator_inv (← getLevels))
    #[ctx.C, ctx.instCat, ctx.instMonoidal, p, f, g, h, pf, pfg, pfgh, η_f, η_g, η_h]

theorem naturality_leftUnitor {p f pf : C} (η_f : p ⊗ f ≅ pf) :
    p ◁ (λ_ f).hom ≫ η_f.hom = (normalizeIso (ρ_ p) η_f).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, triangle_assoc_comp_right_assoc,
    Iso.refl_hom, Category.comp_id]

def mkNaturalityLeftUnitor (p f η_f : Expr) : MonoidalM Expr := do
  let ctx ← read
  let pf ← tgtExprOfIso η_f
  return mkAppN (.const ``naturality_leftUnitor (← getLevels))
    #[ctx.C, ctx.instCat, ctx.instMonoidal, p, f, pf, η_f]

theorem naturality_leftUnitor_inv {p f pf : C} (η_f : p ⊗ f ≅ pf) :
    p ◁ (λ_ f).inv ≫ (normalizeIso (ρ_ p) η_f).hom = η_f.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, triangle_assoc_comp_right_assoc,
    whiskerLeft_inv_hom_assoc, Iso.refl_hom, Category.comp_id]

def mkNaturalityLeftUnitorInv (p f η_f : Expr) : MonoidalM Expr := do
  let ctx ← read
  let pf ← tgtExprOfIso η_f
  return mkAppN (.const ``naturality_leftUnitor_inv (← getLevels))
    #[ctx.C, ctx.instCat, ctx.instMonoidal, p, f, pf, η_f]

theorem naturality_rightUnitor {p f pf : C} (η_f : p ⊗ f ≅ pf) :
    p ◁ (ρ_ f).hom ≫ η_f.hom = (normalizeIso η_f (ρ_ pf)).hom := by
  simp only [whiskerLeft_rightUnitor, Category.assoc, Iso.trans_hom, Iso.symm_hom,
    whiskerRightIso_hom, MonoidalCategory.whiskerRight_id, Iso.inv_hom_id, Category.comp_id,
    Iso.refl_hom]

def mkNaturalityRightUnitor (p f η_f : Expr) : MonoidalM Expr := do
  let ctx ← read
  let pf ← tgtExprOfIso η_f
  return mkAppN (.const ``naturality_rightUnitor (← getLevels))
    #[ctx.C, ctx.instCat, ctx.instMonoidal, p, f, pf, η_f]

theorem naturality_rightUnitor_inv {p f pf : C} (η_f : p ⊗ f ≅ pf) :
    p ◁ (ρ_ f).inv ≫ (normalizeIso η_f (ρ_ pf)).hom = η_f.hom := by
  simp only [whiskerLeft_rightUnitor_inv, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom,
    MonoidalCategory.whiskerRight_id, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.refl_hom]

def mkNaturalityRightUnitorInv (p f η_f : Expr) : MonoidalM Expr := do
  let ctx ← read
  let pf ← tgtExprOfIso η_f
  return mkAppN (.const ``naturality_rightUnitor_inv (← getLevels))
    #[ctx.C, ctx.instCat, ctx.instMonoidal, p, f, pf, η_f]

theorem naturality_id {p f pf : C} (η_f : p ⊗ f ≅ pf) :
    p ◁ (𝟙 f) ≫ η_f.hom = η_f.hom := by
  simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp]

def mkNaturalityId (p f η_f : Expr) : MonoidalM Expr := do
  let ctx ← read
  let pf ← tgtExprOfIso η_f
  return mkAppN (.const ``naturality_id (← getLevels))
    #[ctx.C, ctx.instCat, ctx.instMonoidal, p, f, pf, η_f]

theorem naturality_comp {p f g h pf : C}
    (η : f ⟶ g) (θ : g ⟶ h) (η_f : (p ⊗ f) ≅ pf) (η_g : (p ⊗ g) ≅ pf) (η_h : p ⊗ h ≅ pf)
    (ih_η : p ◁ η ≫ η_g.hom = η_f.hom) (ih_θ : p ◁ θ ≫ η_h.hom = η_g.hom) :
    p ◁ (η ≫ θ) ≫ η_h.hom = η_f.hom := by
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc, ← ih_η, ← ih_θ]

def mkNaturalityComp (p f g h η θ η_f η_g η_h ih_η ih_θ : Expr) : MonoidalM Expr := do
  let ctx ← read
  let pf ← tgtExprOfIso η_f
  return mkAppN (.const ``naturality_comp (← getLevels))
    #[ctx.C, ctx.instCat, ctx.instMonoidal, p, f, g, h, pf, η, θ, η_f, η_g, η_h, ih_η, ih_θ]

theorem naturality_whiskerLeft {p f g h pf pfg : C} (η : g ⟶ h) (η_f : (p ⊗ f) ≅ pf)
    (η_fg : (pf ⊗ g) ≅ pfg)
    (η_fh : (pf ⊗ h) ≅ pfg)
    (ih_η : pf ◁ η ≫ η_fh.hom = η_fg.hom) :
    p ◁ (f ◁ η) ≫ (normalizeIso η_f η_fh).hom =
    (normalizeIso η_f η_fg).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, ← ih_η, ← whisker_exchange_assoc,
    tensor_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id]

def mkNaturalityWhiskerLeft (p f g h η η_f η_fg η_fh ih_η : Expr) : MonoidalM Expr := do
  let ctx ← read
  let pf ← tgtExprOfIso η_f
  let pfg ← tgtExprOfIso η_fg
  return mkAppN (.const ``naturality_whiskerLeft (← getLevels))
    #[ctx.C, ctx.instCat, ctx.instMonoidal, p, f, g, h, pf, pfg, η, η_f, η_fg, η_fh, ih_η]

theorem naturality_whiskerRight {p f g h pf pfh : C} (η : f ⟶ g) (η_f : (p ⊗ f) ≅ pf)
    (η_g : (p ⊗ g) ≅ pf)
    (η_fh : (pf ⊗ h) ≅ pfh)
    (ih_η : p ◁ η ≫ η_g.hom = η_f.hom) :
    p ◁ (η ▷ h) ≫ (normalizeIso η_g η_fh).hom =
    (normalizeIso η_f η_fh).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, ← ih_η, comp_whiskerRight,
    whisker_assoc, Category.assoc, Iso.inv_hom_id_assoc]

def mkNaturalityWhiskerRight (p f g h η η_f η_g η_fh ih_η : Expr) : MonoidalM Expr := do
  let ctx ← read
  let pf ← tgtExprOfIso η_f
  let pfh ← tgtExprOfIso η_fh
  return mkAppN (.const ``naturality_whiskerRight (← getLevels))
    #[ctx.C, ctx.instCat, ctx.instMonoidal, p, f, g, h, pf, pfh, η, η_f, η_g, η_fh, ih_η]

theorem naturality_tensorHom {p f₁ g₁ f₂ g₂ pf₁ pf₁f₂ : C} (η : f₁ ⟶ g₁) (θ : f₂ ⟶ g₂)
    (η_f₁ : p ⊗ f₁ ≅ pf₁) (η_g₁ : p ⊗ g₁ ≅ pf₁)
    (η_f₂ : pf₁ ⊗ f₂ ≅ pf₁f₂) (η_g₂ : pf₁ ⊗ g₂ ≅ pf₁f₂)
    (ih_η : p ◁ η ≫ η_g₁.hom = η_f₁.hom)
    (ih_θ : pf₁ ◁ θ ≫ η_g₂.hom = η_f₂.hom) :
    p ◁ (η ⊗ θ) ≫ (normalizeIso η_g₁ η_g₂).hom = (normalizeIso η_f₁ η_f₂).hom := by
  simp only [tensorHom_def, MonoidalCategory.whiskerLeft_comp, Iso.trans_hom, Iso.symm_hom,
    whiskerRightIso_hom, Category.assoc, ← ih_η, comp_whiskerRight, whisker_assoc, ← ih_θ,
    Iso.inv_hom_id_assoc]
  simp only [← whisker_exchange_assoc, associator_inv_naturality_right_assoc]

def mkNaturalityTensorHom (p f₁ g₁ f₂ g₂ η θ η_f₁ η_g₁ η_f₂ η_g₂ ih_η ih_θ : Expr) :
    MonoidalM Expr := do
  let ctx ← read
  let pf₁ ← tgtExprOfIso η_f₁
  let pf₁f₂ ← tgtExprOfIso η_f₂
  return mkAppN (.const ``naturality_tensorHom (← getLevels))
    #[ctx.C, ctx.instCat, ctx.instMonoidal,
      p, f₁, g₁, f₂, g₂, pf₁, pf₁f₂, η, θ, η_f₁, η_g₁, η_f₂, η_g₂, ih_η, ih_θ]

def eval₁ (p : NormalizedHom Expr) : MonoidalM Expr := do
  match p with
  | .nil => mkTensorUnit
  | .cons fs f => mkTensorObj (← eval₁ fs) f

partial def normalize (p : NormalizedHom Expr) (f : Expr) : MonoidalM Coherence.Result := do
  if let some _ ← isTensorUnit? f then
    let α ← mkRightUnitor (← eval₁ p)
    return ⟨p, α⟩
  else if let some (f, g) ← isTensorObj? f then
    let ⟨pf, Hf⟩ ← normalize p f
    let Hf' ← mkWhiskerRightIso Hf g
    let ⟨pfg, Hg⟩ ← normalize pf g
    let η ← mkIsoTrans Hf' Hg
    let alpha ← mkIsoSymm (← mkAssociator (← eval₁ p) f g)
    let η' ← mkIsoTrans alpha η
    return ⟨pfg, η'⟩
  else
    let α ← mkIsoRefl (← eval₁ (p.cons f))
    return ⟨p.cons f, α⟩

theorem of_normalize_eq {f g f' : C} (η θ : f ⟶ g) (η_f : 𝟙_ C ⊗ f ≅ f') (η_g : 𝟙_ C ⊗ g ≅ f')
  (h_η : 𝟙_ C ◁ η ≫ η_g.hom = η_f.hom)
  (h_θ : 𝟙_ C ◁ θ ≫ η_g.hom = η_f.hom) : η = θ := by
  simp only [id_whiskerLeft, Category.assoc] at h_η h_θ
  calc
    η = (λ_ f).inv ≫ η_f.hom ≫ η_g.inv ≫ (λ_ g).hom := by
      simp [← reassoc_of% h_η]
    _ = θ := by
      simp [← reassoc_of% h_θ]

partial def naturality (p : NormalizedHom Expr) (η : Expr) : MonoidalM Expr := do
  match η.getAppFnArgs with
  | (``Iso.hom, #[_, _, _, _, η]) =>
    match (← whnfR η).getAppFnArgs with
    | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) =>
      withTraceNode `monoidal (fun _ => return m!"associator") do
        let ⟨pf, η_f⟩ ← normalize p f
        let ⟨pfg, η_g⟩ ← normalize pf g
        let ⟨_, η_h⟩ ← normalize pfg h
        let result ← mkNaturalityAssociator (← eval₁ p) f g h η_f η_g η_h
        trace[monoidal] m!"{checkEmoji} {← inferType result}"
        return result
    | (``MonoidalCategoryStruct.leftUnitor, #[_, _, _, f]) =>
      withTraceNode `monoidal (fun _ => return m!"leftUnitor") do
        let ⟨_, η_f⟩ ← normalize p f
        let result ← mkNaturalityLeftUnitor (← eval₁ p) f η_f
        trace[monoidal] m!"{checkEmoji} {← inferType result}"
        return result
    | (``MonoidalCategoryStruct.rightUnitor, #[_, _, _, f]) =>
      withTraceNode `monoidal (fun _ => return m!"rightUnitor") do
        let ⟨_, η_f⟩ ← normalize p f
        let result ← mkNaturalityRightUnitor (← eval₁ p) f η_f
        trace[monoidal] m!"{checkEmoji} {← inferType result}"
        return result
    | _ => throwError "failed to prove the naturality for {η}"
  | (``Iso.inv, #[_, _, _, _, η]) =>
    match (← whnfR η).getAppFnArgs with
    | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) =>
      withTraceNode `monoidal (fun _ => return m!"associator_inv") do
        let ⟨pf, η_f⟩ ← normalize p f
        let ⟨pfg, η_g⟩ ← normalize pf g
        let ⟨_, η_h⟩ ← normalize pfg h
        let result ← mkNaturalityAssociatorInv (← eval₁ p) f g h η_f η_g η_h
        trace[monoidal] m!"{checkEmoji} {← inferType result}"
        return result
    | (``MonoidalCategoryStruct.leftUnitor, #[_, _, _, f]) =>
      withTraceNode `monoidal (fun _ => return m!"leftUnitor_inv") do
        let ⟨_, η_f⟩ ← normalize p f
        let result ← mkNaturalityLeftUnitorInv (← eval₁ p) f η_f
        trace[monoidal] m!"{checkEmoji} {← inferType result}"
        return result
    | (``MonoidalCategoryStruct.rightUnitor, #[_, _, _, f]) =>
      withTraceNode `monoidal (fun _ => return m!"rightUnitor_inv") do
        let ⟨_, η_f⟩ ← normalize p f
        let result ← mkNaturalityRightUnitorInv (← eval₁ p) f η_f
        trace[monoidal] m!"{checkEmoji} {← inferType result}"
        return result
    | _ => throwError "failed to prove the naturality for {η}"
  | _ =>  match (← whnfR η).getAppFnArgs with
    | (``CategoryStruct.id, #[_, _, f]) =>
      withTraceNode `monoidal (fun _ => return m!"id") do
        let ⟨_, η_f⟩ ← normalize p f
        let result ← mkNaturalityId (← eval₁ p) f η_f
        trace[monoidal] m!"{checkEmoji} {← inferType result}"
        return result
    | (``CategoryStruct.comp, #[_, _, f, g, h, η, θ]) =>
      withTraceNode `monoidal (fun _ => return m!"comp") do
        let ⟨_, η_f⟩ ← normalize p f
        let ⟨_, η_g⟩ ← normalize p g
        let ⟨_, η_h⟩ ← normalize p h
        let ih_η ← naturality p η
        let ih_θ ← naturality p θ
        let result ← mkNaturalityComp (← eval₁ p) f g h η θ η_f η_g η_h ih_η ih_θ
        trace[monoidal] m!"{checkEmoji} {← inferType result}"
        return result
    | (``MonoidalCategoryStruct.whiskerLeft, #[_, _, _, f, g, h, η]) =>
      withTraceNode `monoidal (fun _ => return m!"whiskerLeft") do
        let ⟨pf, η_f⟩ ← normalize p f
        let ⟨_, η_fg⟩ ← normalize pf g
        let ⟨_, η_fh⟩ ← normalize pf h
        let ih ← naturality pf η
        let result ← mkNaturalityWhiskerLeft (← eval₁ p) f g h η η_f η_fg η_fh ih
        trace[monoidal] m!"{checkEmoji} {← inferType result}"
        return result
    | (``MonoidalCategoryStruct.whiskerRight, #[_, _, _, f, g, η, h]) =>
      withTraceNode `monoidal (fun _ => return m!"whiskerRight") do
        let ⟨pf, η_f⟩ ← normalize p f
        let ⟨_, η_g⟩ ← normalize p g
        let ⟨_, η_fh⟩ ← normalize pf h
        let ih ← naturality p η
        let result ← mkNaturalityWhiskerRight (← eval₁ p) f g h η η_f η_g η_fh ih
        trace[monoidal] m!"{checkEmoji} {← inferType result}"
        return result
    | (``monoidalComp, #[_, _, _, f, g, _, inst, η, θ]) =>
      withTraceNode `monoidal (fun _ => return m!"monoidalComp") do
        let α ← mkMonoidalCoherenceHom f g inst
        let αθ ← mkComp α θ
        let ηαθ ← mkComp η αθ
        naturality p ηαθ
    | (``MonoidalCoherence.hom, #[_, _, _, _, _]) =>
      withTraceNode `monoidal (fun _ => return m!"MonoidalCoherence.hom") do
        let (η', _) ← dsimp η
          { simpTheorems := #[.addDeclToUnfoldCore {} ``MonoidalCoherence.hom] }
        naturality p η'
    | (``MonoidalCategoryStruct.tensorHom, #[_, _, _, f₁, g₁, f₂, g₂, η, θ]) =>
      withTraceNode `monoidal (fun _ => return m!"tensorHom") do
        let ⟨pf₁, η_f₁⟩ ← normalize p f₁
        let ⟨pg₁, η_g₁⟩ ← normalize p g₁
        let ⟨_, η_f₂⟩ ← normalize pf₁ f₂
        let ⟨_, η_g₂⟩ ← normalize pg₁ g₂
        let ih_η ← naturality p η
        let ih_θ ← naturality pf₁ θ
        let result ← mkNaturalityTensorHom (← eval₁ p) f₁ g₁ f₂ g₂ η θ η_f₁ η_g₁ η_f₂ η_g₂ ih_η ih_θ
        trace[monoidal] m!"{checkEmoji} {← inferType result}"
        return result
    | _ => throwError "failed to prove the naturality for {η}"

def pure_coherence (mvarId : MVarId) : MetaM (List MVarId) :=
  mvarId.withContext do
    withTraceNode `monoidal (fun ex => match ex with
      | .ok _ => return m!"{checkEmoji} coherence equality: {← mvarId.getType}"
      | .error err => return m!"{crossEmoji} {err.toMessageData}") do
      let e ← instantiateMVars <| ← mvarId.getType
      let some (_, η, θ) := (← whnfR e).eq?
        | throwError "coherence requires an equality goal"
      let f ← srcExpr η
      let g ← tgtExpr η
      let some ctx ← mkContext? η | throwError "the lhs and rhs must be 2-morphisms"
      MonoidalM.run ctx do
        trace[monoidal] m!"LHS"
        let ⟨_, αf⟩ ← normalize .nil f
        let Hη ← naturality .nil η
        trace[monoidal] m!"RHS"
        let ⟨_, αg⟩ ← normalize .nil g
        let Hθ ← naturality .nil θ
        let H ← mkAppM ``of_normalize_eq #[η, θ, αf, αg, Hη, Hθ]
        mvarId.apply H

elab "monoidal_coherence" : tactic => withMainContext do
  replaceMainGoal <| ← pure_coherence <| ← getMainGoal

theorem mk_eq_of_cons {C : Type u} [CategoryStruct.{v} C]
    {f₁ f₂ f₃ f₄ : C}
    (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs ηs' : f₃ ⟶ f₄)
    (pf_α : α = α') (pf_η : η = η') (pf_ηs : ηs = ηs') :
    α ≫ η ≫ ηs = α' ≫ η' ≫ ηs' := by
  simp [pf_α, pf_η, pf_ηs]

/-- Transform an equality between 2-morphisms into the equality between their normalizations. -/
def mkEqOfHom₂ (mvarId : MVarId) : MetaM Expr := do
  let some (_, e₁, e₂) := (← whnfR <| ← instantiateMVars <| ← mvarId.getType).eq?
    | throwError "monoidal requires an equality goal"
  let some c ← mkContext? e₁ | throwError "monoidal requires an equality goal"
  MonoidalM.run c do
    let ⟨e₁', p₁⟩ ← eval e₁
    let ⟨e₂', p₂⟩ ← eval e₂
    mkAppM ``mk_eq #[e₁, e₂, ← e₁'.e, ← e₂'.e, p₁, p₂]

def ofNormalizedEq (mvarId : MVarId) : MetaM (List MVarId) :=
  mvarId.withContext do
    let e ← instantiateMVars <| ← mvarId.getType
    let some (_, e₁, e₂) := (← whnfR e).eq? | throwError "monoidal requires an equality goal"
    match (← whnfR e₁).getAppFnArgs, (← whnfR e₂).getAppFnArgs with
    | (``CategoryStruct.comp, #[_, _, _, _, _, α, η]) ,
      (``CategoryStruct.comp, #[_, _, _, _, _, α', η']) =>
      match (← whnfR η).getAppFnArgs, (← whnfR η').getAppFnArgs with
      | (``CategoryStruct.comp, #[_, _, _, _, _, η, ηs]),
        (``CategoryStruct.comp, #[_, _, _, _, _, η', ηs']) =>
        let pf_α ← mkFreshExprMVar (← mkEq α α')
        let pf_η  ← mkFreshExprMVar (← mkEq η η')
        let pf_ηs ← mkFreshExprMVar (← mkEq ηs ηs')
        let x ← mvarId.apply (← mkAppM ``mk_eq_of_cons #[α, α', η, η', ηs, ηs', pf_α, pf_η, pf_ηs])
        return x
      | _, _ => throwError "failed to make a normalized equality for {e}"
    | _, _ => throwError "failed to make a normalized equality for {e}"

def monoidal (mvarId : MVarId) : MetaM (List MVarId) :=
  mvarId.withContext do
    let mvarIds ← mvarId.apply (← mkEqOfHom₂ mvarId)
    let mvarIds' ← repeat' (fun i ↦ ofNormalizedEq i) mvarIds
    let mvarIds'' ← mvarIds'.mapM fun mvarId => do
      try
        mvarId.refl
        return [mvarId]
      catch _ =>
        try
          pure_coherence mvarId
        catch _ => return [mvarId]
    return mvarIds''.join

/-- Normalize the both sides of an equality. -/
elab "monoidal" : tactic => withMainContext do
  replaceMainGoal <| ← monoidal <| ← getMainGoal

end Monoidal

end Mathlib.Tactic
