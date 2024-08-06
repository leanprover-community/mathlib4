import Mathlib.Tactic.CategoryTheory.Monoidal

open Lean Elab Meta Tactic
open CategoryTheory

universe v u

namespace Mathlib.Tactic.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

open MonoidalCategory

inductive NormalizedHom (α : Type u) : Type u
  | nil : NormalizedHom α
  | cons : NormalizedHom α → α → NormalizedHom α

structure Coherence.Result where
  /-- The normalized 1-morphism. -/
  normalizedHom : NormalizedHom Expr
  /-- The 2-morphism to the normalized 1-morphism. -/
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

theorem naturality_associator_inv {p f g h pf pfg pfgh : C}
    (η_f : (p ⊗ f) ≅ pf) (η_g : (pf ⊗ g) ≅ pfg) (η_h : pfg ⊗ h ≅ pfgh) :
    p ◁ (α_ f g h).inv ≫ (normalizeIso (normalizeIso η_f η_g) η_h).hom =
    (normalizeIso η_f (normalizeIso η_g η_h)).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_trans, Iso.trans_assoc,
    whiskerRightIso_hom, pentagon_inv_assoc, whiskerRight_tensor, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id]

theorem naturality_leftUnitor {p f pf : C} (η_f : p ⊗ f ≅ pf) :
    p ◁ (λ_ f).hom ≫ η_f.hom = (normalizeIso (ρ_ p) η_f).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, triangle_assoc_comp_right_assoc,
    Iso.refl_hom, Category.comp_id]

theorem naturality_leftUnitor_inv {p f pf : C} (η_f : p ⊗ f ≅ pf) :
    p ◁ (λ_ f).inv ≫ (normalizeIso (ρ_ p) η_f).hom = η_f.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, triangle_assoc_comp_right_assoc,
    whiskerLeft_inv_hom_assoc, Iso.refl_hom, Category.comp_id]

theorem naturality_rightUnitor {p f pf : C} (η_f : p ⊗ f ≅ pf) :
    p ◁ (ρ_ f).hom ≫ η_f.hom = (normalizeIso η_f (ρ_ pf)).hom := by
  simp only [whiskerLeft_rightUnitor, Category.assoc, Iso.trans_hom, Iso.symm_hom,
    whiskerRightIso_hom, MonoidalCategory.whiskerRight_id, Iso.inv_hom_id, Category.comp_id,
    Iso.refl_hom]

theorem naturality_rightUnitor_inv {p f pf : C} (η_f : p ⊗ f ≅ pf) :
    p ◁ (ρ_ f).inv ≫ (normalizeIso η_f (ρ_ pf)).hom = η_f.hom := by
  simp only [whiskerLeft_rightUnitor_inv, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom,
    MonoidalCategory.whiskerRight_id, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.refl_hom]

theorem naturality_id {p f pf : C} (η_f : p ⊗ f ≅ pf) :
    p ◁ (𝟙 f) ≫ η_f.hom = η_f.hom := by
  simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp]

theorem naturality_comp {p f g h pf : C}
    (η : f ⟶ g) (θ : g ⟶ h) (η_f : (p ⊗ f) ≅ pf) (η_g : (p ⊗ g) ≅ pf) (η_h : p ⊗ h ≅ pf)
    (ih_η : p ◁ η ≫ η_g.hom = η_f.hom) (ih_θ : p ◁ θ ≫ η_h.hom = η_g.hom) :
    p ◁ (η ≫ θ) ≫ η_h.hom = η_f.hom := by
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc, ← ih_η, ← ih_θ]

theorem naturality_whiskerLeft {p f g h pf pfg : C} (η : g ⟶ h) (η_f : (p ⊗ f) ≅ pf)
    (η_fg : (pf ⊗ g) ≅ pfg)
    (η_fh : (pf ⊗ h) ≅ pfg)
    (ih_η : pf ◁ η ≫ η_fh.hom = η_fg.hom) :
    p ◁ (f ◁ η) ≫ (normalizeIso η_f η_fh).hom =
    (normalizeIso η_f η_fg).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, ← ih_η, ← whisker_exchange_assoc,
    tensor_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id]

theorem naturality_whiskerRight {p f g h pf pfh : C} (η : f ⟶ g) (η_f : (p ⊗ f) ≅ pf)
    (η_g : (p ⊗ g) ≅ pf)
    (η_fh : (pf ⊗ h) ≅ pfh)
    (ih_η : p ◁ η ≫ η_g.hom = η_f.hom) :
    p ◁ (η ▷ h) ≫ (normalizeIso η_g η_fh).hom =
    (normalizeIso η_f η_fh).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, ← ih_η, comp_whiskerRight,
    whisker_assoc, Category.assoc, Iso.inv_hom_id_assoc]

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

def eval₁ (p : NormalizedHom Expr) (C : Option Expr := none) : MetaM Expr := do
  match p with
  | .nil =>
    mkAppOptM ``MonoidalCategoryStruct.tensorUnit #[C, none, none]
  | .cons fs f => do
    let fs' ← eval₁ fs C
    mkAppM ``MonoidalCategory.tensorObj #[fs', f]

partial def normalize (p : NormalizedHom Expr) (f : Expr) : MetaM Coherence.Result := do
  let C ← inferType f
  if let some _ ← isTensorUnit? f then
    let α ← mkAppOptM ``MonoidalCategoryStruct.rightUnitor #[C, none, none, ← eval₁ p C]
    return ⟨p, α⟩
  else if let some (f, g) ← isTensorObj? f then
    let ⟨pf, Hf⟩ ← normalize p f
    let Hf' ← mkAppM ``MonoidalCategory.whiskerRightIso #[Hf, g]
    let ⟨pfg, Hg⟩ ← normalize pf g
    let η ← mkAppM ``Iso.trans #[Hf', Hg]
    let alpha ← mkAppM ``Iso.symm #[← mkAppM ``MonoidalCategory.associator #[← eval₁ p C, f, g]]
    let η' ← mkAppM ``Iso.trans #[alpha, η]
    return ⟨pfg, η'⟩
  else
    let α ← mkAppOptM ``Iso.refl #[C, none, ← eval₁ (p.cons f) C]
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

/-- The domain of a morphism. -/
def srcExpr (η : Expr) : MetaM Expr := do
  match (← whnfR (← inferType η)).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, f, _]) => return f
  | _ => throwError "{η} is not a morphism"

/-- The codomain of a morphism. -/
def tgtExpr (η : Expr) : MetaM Expr := do
  match (← whnfR (← inferType η)).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, _, g]) => return g
  | _ => throwError "{η} is not a morphism"

partial def naturality (p : NormalizedHom Expr) (η : Expr) : MetaM Expr := do
  match η.getAppFnArgs with
  | (``Iso.hom, #[_, _, _, _, η]) =>
    match (← whnfR η).getAppFnArgs with
    | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) =>
      let ⟨pf, η_f⟩ ← normalize p f
      let ⟨pfg, η_g⟩ ← normalize pf g
      let ⟨_, η_h⟩ ← normalize pfg h
      mkAppM ``naturality_associator #[η_f, η_g, η_h]
    | (``MonoidalCategoryStruct.leftUnitor, #[_, _, _, f]) =>
      let ⟨_, η_f⟩ ← normalize p f
      mkAppM ``naturality_leftUnitor #[η_f]
    | (``MonoidalCategoryStruct.rightUnitor, #[_, _, _, f]) =>
      let ⟨_, η_f⟩ ← normalize p f
      mkAppM ``naturality_rightUnitor #[η_f]
    | _ => throwError "failed to prove the naturality for {η}"
  | (``Iso.inv, #[_, _, _, _, η]) =>
    match (← whnfR η).getAppFnArgs with
    | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) =>
      let ⟨pf, η_f⟩ ← normalize p f
      let ⟨pfg, η_g⟩ ← normalize pf g
      let ⟨_, η_h⟩ ← normalize pfg h
      mkAppM ``naturality_associator_inv #[η_f, η_g, η_h]
    | (``MonoidalCategoryStruct.leftUnitor, #[_, _, _, f]) =>
      let ⟨_, η_f⟩ ← normalize p f
      mkAppM ``naturality_leftUnitor_inv #[η_f]
    | (``MonoidalCategoryStruct.rightUnitor, #[_, _, _, f]) =>
      let ⟨_, η_f⟩ ← normalize p f
      mkAppM ``naturality_rightUnitor_inv #[η_f]
    | _ => throwError "failed to prove the naturality for {η}"
  | _ =>  match (← whnfR η).getAppFnArgs with
    | (``CategoryStruct.id, #[_, _, f]) =>
      let ⟨_, η_f⟩ ← normalize p f
      mkAppM ``naturality_id #[η_f]
    | (``CategoryStruct.comp, #[_, _, f, g, h, η, θ]) =>
      let ⟨_, η_f⟩ ← normalize p f
      let ⟨_, η_g⟩ ← normalize p g
      let ⟨_, η_h⟩ ← normalize p h
      let ih_η ← naturality p η
      let ih_θ ← naturality p θ
      mkAppM ``naturality_comp #[η, θ, η_f, η_g, η_h, ih_η, ih_θ]
    | (``MonoidalCategoryStruct.whiskerLeft, #[_, _, _, f, g, h, η]) =>
      let ⟨pf, η_f⟩ ← normalize p f
      let ⟨_, η_fg⟩ ← normalize pf g
      let ⟨_, η_fh⟩ ← normalize pf h
      let ih ← naturality pf η
      mkAppM ``naturality_whiskerLeft #[η, η_f, η_fg, η_fh, ih]
    | (``MonoidalCategoryStruct.whiskerRight, #[_, _, _, f, g, η, h]) =>
      let ⟨pf, η_f⟩ ← normalize p f
      let ⟨_, η_g⟩ ← normalize p g
      let ⟨_, η_fh⟩ ← normalize pf h
      let ih ← naturality p η
      mkAppM ``naturality_whiskerRight #[η, η_f, η_g, η_fh, ih]
    | (``monoidalComp, #[_, _, _, _, _, _, inst, η, θ]) =>
        let α ← mkAppOptM ``MonoidalCoherence.hom #[none, none, none, none, inst]
        let αθ ← mkAppM ``CategoryStruct.comp #[α, θ]
        let ηαθ ← mkAppM ``CategoryStruct.comp #[η, αθ]
        naturality p ηαθ
    | (``MonoidalCoherence.hom, #[_, _, _, _, _]) =>
      let (η', _) ← dsimp η
        { simpTheorems := #[.addDeclToUnfoldCore {} ``MonoidalCoherence.hom] }
      naturality p η'
    | (``MonoidalCategoryStruct.tensorHom, #[_, _, _, f₁, g₁, f₂, g₂, η, θ]) =>
      let ⟨pf₁, η_f₁⟩ ← normalize p f₁
      let ⟨pg₁, η_g₁⟩ ← normalize p g₁
      let ⟨_, η_f₂⟩ ← normalize pf₁ f₂
      let ⟨_, η_g₂⟩ ← normalize pg₁ g₂
      let ih_η ← naturality p η
      let ih_θ ← naturality pf₁ θ
      mkAppM ``naturality_tensorHom #[η, θ, η_f₁, η_g₁, η_f₂, η_g₂, ih_η, ih_θ]
    | _ => throwError "failed to prove the naturality for {η}"

def pure_coherence (mvarId : MVarId) : MetaM (List MVarId) := mvarId.withContext do
  let some (_, η, θ) := (← whnfR <| ← mvarId.getType).eq?
    | throwError "monoidal requires an equality goal"
  let f ← srcExpr η
  let g ← tgtExpr η
  let ⟨_, αf⟩ ← normalize .nil f
  let ⟨_, αg⟩ ← normalize .nil g
  let Hη ← naturality .nil η
  let Hθ ← naturality .nil θ
  let H ← mkAppM ``of_normalize_eq #[η, θ, αf, αg, Hη, Hθ]
  mvarId.apply H

elab "monoidal_coherence" : tactic => withMainContext do
  let g ← getMainGoal
  replaceMainGoal <| ← pure_coherence g

theorem mk_eq_of_cons {C : Type u} [CategoryStruct.{v} C]
    {f₁ f₂ f₃ f₄ : C}
    (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs ηs' : f₃ ⟶ f₄)
    (pf_α : α = α') (pf_η : η = η') (pf_ηs : ηs = ηs') :
    α ≫ η ≫ ηs = α' ≫ η' ≫ ηs' := by
  simp [pf_α, pf_η, pf_ηs]

/-- Transform an equality between 2-morphisms into the equality between their normalizations. -/
def mkEqOfHom₂ (mvarId : MVarId) : MetaM Expr := do
  let some (_, e₁, e₂) := (← whnfR <| ← mvarId.getType).eq?
    | throwError "monoidal requires an equality goal"
  let some c ← mkContext? e₁ | throwError "monoidal requires an equality goal"
  MonoidalM.run c do
    let ⟨e₁', p₁⟩ ← eval e₁
    let ⟨e₂', p₂⟩ ← eval e₂
    mkAppM ``mk_eq #[e₁, e₂, ← e₁'.e, ← e₂'.e, p₁, p₂]

def ofNormalizedEq (mvarId : MVarId) : MetaM (List MVarId) := do
  let e ← mvarId.getType
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

def monoidal (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let mvarIds ← g.apply (← mkEqOfHom₂ g)
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
  replaceMainGoal (← monoidal (← getMainGoal))

end Monoidal

end Mathlib.Tactic
