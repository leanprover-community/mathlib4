import Mathlib.Tactic.CategoryTheory.Coherence.Normalize

import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence

open Lean Meta Elab
open CategoryTheory Mathlib.Tactic.BicategoryLike
-- MkClass

namespace Mathlib.Tactic.Monoidal

open MonoidalCategory

section

open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C]

variable {f f' g g' h h' i i' j : C}

@[nolint synTaut]
theorem evalComp_nil_nil {f g h : C} (α : f ≅ g) (β : g ≅ h) :
    (α ≪≫ β).hom = (α ≪≫ β).hom := by
  simp

theorem evalComp_nil_cons {f g h i j : C} (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) :
    α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).hom ≫ η ≫ ηs := by
  simp

theorem evalComp_cons {f g h i j : C} (α : f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j}
    (e_ι : ηs ≫ θ = ι)  :
    (α.hom ≫ η ≫ ηs) ≫ θ = α.hom ≫ η ≫ ι := by
  simp [e_ι]

theorem eval_comp
    {η η' : f ⟶ g} {θ θ' : g ⟶ h} {ι : f ⟶ h}
    (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) :
    η ≫ θ = ι := by
  simp [e_η, e_θ, e_ηθ]

theorem eval_of (η : f ⟶ g) :
    η = (Iso.refl _).hom ≫ η ≫ (Iso.refl _).hom := by
  simp

theorem eval_monoidalComp
    {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i}
    (e_η : η = η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ' = αθ) (e_ηαθ : η' ≫ αθ = ηαθ) :
    η ≫ α.hom ≫ θ = ηαθ := by
  simp [e_η, e_θ, e_αθ, e_ηαθ]

variable [MonoidalCategory C]

@[nolint synTaut]
theorem evalWhiskerLeft_nil (f : C) {g h : C} (α : g ≅ h) :
    (whiskerLeftIso f α).hom = (whiskerLeftIso f α).hom := by
  simp

theorem evalWhiskerLeft_of_cons {f g h i j : C}
    (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ⊗ i ⟶ f ⊗ j} (e_θ : f ◁ ηs = θ) :
    f ◁ (α.hom ≫ η ≫ ηs) = (whiskerLeftIso f α).hom ≫ f ◁ η ≫ θ := by
  simp [e_θ]

theorem evalWhiskerLeft_comp {f g h i : C}
    {η : h ⟶ i} {θ : g ⊗ h ⟶ g ⊗ i} {ι : f ⊗ g ⊗ h ⟶ f ⊗ g ⊗ i}
    {ι' : f ⊗ g ⊗ h ⟶ (f ⊗ g) ⊗ i} {ι'' : (f ⊗ g) ⊗ h ⟶ (f ⊗ g) ⊗ i}
    (e_θ : g ◁ η = θ) (e_ι : f ◁ θ = ι)
    (e_ι' : ι ≫ (α_ _ _ _).inv = ι') (e_ι'' : (α_ _ _ _).hom ≫ ι' = ι'') :
    (f ⊗ g) ◁ η = ι'' := by
  simp [e_θ, e_ι, e_ι', e_ι'']

theorem evalWhiskerLeft_id {f g : C} {η : f ⟶ g}
    {η' : f ⟶ 𝟙_ C ⊗ g} {η'' : 𝟙_ C ⊗ f ⟶ 𝟙_ C ⊗ g}
    (e_η' : η ≫ (λ_ _).inv = η') (e_η'' : (λ_ _).hom ≫ η' = η'') :
    𝟙_ C ◁ η = η'' := by
  simp [e_η', e_η'']

theorem eval_whiskerLeft {f g h : C}
    {η η' : g ⟶ h} {θ : f ⊗ g ⟶ f ⊗ h}
    (e_η : η = η') (e_θ : f ◁ η' = θ) :
    f ◁ η = θ := by
  simp [e_η, e_θ]

theorem eval_whiskerRight {f g h : C}
    {η η' : f ⟶ g} {θ : f ⊗ h ⟶ g ⊗ h}
    (e_η : η = η') (e_θ : η' ▷ h = θ) :
    η ▷ h = θ := by
  simp [e_η, e_θ]

theorem eval_tensorHom {f g h i : C}
    {η η' : f ⟶ g} {θ θ' : h ⟶ i} {ι : f ⊗ h ⟶ g ⊗ i}
    (e_η : η = η') (e_θ : θ = θ') (e_ι : η' ⊗ θ' = ι) :
    η ⊗ θ = ι := by
  simp [e_η, e_θ, e_ι]

@[nolint synTaut]
theorem evalWhiskerRight_nil {f g : C} (α : f ≅ g) (h : C) :
    (whiskerRightIso α h).hom = (whiskerRightIso α h).hom := by
  simp

theorem evalWhiskerRight_cons_of_of {f g h i j : C}
    {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {ηs₁ : h ⊗ j ⟶ i ⊗ j}
    {η₁ : g ⊗ j ⟶ h ⊗ j} {η₂ : g ⊗ j ⟶ i ⊗ j} {η₃ : f ⊗ j ⟶ i ⊗ j}
    (e_ηs₁ : ηs ▷ j = ηs₁) (e_η₁ : η ▷ j = η₁)
    (e_η₂ : η₁ ≫ ηs₁ = η₂) (e_η₃ : (whiskerRightIso α j).hom ≫ η₂ = η₃) :
    (α.hom ≫ η ≫ ηs) ▷ j = η₃ := by
  simp_all

theorem evalWhiskerRight_cons_whisker {f g h i j k : C}
    {α : g ≅ f ⊗ h} {η : h ⟶ i} {ηs : f ⊗ i ⟶ j}
    {η₁ : h ⊗ k ⟶ i ⊗ k} {η₂ : f ⊗ (h ⊗ k) ⟶ f ⊗ (i ⊗ k)} {ηs₁ : (f ⊗ i) ⊗ k ⟶ j ⊗ k}
    {ηs₂ : f ⊗ (i ⊗ k) ⟶ j ⊗ k} {η₃ : f ⊗ (h ⊗ k) ⟶ j ⊗ k} {η₄ : (f ⊗ h) ⊗ k ⟶ j ⊗ k}
    {η₅ : g ⊗ k ⟶ j ⊗ k}
    (e_η₁ : ((Iso.refl _).hom ≫ η ≫ (Iso.refl _).hom) ▷ k = η₁) (e_η₂ : f ◁ η₁ = η₂)
    (e_ηs₁ : ηs ▷ k = ηs₁) (e_ηs₂ : (α_ _ _ _).inv ≫ ηs₁ = ηs₂)
    (e_η₃ : η₂ ≫ ηs₂ = η₃) (e_η₄ : (α_ _ _ _).hom ≫ η₃ = η₄) (e_η₅ : (whiskerRightIso α k).hom ≫ η₄ = η₅) :
    (α.hom ≫ (f ◁ η) ≫ ηs) ▷ k = η₅ := by
  simp at e_η₁ e_η₅
  simp [e_η₁, e_η₂, e_ηs₁, e_ηs₂, e_η₃, e_η₄, e_η₅]

theorem evalWhiskerRight_comp {f f' g h : C}
    {η : f ⟶ f'} {η₁ : f ⊗ g ⟶ f' ⊗ g} {η₂ : (f ⊗ g) ⊗ h ⟶ (f' ⊗ g) ⊗ h}
    {η₃ : (f ⊗ g) ⊗ h ⟶ f' ⊗ (g ⊗ h)} {η₄ : f ⊗ (g ⊗ h) ⟶ f' ⊗ (g ⊗ h)}
    (e_η₁ : η ▷ g = η₁) (e_η₂ : η₁ ▷ h = η₂)
    (e_η₃ : η₂ ≫ (α_ _ _ _).hom = η₃) (e_η₄ : (α_ _ _ _).inv ≫ η₃ = η₄) :
    η ▷ (g ⊗ h) = η₄ := by
  simp [e_η₁, e_η₂, e_η₃, e_η₄]

theorem evalWhiskerRight_id {f g : C}
    {η : f ⟶ g} {η₁ : f ⟶ g ⊗ 𝟙_ C} {η₂ : f ⊗ 𝟙_ C ⟶ g ⊗ 𝟙_ C}
    (e_η₁ : η ≫ (ρ_ _).inv = η₁) (e_η₂ : (ρ_ _).hom ≫ η₁ = η₂) :
    η ▷ 𝟙_ C = η₂ := by
  simp [e_η₁, e_η₂]

theorem evalWhiskerRightAux_of {g h : C} (η : g ⟶ h) (f : C) :
    η ▷ f = (Iso.refl _).hom ≫ η ▷ f ≫ (Iso.refl _).hom := by
  simp

theorem evalWhiskerRightAux_cons {f g h i j : C} {η : g ⟶ h} {ηs : i ⟶ j}
    {ηs' : i ⊗ f ⟶ j ⊗ f} {η₁ : g ⊗ (i ⊗ f) ⟶ h ⊗ (j ⊗ f)}
    {η₂ : g ⊗ (i ⊗ f) ⟶ (h ⊗ j) ⊗ f} {η₃ : (g ⊗ i) ⊗ f ⟶ (h ⊗ j) ⊗ f}
    (e_ηs' : ηs ▷ f = ηs') (e_η₁ : ((Iso.refl _).hom ≫ η ≫ (Iso.refl _).hom) ⊗ ηs' = η₁)
    (e_η₂ : η₁ ≫ (α_ _ _ _).inv = η₂) (e_η₃ : (α_ _ _ _).hom ≫ η₂ = η₃) :
    (η ⊗ ηs) ▷ f = η₃ := by
  simp [← e_ηs', ← e_η₁, ← e_η₂, ← e_η₃, MonoidalCategory.tensorHom_def]

theorem evalWhiskerRight_cons_of {f f' g h i : C} {α : f' ≅ g} {η : g ⟶ h} {ηs : h ⟶ i}
    {ηs₁ : h ⊗ f ⟶ i ⊗ f} {η₁ : g ⊗ f ⟶ h ⊗ f} {η₂ : g ⊗ f ⟶ i ⊗ f}
    {η₃ : f' ⊗ f ⟶ i ⊗ f}
    (e_ηs₁ : ηs ▷ f = ηs₁) (e_η₁ : η ▷ f = η₁)
    (e_η₂ : η₁ ≫ ηs₁ = η₂) (e_η₃ : (whiskerRightIso α f).hom ≫ η₂ = η₃) :
    (α.hom ≫ η ≫ ηs) ▷ f = η₃ := by
  simp_all

theorem evalHorizontalCompAux_of {f g h i : C} (η : f ⟶ g) (θ : h ⟶ i) :
    η ⊗ θ = (Iso.refl _).hom ≫ (η ⊗ θ) ≫ (Iso.refl _).hom := by
  simp

theorem evalHorizontalCompAux_cons {f f' g g' h i : C} {η : f ⟶ g} {ηs : f' ⟶ g'} {θ : h ⟶ i}
    {ηθ : f' ⊗ h ⟶ g' ⊗ i} {η₁ : f ⊗ (f' ⊗ h) ⟶ g ⊗ (g' ⊗ i)}
    {ηθ₁ : f ⊗ (f' ⊗ h) ⟶ (g ⊗ g') ⊗ i} {ηθ₂ : (f ⊗ f') ⊗ h ⟶ (g ⊗ g') ⊗ i}
    (e_ηθ : ηs ⊗ θ = ηθ) (e_η₁ : ((Iso.refl _).hom ≫ η ≫ (Iso.refl _).hom) ⊗ ηθ = η₁)
    (e_ηθ₁ : η₁ ≫ (α_ _ _ _).inv = ηθ₁) (e_ηθ₂ : (α_ _ _ _).hom ≫ ηθ₁ = ηθ₂) :
    (η ⊗ ηs) ⊗ θ = ηθ₂ := by
  simp_all

theorem evalHorizontalCompAux'_whisker {f f' g g' h : C} {η : g ⟶ h} {θ : f' ⟶ g'}
    {ηθ : g ⊗ f' ⟶ h ⊗ g'} {η₁ : f ⊗ (g ⊗ f') ⟶ f ⊗ (h ⊗ g')}
    {η₂ :  f ⊗ (g ⊗ f') ⟶ (f ⊗ h) ⊗ g'} {η₃ : (f ⊗ g) ⊗ f' ⟶ (f ⊗ h) ⊗ g'}
    (e_ηθ : η ⊗ θ = ηθ) (e_η₁ : f ◁ ηθ = η₁)
    (e_η₂ : η₁ ≫ (α_ _ _ _).inv = η₂) (e_η₃ : (α_ _ _ _).hom ≫ η₂ = η₃) :
    (f ◁ η) ⊗ θ = η₃ := by
  simp only [← e_ηθ, ← e_η₁, ← e_η₂, ← e_η₃]
  simp [MonoidalCategory.tensorHom_def]

theorem evalHorizontalCompAux'_of_whisker {f f' g g' h : C} {η : g ⟶ h} {θ : f' ⟶ g'}
    {η₁ : g ⊗ f ⟶ h ⊗ f} {ηθ : (g ⊗ f) ⊗ f' ⟶ (h ⊗ f) ⊗ g'}
    {ηθ₁ : (g ⊗ f) ⊗ f' ⟶ h ⊗ (f ⊗ g')}
    {ηθ₂ : g ⊗ (f ⊗ f') ⟶ h ⊗ (f ⊗ g')}
    (e_η₁ : η ▷ f = η₁) (e_ηθ : η₁ ⊗ ((Iso.refl _).hom ≫ θ ≫ (Iso.refl _).hom) = ηθ)
    (e_ηθ₁ : ηθ ≫ (α_ _ _ _).hom = ηθ₁) (e_ηθ₂ : (α_ _ _ _).inv ≫ ηθ₁ = ηθ₂) :
    η ⊗ (f ◁ θ) = ηθ₂ := by
  simp only [← e_η₁, ← e_ηθ, ← e_ηθ₁, ← e_ηθ₂]
  simp [MonoidalCategory.tensorHom_def]

@[nolint synTaut]
theorem evalHorizontalComp_nil_nil {f g h i : C} (α : f ≅ g) (β : h ≅ i) :
    (α ⊗ β).hom = (α ⊗ β).hom := by
  simp

theorem evalHorizontalComp_nil_cons {f f' g g' h i : C}
    {α : f ≅ g} {β : f' ≅ g'} {η : g' ⟶ h} {ηs : h ⟶ i}
    {η₁ : g ⊗ g' ⟶ g ⊗ h} {ηs₁ : g ⊗ h ⟶ g ⊗ i}
    {η₂ : g ⊗ g' ⟶ g ⊗ i} {η₃ : f ⊗ f' ⟶ g ⊗ i}
    (e_η₁ : g ◁ ((Iso.refl _).hom ≫ η ≫ (Iso.refl _).hom) = η₁)
    (e_ηs₁ : g ◁ ηs = ηs₁) (e_η₂ : η₁ ≫ ηs₁ = η₂)
    (e_η₃ : (α ⊗ β).hom ≫ η₂ = η₃) :
    α.hom ⊗ (β.hom ≫ η ≫ ηs) = η₃ := by
  simp_all [MonoidalCategory.tensorHom_def]

theorem evalHorizontalComp_cons_nil {f f' g g' h i : C}
    {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {β : f' ≅ g'}
    {η₁ : g ⊗ g' ⟶ h ⊗ g'} {ηs₁ : h ⊗ g' ⟶ i ⊗ g'} {η₂ : g ⊗ g' ⟶ i ⊗ g'} {η₃ : f ⊗ f' ⟶ i ⊗ g'}
    (e_η₁ : ((Iso.refl _).hom ≫ η ≫ (Iso.refl _).hom) ▷ g' = η₁) (e_ηs₁ : ηs ▷ g' = ηs₁)
    (e_η₂ : η₁ ≫ ηs₁ = η₂) (e_η₃ : (α ⊗ β).hom ≫ η₂ = η₃) :
    (α.hom ≫ η ≫ ηs) ⊗ β.hom = η₃ := by
  simp_all [MonoidalCategory.tensorHom_def']

theorem evalHorizontalComp_cons_cons {f f' g g' h h' i i' : C}
    {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i}
    {β : f' ≅ g'} {θ : g' ⟶ h'} {θs : h' ⟶ i'}
    {ηθ : g ⊗ g' ⟶ h ⊗ h'} {ηθs : h ⊗ h' ⟶ i ⊗ i'}
    {ηθ₁ : g ⊗ g' ⟶ i ⊗ i'} {ηθ₂ : f ⊗ f' ⟶ i ⊗ i'}
    (e_ηθ : η ⊗ θ = ηθ) (e_ηθs : ηs ⊗ θs = ηθs)
    (e_ηθ₁ : ηθ ≫ ηθs = ηθ₁) (e_ηθ₂ : (α ⊗ β).hom ≫ ηθ₁ = ηθ₂) :
    (α.hom ≫ η ≫ ηs) ⊗ (β.hom ≫ θ ≫ θs) = ηθ₂ := by
  simp [← e_ηθ , ← e_ηθs , ← e_ηθ₁, ← e_ηθ₂]

end

open Mor₂Iso

instance : MkEvalComp MonoidalM where
  mkEvalCompNilNil α β := do
    let ctx ← read
    let f ← α.srcM
    let g ← α.tgtM
    let h ← β.tgtM
    return mkAppN (.const ``evalComp_nil_nil (← getLevels))
      #[ctx.C, ctx.instCat, f.e, g.e, h.e, α.e, β.e]
  mkEvalCompNilCons α β η ηs := do
    let ctx ← read
    let f ← α.srcM
    let g ← α.tgtM
    let h ← β.tgtM
    let i ← η.tgtM
    let j ← ηs.tgtM
    return mkAppN (.const ``evalComp_nil_cons (← getLevels))
      #[ctx.C, ctx.instCat, f.e, g.e, h.e, i.e, j.e, α.e, β.e, η.e, ηs.e]
  mkEvalCompCons α η ηs θ ι e_ι := do
    let ctx ← read
    let f ← α.srcM
    let g ← α.tgtM
    let h ← η.tgtM
    let i ← ηs.tgtM
    let j ← θ.tgtM
    return mkAppN (.const ``evalComp_cons (← getLevels))
      #[ctx.C, ctx.instCat, f.e, g.e, h.e, i.e, j.e, α.e, η.e, ηs.e, θ.e, ι.e, e_ι]

instance : MkEvalWhiskerLeft MonoidalM where
  mkEvalWhiskerLeftNil f α := do
    let ctx ← read
    let g ← α.srcM
    let h ← α.tgtM
    return mkAppN (.const ``evalWhiskerLeft_nil (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, f.e, g.e, h.e, α.e]
  mkEvalWhiskerLeftOfCons f α η ηs θ e_θ := do
    let ctx ← read
    let g ← α.srcM
    let h ← α.tgtM
    let i ← η.tgtM
    let j ← ηs.tgtM
    return mkAppN (.const ``evalWhiskerLeft_of_cons (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, f.e, g.e, h.e, i.e, j.e, α.e, η.e, ηs.e, θ.e, e_θ]

  mkEvalWhiskerLeftComp f g η η₁ η₂ η₃ η₄ e_η₁ e_η₂ e_η₃ e_η₄ := do
    let ctx ← read
    let h ← η.srcM
    let i ← η.tgtM
    return mkAppN (.const ``evalWhiskerLeft_comp (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, f.e, g.e, h.e, i.e, η.e, η₁.e, η₂.e, η₃.e, η₄.e,
        e_η₁, e_η₂, e_η₃, e_η₄]

  mkEvalWhiskerLeftId η η₁ η₂ e_η₁ e_η₂ := do
    let ctx ← read
    let f ← η.srcM
    let g ← η.tgtM
    return mkAppN (.const ``evalWhiskerLeft_id (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, f.e, g.e, η.e, η₁.e, η₂.e, e_η₁, e_η₂]

instance : MkEvalWhiskerRight MonoidalM where
  mkEvalWhiskerRightAuxOf η f := do
    let ctx ← read
    let g ← η.srcM
    let h ← η.tgtM
    return mkAppN (.const ``evalWhiskerRightAux_of (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, g.e, h.e, η.e, f.e]

  mkEvalWhiskerRightAuxCons f η ηs ηs' η₁ η₂ η₃ e_ηs' e_η₁ e_η₂ e_η₃ := do
    let ctx ← read
    let g ← η.srcM
    let h ← η.tgtM
    let i ← ηs.srcM
    let j ← ηs.tgtM
    return mkAppN (.const ``evalWhiskerRightAux_cons (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, f.e, g.e, h.e, i.e, j.e, η.e, ηs.e, ηs'.e,
        η₁.e, η₂.e, η₃.e, e_ηs', e_η₁, e_η₂, e_η₃]

  mkEvalWhiskerRightNil α h := do
    let ctx ← read
    let f ← α.srcM
    let g ← α.tgtM
    return mkAppN (.const ``evalWhiskerRight_nil (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, f.e, g.e, α.e, h.e]

  mkEvalWhiskerRightConsOfOf j α η ηs ηs₁ η₁ η₂ η₃ e_ηs₁ e_η₁ e_η₂ e_η₃ := do
    let ctx ← read
    let f ← α.srcM
    let g ← α.tgtM
    let h ← η.tgtM
    let i ← ηs.tgtM
    return mkAppN (.const ``evalWhiskerRight_cons_of_of (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, f.e, g.e, h.e, i.e, j.e,
        α.e, η.e, ηs.e, ηs₁.e, η₁.e, η₂.e, η₃.e, e_ηs₁, e_η₁, e_η₂, e_η₃]

  mkEvalWhiskerRightConsWhisker f k α η ηs η₁ η₂ ηs₁ ηs₂ η₃ η₄ η₅
      e_η₁ e_η₂ e_ηs₁ e_ηs₂ e_η₃ e_η₄ e_η₅ := do
    let ctx ← read
    let g ← α.srcM
    let h ← η.srcM
    let i ← η.tgtM
    let j ← ηs.tgtM
    return mkAppN (.const ``evalWhiskerRight_cons_whisker (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, f.e, g.e, h.e, i.e, j.e, k.e,
        α.e, η.e, ηs.e, η₁.e, η₂.e, ηs₁.e, ηs₂.e, η₃.e, η₄.e, η₅.e,
        e_η₁, e_η₂, e_ηs₁, e_ηs₂, e_η₃, e_η₄, e_η₅]

  mkEvalWhiskerRightComp g h η η₁ η₂ η₃ η₄ e_η₁ e_η₂ e_η₃ e_η₄ := do
    let ctx ← read
    let f ← η.srcM
    let f' ← η.tgtM
    return mkAppN (.const ``evalWhiskerRight_comp (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, f.e, f'.e, g.e, h.e,
        η.e, η₁.e, η₂.e, η₃.e, η₄.e, e_η₁, e_η₂, e_η₃, e_η₄]

  mkEvalWhiskerRightId η η₁ η₂ e_η₁ e_η₂ := do
    let ctx ← read
    let f ← η.srcM
    let g ← η.tgtM
    return mkAppN (.const ``evalWhiskerRight_id (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, f.e, g.e, η.e, η₁.e, η₂.e, e_η₁, e_η₂]

instance : MkEvalHorizontalComp MonoidalM where
  mkEvalHorizontalCompAuxOf η θ := do
    let ctx ← read
    let f ← η.srcM
    let g ← η.tgtM
    let h ← θ.srcM
    let i ← θ.tgtM
    return mkAppN (.const ``evalHorizontalCompAux_of (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, f.e, g.e, h.e, i.e, η.e, θ.e]

  mkEvalHorizontalCompAuxCons η ηs θ ηθ η₁ ηθ₁ ηθ₂ e_ηθ e_η₁ e_ηθ₁ e_ηθ₂ := do
    let ctx ← read
    let f ← η.srcM
    let g ← η.tgtM
    let f' ← ηs.srcM
    let g' ← ηs.tgtM
    let h ← θ.srcM
    let i ← θ.tgtM
    return mkAppN (.const ``evalHorizontalCompAux_cons (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, f.e, f'.e, g.e, g'.e, h.e, i.e,
        η.e, ηs.e, θ.e, ηθ.e, η₁.e, ηθ₁.e, ηθ₂.e, e_ηθ, e_η₁, e_ηθ₁, e_ηθ₂]

  mkEvalHorizontalCompAux'Whisker f η θ ηθ η₁ η₂ η₃ e_ηθ e_η₁ e_η₂ e_η₃ := do
    let ctx ← read
    let g ← η.srcM
    let h ← η.tgtM
    let f' ← θ.srcM
    let g' ← θ.tgtM
    return mkAppN (.const ``evalHorizontalCompAux'_whisker (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, f.e, f'.e, g.e, g'.e, h.e,
        η.e, θ.e, ηθ.e, η₁.e, η₂.e, η₃.e, e_ηθ, e_η₁, e_η₂, e_η₃]

  mkEvalHorizontalCompAux'OfWhisker f η θ η₁ ηθ ηθ₁ ηθ₂ e_η₁ e_ηθ e_ηθ₁ e_ηθ₂ := do
    let ctx ← read
    let g ← η.srcM
    let h ← η.tgtM
    let f' ← θ.srcM
    let g' ← θ.tgtM
    return mkAppN (.const ``evalHorizontalCompAux'_of_whisker (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, f.e, f'.e, g.e, g'.e, h.e,
        η.e, θ.e, η₁.e, ηθ.e, ηθ₁.e, ηθ₂.e, e_η₁, e_ηθ, e_ηθ₁, e_ηθ₂]

  mkEvalHorizontalCompNilNil α β := do
    let ctx ← read
    let f ← α.srcM
    let g ← α.tgtM
    let h ← β.srcM
    let i ← β.tgtM
    return mkAppN (.const ``evalHorizontalComp_nil_nil (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, f.e, g.e, h.e, i.e, α.e, β.e]

  mkEvalHorizontalCompNilCons α β η ηs η₁ ηs₁ η₂ η₃ e_η₁ e_ηs₁ e_η₂ e_η₃ := do
    let ctx ← read
    let f ← α.srcM
    let g ← α.tgtM
    let f' ← β.srcM
    let g' ← β.tgtM
    let h ← η.tgtM
    let i ← ηs.tgtM
    return mkAppN (.const ``evalHorizontalComp_nil_cons (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, f.e, f'.e, g.e, g'.e, h.e, i.e,
        α.e, β.e, η.e, ηs.e, η₁.e, ηs₁.e, η₂.e, η₃.e, e_η₁, e_ηs₁, e_η₂, e_η₃]

  mkEvalHorizontalCompConsNil α η ηs β η₁ ηs₁ η₂ η₃ e_η₁ e_ηs₁ e_η₂ e_η₃ := do
    let ctx ← read
    let f ← α.srcM
    let g ← α.tgtM
    let h ← η.tgtM
    let i ← ηs.tgtM
    let f' ← β.srcM
    let g' ← β.tgtM
    return mkAppN (.const ``evalHorizontalComp_cons_nil (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, f.e, f'.e, g.e, g'.e, h.e, i.e,
        α.e, η.e, ηs.e, β.e, η₁.e, ηs₁.e, η₂.e, η₃.e, e_η₁, e_ηs₁, e_η₂, e_η₃]

  mkEvalHorizontalCompConsCons α β η θ ηs θs ηθ ηθs ηθ₁ ηθ₂ e_ηθ e_ηθs e_ηθ₁ e_ηθ₂ := do
    let ctx ← read
    let f ← α.srcM
    let g ← α.tgtM
    let h ← η.tgtM
    let i ← ηs.tgtM
    let f' ← β.srcM
    let g' ← β.tgtM
    let h' ← θ.tgtM
    let i' ← θs.tgtM
    return mkAppN (.const ``evalHorizontalComp_cons_cons (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, f.e, f'.e, g.e, g'.e, h.e, h'.e, i.e, i'.e,
        α.e, η.e, ηs.e, β.e, θ.e, θs.e, ηθ.e, ηθs.e, ηθ₁.e, ηθ₂.e, e_ηθ, e_ηθs, e_ηθ₁, e_ηθ₂]

instance : MkEval MonoidalM where
  mkEvalComp η θ η' θ' ι pf_η pf_θ pf_ηθ := do
    let ctx ← read
    let f ← η'.srcM
    let g ← η'.tgtM
    let h ← θ'.tgtM
    return mkAppN (.const ``eval_comp (← getLevels))
      #[ctx.C, ctx.instCat, f.e, g.e, h.e, η.e, η'.e, θ.e, θ'.e, ι.e, pf_η, pf_θ, pf_ηθ]

  mkEvalWhiskerLeft f η η' θ pf_η pf_θ := do
    let ctx ← read
    let g ← η'.srcM
    let h ← η'.tgtM
    return mkAppN (.const ``eval_whiskerLeft (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, f.e, g.e, h.e, η.e, η'.e, θ.e, pf_η, pf_θ]

  mkEvalWhiskerRight η h η' θ pf_η pf_θ := do
    let ctx ← read
    let f ← η'.srcM
    let g ← η'.tgtM
    return mkAppN (.const ``eval_whiskerRight (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, f.e, g.e, h.e, η.e, η'.e, θ.e, pf_η, pf_θ]

  mkEvalHorizontalComp η θ η' θ' ι pf_η pf_θ pf_ι := do
    let ctx ← read
    let f ← η'.srcM
    let g ← η'.tgtM
    let h ← θ'.srcM
    let i ← θ'.tgtM
    return mkAppN (.const ``eval_tensorHom (← getLevels))
      #[ctx.C, ctx.instCat, ctx.instMonoidal, f.e, g.e, h.e, i.e, η.e, η'.e, θ.e, θ'.e, ι.e, pf_η, pf_θ, pf_ι]

  mkEvalOf η := do
    let ctx ← read
    let f := η.src
    let g := η.tgt
    return mkAppN (.const ``eval_of (← getLevels))
      #[ctx.C, ctx.instCat, f.e, g.e, η.e]

  mkEvalMonoidalComp η θ α η' θ' αθ ηαθ pf_η pf_θ pf_αθ pf_ηαθ := do
    let ctx ← read
    let f ← η'.srcM
    let g ← η'.tgtM
    let h ← α.tgtM
    let i ← θ'.tgtM
    return mkAppN (.const ``eval_monoidalComp (← getLevels))
      #[ctx.C, ctx.instCat, f.e, g.e, h.e, i.e, η.e, η'.e, α.e, θ.e, θ'.e, αθ.e, ηαθ.e, pf_η, pf_θ, pf_αθ, pf_ηαθ]

instance : MonadNormalExpr MonoidalM where
  whiskerRightM η h := do
    let ctx ← read
    let f ← η.srcM
    let g ← η.tgtM
    let e := mkAppN (.const ``MonoidalCategoryStruct.whiskerRight (← getLevels))
      #[ctx.C, ctx.instCat, ← mkMonoidalCategoryStructInst, f.e, g.e, η.e, h.e]
    return .whisker e η h
  hConsM η θ := do
    let ctx ← read
    let f ← η.srcM
    let g ← η.tgtM
    let h ← θ.srcM
    let i ← θ.tgtM
    let e := mkAppN (.const ``MonoidalCategoryStruct.tensorHom (← getLevels))
      #[ctx.C, ctx.instCat, ← mkMonoidalCategoryStructInst, f.e, g.e, h.e, i.e, η.e, θ.e]
    return .cons e η θ
  whiskerLeftM f η := do
    let ctx ← read
    let g ← η.srcM
    let h ← η.tgtM
    let e := mkAppN (.const ``MonoidalCategoryStruct.whiskerLeft (← getLevels))
      #[ctx.C, ctx.instCat, ← mkMonoidalCategoryStructInst, f.e, g.e, h.e, η.e]
    return .whisker e f η
  nilM α := do
    return .nil (← Mor₂.homM α).e α
  consM α η ηs := do
    let ctx ← read
    let f ← α.srcM
    let g ← α.tgtM
    let h ← η.tgtM
    let i ← ηs.tgtM
    -- let α' ← MkMor₂.ofExpr (← MonadMor₂.homM α).e
    -- let α'' ← (match α' with
    -- | .isoHom _ _ (.structuralAtom (.coherenceHom α'')) => return α''
    -- | _ => throwError "failed to unfold {α'.e}")
    -- -- let α''' ← coherenceHomM' α''.src α''.tgt α''.inst
    -- let e := mkAppN (.const ``monoidalComp (← getLevels))
    --   #[ctx.C, ctx.instCat, f.e, g.e, h.e, i.e, α''.inst]
    let e := mkAppN (.const ``CategoryStruct.comp (← getLevels))
      #[ctx.C, ← mkCategoryStructInst, g.e, h.e, i.e, η.e, ηs.e]
    let e' := mkAppN (.const ``CategoryStruct.comp (← getLevels))
      #[ctx.C, ← mkCategoryStructInst, f.e, g.e, i.e, (← mkIsoHom α.e), e]
    return .cons e' α η ηs

instance : MkMor₂ MonoidalM where
  ofExpr := Mor₂OfExpr

def monoidalNf (mvarId : MVarId) : MetaM (List MVarId) := do
  BicategoryLike.normalForm `monoidal Monoidal.Context mvarId

open Lean Elab Tactic
/-- Normalize the both sides of an equality. -/
elab "monoidal_nf" : tactic => withMainContext do
  replaceMainGoal (← monoidalNf (← getMainGoal))


def monoidal (mvarId : MVarId) : MetaM (List MVarId) :=
  BicategoryLike.main  Monoidal.Context (mkAppM ``mk_eq_of_normalized_eq) `monoidal mvarId

elab "monoidal" : tactic => withMainContext do
  replaceMainGoal <| ← monoidal <| ← getMainGoal

end Mathlib.Tactic.Monoidal
