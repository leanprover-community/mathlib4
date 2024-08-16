import Mathlib.Tactic.CategoryTheory.Coherence.Normalize

import Mathlib.Tactic.CategoryTheory.Bicategory.PureCoherence

open Lean Meta Elab
open CategoryTheory Mathlib.Tactic.BicategoryLike
-- MkClass

namespace Mathlib.Tactic.Bicategory

open Bicategory

section

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

variable {a₀ a₁ a b c d : B}
variable {f f' g g' h i j : a ⟶ b}

@[nolint synTaut]
theorem evalComp_nil_nil (α : f ≅ g) (β : g ≅ h) :
    (α ≪≫ β).hom = (α ≪≫ β).hom := by
  simp

theorem evalComp_nil_cons (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) :
    α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).hom ≫ η ≫ ηs := by
  simp

theorem evalComp_cons (α : f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j}
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

@[nolint synTaut]
theorem evalWhiskerLeft_nil (f : a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) :
    (whiskerLeftIso f α).hom = (whiskerLeftIso f α).hom := by
  simp

theorem evalWhiskerLeft_of_cons
    {f : a ⟶ b} {g h i j : b ⟶ c}
    (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ≫ i ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) :
    f ◁ (α.hom ≫ η ≫ ηs) = (whiskerLeftIso f α).hom ≫ f ◁ η ≫ θ := by
  simp [e_θ]

theorem evalWhiskerLeft_comp
    {f : a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d}
    {η : h ⟶ i} {θ : g ≫ h ⟶ g ≫ i} {ι : f ≫ g ≫ h ⟶ f ≫ g ≫ i}
    {ι' : f ≫ g ≫ h ⟶ (f ≫ g) ≫ i} {ι'' : (f ≫ g) ≫ h ⟶ (f ≫ g) ≫ i}
    (pf_θ : g ◁ η = θ) (pf_ι : f ◁ θ = ι)
    (pf_ι' : ι ≫ (α_ _ _ _).inv = ι') (pf_ι'' : (α_ _ _ _).hom ≫ ι' = ι'') :
    (f ≫ g) ◁ η = ι'' := by
  simp [pf_θ, pf_ι, pf_ι', pf_ι'']

theorem evalWhiskerLeft_id {η : f ⟶ g}
    {η' : f ⟶ 𝟙 a ≫ g} {η'' : 𝟙 a ≫ f ⟶ 𝟙 a ≫ g}
    (pf_η' : η ≫ (λ_ _).inv = η') (pf_η'' : (λ_ _).hom ≫ η' = η'') :
    𝟙 a ◁ η = η'' := by
  simp [pf_η', pf_η'']

theorem eval_whiskerLeft
    {f : a ⟶ b} {g h : b ⟶ c}
    {η η' : g ⟶ h} {θ : f ≫ g ⟶ f ≫ h}
    (pf_η : η = η') (pf_θ : f ◁ η' = θ) :
    f ◁ η = θ := by
  simp [pf_η, pf_θ]

theorem eval_whiskerRight
    {f g : a ⟶ b} {h : b ⟶ c}
    {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h}
    (pf_η : η = η') (pf_θ : η' ▷ h = θ) :
    η ▷ h = θ := by
  simp [pf_η, pf_θ]

@[nolint synTaut]
theorem evalWhiskerRight_nil (α : f ≅ g) (h : b ⟶ c) :
    α.hom ▷ h = α.hom ▷ h := by
  simp

theorem evalWhiskerRightAux_of {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso.refl _).hom := by
  simp

theorem evalWhiskerRight_cons_of_of
    {f g h i : a ⟶ b} {j : b ⟶ c}
    {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {ηs₁ : h ≫ j ⟶ i ≫ j}
    {η₁ : g ≫ j ⟶ h ≫ j} {η₂ : g ≫ j ⟶ i ≫ j} {η₃ : f ≫ j ⟶ i ≫ j}
    (e_ηs₁ : ηs ▷ j = ηs₁) (e_η₁ : η ▷ j = η₁)
    (e_η₂ : η₁ ≫ ηs₁ = η₂) (e_η₃ : (whiskerRightIso α j).hom ≫ η₂ = η₃) :
    (α.hom ≫ η ≫ ηs) ▷ j = η₃ := by
  simp_all

theorem evalWhiskerRight_cons_whisker
    {f : a ⟶ b} {g : a ⟶ c} {h : b ⟶ c} {i : b ⟶ c} {j : a ⟶ c} {k : c ⟶ d}
    {α : g ≅ f ≫ h} {η : h ⟶ i} {ηs : f ≫ i ⟶ j}
    {η₁ : h ≫ k ⟶ i ≫ k} {η₂ : f ≫ (h ≫ k) ⟶ f ≫ (i ≫ k)} {ηs₁ : (f ≫ i) ≫ k ⟶ j ≫ k}
    {ηs₂ : f ≫ (i ≫ k) ⟶ j ≫ k} {η₃ : f ≫ (h ≫ k) ⟶ j ≫ k} {η₄ : (f ≫ h) ≫ k ⟶ j ≫ k}
    {η₅ : g ≫ k ⟶ j ≫ k}
    (e_η₁ : ((Iso.refl _).hom ≫ η ≫ (Iso.refl _).hom) ▷ k = η₁) (e_η₂ : f ◁ η₁ = η₂)
    (e_ηs₁ : ηs ▷ k = ηs₁) (e_ηs₂ : (α_ _ _ _).inv ≫ ηs₁ = ηs₂)
    (e_η₃ : η₂ ≫ ηs₂ = η₃) (e_η₄ : (α_ _ _ _).hom ≫ η₃ = η₄) (e_η₅ : (whiskerRightIso α k).hom ≫ η₄ = η₅) :
    (α.hom ≫ (f ◁ η) ≫ ηs) ▷ k = η₅ := by
  simp at e_η₁ e_η₅
  simp [e_η₁, e_η₂, e_ηs₁, e_ηs₂, e_η₃, e_η₄, e_η₅]

theorem evalWhiskerRight_comp
    {f f' : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d}
    {η : f ⟶ f'} {η₁ : f ≫ g ⟶ f' ≫ g} {η₂ : (f ≫ g) ≫ h ⟶ (f' ≫ g) ≫ h}
    {η₃ : (f ≫ g) ≫ h ⟶ f' ≫ (g ≫ h)} {η₄ : f ≫ (g ≫ h) ⟶ f' ≫ (g ≫ h)}
    (pf_η₁ : η ▷ g = η₁) (pf_η₂ : η₁ ▷ h = η₂)
    (pf_η₃ : η₂ ≫ (α_ _ _ _).hom = η₃) (pf_η₄ : (α_ _ _ _).inv ≫ η₃ = η₄) :
    η ▷ (g ≫ h) = η₄ := by
  simp [pf_η₁, pf_η₂, pf_η₃, pf_η₄]

theorem evalWhiskerRight_id
    {η : f ⟶ g} {η₁ : f ⟶ g ≫ 𝟙 b} {η₂ : f ≫ 𝟙 b ⟶ g ≫ 𝟙 b}
    (pf_η₁ : η ≫ (ρ_ _).inv = η₁) (pf_η₂ : (ρ_ _).hom ≫ η₁ = η₂) :
    η ▷ 𝟙 b = η₂ := by
  simp [pf_η₁, pf_η₂]

theorem eval_bicategoricalComp
    {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i}
    (e_η : η = η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ' = αθ) (e_ηαθ : η' ≫ αθ = ηαθ) :
    η ≫ α.hom ≫ θ = ηαθ := by
  simp [e_η, e_θ, e_αθ, e_ηαθ]

end

open Mor₂Iso

instance : MkEvalComp BicategoryM where
  mkEvalCompNilNil α β := do
    let ctx ← read
    let f ← α.srcM
    let g ← α.tgtM
    let h ← β.tgtM
    let a := f.src
    let b := f.tgt
    return mkAppN (.const ``evalComp_nil_nil (← getLevels))
      #[ctx.B, ctx.instBicategory, a.e, b.e, f.e, g.e, h.e, α.e, β.e]
  mkEvalCompNilCons α β η ηs := do
    let ctx ← read
    let f ← α.srcM
    let g ← α.tgtM
    let h ← β.tgtM
    let i ← η.tgtM
    let j ← ηs.tgtM
    let a := f.src
    let b := f.tgt
    return mkAppN (.const ``evalComp_nil_cons (← getLevels))
      #[ctx.B, ctx.instBicategory, a.e, b.e, f.e, g.e, h.e, i.e, j.e, α.e, β.e, η.e, ηs.e]
  mkEvalCompCons α η ηs θ ι e_ι := do
    let ctx ← read
    let f ← α.srcM
    let g ← α.tgtM
    let h ← η.tgtM
    let i ← ηs.tgtM
    let j ← θ.tgtM
    let a := f.src
    let b := f.tgt
    return mkAppN (.const ``evalComp_cons (← getLevels))
      #[ctx.B, ctx.instBicategory, a.e, b.e, f.e, g.e, h.e, i.e, j.e, α.e, η.e, ηs.e, θ.e, ι.e, e_ι]

instance : MkEvalWhiskerLeft BicategoryM where
  mkEvalWhiskerLeftNil f α := do
    let ctx ← read
    let g ← α.srcM
    let h ← α.tgtM
    let a := f.src
    let b := f.tgt
    let c := g.tgt
    return mkAppN (.const ``evalWhiskerLeft_nil (← getLevels))
      #[ctx.B, ctx.instBicategory, a.e, b.e, c.e, f.e, g.e, h.e, α.e]
  mkEvalWhiskerLeftOfCons f α η ηs θ e_θ := do
    let ctx ← read
    let g ← α.srcM
    let h ← α.tgtM
    let i ← η.tgtM
    let j ← ηs.tgtM
    let a := f.src
    let b := f.tgt
    let c := g.tgt
    return mkAppN (.const ``evalWhiskerLeft_of_cons (← getLevels))
      #[ctx.B, ctx.instBicategory, a.e, b.e, c.e, f.e, g.e, h.e, i.e, j.e, α.e, η.e, ηs.e, θ.e, e_θ]

  mkEvalWhiskerLeftComp f g η η₁ η₂ η₃ η₄ e_η₁ e_η₂ e_η₃ e_η₄ := do
    let ctx ← read
    let h ← η.srcM
    let i ← η.tgtM
    let a := f.src
    let b := f.tgt
    let c := g.tgt
    let d := h.tgt
    return mkAppN (.const ``evalWhiskerLeft_comp (← getLevels))
      #[ctx.B, ctx.instBicategory, a.e, b.e, c.e, d.e, f.e, g.e, h.e, i.e, η.e, η₁.e, η₂.e, η₃.e, η₄.e,
        e_η₁, e_η₂, e_η₃, e_η₄]

  mkEvalWhiskerLeftId η η₁ η₂ e_η₁ e_η₂ := do
    let ctx ← read
    let f ← η.srcM
    let g ← η.tgtM
    let a := f.src
    let b := f.tgt
    return mkAppN (.const ``evalWhiskerLeft_id (← getLevels))
      #[ctx.B, ctx.instBicategory, a.e, b.e, f.e, g.e, η.e, η₁.e, η₂.e, e_η₁, e_η₂]

instance : MkEvalWhiskerRight BicategoryM where
  mkEvalWhiskerRightAuxOf η h := do
    let ctx ← read
    let f ← η.srcM
    let g ← η.tgtM
    let a := f.src
    let b := f.tgt
    let c := h.tgt
    return mkAppN (.const ``evalWhiskerRightAux_of (← getLevels))
      #[ctx.B, ctx.instBicategory, a.e, b.e, c.e, f.e, g.e, η.e, h.e]

  mkEvalWhiskerRightAuxCons f η ηs ηs' η₁ η₂ η₃ e_ηs' e_η₁ e_η₂ e_η₃ := do
    throwError "not implemented"

  mkEvalWhiskerRightNil α h := do
    let ctx ← read
    let f ← α.srcM
    let g ← α.tgtM
    let a := f.src
    let b := f.tgt
    let c := h.tgt
    return mkAppN (.const ``evalWhiskerRight_nil (← getLevels))
      #[ctx.B, ctx.instBicategory, a.e, b.e, c.e, f.e, g.e, α.e, h.e]

  mkEvalWhiskerRightConsOfOf j α η ηs ηs₁ η₁ η₂ η₃ e_ηs₁ e_η₁ e_η₂ e_η₃ := do
    let ctx ← read
    let f ← α.srcM
    let g ← α.tgtM
    let h ← η.tgtM
    let i ← ηs.tgtM
    let a := f.src
    let b := f.tgt
    let c := j.tgt
    return mkAppN (.const ``evalWhiskerRight_cons_of_of (← getLevels))
      #[ctx.B, ctx.instBicategory, a.e, b.e, c.e, f.e, g.e, h.e, i.e, j.e,
        α.e, η.e, ηs.e, ηs₁.e, η₁.e, η₂.e, η₃.e, e_ηs₁, e_η₁, e_η₂, e_η₃]

  mkEvalWhiskerRightConsWhisker f k α η ηs η₁ η₂ ηs₁ ηs₂ η₃ η₄ η₅
      e_η₁ e_η₂ e_ηs₁ e_ηs₂ e_η₃ e_η₄ e_η₅ := do
    let ctx ← read
    let g ← α.srcM
    let h ← η.srcM
    let i ← η.tgtM
    let j ← ηs.tgtM
    let a := f.src
    let b := f.tgt
    let c := h.tgt
    let d := k.tgt
    return mkAppN (.const ``evalWhiskerRight_cons_whisker (← getLevels))
      #[ctx.B, ctx.instBicategory, a.e, b.e, c.e, d.e, f.e, g.e, h.e, i.e, j.e, k.e,
        α.e, η.e, ηs.e, η₁.e, η₂.e, ηs₁.e, ηs₂.e, η₃.e, η₄.e, η₅.e,
        e_η₁, e_η₂, e_ηs₁, e_ηs₂, e_η₃, e_η₄, e_η₅]

  mkEvalWhiskerRightComp g h η η₁ η₂ η₃ η₄ e_η₁ e_η₂ e_η₃ e_η₄ := do
    let ctx ← read
    let f ← η.srcM
    let f' ← η.tgtM
    let a := f.src
    let b := f.tgt
    let c := g.tgt
    let d := h.tgt
    return mkAppN (.const ``evalWhiskerRight_comp (← getLevels))
      #[ctx.B, ctx.instBicategory, a.e, b.e, c.e, d.e, f.e, f'.e, g.e, h.e,
        η.e, η₁.e, η₂.e, η₃.e, η₄.e, e_η₁, e_η₂, e_η₃, e_η₄]

  mkEvalWhiskerRightId η η₁ η₂ e_η₁ e_η₂ := do
    let ctx ← read
    let f ← η.srcM
    let g ← η.tgtM
    let a := f.src
    let b := f.tgt
    return mkAppN (.const ``evalWhiskerRight_id (← getLevels))
      #[ctx.B, ctx.instBicategory, a.e, b.e, f.e, g.e, η.e, η₁.e, η₂.e, e_η₁, e_η₂]

instance : MkEvalHorizontalComp BicategoryM where
  mkEvalHorizontalCompAuxOf η θ := do
    throwError "not implemented"

  mkEvalHorizontalCompAuxCons η ηs θ ηθ η₁ ηθ₁ ηθ₂ e_ηθ e_η₁ e_ηθ₁ e_ηθ₂ := do
    throwError "not implemented"

  mkEvalHorizontalCompAux'Whisker f η θ ηθ η₁ η₂ η₃ e_ηθ e_η₁ e_η₂ e_η₃ := do
    throwError "not implemented"

  mkEvalHorizontalCompAux'OfWhisker f η θ η₁ ηθ ηθ₁ ηθ₂ e_η₁ e_ηθ e_ηθ₁ e_ηθ₂ := do
    throwError "not implemented"

  mkEvalHorizontalCompNilNil α β := do
    throwError "not implemented"

  mkEvalHorizontalCompNilCons α β η ηs η₁ ηs₁ η₂ η₃ e_η₁ e_ηs₁ e_η₂ e_η₃ := do
    throwError "not implemented"

  mkEvalHorizontalCompConsNil α η ηs β η₁ ηs₁ η₂ η₃ e_η₁ e_ηs₁ e_η₂ e_η₃ := do
    throwError "not implemented"

  mkEvalHorizontalCompConsCons α β η θ ηs θs ηθ ηθs ηθ₁ ηθ₂ e_ηθ e_ηθs e_ηθ₁ e_ηθ₂ := do
    throwError "not implemented"

instance : MkEval BicategoryM where
  mkEvalComp η θ η' θ' ι pf_η pf_θ pf_ηθ := do
    let ctx ← read
    let f ← η'.srcM
    let g ← η'.tgtM
    let h ← θ'.tgtM
    let a := f.src
    let b := f.tgt
    return mkAppN (.const ``eval_comp (← getLevels))
      #[ctx.B, ctx.instBicategory, a.e, b.e, f.e, g.e, h.e, η.e, η'.e, θ.e, θ'.e, ι.e, pf_η, pf_θ, pf_ηθ]

  mkEvalWhiskerLeft f η η' θ pf_η pf_θ := do
    let ctx ← read
    let g ← η'.srcM
    let h ← η'.tgtM
    let a := f.src
    let b := f.tgt
    let c := g.tgt
    return mkAppN (.const ``eval_whiskerLeft (← getLevels))
      #[ctx.B, ctx.instBicategory, a.e, b.e, c.e, f.e, g.e, h.e, η.e, η'.e, θ.e, pf_η, pf_θ]

  mkEvalWhiskerRight η h η' θ pf_η pf_θ := do
    let ctx ← read
    let f ← η'.srcM
    let g ← η'.tgtM
    let a := f.src
    let b := f.tgt
    let c := h.tgt
    return mkAppN (.const ``eval_whiskerRight (← getLevels))
      #[ctx.B, ctx.instBicategory, a.e, b.e, c.e, f.e, g.e, h.e, η.e, η'.e, θ.e, pf_η, pf_θ]

  mkEvalHorizontalComp η θ η' θ' ι pf_η pf_θ pf_ι := do
    throwError "not implemented"

  mkEvalOf η := do
    let ctx ← read
    let f := η.src
    let g := η.tgt
    let a := f.src
    let b := f.tgt
    return mkAppN (.const ``eval_of (← getLevels))
      #[ctx.B, ctx.instBicategory, a.e, b.e, f.e, g.e, η.e]

  mkEvalMonoidalComp η θ α η' θ' αθ ηαθ pf_η pf_θ pf_αθ pf_ηαθ := do
    let ctx ← read
    let f ← η'.srcM
    let g ← η'.tgtM
    let h ← α.tgtM
    let i ← θ'.tgtM
    let a := f.src
    let b := f.tgt
    return mkAppN (.const ``eval_monoidalComp (← getLevels))
      #[ctx.B, ctx.instBicategory, a.e, b.e, f.e, g.e, h.e, i.e,
        η.e, η'.e, α.e, θ.e, θ'.e, αθ.e, ηαθ.e, pf_η, pf_θ, pf_αθ, pf_ηαθ]

instance : MonadNormalExpr BicategoryM where
  whiskerRightM η h := do
    let ctx ← read
    let f ← η.srcM
    let g ← η.tgtM
    let a := f.src
    let b := f.tgt
    let c := h.tgt
    let e := mkAppN (.const ``Bicategory.whiskerRight (← getLevels))
      #[ctx.B, ctx.instBicategory, a.e, b.e, c.e, f.e, g.e, η.e, h.e]
    return .whisker e η h
  hConsM η θ := do
    throwError "not implemented"
  whiskerLeftM f η := do
    let ctx ← read
    let g ← η.srcM
    let h ← η.tgtM
    let a := f.src
    let b := f.tgt
    let c := g.tgt
    let e := mkAppN (.const ``Bicategory.whiskerLeft (← getLevels))
      #[ctx.B, ctx.instBicategory, a.e, b.e, c.e, f.e, g.e, h.e, η.e]
    return .whisker e f η
  nilM α := do
    return .nil (← Mor₂.homM α).e α
  consM α η ηs := do
    let ctx ← read
    let f ← α.srcM
    let g ← α.tgtM
    let h ← η.tgtM
    let i ← ηs.tgtM
    let a := f.src
    let b := f.tgt
    -- let c := h.tgt
    -- let d := i.tgt
    -- let α' ← MkMor₂.ofExpr (← MonadMor₂.homM α).e
    -- let α'' ← (match α' with
    -- | .isoHom _ _ (.structuralAtom (.coherenceHom α'')) => return α''
    -- | _ => throwError "failed to unfold {α'.e}")
    -- -- let α''' ← coherenceHomM' α''.src α''.tgt α''.inst
    -- let e := mkAppN (.const ``monoidalComp (← getLevels))
    --   #[ctx.C, ctx.instCat, f.e, g.e, h.e, i.e, α''.inst]
    let e := mkAppN (.const ``CategoryStruct.comp [ctx.level₂, ctx.level₁])
      #[← mkHom₁ a.e b.e, ← mkHomCatStructInst a.e b.e, g.e, h.e, i.e, η.e, ηs.e]
    let e' := mkAppN (.const ``CategoryStruct.comp [ctx.level₂, ctx.level₁])
      #[← mkHom₁ a.e b.e, ← mkHomCatStructInst a.e b.e, f.e, g.e, i.e, (← mkIsoHom α.e), e]
    return .cons e' α η ηs

-- f ⟶ g ⟶ h ⟶ i
-- α η ηs

instance : MkMor₂ BicategoryM where
  ofExpr := Mor₂OfExpr

def monoidalNf (mvarId : MVarId) : MetaM (List MVarId) := do
  BicategoryLike.normalForm `bicategory Bicategory.Context mvarId

open Lean Elab Tactic
/-- Normalize the both sides of an equality. -/
elab "bicategory_nf" : tactic => withMainContext do
  replaceMainGoal (← monoidalNf (← getMainGoal))


def bicategory (mvarId : MVarId) : MetaM (List MVarId) :=
  BicategoryLike.main  Bicategory.Context (mkAppM ``mk_eq_of_normalized_eq) `bicategory mvarId

elab "bicategory" : tactic => withMainContext do
  replaceMainGoal <| ← bicategory <| ← getMainGoal

end Mathlib.Tactic.Bicategory
