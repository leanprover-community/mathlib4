/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.Tactic.CategoryTheory.Coherence.PureCoherence

open Lean Meta

namespace Mathlib.Tactic

namespace BicategoryLike


open BicategoryLike
-- CategoryTheory
-- open
--  Eval₁

variable {m : Type → Type} [Monad m]
-- [Eval₁ m]

-- /-- Construct a `Mor₁` expression from a Lean expression. -/
-- partial def eval₁ (e : Expr) : m Mor₁ := do
--   if let some a ← isId₁? e then
--     return Mor₁.id e a
--   else if let some (f, g) ← isComp₁? e then
--     return Mor₁.comp e f g
--   else
--     return Mor₁.of (← mkAtom₁ e)

-- def mkAtomM (e : Expr) : m Atom := do
--   let src ← eval₁ (← srcExpr e)
--   let tgt ← eval₁ (← tgtExpr e)
--   return ⟨e, src, tgt⟩

-- def mkCategoryStructInst : MonoidalM Expr := do
--   let ctx ← read
--   return mkAppN (.const ``Category.toCategoryStruct (← getLevels)) #[ctx.C, ctx.instCat]

-- def mkQuiverInst : MonoidalM Expr := do
--   let ctx ← read
--   return mkAppN (.const ``CategoryStruct.toQuiver (← getLevels)) #[ctx.C, ← mkCategoryStructInst]

-- def mkHom (f g : Expr) : MonoidalM Expr := do
--   let ctx ← read
--   return mkAppN (.const ``Quiver.Hom [ctx.level₂.succ, ctx.level₁]) #[ctx.C, ← mkQuiverInst, f, g]


-- /-- Construct a `NormalExpr` expression from a Lean expression for an atomic 2-morphism. -/
-- def NormalExpr.ofExpr (η : Expr) : m NormalExpr := do
--   return NormalExpr.of <| .of <| .of <| .of ⟨η, ← eval₁ (← srcExpr η), ← eval₁ (← tgtExpr η)⟩

/-- The result of evaluating an expression into normal form. -/
structure Eval.Result where
  /-- The normalized expression of the 2-morphism. -/
  expr : NormalExpr
  /-- The proof that the normalized expression is equal to the original expression. -/
  proof : Expr
  deriving Inhabited

-- def structuralAtom? (e : Expr) : m (Option StructuralIsoAtom) := sorry

variable {m : Type → Type} [Monad m]

class MkEvalComp (m : Type → Type) where
  mkEvalCompNilNil (α β : StructuralIso) : m Expr
  mkEvalCompNilCons (α β : StructuralIso) (η : WhiskerLeft) (ηs : NormalExpr) : m Expr
  mkEvalCompCons (α : StructuralIso) (η : WhiskerLeft) (ηs θ ι : NormalExpr) (e_η : Expr) : m Expr

/-- Evaluatte the expression `f ◁ η`. -/
class MkEvalWhiskerLeft (m : Type → Type) where
  /-- Evaluatte `f ◁ α` -/
  mkEvalWhiskerLeftNil (f : Mor₁) (α : StructuralIso) : m Expr
  /-- Evaluate `f ◁ (α ≫ η ≫ ηs)`. -/
  mkEvalWhiskerLeftOfCons (f : Atom₁) (α : StructuralIso) (η : WhiskerLeft) (ηs f_ηs : NormalExpr)
    (e_f_ηs : Expr) : m Expr
  /-- Evaluate `(f ≫ g) ◁ η` -/
  mkEvalWhiskerLeftComp (f g : Mor₁) (η gη fgη fgη' fgη'' : NormalExpr)
    (e_gη e_fgη e_fgη' e_fgη'' : Expr) : m Expr
  /-- Evaluate `𝟙 _ ◁ η` -/
  mkEvalWhiskerLeftId (η η' η'' : NormalExpr) (e_η' e_η'' : Expr) : m Expr

-- class MkEvalWhiskerRightAux (m : Type → Type) where
--   /-- Evaluate `η ▷ f` -/
--   mkEvalWhiskerRightAuxOf (η : WhiskerRight) (f : Atom₁) : m Expr
--   /-- Evaluate `(η ◫ ηs) ▷ f` -/
--   mkEvalWhiskerRightAuxCons (f : Atom₁) (η : WhiskerRight) (ηs : HorizontalComp)
--     (ηsf ηηsf ηηsf' ηηsf'' : NormalExpr) (e_ηsf e_ηηsf e_ηηsf' e_ηηsf'' : Expr) : m Expr

class MkEvalWhiskerRight (m : Type → Type) where
  /-- Evaluate `η ▷ f` -/
  mkEvalWhiskerRightAuxOf (η : WhiskerRight) (f : Atom₁) : m Expr
  /-- Evaluate `(η ◫ ηs) ▷ f` -/
  mkEvalWhiskerRightAuxCons (f : Atom₁) (η : WhiskerRight) (ηs : HorizontalComp)
    (ηs' η₁ η₂ η₃ : NormalExpr) (e_ηs' e_η₁ e_η₂ e_η₃ : Expr) : m Expr
  /-- Evaluate `α ▷ f` -/
  mkEvalWhiskerRightNil (α : StructuralIso) (f : Mor₁) : m Expr
  mkEvalWhiskerRightConsOfOf (f : Atom₁) (α : StructuralIso) (η : HorizontalComp)
    (ηs ηs₁ η₁ η₂ η₃ : NormalExpr)
    (e_ηs₁ e_η₁ e_η₂ e_η₃ : Expr) : m Expr
  /-- Evaluate `(α ≫ (f ◁ η) ≫ ηs) ▷ g` -/
  mkEvalWhiskerRightConsWhisker (f : Atom₁) (g : Mor₁) (α : StructuralIso) (η : WhiskerLeft)
    (ηs η₁ η₂ ηs₁ ηs₂ η₃ η₄ η₅ : NormalExpr) (e_η₁ e_η₂ e_ηs₁ e_ηs₂ e_η₃ e_η₄ e_η₅ : Expr) : m Expr
  mkEvalWhiskerRightComp (g h : Mor₁)
    (η η₁ η₂ η₃ η₄ : NormalExpr) (e_η₁ e_η₂ e_η₃ e_η₄ : Expr) : m Expr
  mkEvalWhiskerRightId (η η₁ η₂ : NormalExpr) (e_η₁ e_η₂ : Expr) : m Expr

class MkEvalHorizontalComp (m : Type → Type) where
  mkEvalHorizontalCompAuxOf (η : WhiskerRight) (θ : HorizontalComp) : m Expr
  mkEvalHorizontalCompAuxCons (η : WhiskerRight) (ηs θ : HorizontalComp)
    (ηθ η₁ ηθ₁ ηθ₂ : NormalExpr) (e_ηθ e_η₁ e_ηθ₁ e_ηθ₂ : Expr) : m Expr
  mkEvalHorizontalCompAux'Whisker (f : Atom₁) (η θ : WhiskerLeft)
    (ηθ ηθ₁ ηθ₂ ηθ₃ : NormalExpr) (e_ηθ e_ηθ₁ e_ηθ₂ e_ηθ₃ : Expr) : m Expr
  mkEvalHorizontalCompAux'OfWhisker (f : Atom₁) (η : HorizontalComp) (θ : WhiskerLeft)
    (η₁ ηθ ηθ₁ ηθ₂ : NormalExpr) (e_ηθ e_η₁ e_ηθ₁ e_ηθ₂ : Expr) : m Expr
  mkEvalHorizontalCompNilNil (α β : StructuralIso) : m Expr
  mkEvalHorizontalCompNilCons (α β : StructuralIso) (η : WhiskerLeft)
    (ηs η₁ ηs₁ η₂ η₃ : NormalExpr) (e_η₁ e_ηs₁ e_η₂ e_η₃ : Expr) : m Expr
  mkEvalHorizontalCompConsNil (α β : StructuralIso) (η : WhiskerLeft) (ηs : NormalExpr)
    (η₁ ηs₁ η₂ η₃ : NormalExpr) (e_η₁ e_ηs₁ e_η₂ e_η₃ : Expr) : m Expr
  mkEvalHorizontalCompConsCons (α β : StructuralIso) (η θ : WhiskerLeft)
    (ηs θs ηθ ηθs ηθ₁ ηθ₂ : NormalExpr) (e_ηθ e_ηθs e_ηθ₁ e_ηθ₂ : Expr) : m Expr

class MkEval (m : Type → Type) extends
    MkEvalComp m, MkEvalWhiskerLeft m, MkEvalWhiskerRight m, MkEvalHorizontalComp m where
  mkEvalComp (η θ : Mor₂) (η' θ' ηθ : NormalExpr) (e_η e_θ e_ηθ : Expr) : m Expr
  mkEvalWhiskerLeft (f : Mor₁) (η : Mor₂) (η' θ : NormalExpr) (e_η e_θ : Expr) : m Expr
  mkEvalWhiskerRight (η : Mor₂) (h : Mor₁) (η' θ : NormalExpr) (e_η e_θ : Expr) : m Expr
  mkEvalHorizontalComp (η θ : Mor₂) (η' θ' ι : NormalExpr) (e_η e_θ e_ι : Expr) : m Expr
  mkEvalOf (η : Atom) : m Expr
  mkEvalMonoidalComp (η θ : Mor₂) (α : StructuralIso) (η' θ' αθ ηαθ : NormalExpr)
    (e_η e_θ e_αθ e_ηαθ : Expr) : m Expr

open MkEvalComp MonadStructuralIso MonadNormalExpr

def evalCompNil [MonadStructuralIso m] [MonadNormalExpr m] [MkEval m] (α : StructuralIso) :
    NormalExpr → m Eval.Result
  | .nil β => do return ⟨.nil (← comp₂M α β), ← mkEvalCompNilNil α β⟩
  | .cons _ β η ηs => do return ⟨← consM (← comp₂M α β) η ηs, ← mkEvalCompNilCons α β η ηs⟩

/-- Evaluate the expression `η ≫ θ` into a normalized form. -/
def evalComp [MonadStructuralIso m] [MonadNormalExpr m] [MkEval m] : NormalExpr → NormalExpr → m Eval.Result
  | .nil α, η => do evalCompNil α η
  | .cons _ α η ηs, θ => do
    let ⟨ι, e_ι⟩ ← evalComp ηs θ
    return ⟨← consM α η ι, ← mkEvalCompCons α η ηs θ ι e_ι⟩

open MkEvalWhiskerLeft

/-- Evaluate the expression `f ◁ η` into a normalized form. -/
def evalWhiskerLeft [MonadMor₁ m] [MonadNormalExpr m] [MonadStructuralIso m]
    [MkEval m] :
    Mor₁ → NormalExpr → m Eval.Result
  | f, .nil α => do
    return ⟨.nil (← whiskerLeftM f α), ← mkEvalWhiskerLeftNil f α⟩
  | .of f, .cons _ α η ηs => do
    let η' ← MonadWhiskerLeft.whiskerLeftM f η
    let ⟨θ, e_θ⟩ ← evalWhiskerLeft (.of f) ηs
    let η'' ← consM (← whiskerLeftM (.of f) α) η' θ
    return ⟨η'', ← mkEvalWhiskerLeftOfCons f α η ηs θ e_θ⟩
  | .comp _ f g, η => do
    let ⟨θ, e_θ⟩ ← evalWhiskerLeft g η
    let ⟨ι, e_ι⟩ ← evalWhiskerLeft f θ
    let h ← η.srcM
    let h' ← η.tgtM
    let ⟨ι', e_ι'⟩ ← evalComp ι (← NormalExpr.associatorInvM f g h')
    let ⟨ι'', e_ι''⟩ ← evalComp (← NormalExpr.associatorM f g h) ι'
    return ⟨ι'', ← mkEvalWhiskerLeftComp f g η θ ι ι' ι'' e_θ e_ι e_ι' e_ι''⟩
  | .id _ _, η => do
    let f ← η.srcM
    let g ← η.tgtM
    let ⟨η', e_η'⟩ ← evalComp η (← NormalExpr.leftUnitorInvM g)
    let ⟨η'', e_η''⟩ ← evalComp (← NormalExpr.leftUnitorM f) η'
    return ⟨η'', ← mkEvalWhiskerLeftId η η' η'' e_η' e_η''⟩

open MkEvalWhiskerRight MkEvalHorizontalComp
open MonadStructuralIso


mutual

/-- Evaluate the expression `η ▷ f` into a normalized form. -/
partial def evalWhiskerRightAux [MonadMor₁ m] [MonadNormalExpr m] [MonadStructuralIso m]
    [MkEval m] : HorizontalComp → Atom₁ → m Eval.Result
  | .of η, f => do
    let η' ← NormalExpr.ofM <| .of <| .of <| ← MonadWhiskerRight.whiskerRightM η f
    return ⟨η', ← mkEvalWhiskerRightAuxOf η f⟩
  | .cons _ η ηs, f => do
    let ⟨ηs', e_ηs'⟩ ← evalWhiskerRightAux ηs f
    let ⟨η₁, e_η₁⟩ ← evalHorizontalComp (← NormalExpr.ofM <| .of <| .of η) ηs'
    let ⟨η₂, e_η₂⟩ ← evalComp η₁ (← NormalExpr.associatorInvM (← η.tgtM) (← ηs.tgtM) (.of f))
    let ⟨η₃, e_η₃⟩ ← evalComp (← NormalExpr.associatorM (← η.srcM) (← ηs.srcM) (.of f)) η₂
    return ⟨η₃, ← mkEvalWhiskerRightAuxCons f η ηs ηs' η₁ η₂ η₃ e_ηs' e_η₁ e_η₂ e_η₃⟩

/-- Evaluate the expression `η ▷ f` into a normalized form. -/
partial def evalWhiskerRight [MonadMor₁ m] [MonadNormalExpr m] [MonadStructuralIso m]
    [MkEval m] : NormalExpr → Mor₁ → m Eval.Result
  | .nil α, h => do
    return ⟨.nil (← whiskerRightM α h), ← mkEvalWhiskerRightNil α h⟩
  | .cons _ α (.of η) ηs, .of f => do
    let ⟨ηs₁, e_ηs₁⟩ ← evalWhiskerRight ηs (.of f)
    let ⟨η₁, e_η₁⟩ ← evalWhiskerRightAux η f
    let ⟨η₂, e_η₂⟩ ← evalComp η₁ ηs₁
    let ⟨η₃, e_η₃⟩ ← evalCompNil (← whiskerRightM α (.of f)) η₂
    return ⟨η₃, ← mkEvalWhiskerRightConsOfOf f α η ηs ηs₁ η₁ η₂ η₃ e_ηs₁ e_η₁ e_η₂ e_η₃⟩
  | .cons _ α (.whisker _ f η) ηs, h => do
    let g ← η.srcM
    let g' ← η.tgtM
    let ⟨η₁, e_η₁⟩ ← evalWhiskerRight (← consM (← id₂M g) η (← NormalExpr.idM g')) h
    let ⟨η₂, e_η₂⟩ ← evalWhiskerLeft (.of f) η₁
    let ⟨ηs₁, e_ηs₁⟩ ← evalWhiskerRight ηs h
    let α' ← whiskerRightM α h
    let ⟨ηs₂, e_ηs₂⟩ ← evalComp (← NormalExpr.associatorInvM (.of f) g' h) ηs₁
    let ⟨η₃, e_η₃⟩ ← evalComp η₂ ηs₂
    let ⟨η₄, e_η₄⟩ ← evalComp (← NormalExpr.associatorM (.of f) g h) η₃
    let ⟨η₅, e_η₅⟩ ← evalComp (.nil α') η₄
    return ⟨η₅, ← mkEvalWhiskerRightConsWhisker f h α η ηs η₁ η₂ ηs₁ ηs₂ η₃ η₄ η₅
      e_η₁ e_η₂ e_ηs₁ e_ηs₂ e_η₃ e_η₄ e_η₅⟩
  | η, .comp _ g h => do
    let ⟨η₁, e_η₁⟩ ← evalWhiskerRight η g
    let ⟨η₂, e_η₂⟩ ← evalWhiskerRight η₁ h
    let f ← η.srcM
    let f' ← η.tgtM
    let ⟨η₃, e_η₃⟩ ← evalComp η₂ (← NormalExpr.associatorM f' g h)
    let ⟨η₄, e_η₄⟩ ← evalComp (← NormalExpr.associatorInvM f g h) η₃
    return ⟨η₄, ← mkEvalWhiskerRightComp g h η η₁ η₂ η₃ η₄ e_η₁ e_η₂ e_η₃ e_η₄⟩
  | η, .id _ _ => do
    let f ← η.srcM
    let g ← η.tgtM
    let ⟨η₁, e_η₁⟩ ← evalComp η (← NormalExpr.rightUnitorInvM g)
    let ⟨η₂, e_η₂⟩ ← evalComp (← NormalExpr.rightUnitorM f) η₁
    return ⟨η₂, ← mkEvalWhiskerRightId η η₁ η₂ e_η₁ e_η₂⟩

/-- Evaluate the expression `η ⊗ θ` into a normalized form. -/
partial def evalHorizontalCompAux [MonadMor₁ m] [MonadNormalExpr m] [MonadStructuralIso m]
    [MkEval m] : HorizontalComp → HorizontalComp → m Eval.Result
  | .of η, θ => do
    return ⟨← NormalExpr.ofM <| .of <| ← MonadHorizontalComp.hConsM η θ,
      ← mkEvalHorizontalCompAuxOf η θ⟩
  | .cons _ η ηs, θ => do
    let α ← NormalExpr.associatorM (← η.srcM) (← ηs.srcM) (← θ.srcM)
    let α' ← NormalExpr.associatorInvM (← η.tgtM) (← ηs.tgtM) (← θ.tgtM)
    let ⟨ηθ, e_ηθ⟩ ← evalHorizontalCompAux ηs θ
    let ⟨η₁, e_η₁⟩ ← evalHorizontalComp (← NormalExpr.ofM <| .of <| .of η) ηθ
    let ⟨ηθ₁, e_ηθ₁⟩ ← evalComp η₁ α'
    let ⟨ηθ₂, e_ηθ₂⟩ ← evalComp α ηθ₁
    return ⟨ηθ₂, ← mkEvalHorizontalCompAuxCons η ηs θ ηθ η₁ ηθ₁ ηθ₂ e_ηθ e_η₁ e_ηθ₁ e_ηθ₂⟩

/-- Evaluate the expression `η ⊗ θ` into a normalized form. -/
partial def evalHorizontalCompAux' [MonadMor₁ m] [MonadNormalExpr m] [MonadStructuralIso m]
    [MkEval m] : WhiskerLeft → WhiskerLeft → m Eval.Result
  | .of η, .of θ => evalHorizontalCompAux η θ
  | .whisker _ f η, θ => do
    let ⟨ηθ, e_ηθ⟩ ← evalHorizontalCompAux' η θ
    let ⟨ηθ₁, e_ηθ₁⟩ ← evalWhiskerLeft (.of f) ηθ
    let ⟨ηθ₂, e_ηθ₂⟩ ← evalComp ηθ₁ (← NormalExpr.associatorInvM (.of f) (← η.tgtM) (← θ.tgtM))
    let ⟨ηθ₃, e_ηθ₃⟩ ← evalComp (← NormalExpr.associatorM (.of f) (← η.srcM) (← θ.srcM)) ηθ₂
    return ⟨ηθ₃, ← mkEvalHorizontalCompAux'Whisker f η θ ηθ ηθ₁ ηθ₂ ηθ₃ e_ηθ e_ηθ₁ e_ηθ₂ e_ηθ₃⟩
  | .of η, .whisker _ f θ => do
    let ⟨η₁, e_η₁⟩ ← evalWhiskerRightAux η f
    let ⟨ηθ, e_ηθ⟩ ← evalHorizontalComp η₁ (← NormalExpr.ofM θ)
    let ⟨ηθ₁, e_ηθ₁⟩ ← evalComp ηθ (← NormalExpr.associatorM (← η.tgtM) (.of f) (← θ.tgtM))
    let ⟨ηθ₂, e_ηθ₂⟩ ← evalComp (← NormalExpr.associatorInvM (← η.srcM) (.of f) (← θ.srcM)) ηθ₁
    return ⟨ηθ₂, ← mkEvalHorizontalCompAux'OfWhisker f η θ ηθ η₁ ηθ₁ ηθ₂ e_η₁ e_ηθ e_ηθ₁ e_ηθ₂⟩

/-- Evaluate the expression `η ⊗ θ` into a normalized form. -/
partial def evalHorizontalComp [MonadMor₁ m] [MonadNormalExpr m] [MonadStructuralIso m]
    [MkEval m] : NormalExpr → NormalExpr → m Eval.Result
  | .nil α, .nil β => do
    return ⟨.nil <| ← horizontalCompM α β, ← mkEvalHorizontalCompNilNil α β⟩
  | .nil α, .cons _ β η ηs => do
    let ⟨η₁, e_η₁⟩ ← evalWhiskerLeft (← α.tgtM) (← NormalExpr.ofM η)
    let ⟨ηs₁, e_ηs₁⟩ ← evalWhiskerLeft (← α.tgtM) ηs
    let ⟨η₂, e_η₂⟩ ← evalComp η₁ ηs₁
    let ⟨η₃, e_η₃⟩ ← evalCompNil (← horizontalCompM α β) η₂
    return ⟨η₃, ← mkEvalHorizontalCompNilCons α β η ηs η₁ ηs₁ η₂ η₃ e_η₁ e_ηs₁ e_η₂ e_η₃⟩
  | .cons _ α η ηs, .nil β => do
    let ⟨η₁, e_η₁⟩ ← evalWhiskerRight (← NormalExpr.ofM η) (← β.tgtM)
    let ⟨ηs₁, e_ηs₁⟩ ← evalWhiskerRight ηs (← β.tgtM)
    let ⟨η₂, e_η₂⟩ ← evalComp η₁ ηs₁
    let ⟨η₃, e_η₃⟩ ← evalCompNil (← horizontalCompM α β) η₂
    return ⟨η₃, ← mkEvalHorizontalCompConsNil α β η ηs η₁ ηs₁ η₂ η₃ e_η₁ e_ηs₁ e_η₂ e_η₃⟩
  | .cons _ α η ηs, .cons _ β θ θs => do
    let ⟨ηθ, e_ηθ⟩ ← evalHorizontalCompAux' η θ
    let ⟨ηθs, e_ηθs⟩ ← evalHorizontalComp ηs θs
    let ⟨ηθ₁, e_ηθ₁⟩ ← evalComp ηθ ηθs
    let ⟨ηθ₂, e_ηθ₂⟩ ← evalCompNil (← horizontalCompM α β) ηθ₁
    return ⟨ηθ₂,
      ← mkEvalHorizontalCompConsCons α β η θ ηs θs ηθ ηθs ηθ₁ ηθ₂ e_ηθ e_ηθs e_ηθ₁ e_ηθ₂⟩

end

variable
[MonadMor₁ m] [MonadStructuralIso m]
    [MonadLift MetaM m] [MonadAlwaysExcept Exception m] [MonadRef m]
    [MonadStructuralIso m] [MonadNormalExpr m] [MkEval m]

open MonadMor₂ MkEval

variable [MkMor₁ m] [MonadMor₂ m]

-- def mkEvalComp (η θ : Mor₂) (η' θ' ι : NormalExpr) (e_η e_θ e_ηθ : Expr) : m Expr := do sorry

-- def evalComp : NormalExpr → NormalExpr → m Eval.Result := sorry

def traceProof (nm : Name) (result : Expr) : m Unit := do
  withTraceNode nm (fun _ => return m!"{checkEmoji} {← inferType result}") do
    if ← isTracingEnabledFor nm then addTrace nm m!"proof: {result}"

/-- Evaluate the expression of a 2-morphism into a normalized form. -/
def eval (nm : Name) (e : Mor₂) : m Eval.Result := do
  -- let e ← instantiateMVars e
  withTraceNode nm (fun _ => return m!"eval: {e.e}") do
    match e with
    | .structuralAtom α =>
      return ⟨.nil <| .atom α, ← mkEqRefl α.e⟩
    -- if let .some α ← structuralAtom? e then
      -- return ⟨.nil <| .atom α, ← mkEqRefl (← α.e)⟩
    -- else
      -- match (← whnfR e).getAppFnArgs with
    -- | .id e f  =>
    --   return ⟨.nil (.id e f), ← mkEqRefl ((← id₂M f).e)⟩
    | .comp _ η θ => withTraceNode nm (fun _ => return m!"comp") do
      let ⟨η', e_η⟩ ← eval nm η
      let ⟨θ', e_θ⟩ ← eval nm θ
      let ⟨ηθ, pf⟩ ← evalComp η' θ'
      let result ← mkEvalComp η θ η' θ' ηθ e_η e_θ pf
      traceProof nm result
      return ⟨ηθ, result⟩
    | .whiskerLeft _ f η => withTraceNode nm (fun _ => return m!"whiskerLeft") do
      let ⟨η', e_η⟩ ← eval nm η
      let ⟨θ, e_θ⟩ ← evalWhiskerLeft f η'
      let result ← mkEvalWhiskerLeft f η θ η' e_η e_θ
      traceProof nm result
      return ⟨θ, result⟩
    | .whiskerRight _ η h =>
      withTraceNode `monoidal (fun _ => return m!"whiskerRight") do
        let ⟨η', e_η⟩ ← eval nm η
        let ⟨θ, e_θ⟩ ← evalWhiskerRight η' h
        let result ← mkEvalWhiskerRight η h η' θ e_η e_θ
        traceProof nm result
        return ⟨θ, result⟩
    | .coherenceComp _ _ α₀ η θ =>
      withTraceNode `monoidal (fun _ => return m!"monoidalComp") do
        let ⟨η', e_η⟩ ← eval nm η
        -- let α₀ ← structuralOfMonoidalComp e
        let α := NormalExpr.nil α₀
        let ⟨θ', e_θ⟩ ← eval nm θ
        let ⟨αθ, e_αθ⟩ ← evalComp α θ'
        let ⟨ηαθ, e_ηαθ⟩ ← evalComp η' αθ
        let result ← mkEvalMonoidalComp η θ α₀ η' θ' αθ ηαθ e_η e_θ e_αθ e_ηαθ
        traceProof nm result
        return ⟨ηαθ, result⟩
    | .horizontalComp _ η θ =>
      withTraceNode `monoidal (fun _ => return m!"tensorHom") do
        let ⟨η', e_η⟩ ← eval nm η
        let ⟨θ', e_θ⟩ ← eval nm θ
        let ⟨ηθ, e_ηθ⟩ ← evalHorizontalComp η' θ'
        let result ← mkEvalHorizontalComp η θ η' θ' ηθ e_η e_θ e_ηθ
        traceProof nm result
        return ⟨ηθ, result⟩
    | .of η  =>
      let result ← mkEvalOf η
      traceProof nm result
      return ⟨← NormalExpr.ofAtomM η, result⟩

end Mathlib.Tactic.BicategoryLike
