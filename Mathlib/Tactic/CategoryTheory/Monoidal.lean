/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.Tactic.CategoryTheory.MonoidalComp
import Mathlib.CategoryTheory.Monoidal.Free.Coherence

/-!
# Normalization of morphisms in monoidal categories
This file provides a tactic that normalizes morphisms in monoidal categories. This is used in the
string diagram widget given in `Mathlib.Tactic.StringDiagram`.
We say that the morphism `η` in a monoidal category is in normal form if
1. `η` is of the form `α₀ ≫ η₀ ≫ α₁ ≫ η₁ ≫ ... αₘ ≫ ηₘ ≫ αₘ₊₁` where each `αᵢ` is a
  structural 2-morphism (consisting of associators and unitors),
2. each `ηᵢ` is a non-structural 2-morphism of the form `f₁ ◁ ... ◁ fₘ ◁ θ`, and
3. `θ` is of the form `ι ▷ g₁ ▷ ... ▷ gₗ`

-/

namespace Mathlib.Tactic.Monoidal

open Lean Meta Elab
open CategoryTheory
open Mathlib.Tactic.Monoidal

/-- The context for evaluating expressions. -/
structure Context where
  /-- The expression for the underlying category. -/
  C : Expr

/-- Populate a `context` object for evaluating `e`. -/
def mkContext (e : Expr) : MetaM Context := do
  match (← inferType e).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, f, _]) =>
    let C ← inferType f
    return ⟨C⟩
  | _ => throwError "not a morphism"

/-- The monad for the normalization of 2-morphisms. -/
abbrev MonoidalM := ReaderT Context MetaM

/-- Run a computation in the `M` monad. -/
abbrev MonoidalM.run {α : Type} (c : Context) (m : MonoidalM α) : MetaM α :=
  ReaderT.run m c

/-- Expressions for atomic 1-morphisms. -/
structure Atom₁ : Type where
  /-- Extract a Lean expression from an `Atom₁` expression. -/
  e : Expr

/-- Expressions for 1-morphisms. -/
inductive Mor₁ : Type
  /-- `id` is the expression for `𝟙_ C`. -/
  | id : Mor₁
  /-- `comp X Y` is the expression for `X ⊗ Y` -/
  | comp : Mor₁ → Mor₁ → Mor₁
  /-- Construct the expression for an atomic 1-morphism. -/
  | of : Atom₁ → Mor₁
  deriving Inhabited

/-- Converts a 1-morphism into a list of its components. -/
def Mor₁.toList : Mor₁ → List Atom₁
  | .id => []
  | .comp f g => f.toList ++ g.toList
  | .of f => [f]

/-- Returns `𝟙_ C` if the expression `e` is of the form `𝟙_ C`. -/
def isTensorUnit? (e : Expr) : MetaM (Option Expr) := do
  let C ← mkFreshExprMVar none
  let instC ← mkFreshExprMVar none
  let instMC ← mkFreshExprMVar none
  let unit := mkAppN (← mkConstWithFreshMVarLevels
    ``MonoidalCategoryStruct.tensorUnit) #[C, instC, instMC]
  if ← withDefault <| isDefEq e unit then
    return ← instantiateMVars unit
  else
    return none

/-- Returns `(f, g)` if the expression `e` is of the form `f ⊗ g`. -/
def isTensorObj? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let C ← mkFreshExprMVar none
  let f ← mkFreshExprMVar C
  let g ← mkFreshExprMVar C
  let instC ← mkFreshExprMVar none
  let instMC ← mkFreshExprMVar none
  let fg := mkAppN (← mkConstWithFreshMVarLevels
    ``MonoidalCategoryStruct.tensorObj) #[C, instC, instMC, f, g]
  if ← withDefault <| isDefEq e fg then
    return (← instantiateMVars f, ← instantiateMVars g)
  else
    return none

/-- Construct a `Mor₁` expression from a Lean expression. -/
partial def toMor₁ (e : Expr) : MetaM Mor₁ := do
  if let some _ ← isTensorUnit? e then
    return Mor₁.id
  else if let some (f, g) ← isTensorObj? e then
    return (← toMor₁ f).comp (← toMor₁ g)
  else
    return Mor₁.of ⟨e⟩

/-- Expressions for atomic structural 2-morphisms. -/
inductive StructuralAtom : Type
  /-- The expression for the associator `(α_ f g h).hom`. -/
  | associator (f g h : Mor₁) : StructuralAtom
  /-- The expression for the inverse of the associator `(α_ f g h).inv`. -/
  | associatorInv (f g h : Mor₁) : StructuralAtom
  /-- The expression for the left unitor `(λ_ f).hom`. -/
  | leftUnitor (f : Mor₁) : StructuralAtom
  /-- The expression for the inverse of the left unitor `(λ_ f).inv`. -/
  | leftUnitorInv (f : Mor₁) : StructuralAtom
  /-- The expression for the right unitor `(ρ_ f).hom`. -/
  | rightUnitor (f : Mor₁) : StructuralAtom
  /-- The expression for the inverse of the right unitor `(ρ_ f).inv`. -/
  | rightUnitorInv (f : Mor₁) : StructuralAtom
  /-- Expressions for `α` in the monoidal composition `η ⊗≫ θ := η ≫ α ≫ θ`. -/
  | monoidalCoherence (f g : Mor₁) (e : Expr) : StructuralAtom
  deriving Inhabited

/-- Construct a `StructuralAtom` expression from a Lean expression. -/
def structuralAtom? (e : Expr) : MetaM (Option StructuralAtom) := do
  match e.getAppFnArgs with
  | (``Iso.hom, #[_, _, _, _, η]) =>
    match (← whnfR η).getAppFnArgs with
    | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) =>
      return some <| .associator (← toMor₁ f) (← toMor₁ g) (← toMor₁ h)
    | (``MonoidalCategoryStruct.leftUnitor, #[_, _, _, f]) =>
      return some <| .leftUnitor (← toMor₁ f)
    | (``MonoidalCategoryStruct.rightUnitor, #[_, _, _, f]) =>
      return some <| .rightUnitor (← toMor₁ f)
    | _ => return none
  | (``Iso.inv, #[_, _, _, _, η]) =>
    match (← whnfR η).getAppFnArgs with
    | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) =>
      return some <| .associatorInv (← toMor₁ f) (← toMor₁ g) (← toMor₁ h)
    | (``MonoidalCategoryStruct.leftUnitor, #[_, _, _, f]) =>
      return some <| .leftUnitorInv (← toMor₁ f)
    | (``MonoidalCategoryStruct.rightUnitor, #[_, _, _, f]) =>
      return some <| .rightUnitorInv (← toMor₁ f)
    | _ => return none
  | _ =>
    match (← whnfR e).getAppFnArgs with
    | (``MonoidalCoherence.hom, #[_, _, f, g, inst]) =>
      return some <| .monoidalCoherence (← toMor₁ f) (← toMor₁ g) inst
    | _ => return none

/-- Expressions for atomic non-structural 2-morphisms. -/
structure Atom where
  /-- Extract a Lean expression from an `Atom` expression. -/
  e : Expr
  deriving Inhabited

/-- Expressions of the form `η ▷ f₁ ▷ ... ▷ fₙ`. -/
inductive WhiskerRightExpr : Type
  /-- Construct the expression for an atomic 2-morphism. -/
  | of (η : Atom) : WhiskerRightExpr
  /-- Construct the expression for `η ▷ f`. -/
  | whisker (η : WhiskerRightExpr) (f : Atom₁) : WhiskerRightExpr
  deriving Inhabited

/-- Expressions of the form `η₁ ⊗ ... ⊗ ηₙ`. -/
inductive TensorHomExpr : Type
  | of (η : WhiskerRightExpr) : TensorHomExpr
  | cons (head : WhiskerRightExpr) (tail : TensorHomExpr) : TensorHomExpr
  deriving Inhabited

/-- Expressions of the form `f₁ ◁ ... ◁ fₙ ◁ η`. -/
inductive WhiskerLeftExpr : Type
  /-- Construct the expression for a right-whiskered 2-morphism. -/
  | of (η : TensorHomExpr) : WhiskerLeftExpr
  /-- Construct the expression for `f ◁ η`. -/
  | whisker (f : Atom₁) (η : WhiskerLeftExpr) : WhiskerLeftExpr
  deriving Inhabited

/-- Expressions for structural 2-morphisms. -/
inductive Structural : Type
  /-- Expressions for atomic structural 2-morphisms. -/
  | atom (η : StructuralAtom) : Structural
  /-- Expressions for the identity `𝟙 f`. -/
  | id (f : Mor₁) : Structural
  /-- Expressions for the composition `η ≫ θ`. -/
  | comp (α β : Structural) : Structural
  /-- Expressions for the left whiskering `f ◁ η`. -/
  | whiskerLeft (f : Mor₁) (η : Structural) : Structural
  /-- Expressions for the right whiskering `η ▷ f`. -/
  | whiskerRight (η : Structural) (f : Mor₁) : Structural
    /-- Expressions for the tensor `α ⊗ β`. -/
  | tensorHom (α β : Structural) : Structural
  deriving Inhabited

/-- Normalized expressions for 2-morphisms. -/
inductive NormalExpr : Type
  /-- Construct the expression for a structural 2-morphism. -/
  | nil (α : Structural) : NormalExpr
  /-- Construct the normalized expression of 2-morphisms recursively. -/
  | cons (head_structural : Structural) (head : WhiskerLeftExpr) (tail : NormalExpr) : NormalExpr
  deriving Inhabited

/-- The domain of a morphism. -/
def src (η : Expr) : MetaM Mor₁ := do
  match (← inferType η).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, f, _]) => toMor₁ f
  | _ => throwError "{η} is not a morphism"

/-- The codomain of a morphism. -/
def tar (η : Expr) : MetaM Mor₁ := do
  match (← inferType η).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, _, g]) => toMor₁ g
  | _ => throwError "{η} is not a morphism"

/-- The domain of a 2-morphism. -/
def Atom.src (η : Atom) : MetaM Mor₁ := do Monoidal.src η.e

/-- The codomain of a 2-morphism. -/
def Atom.tar (η : Atom) : MetaM Mor₁ := do Monoidal.tar η.e

/-- The domain of a 2-morphism. -/
def WhiskerRightExpr.src : WhiskerRightExpr → MetaM Mor₁
  | WhiskerRightExpr.of η => η.src
  | WhiskerRightExpr.whisker η f => return (← WhiskerRightExpr.src η).comp (Mor₁.of f)

/-- The codomain of a 2-morphism. -/
def WhiskerRightExpr.tar : WhiskerRightExpr → MetaM Mor₁
  | WhiskerRightExpr.of η => η.tar
  | WhiskerRightExpr.whisker η f => return (← WhiskerRightExpr.tar η).comp (Mor₁.of f)

/-- The domain of a 2-morphism. -/
def TensorHomExpr.src : TensorHomExpr → MetaM Mor₁
  | TensorHomExpr.of η => η.src
  | TensorHomExpr.cons η ηs => return (← η.src).comp (← ηs.src)

/-- The codomain of a 2-morphism. -/
def TensorHomExpr.tar : TensorHomExpr → MetaM Mor₁
  | TensorHomExpr.of η => η.tar
  | TensorHomExpr.cons η ηs => return (← η.tar).comp (← ηs.tar)

/-- The domain of a 2-morphism. -/
def WhiskerLeftExpr.src : WhiskerLeftExpr → MetaM Mor₁
  | WhiskerLeftExpr.of η => η.src
  | WhiskerLeftExpr.whisker f η => return (Mor₁.of f).comp (← η.src)

/-- The codomain of a 2-morphism. -/
def WhiskerLeftExpr.tar : WhiskerLeftExpr → MetaM Mor₁
  | WhiskerLeftExpr.of η => η.tar
  | WhiskerLeftExpr.whisker f η => return (Mor₁.of f).comp (← η.tar)

/-- The domain of a 2-morphism. -/
def StructuralAtom.src : StructuralAtom → Mor₁
  | .associator f g h => (f.comp g).comp h
  | .associatorInv f g h => f.comp (g.comp h)
  | .leftUnitor f => Mor₁.id.comp f
  | .leftUnitorInv f => f
  | .rightUnitor f => f.comp Mor₁.id
  | .rightUnitorInv f => f
  | .monoidalCoherence f _ _ => f

/-- The codomain of a 2-morphism. -/
def StructuralAtom.tar : StructuralAtom → Mor₁
  | .associator f g h => f.comp (g.comp h)
  | .associatorInv f g h => (f.comp g).comp h
  | .leftUnitor f => f
  | .leftUnitorInv f => Mor₁.id.comp f
  | .rightUnitor f => f
  | .rightUnitorInv f => f.comp Mor₁.id
  | .monoidalCoherence _ g _ => g

/-- The domain of a 2-morphism. -/
def Structural.src : Structural → Mor₁
  | .atom α => α.src
  | .id f => f
  | .comp α _ => α.src
  | .whiskerLeft f α => f.comp α.src
  | .whiskerRight α f => α.src.comp f
  | .tensorHom α β => α.src.comp β.src

/-- The codomain of a 2-morphism. -/
def Structural.tar : Structural → Mor₁
  | .atom α => α.tar
  | .id f => f
  | .comp _ β => β.tar
  | .whiskerLeft f α => f.comp α.tar
  | .whiskerRight α f => α.tar.comp f
  | .tensorHom α β => α.tar.comp β.tar

/-- The domain of a 2-morphism. -/
def NormalExpr.src : NormalExpr → Mor₁
  | NormalExpr.nil η => η.src
  | NormalExpr.cons α _ _ => α.src

/-- The codomain of a 2-morphism. -/
def NormalExpr.tar : NormalExpr → Mor₁
  | NormalExpr.nil η => η.tar
  | NormalExpr.cons _ _ ηs => ηs.tar

/-- The associator as a term of `normalExpr`. -/
def NormalExpr.associator (f g h : Mor₁) : NormalExpr :=
  .nil <| .atom <| .associator f g h

/-- The inverse of the associator as a term of `normalExpr`. -/
def NormalExpr.associatorInv (f g h : Mor₁) : NormalExpr :=
  .nil <| .atom <| .associatorInv f g h

/-- The left unitor as a term of `normalExpr`. -/
def NormalExpr.leftUnitor (f : Mor₁) : NormalExpr :=
  .nil <| .atom <| .leftUnitor f

/-- The inverse of the left unitor as a term of `normalExpr`. -/
def NormalExpr.leftUnitorInv (f : Mor₁) : NormalExpr :=
  .nil <| .atom <| .leftUnitorInv f

/-- The right unitor as a term of `normalExpr`. -/
def NormalExpr.rightUnitor (f : Mor₁) : NormalExpr :=
  .nil <| .atom <| .rightUnitor f

/-- The inverse of the right unitor as a term of `normalExpr`. -/
def NormalExpr.rightUnitorInv (f : Mor₁) : NormalExpr :=
  .nil <| .atom <| .rightUnitorInv f

-- /-- Return `η` for `η ▷ g₁ ▷ ... ▷ gₙ`. -/
-- def WhiskerRightExpr.atom : WhiskerRightExpr → Atom
--   | WhiskerRightExpr.of η => η
--   | WhiskerRightExpr.whisker η _ => η.atom

-- /-- Return `η` for `f₁ ◁ ... ◁ fₙ ◁ η ▷ g₁ ▷ ... ▷ gₙ`. -/
-- def WhiskerLeftExpr.atom : WhiskerLeftExpr → Atom
--   | WhiskerLeftExpr.of η => η.atom
--   | WhiskerLeftExpr.whisker _ η => η.atom

-- /-- Construct a `Structural` expression from a Lean expression for a structural 2-morphism. -/
-- partial def structural? (e : Expr) : MetaM Structural := do
--   match (← whnfR e).getAppFnArgs with
--   | (``CategoryStruct.comp, #[_, _, _, α, β]) =>
--     return .comp (← structural? α) (← structural? β)
--   | (``CategoryStruct.id, #[_, f]) => return .id (← toMor₁ f)
--   | (``MonoidalCategoryStruct.whiskerLeft, #[f, η]) =>
--     return .whiskerLeft (← toMor₁ f) (← structural? η)
--   | (``MonoidalCategoryStruct.whiskerRight, #[η, f]) =>
--     return .whiskerRight (← structural? η) (← toMor₁ f)
--   | _ => match ← structuralAtom? e with
--     | some η => return .atom η
--     | none => throwError "{e} is not a structural 2-morphism"

/-- Construct a `NormalExpr` expression from a `WhiskerLeftExpr` expression. -/
def NormalExpr.of (η : WhiskerLeftExpr) : MetaM NormalExpr := do
  return .cons (.id (← η.src)) η (.nil (.id (← η.tar)))

/-- Construct a `NormalExpr` expression from a Lean expression for an atomic 2-morphism. -/
def NormalExpr.ofExpr (η : Expr) : MetaM NormalExpr :=
  NormalExpr.of <| .of <| .of <| .of ⟨η⟩

/-- Construct a `NormalExpr` expression from another `NormalExpr` expression by adding a structural
2-morphism at the head. -/
def NormalExpr.ofNormalExpr (α : Structural) (e : NormalExpr) : MetaM NormalExpr :=
  match e with
  | .nil β => return .nil (α.comp β)
  | .cons β η ηs => return .cons (α.comp β) η ηs

/-- If `e` is an expression of the form `η ⊗≫ θ := η ≫ α ≫ θ` in the monoidal category `C`,
return the expression for `α` .-/
def structuralOfMonoidalComp (C e : Expr) : MetaM StructuralAtom := do
  let v ← mkFreshLevelMVar
  let u ← mkFreshLevelMVar
  _ ← isDefEq (.sort (.succ v)) (← inferType (← inferType e))
  _ ← isDefEq (.sort (.succ u)) (← inferType C)
  let W ← mkFreshExprMVar none
  let X ← mkFreshExprMVar none
  let Y ← mkFreshExprMVar none
  let Z ← mkFreshExprMVar none
  let f ← mkFreshExprMVar none
  let g ← mkFreshExprMVar none
  let α₀ ← mkFreshExprMVar none
  let instC ← mkFreshExprMVar none
  let αg := mkAppN (.const ``CategoryStruct.comp [v, u]) #[C, instC, X, Y, Z, α₀, g]
  let fαg := mkAppN (.const ``CategoryStruct.comp [v, u]) #[C, instC, W, X, Z, f, αg]
  _ ← isDefEq e fαg
  match ← structuralAtom? α₀ with
  | some α => return α
  | none => throwError "not a structural 2-morphism"

section

open scoped MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable {f f' g g' h i j f₁ f₂ f₃ g₁ g₂ g₃ h₁ h₂ h₃ i₁ i₂ i₃ : C}

theorem evalComp_nil_cons {f g h i j : C} (α : f ⟶ g) (β : g ⟶ h) (η : h ⟶ i) (ηs : i ⟶ j) :
    α ≫ (β ≫ η ≫ ηs) = (α ≫ β) ≫ η ≫ ηs := by
  simp

@[nolint synTaut]
theorem evalComp_nil_nil {f g h : C} (α : f ⟶ g) (β : g ⟶ h) :
    α ≫ β = α ≫ β := by
  simp

theorem evalComp_cons {f g h i j : C} (α : f ⟶ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j}
    (pf_ι : ηs ≫ θ = ι)  :
    (α ≫ η ≫ ηs) ≫ θ = α ≫ η ≫ ι := by
  simp [pf_ι]

@[nolint synTaut]
theorem evalWhiskerLeft_nil (f : C) (α : g ⟶ h) :
    f ◁ α = f ◁ α := by
  simp

theorem evalWhiskerLeft_of_cons
    (α : g ⟶ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ⊗ i ⟶ f ⊗ j} (pf_θ : f ◁ ηs = θ) :
    f ◁ (α ≫ η ≫ ηs) = f ◁ α ≫ f ◁ η ≫ θ := by
  simp [pf_θ]

theorem evalWhiskerLeft_comp {η : h ⟶ i} {θ : g ⊗ h ⟶ g ⊗ i} {ι : f ⊗ g ⊗ h ⟶ f ⊗ g ⊗ i}
    {ι' : f ⊗ g ⊗ h ⟶ (f ⊗ g) ⊗ i} {ι'' : (f ⊗ g) ⊗ h ⟶ (f ⊗ g) ⊗ i}
    (pf_θ : g ◁ η = θ) (pf_ι : f ◁ θ = ι)
    (pf_ι' : ι ≫ (α_ _ _ _).inv = ι') (pf_ι'' : (α_ _ _ _).hom ≫ ι' = ι'') :
    (f ⊗ g) ◁ η = ι'' := by
  simp [pf_θ, pf_ι, pf_ι', pf_ι'']

theorem evalWhiskerLeft_id {f g : C} {η : f ⟶ g}
    {η' : f ⟶ 𝟙_ C ⊗ g} {η'' : 𝟙_ C ⊗ f ⟶ 𝟙_ C ⊗ g}
    (pf_η' : η ≫ (λ_ _).inv = η') (pf_η'' : (λ_ _).hom ≫ η' = η'') :
    𝟙_ C ◁ η = η'' := by
  simp [pf_η', pf_η'']

theorem eval_comp
    {η η' : f ⟶ g} {θ θ' : g ⟶ h} {ι : f ⟶ h}
    (pf_η : η = η') (pf_θ : θ = θ') (pf_ηθ : η' ≫ θ' = ι) :
    η ≫ θ = ι := by
  simp [pf_η, pf_θ, pf_ηθ]

theorem eval_whiskerLeft
    {η η' : g ⟶ h} {θ : f ⊗ g ⟶ f ⊗ h}
    (pf_η : η = η') (pf_θ : f ◁ η' = θ) :
    f ◁ η = θ := by
  simp [pf_η, pf_θ]

theorem eval_whiskerRight
    {η η' : f ⟶ g} {θ : f ⊗ h ⟶ g ⊗ h}
    (pf_η : η = η') (pf_θ : η' ▷ h = θ) :
    η ▷ h = θ := by
  simp [pf_η, pf_θ]

theorem eval_tensorHom
    {η η' : f₁ ⟶ g₁} {θ θ' : f₂ ⟶ g₂}
    {ι : f₁ ⊗ f₂ ⟶ g₁ ⊗ g₂}
    (pf_η : η = η') (pf_θ : θ = θ') (pf_ηθ : η' ⊗ θ' = ι) :
    η ⊗ θ = ι := by
  simp [pf_η, pf_θ, pf_ηθ]

theorem eval_of (η : f ⟶ g) :
    η = 𝟙 _ ≫ η ≫ 𝟙 _ := by
  simp

@[nolint synTaut]
theorem evalWhiskerRight_nil (α : f ⟶ g) (h : C) :
    α ▷ h = α ▷ h := by
  simp

-- theorem evalWhiskerRight_cons_of_of
--     (α : f ⟶ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : h ⊗ j ⟶ i ⊗ j}
--     (pf_θ : ηs ▷ j = θ) :
--     (α ≫ η ≫ ηs) ▷ j = α ▷ j ≫ η ▷ j ≫ θ := by
--   simp [pf_θ]

theorem evalWhiskerRight_cons_whisker
    {α : g ⟶ f ⊗ h} {η : h ⟶ i} {ηs : f ⊗ i ⟶ j} {k : C}
    {η₁ : h ⊗ k ⟶ i ⊗ k} {η₂ : f ⊗ (h ⊗ k) ⟶ f ⊗ (i ⊗ k)} {ηs₁ : (f ⊗ i) ⊗ k ⟶ j ⊗ k}
    {ηs₂ : f ⊗ (i ⊗ k) ⟶ j ⊗ k} {η₃ : f ⊗ (h ⊗ k) ⟶ j ⊗ k} {η₄ : (f ⊗ h) ⊗ k ⟶ j ⊗ k}
    {η₅ : g ⊗ k ⟶ j ⊗ k}
    (pf_η₁ : (𝟙 _ ≫ η ≫ 𝟙 _ ) ▷ k = η₁) (pf_η₂ : f ◁ η₁ = η₂)
    (pf_ηs₁ : ηs ▷ k = ηs₁) (pf_ηs₂ : (α_ _ _ _).inv ≫ ηs₁ = ηs₂)
    (pf_η₃ : η₂ ≫ ηs₂ = η₃) (pf_η₄ : (α_ _ _ _).hom ≫ η₃ = η₄) (pf_η₅ : α ▷ k ≫ η₄ = η₅) :
    (α ≫ (f ◁ η) ≫ ηs) ▷ k = η₅ := by
  simp at pf_η₁
  simp [pf_η₁, pf_η₂, pf_ηs₁, pf_ηs₂, pf_η₃, pf_η₄, pf_η₅]

theorem evalWhiskerRight_comp
    {η : f ⟶ f'} {η₁ : f ⊗ g ⟶ f' ⊗ g} {η₂ : (f ⊗ g) ⊗ h ⟶ (f' ⊗ g) ⊗ h}
    {η₃ : (f ⊗ g) ⊗ h ⟶ f' ⊗ (g ⊗ h)} {η₄ : f ⊗ (g ⊗ h) ⟶ f' ⊗ (g ⊗ h)}
    (pf_η₁ : η ▷ g = η₁) (pf_η₂ : η₁ ▷ h = η₂)
    (pf_η₃ : η₂ ≫ (α_ _ _ _).hom = η₃) (pf_η₄ : (α_ _ _ _).inv ≫ η₃ = η₄) :
    η ▷ (g ⊗ h) = η₄ := by
  simp [pf_η₁, pf_η₂, pf_η₃, pf_η₄]

theorem evalWhiskerRight_id
    {η : f ⟶ g} {η₁ : f ⟶ g ⊗ 𝟙_ C} {η₂ : f ⊗ 𝟙_ C ⟶ g ⊗ 𝟙_ C}
    (pf_η₁ : η ≫ (ρ_ _).inv = η₁) (pf_η₂ : (ρ_ _).hom ≫ η₁ = η₂) :
    η ▷ 𝟙_ C = η₂ := by
  simp [pf_η₁, pf_η₂]

theorem eval_monoidalComp
    {η η' : f ⟶ g} {α : g ⟶ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i}
    (pf_η : η = η') (pf_θ : θ = θ') (pf_αθ : α ≫ θ' = αθ) (pf_ηαθ : η' ≫ αθ = ηαθ) :
    η ≫ α ≫ θ = ηαθ := by
  simp [pf_η, pf_θ, pf_αθ, pf_ηαθ]

open MonoidalCategory

theorem eval_evalWhiskerRightExprAux_cons
    {η : g ⟶ h} {ηs : i ⟶ j} {ηs' : i ⊗ f ⟶ j ⊗ f}
    {η₁ : g ⊗ (i ⊗ f) ⟶ h ⊗ (j ⊗ f)} {η₂ : g ⊗ (i ⊗ f) ⟶ (h ⊗ j) ⊗ f}
    {η₃ : (g ⊗ i) ⊗ f ⟶ (h ⊗ j) ⊗ f}
    (pf_ηs' : ηs ▷ f = ηs') (pf_η₁ : (𝟙 _ ≫ η ≫ 𝟙 _) ⊗ ηs' = η₁)
    (pf_η₂ : η₁ ≫ (α_ _ _ _).inv = η₂) (pf_η₃ : (α_ _ _ _).hom ≫ η₂ = η₃) :
    (η ⊗ ηs) ▷ f = η₃ := by
  simp [← pf_ηs', ← pf_η₁, ← pf_η₂, ← pf_η₃]

theorem evalWhiskerRight_cons_of_of
    (α : f ⟶ g) {η : g ⟶ h} {ηs : h ⟶ i} {ηs₁ : h ⊗ j ⟶ i ⊗ j}
    {η₁ : _} {η₂ : _}
    (pf_ηs₁ : ηs ▷ j = ηs₁) (pf_η₁ : η ▷ j = η₁)
    (pf_η₂ : η₁ ≫ ηs₁ = η₂) :
    (α ≫ η ≫ ηs) ▷ j = α ▷ j ≫ η₂ := by
  simp [← pf_ηs₁, ← pf_η₁, ← pf_η₂]

theorem evalTensorHomAux_cons
    {η : f₁ ⟶ g₁} {ηs : f₂ ⟶ g₂} {θ : f₃ ⟶ g₃}
    {ηsθ : f₂ ⊗ f₃ ⟶ g₂ ⊗ g₃} {η₁ : f₁ ⊗ (f₂ ⊗ f₃) ⟶ g₁ ⊗ (g₂ ⊗ g₃)}
    {η₂ : f₁ ⊗ (f₂ ⊗ f₃) ⟶ (g₁ ⊗ g₂) ⊗ g₃} {η₃ : (f₁ ⊗ f₂) ⊗ f₃ ⟶ (g₁ ⊗ g₂) ⊗ g₃}
    (pf_ηsθ : ηs ⊗ θ = ηsθ) (pf_η₁ : η ⊗ ηsθ = η₁)
    (pf_η₂ : η₁ ≫ (α_ _ _ _).inv = η₂) (pf_η₃ : (α_ _ _ _).hom ≫ η₂ = η₃) :
    (η ⊗ ηs) ⊗ θ = η₃ := by
  simp [← pf_ηsθ, ← pf_η₁, ← pf_η₂, ← pf_η₃]

theorem evalTensorHomAux'_whisker
    {η : f₁ ⟶ g₁} {θ : f₂ ⟶ g₂} {ηθ : f₁ ⊗ f₂ ⟶ g₁ ⊗ g₂}
    {ηθ₁ : f ⊗ (f₁ ⊗ f₂) ⟶ f ⊗ (g₁ ⊗ g₂)}
    {ηθ₂ : f ⊗ (f₁ ⊗ f₂) ⟶ (f ⊗ g₁) ⊗ g₂}
    {ηθ₃ : (f ⊗ f₁) ⊗ f₂ ⟶ (f ⊗ g₁) ⊗ g₂}
    (pf_ηθ : η ⊗ θ = ηθ) (pf_ηθ₁ : f ◁ ηθ = ηθ₁)
    (pf_ηθ₂ : ηθ₁ ≫ (α_ _ _ _).inv = ηθ₂) (pf_ηθ₃ : (α_ _ _ _).hom ≫ ηθ₂ = ηθ₃) :
    (f ◁ η) ⊗ θ = ηθ₃ := by
  simp [← pf_ηθ, ← pf_ηθ₁, ← pf_ηθ₂, ← pf_ηθ₃]

theorem evalTensorHomAux'_of_whisker
    {η : f₁ ⟶ g₁} {θ : f₂ ⟶ g₂} {η₁ : f₁ ⊗ f ⟶ g₁ ⊗ f}
    {ηθ : (f₁ ⊗ f) ⊗ f₂ ⟶ (g₁ ⊗ f) ⊗ g₂}
    {η₂ : (f₁ ⊗ f) ⊗ f₂ ⟶ g₁ ⊗ (f ⊗ g₂)}
    {η₃ : f₁ ⊗ (f ⊗ f₂) ⟶ g₁ ⊗ (f ⊗ g₂)}
    (pf_η₁ : η ▷ f = η₁) (pf_ηθ : η₁ ⊗ θ = ηθ)
    (pf_η₂ : ηθ ≫ (α_ _ _ _).hom = η₂) (pf_η₃ : (α_ _ _ _).inv ≫ η₂ = η₃) :
    η ⊗ (f ◁ θ) = η₃ := by
  simp [← pf_η₁, ← pf_ηθ, ← pf_η₂, ← pf_η₃]

theorem evalTensorHomExpr_nil_nil
    (α : f₁ ⟶ g₁) (β : f₂ ⟶ g₂) :
    α ⊗ β = α ⊗ β := by
  simp

theorem evalTensorHomExpr_nil_cons
    (α : f₁ ⟶ g₁) (β : f₂ ⟶ g₂) {η : g₂ ⟶ h} {ηs : h ⟶ i}
    {η₁ : g₁ ⊗ g₂ ⟶ g₁ ⊗ h} {ηs₁ : g₁ ⊗ h ⟶ g₁ ⊗ i}
    {η₂ : g₁ ⊗ g₂ ⟶ g₁ ⊗ i}
    (pf_η₁ : g₁ ◁ η = η₁) (pf_ηs₁ : g₁ ◁ ηs = ηs₁)
    (pf_η₂ : η₁ ≫ ηs₁ = η₂) :
    α ⊗ (β ≫ η ≫ ηs) = (α ⊗ β) ≫ η₂ := by
  simp [← pf_η₁, ← pf_ηs₁, ← pf_η₂, tensorHom_def]

theorem evalTensorHomExpr_cons_nil
    (α : f₁ ⟶ g₁) {η : g₁ ⟶ h} {ηs : h ⟶ i}
    (β : f₂ ⟶ g₂)
    {η₁ : g₁ ⊗ g₂ ⟶ h ⊗ g₂} {ηs₁ : h ⊗ g₂ ⟶ i ⊗ g₂}
    {η₂ : g₁ ⊗ g₂ ⟶ i ⊗ g₂}
    (pf_η₁ : η ▷ g₂ = η₁) (pf_ηs₁ : ηs ▷ g₂ = ηs₁)
    (pf_η₂ : η₁ ≫ ηs₁ = η₂) :
    (α ≫ η ≫ ηs) ⊗ β = (α ⊗ β) ≫ η₂ := by
  simp [← pf_η₁, ← pf_ηs₁, ← pf_η₂, tensorHom_def']

theorem evalTensorHomExpr_cons_cons
    (α : f₁ ⟶ g₁) {η : g₁ ⟶ h₁} {ηs : h₁ ⟶ i₁}
    (β : f₂ ⟶ g₂) {θ : g₂ ⟶ h₂} {θs : h₂ ⟶ i₂}
    {ηθ : g₁ ⊗ g₂ ⟶ h₁ ⊗ h₂} {ηθs : h₁ ⊗ h₂ ⟶ i₁ ⊗ i₂}
    {ηθ₁ : g₁ ⊗ g₂ ⟶ i₁ ⊗ i₂}
    (pf_ηθ : η ⊗ θ = ηθ) (pf_ηθs : ηs ⊗ θs = ηθs)
    (pf_ηθ₁ : ηθ ≫ ηθs = ηθ₁) :
    (α ≫ η ≫ ηs) ⊗ (β ≫ θ ≫ θs) = (α ⊗ β) ≫ ηθ₁ := by
  simp [← pf_ηθ, ← pf_ηθs, ← pf_ηθ₁]

end

/-- Extract a Lean expression from a `Mor₁` expression. -/
def Mor₁.e : Mor₁ → MonoidalM Expr
  | .id => do
    let ctx ← read
    mkAppOptM ``MonoidalCategoryStruct.tensorUnit #[ctx.C, none, none]
  | .comp f g => do
    mkAppM ``MonoidalCategoryStruct.tensorObj #[← Mor₁.e f, ← Mor₁.e g]
  | .of f => return f.e

/-- Extract a Lean expression from a `StructuralAtom` expression. -/
def StructuralAtom.e : StructuralAtom → MonoidalM Expr
  | .associator f g h => do
    mkAppM ``Iso.hom #[← mkAppM ``MonoidalCategoryStruct.associator #[← f.e, ← g.e, ← h.e]]
  | .associatorInv f g h => do
    mkAppM ``Iso.inv #[← mkAppM ``MonoidalCategoryStruct.associator #[← f.e, ← g.e, ← h.e]]
  | .leftUnitor f => do
    mkAppM ``Iso.hom #[← mkAppM ``MonoidalCategoryStruct.leftUnitor #[← f.e]]
  | .leftUnitorInv f => do
    mkAppM ``Iso.inv #[← mkAppM ``MonoidalCategoryStruct.leftUnitor #[← f.e]]
  | .rightUnitor f => do
    mkAppM ``Iso.hom #[← mkAppM ``MonoidalCategoryStruct.rightUnitor #[← f.e]]
  | .rightUnitorInv f => do
    mkAppM ``Iso.inv #[← mkAppM ``MonoidalCategoryStruct.rightUnitor #[← f.e]]
  | .monoidalCoherence f g e => do
    mkAppOptM ``MonoidalCoherence.hom #[none, none, ← f.e, ← g.e, e]

/-- Extract a Lean expression from a `Structural` expression. -/
partial def Structural.e : Structural → MonoidalM Expr
  | .atom α => α.e
  | .id f => do mkAppM ``CategoryStruct.id #[← f.e]
  | .comp α β => do match α, β with
    | _, _ => mkAppM ``CategoryStruct.comp #[← α.e, ← β.e]
  | .whiskerLeft f α => do mkAppM ``MonoidalCategoryStruct.whiskerLeft #[← f.e, ← α.e]
  | .whiskerRight α f => do mkAppM ``MonoidalCategoryStruct.whiskerRight #[← α.e, ← f.e]
  | .tensorHom α β => do mkAppM ``MonoidalCategoryStruct.tensorHom #[← α.e, ← β.e]

/-- Extract a Lean expression from a `WhiskerRightExpr` expression. -/
def WhiskerRightExpr.e : WhiskerRightExpr → MonoidalM Expr
  | WhiskerRightExpr.of η => return η.e
  | WhiskerRightExpr.whisker η f => do
    mkAppM ``MonoidalCategoryStruct.whiskerRight #[← η.e, f.e]

/-- Extract a Lean expression from a `TensorHomExpr` expression. -/
def TensorHomExpr.e : TensorHomExpr → MonoidalM Expr
  | TensorHomExpr.of η => η.e
  | TensorHomExpr.cons η ηs => do
    mkAppM ``MonoidalCategoryStruct.tensorHom #[← η.e, ← ηs.e]

/-- Extract a Lean expression from a `WhiskerLeftExpr` expression. -/
def WhiskerLeftExpr.e : WhiskerLeftExpr → MonoidalM Expr
  | WhiskerLeftExpr.of η => η.e
  | WhiskerLeftExpr.whisker f η => do
    mkAppM ``MonoidalCategoryStruct.whiskerLeft #[f.e, ← η.e]

/-- Extract a Lean expression from a `NormalExpr` expression. -/
def NormalExpr.e : NormalExpr → MonoidalM Expr
  | NormalExpr.nil α => α.e
  | NormalExpr.cons α η θ => do
    mkAppM ``CategoryStruct.comp #[← α.e, ← mkAppM ``CategoryStruct.comp #[← η.e, ← θ.e]]

/-- The result of evaluating an expression into normal form. -/
structure Result where
  /-- The normalized expression of the 2-morphism. -/
  expr : NormalExpr
  /-- The proof that the normalized expression is equal to the original expression. -/
  proof : Expr

open scoped MonoidalCategory

mutual

/-- Evaluate the expression `η ≫ θ` into a normalized form. -/
partial def evalComp : NormalExpr → NormalExpr → MonoidalM Result
  | .nil α, .cons β η ηs => do
    let η' := .cons (α.comp β) η ηs
    try return ⟨η', ← mkAppM ``evalComp_nil_cons #[← α.e, ← β.e, ← η.e, ← ηs.e]⟩
    catch e => throw e return ⟨η', mkConst ``True⟩
  | .nil α, .nil α' => do
    try return ⟨.nil (α.comp α'), ← mkAppM ``evalComp_nil_nil #[← α.e, ← α'.e]⟩
    catch _ => return ⟨.nil (α.comp α'), mkConst ``True⟩
  | .cons α η ηs, θ => do
    let ⟨ι, pf_ι⟩ ← evalComp ηs θ
    let ι' := .cons α η ι
    try return ⟨ι', ← mkAppM ``evalComp_cons #[← α.e, ← η.e, pf_ι]⟩
    catch _ => return ⟨ι', mkConst ``True⟩

/-- Evaluate the expression `f ◁ η` into a normalized form. -/
partial def evalWhiskerLeftExpr : Mor₁ → NormalExpr → MonoidalM Result
  | f, .nil α => do
    try return ⟨.nil (.whiskerLeft f α), ← mkAppM ``evalWhiskerLeft_nil #[← f.e, ← α.e]⟩
    catch _ => return ⟨.nil (.whiskerLeft f α), mkConst ``True⟩
  | .of f, .cons α η ηs => do
    let η' := WhiskerLeftExpr.whisker f η
    let ⟨θ, pf_θ⟩ ← evalWhiskerLeftExpr (.of f) ηs
    let η'' := .cons (.whiskerLeft (.of f) α) η' θ
    try return ⟨η'', ← mkAppM ``evalWhiskerLeft_of_cons #[← α.e, ← η.e, pf_θ]⟩
    catch _ => return ⟨η'', mkConst ``True⟩
  | .comp f g, η => do
    let ⟨θ, pf_θ⟩ ← evalWhiskerLeftExpr g η
    let ⟨ι, pf_ι⟩ ← evalWhiskerLeftExpr f θ
    let h := η.src
    let h' := η.tar
    let ⟨ι', pf_ι'⟩ ← evalComp ι (NormalExpr.associatorInv f g h')
    let ⟨ι'', pf_ι''⟩ ← evalComp (NormalExpr.associator f g h) ι'
    try return ⟨ι'', ← mkAppM ``evalWhiskerLeft_comp #[pf_θ, pf_ι, pf_ι', pf_ι'']⟩
    catch _ => return ⟨ι'', mkConst ``True⟩
  | .id, η => do
    let f := η.src
    let g := η.tar
    let ⟨η', pf_η'⟩ ← evalComp η (NormalExpr.leftUnitorInv g)
    let ⟨η'', pf_η''⟩ ← evalComp (NormalExpr.leftUnitor f) η'
    try return ⟨η'', ← mkAppM ``evalWhiskerLeft_id #[pf_η', pf_η'']⟩
    catch _ => return ⟨η'', mkConst ``True⟩

/-- Evaluate the expression `η ▷ f` into a normalized form. -/
partial def evalWhiskerRightExprAux : TensorHomExpr → Atom₁ → MonoidalM Result
  | .of η, f => do
    -- let ⟨θ, pf_θ⟩ ← evalWhiskerRightExpr ηs (.of f)
    -- let η' := .cons (.whiskerRight α (.of f)) (.of (.whisker η f)) θ
    -- try return ⟨η', ← mkAppM ``evalWhiskerRight_cons_of_of #[← α.e, ← η.e, pf_θ]⟩
    -- catch _ => return ⟨η', mkConst ``True⟩
    let η ← NormalExpr.of <| .of <| .of <| .whisker η f
    try return ⟨η, ← mkAppM ``eval_of #[← η.e]⟩
    catch _ => return ⟨η, mkConst ``True⟩
  | .cons η ηs, f => do
    let ⟨ηs', pf_ηs'⟩ ← evalWhiskerRightExprAux ηs f
    let ⟨η₁, pf_η₁⟩ ← evalTensorHomExpr (← NormalExpr.of <| .of <| .of η) ηs'
    let ⟨η₂, pf_η₂⟩ ← evalComp η₁ (.associatorInv (← η.tar) (← ηs.tar) (.of f))
    let ⟨η₃, pf_η₃⟩ ← evalComp (.associator (← η.src) (← ηs.src) (.of f)) η₂
    try return ⟨η₃, ← mkAppM ``eval_evalWhiskerRightExprAux_cons #[pf_ηs', pf_η₁, pf_η₂, pf_η₃]⟩
    catch _ => return ⟨η₃, mkConst ``True⟩

/-- Evaluate the expression `η ▷ f` into a normalized form. -/
partial def evalWhiskerRightExpr : NormalExpr → Mor₁ → MonoidalM Result
  | .nil α, h => do
    try return ⟨.nil (.whiskerRight α h), ← mkAppM ``evalWhiskerRight_nil #[← α.e, ← h.e]⟩
    catch _ => return ⟨.nil (.whiskerRight α h), mkConst ``True⟩
  | .cons α (.of η) ηs, .of f => do
    /-
    let ηs₁ ← evalWhiskerRightExpr ηs (.of f)
    let η₁ ← evalWhiskerRightExprAux η f
    let η₂ ← evalComp η₁ ηs₁
    let η₃ ← NormalExpr.ofNormalExpr (.whiskerRight α (.of f)) η₂
    -/
    let ⟨ηs₁, pf_ηs₁⟩ ← evalWhiskerRightExpr ηs (.of f)
    let ⟨η₁, pf_η₁⟩ ← evalWhiskerRightExprAux η f
    let ⟨η₂, pf_η₂⟩ ← evalComp η₁ ηs₁
    let η₃ ← NormalExpr.ofNormalExpr (.whiskerRight α (.of f)) η₂

    -- let ⟨θ, pf_θ⟩ ← evalWhiskerRightExpr ηs (.of f)
    -- let η' := .cons (.whiskerRight α (.of f)) (.of (.whisker η f)) θ
    try return ⟨η₃, ← mkAppM ``evalWhiskerRight_cons_of_of #[← α.e, pf_ηs₁, pf_η₁, pf_η₂]⟩
    catch _ => return ⟨η₃, mkConst ``True⟩
  | .cons α (.whisker f η) ηs, h => do
    let g ← η.src
    let g' ← η.tar
    let ⟨η₁, pf_η₁⟩ ← evalWhiskerRightExpr (.cons (.id g) η (.nil (.id g'))) h
    let ⟨η₂, pf_η₂⟩ ← evalWhiskerLeftExpr (.of f) η₁
    let ⟨ηs₁, pf_ηs₁⟩ ← evalWhiskerRightExpr ηs h
    let α' := .whiskerRight α h
    let ⟨ηs₂, pf_ηs₂⟩ ← evalComp (.associatorInv (.of f) g' h) ηs₁
    let ⟨η₃, pf_η₃⟩ ← evalComp η₂ ηs₂
    let ⟨η₄, pf_η₄⟩ ← evalComp (.associator (.of f) g h) η₃
    let ⟨η₅, pf_η₅⟩ ← evalComp (.nil α') η₄
    try return ⟨η₅,
      ← mkAppM ``evalWhiskerRight_cons_whisker
        #[pf_η₁, pf_η₂, pf_ηs₁, pf_ηs₂, pf_η₃, pf_η₄, pf_η₅]⟩
    catch _ => return ⟨η₅, mkConst ``True⟩
  | η, .comp g h => do
    let ⟨η₁, pf_η₁⟩ ← evalWhiskerRightExpr η g
    let ⟨η₂, pf_η₂⟩ ← evalWhiskerRightExpr η₁ h
    let f := η.src
    let f' := η.tar
    let ⟨η₃, pf_η₃⟩ ← evalComp η₂ (.associator f' g h)
    let ⟨η₄, pf_η₄⟩ ← evalComp (.associatorInv f g h) η₃
    try return ⟨η₄, ← mkAppM ``evalWhiskerRight_comp #[pf_η₁, pf_η₂, pf_η₃, pf_η₄]⟩
    catch _ => return ⟨η₄, mkConst ``True⟩
  | η, .id => do
    let f := η.src
    let g := η.tar
    let ⟨η₁, pf_η₁⟩ ← evalComp η (.rightUnitorInv g)
    let ⟨η₂, pf_η₂⟩ ← evalComp (.rightUnitor f) η₁
    try return ⟨η₂, ← mkAppM ``evalWhiskerRight_id #[pf_η₁, pf_η₂]⟩
    catch _ => return ⟨η₂, mkConst ``True⟩

/-- Evaluate the expression `η ⊗ θ` into a normalized form. -/
partial def evalTensorHomAux : TensorHomExpr → TensorHomExpr → MonoidalM Result
  | .of η, θ =>
    try return ⟨← NormalExpr.of <| .of <| .cons η θ, ← mkAppM ``eval_of #[← η.e]⟩
    catch _ => return ⟨← NormalExpr.of <| .of <| .cons η θ, mkConst ``True⟩
    -- NormalExpr.of <| .of <| .cons η θ
  | .cons η ηs, θ => do
    let α := NormalExpr.associator (← η.src) (← ηs.src) (← θ.src)
    let α' := NormalExpr.associatorInv (← η.tar) (← ηs.tar) (← θ.tar)
    -- let ηθ ← evalTensorHomAux ηs θ
    -- let η₁ ← evalTensorHomExpr (← NormalExpr.of <| .of <| .of η) ηθ
    -- let ηθ₁ ← evalComp η₁ α'
    -- let ηθ₂ ← evalComp α ηθ₁
    let ⟨ηsθ, pf_ηsθ⟩ ← evalTensorHomAux ηs θ
    let ⟨η₁, pf_η₁⟩ ← evalTensorHomExpr (← NormalExpr.of <| .of <| .of η) ηsθ
    let ⟨ηθ₁, pf_ηθ₁⟩ ← evalComp η₁ α'
    let ⟨ηθ₂, pf_ηθ₂⟩ ← evalComp α ηθ₁
    try return ⟨ηθ₂, ← mkAppM ``evalTensorHomAux_cons #[pf_ηsθ, pf_η₁, pf_ηθ₁, pf_ηθ₂]⟩
    catch _ => return ⟨ηθ₂, mkConst ``True⟩

/-- Evaluate the expression `η ⊗ θ` into a normalized form. -/
partial def evalTensorHomAux' : WhiskerLeftExpr → WhiskerLeftExpr → MonoidalM Result
  | .of η, .of θ => evalTensorHomAux η θ
  | .whisker f η, θ => do
    -- let ηθ ← evalTensorHomAux' η θ
    -- let ηθ₁ ← evalWhiskerLeftExpr (.of f) ηθ
    -- let ηθ₂ ← evalComp ηθ₁ (.associatorInv (.of f) (← η.tar) (← θ.tar))
    -- let ηθ₃ ← evalComp (.associator (.of f) (← η.src) (← θ.src)) ηθ₂
    let ⟨ηθ, pf_ηθ⟩ ← evalTensorHomAux' η θ
    let ⟨ηθ₁, pf_ηθ₁⟩ ← evalWhiskerLeftExpr (.of f) ηθ
    let ⟨ηθ₂, pf_ηθ₂⟩ ← evalComp ηθ₁ (.associatorInv (.of f) (← η.tar) (← θ.tar))
    let ⟨ηθ₃, pf_ηθ₃⟩ ← evalComp (.associator (.of f) (← η.src) (← θ.src)) ηθ₂
    try return ⟨ηθ₃, ← mkAppM ``evalTensorHomAux'_whisker #[pf_ηθ, pf_ηθ₁, pf_ηθ₂, pf_ηθ₃]⟩
    catch _ => return ⟨ηθ₃, mkConst ``True⟩
    -- return ηθ₃
  | .of η, .whisker f θ => do
    -- let η₁ ← evalWhiskerRightExprAux η f
    -- let ηθ ← evalTensorHomExpr η₁ (← NormalExpr.of θ)
    -- let ηθ₁ ← evalComp ηθ (.associator (← η.tar) (.of f) (← θ.tar))
    -- let ηθ₂ ← evalComp (.associatorInv (← η.src) (.of f) (← θ.src)) ηθ₁
    let ⟨η₁, pf_η₁⟩ ← evalWhiskerRightExprAux η f
    let ⟨ηθ, pf_ηθ⟩ ← evalTensorHomExpr η₁ (← NormalExpr.of θ)
    let ⟨ηθ₁, pf_ηθ₁⟩ ← evalComp ηθ (.associator (← η.tar) (.of f) (← θ.tar))
    let ⟨ηθ₂, pf_ηθ₂⟩ ← evalComp (.associatorInv (← η.src) (.of f) (← θ.src)) ηθ₁
    try return ⟨ηθ₂, ← mkAppM ``evalTensorHomAux'_of_whisker #[pf_η₁, pf_ηθ, pf_ηθ₁, pf_ηθ₂]⟩
    catch _ => return ⟨ηθ₂, mkConst ``True⟩

/-- Evaluate the expression `η ⊗ θ` into a normalized form. -/
partial def evalTensorHomExpr : NormalExpr → NormalExpr → MonoidalM Result
  | .nil α, .nil β => do
    try return ⟨.nil (α.tensorHom β), ← mkAppM ``evalTensorHomExpr_nil_nil #[← α.e, ← β.e]⟩
    catch _ => return ⟨.nil (α.tensorHom β), mkConst ``True⟩
    -- return .nil (α.tensorHom β)
  | .nil α, .cons β η ηs => do
    -- let η₁ ← evalWhiskerLeftExpr α.tar (← NormalExpr.of η)
    -- let ηs₁ ← evalWhiskerLeftExpr α.tar ηs
    -- let η₂ ← evalComp η₁ ηs₁
    -- let η₃ ← NormalExpr.ofNormalExpr (α.tensorHom β) η₂
    let ⟨η₁, pf_η₁⟩ ← evalWhiskerLeftExpr α.tar (← NormalExpr.of η)
    let ⟨ηs₁, pf_ηs₁⟩ ← evalWhiskerLeftExpr α.tar ηs
    let ⟨η₂, pf_η₂⟩ ← evalComp η₁ ηs₁
    let η₃ ← NormalExpr.ofNormalExpr (α.tensorHom β) η₂
    try return ⟨η₃, ← mkAppM ``evalTensorHomExpr_nil_cons #[← α.e, pf_η₁, pf_ηs₁, pf_η₂]⟩
    catch _ => return ⟨η₃, mkConst ``True⟩
    -- return η₃
  | .cons α η ηs, .nil β => do
    -- let η₁ ← evalWhiskerRightExpr (← NormalExpr.of η) β.tar
    -- let ηs₁ ← evalWhiskerRightExpr ηs β.tar
    -- let η₂ ← evalComp η₁ ηs₁
    -- let η₃ ← NormalExpr.ofNormalExpr (α.tensorHom β) η₂
    let ⟨η₁, pf_η₁⟩ ← evalWhiskerRightExpr (← NormalExpr.of η) β.tar
    let ⟨ηs₁, pf_ηs₁⟩ ← evalWhiskerRightExpr ηs β.tar
    let ⟨η₂, pf_η₂⟩ ← evalComp η₁ ηs₁
    let η₃ ← NormalExpr.ofNormalExpr (α.tensorHom β) η₂
    try return ⟨η₃, ← mkAppM ``evalTensorHomExpr_cons_nil #[← α.e, pf_η₁, pf_ηs₁, pf_η₂]⟩
    catch _ => return ⟨η₃, mkConst ``True⟩
    -- return η₃
  | .cons α η ηs, .cons β θ θs => do
    -- let ηθ ← evalTensorHomAux' η θ
    -- let ηθs ← evalTensorHomExpr ηs θs
    -- let ηθ₁ ← evalComp ηθ ηθs
    -- let ηθ₂ ← NormalExpr.ofNormalExpr (α.tensorHom β) ηθ₁
    let ⟨ηθ, pf_ηθ⟩ ← evalTensorHomAux' η θ
    let ⟨ηθs, pf_ηθs⟩ ← evalTensorHomExpr ηs θs
    let ⟨ηθ₁, pf_ηθ₁⟩ ← evalComp ηθ ηθs
    let ηθ₂ ← NormalExpr.ofNormalExpr (α.tensorHom β) ηθ₁
    try return ⟨ηθ₂, ← mkAppM ``evalTensorHomExpr_cons_cons #[← α.e, ← β.e, pf_ηθ, pf_ηθs, pf_ηθ₁]⟩
    catch _ => return ⟨ηθ₂, mkConst ``True⟩
    -- return ηθ₂

end

/-- Evaluate the expression of a 2-morphism into a normalized form. -/
partial def eval (e : Expr) : MonoidalM Result := do
  if let .some α ← structuralAtom? e then
    try return ⟨.nil <| .atom α, ← mkEqRefl (← α.e)⟩
    catch _ => return ⟨.nil <| .atom α, mkConst ``True⟩
  else
    match (← whnfR e).getAppFnArgs with
    | (``CategoryStruct.id, #[_, _, f]) =>
      try return ⟨.nil (.id (← toMor₁ f)), ← mkEqRefl (← mkAppM ``CategoryStruct.id #[f])⟩
      catch _ => return ⟨.nil (.id (← toMor₁ f)), mkConst ``True⟩
    | (``CategoryStruct.comp, #[_, _, _, _, _, η, θ]) =>
      let ⟨η_e, pf_η⟩ ← eval η
      let ⟨θ_e, pf_θ⟩ ← eval θ
      let ⟨ηθ, pf⟩ ← evalComp η_e θ_e
      try return ⟨ηθ, ← mkAppM ``eval_comp #[pf_η, pf_θ, pf]⟩
      catch _ => return ⟨ηθ, mkConst ``True⟩
    | (``MonoidalCategoryStruct.whiskerLeft, #[_, _, _, f, _, _, η]) =>
      let ⟨η_e, pf_η⟩ ← eval η
      let ⟨θ, pf_θ⟩ ← evalWhiskerLeftExpr (← toMor₁ f) η_e
      try return ⟨θ, ← mkAppM ``eval_whiskerLeft #[pf_η, pf_θ]⟩
      catch _ => return ⟨θ, mkConst ``True⟩
    | (``MonoidalCategoryStruct.whiskerRight, #[_, _, _, _, _, η, h]) =>
      let ⟨η_e, pf_η⟩ ← eval η
      let ⟨θ, pf_θ⟩ ← evalWhiskerRightExpr η_e (← toMor₁ h)
      try return ⟨θ, ← mkAppM ``eval_whiskerRight #[pf_η, pf_θ]⟩
      catch _ => return ⟨θ, mkConst ``True⟩
    | (``MonoidalCategoryStruct.tensorHom, #[_, _, _, _, _, _, _, η, θ]) =>
      let ⟨η_e, pf_η⟩ ← eval η
      let ⟨θ_e, pf_θ⟩ ← eval θ
      let ⟨ηθ, pf⟩ ← evalTensorHomExpr η_e θ_e
      try return ⟨ηθ, ← mkAppM ``eval_tensorHom #[pf_η, pf_θ, pf]⟩
      catch _ => return ⟨ηθ, mkConst ``True⟩
      -- evalTensorHomExpr (← eval η) (← eval θ)
    | (``monoidalComp, #[C, _, _, _, _, _, _, η, θ]) =>
      let ⟨η_e, pf_η⟩ ← eval η
      let α₀ ← structuralOfMonoidalComp C e
      let α := NormalExpr.nil <| .atom α₀
      let ⟨θ_e, pf_θ⟩ ← eval θ
      let ⟨αθ, pf_θα⟩ ← evalComp α θ_e
      let ⟨ηαθ, pf_ηαθ⟩ ← evalComp η_e αθ
      try return ⟨ηαθ, ← mkAppM ``eval_monoidalComp #[pf_η, pf_θ, pf_θα, pf_ηαθ]⟩
      catch _ => return ⟨ηαθ, mkConst ``True⟩
    | _ =>
      try return ⟨← NormalExpr.ofExpr e, ← mkAppM ``eval_of #[e]⟩
      catch _ => return ⟨← NormalExpr.ofExpr e, mkConst ``True⟩

/-- Convert a `NormalExpr` expression into a list of `WhiskerLeftExpr` expressions. -/
def NormalExpr.toList : NormalExpr → List WhiskerLeftExpr
  | NormalExpr.nil _ => []
  | NormalExpr.cons _ η ηs => η :: NormalExpr.toList ηs

/-- `normalize% η` is the normalization of the 2-morphism `η`. It is of the form
`α₀ ≫ η₀ ≫ α₁ ≫ η₁ ≫ ... αₙ ≫ ηₙ ≫ αₙ₊₁`, where `αᵢ` are structural 2-morphisms
and `ηᵢ` are non-structural 2-morphisms. -/
elab "normalize% " t:term:51 : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  MonoidalM.run (← mkContext e) do (← eval e).expr.e

theorem mk_eq {α : Type _} (a b a' b' : α) (ha : a = a') (hb : b = b') (h : a' = b') : a = b := by
  simp [h, ha, hb]

universe v u

theorem mk_eq_of_cons {C : Type u} [CategoryStruct.{v} C]
    {f₁ f₂ f₃ f₄ : C}
    -- {α α' : f₁ ⟶ f₂} {η η' : f₂ ⟶ f₃} {ηs ηs' : f₃ ⟶ f₄}
    -- copy the same variables
    (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs ηs' : f₃ ⟶ f₄)
    (pf_α : α = α') (pf_η : η = η') (pf_ηs : ηs = ηs') :
    α ≫ η ≫ ηs = α' ≫ η' ≫ ηs' := by
  simp [pf_α, pf_η, pf_ηs]

open Lean Elab Meta Tactic

/-- Transform an equality between 2-morphisms into the equality between their normalizations. -/
def mkEqOfHom₂ (mvarId : MVarId) : MetaM Expr := do
  let some (_, e₁, e₂) := (← whnfR <| ← mvarId.getType).eq?
    | throwError "monoidal_nf requires an equality goal"
  MonoidalM.run (← mkContext e₁) do
    let ⟨e₁', p₁⟩ ← eval e₁
    let ⟨e₂', p₂⟩ ← eval e₂
    mkAppM ``mk_eq #[e₁, e₂, ← e₁'.e, ← e₂'.e, p₁, p₂]

def mkApply (mvarId : MVarId) : MetaM (List MVarId) := do
  let e ← mvarId.getType
  -- let error := throwError "monoidal_nf requires an equality goal"
  let some (_, e₁, e₂) := (← whnfR e).eq? | throwError "monoidal_nf requires an equality goal"
  match e₁.getAppFnArgs, e₂.getAppFnArgs with
  | (``CategoryStruct.comp, #[_, _, _, _, _, α, η]) , (``CategoryStruct.comp, #[_, _, _, _, _, α', η']) =>
    match η.getAppFnArgs, η'.getAppFnArgs with
    | (``CategoryStruct.comp, #[_, _, _, _, _, η, ηs]), (``CategoryStruct.comp, #[_, _, _, _, _, η', ηs']) =>
      let pf_α ← mkFreshExprMVar (← mkEq α α')
      let pf_η ← mkAppM ``Eq.refl #[η]
      let pf_ηs ← mkFreshExprMVar (← mkEq ηs ηs')
      let x ← mvarId.apply (← mkAppM ``mk_eq_of_cons #[α, α', η, η', ηs, ηs', pf_α, pf_η, pf_ηs])
      return x
    | _, _ => throwError "monoidal_nf requires an equality goal"
  | _, _ => throwError "monoidal_nf requires an equality goal"

/-- Returns `𝟙_ C` if the expression `e` is of the form `𝟙_ C`. -/
def liftTensorUnit? (e : Expr) : MetaM (Option Expr) := do
  let C ← mkFreshExprMVar none
  let instC ← mkFreshExprMVar none
  let instMC ← mkFreshExprMVar none
  let unit := mkAppN (← mkConstWithFreshMVarLevels
    ``MonoidalCategoryStruct.tensorUnit) #[C, instC, instMC]
  if ← withDefault <| isDefEq e unit then
    mkAppOptM ``FreeMonoidalCategory.unit #[← instantiateMVars C]
  else
    return none

mutual

/-- Returns `(f, g)` if the expression `e` is of the form `f ⊗ g`. -/
partial def liftTensorObj? (e : Expr) : MetaM (Option (Expr)) := do
  let C ← mkFreshExprMVar none
  let f ← mkFreshExprMVar C
  let g ← mkFreshExprMVar C
  let instC ← mkFreshExprMVar none
  let instMC ← mkFreshExprMVar none
  let fg := mkAppN (← mkConstWithFreshMVarLevels
    ``MonoidalCategoryStruct.tensorObj) #[C, instC, instMC, f, g]
  if ← withDefault <| isDefEq e fg then
    mkAppM ``MonoidalCategory.tensorObj #[← lift₁ (← instantiateMVars f), ← lift₁ (← instantiateMVars g)]
  else
    return none

partial def lift₁ (e : Expr) : MetaM Expr := do
  if let some e ← liftTensorUnit? e then
    return e
  else if let some e ← liftTensorObj? e then
    return e
  else
    mkAppM ``FreeMonoidalCategory.of #[e]

end

partial def liftStructuralAtom? (e : Expr) : MetaM (Option Expr) := do
  match e.getAppFnArgs with
  | (``Iso.hom, #[_, _, _, _, η]) =>
    match (← whnfR η).getAppFnArgs with
    | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) =>
      return some <| ← mkAppM ``Iso.hom #[← mkAppM ``MonoidalCategory.associator #[← lift₁ f, ← lift₁ g, ← lift₁ h]]
    | (``MonoidalCategoryStruct.leftUnitor, #[_, _, _, f]) =>
      return some <| ← mkAppM ``Iso.hom #[← mkAppM ``MonoidalCategory.leftUnitor #[← lift₁ f]]
    | (``MonoidalCategoryStruct.rightUnitor, #[_, _, _, f]) =>
      return some <| ← mkAppM ``Iso.hom #[← mkAppM ``MonoidalCategory.rightUnitor #[← lift₁ f]]
    | _ => return none
  | (``Iso.inv, #[_, _, _, _, η]) =>
    match (← whnfR η).getAppFnArgs with
    | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) =>
      return some <| ← mkAppM ``Iso.inv #[← mkAppM ``MonoidalCategory.associator #[← lift₁ f, ← lift₁ g, ← lift₁ h]]
    | (``MonoidalCategoryStruct.leftUnitor, #[_, _, _, f]) =>
      return some <| ← mkAppM ``Iso.inv #[← mkAppM ``MonoidalCategory.leftUnitor #[← lift₁ f]]
    | (``MonoidalCategoryStruct.rightUnitor, #[_, _, _, f]) =>
      return some <| ← mkAppM ``Iso.inv #[← mkAppM ``MonoidalCategory.rightUnitor #[← lift₁ f]]
    | _ => return none
  | _ => match (← whnfR e).getAppFnArgs with
    | _ => return none

open MonoidalCoherence in
def monoidalCompHomSimps : MetaM Simp.Context := do
  Simp.Context.ofNames (simpOnly := true) [
    ``refl_hom, ``whiskerLeft_hom, ``whiskerRight_hom,
    ``tensor_right_hom, ``tensor_right'_hom, ``left_hom, ``left'_hom,
    ``right_hom, ``right'_hom, ``assoc_hom, ``assoc'_hom]

partial def free₂ (e : Expr) : MetaM Expr := do
  let error : MetaM Expr := throwError "{e} is not a structural 2-morphism  ddd"
  if let some e ← liftStructuralAtom? e then
    return e
  else
    match (← whnfR e).getAppFnArgs with
    | (``CategoryStruct.comp, #[_, _, _, _, _, η, θ]) =>
      mkAppM ``CategoryStruct.comp #[← free₂ η, ← free₂ θ]
    | (``MonoidalCategory.whiskerLeft, #[_, _, _, f, _, _, η]) =>
      mkAppM ``MonoidalCategory.whiskerLeft #[← lift₁ f, ← free₂ η]
    | (``MonoidalCategory.whiskerRight, #[_, _, _, _, _, η, h]) =>
      mkAppM ``MonoidalCategory.whiskerRight #[← free₂ η, ← lift₁ h]
    | (``CategoryStruct.id, #[_, _, f]) =>
      mkAppM ``CategoryStruct.id #[← lift₁ f]
    | (``MonoidalCategoryStruct.tensorHom, #[_, _, _, _, _, _, _, η, θ]) =>
      mkAppM ``MonoidalCategoryStruct.tensorHom #[← free₂ η, ← free₂ θ]
    | (``MonoidalCoherence.hom, #[_, _, f, g, inst]) =>
      -- IO.println (← ppExpr e)
      let (e', _) ← dsimp e (← monoidalCompHomSimps)
      -- IO.println (← ppExpr e')
      free₂ e'
    | (``monoidalComp, #[C, _, _, _, _, _, inst, η, θ]) =>
        -- let η_e ← free₂ η
        -- let α₀ ← structuralOfMonoidalComp C e
        -- let α := NormalExpr.nil α₀
        -- let θ_e ← free₂ θ
        let α ← mkAppOptM ``MonoidalCoherence.hom #[none, none, none, none, inst]
        let αθ ← mkAppM ``CategoryStruct.comp #[α, θ]
        let ηαθ ← mkAppM ``CategoryStruct.comp #[η, αθ]
        free₂ ηαθ
        -- let ⟨αθ, pf_θα⟩ ← evalComp α θ_e
        -- let ⟨ηαθ, pf_ηαθ⟩ ← evalComp η_e αθ
        -- try return ⟨ηαθ, ← mkAppM ``eval_monoidalComp #[pf_η, pf_θ, pf_θα, pf_ηαθ]⟩
        -- catch _ => return ⟨ηαθ, mkConst ``True⟩
    | _ => error

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

def FreeMonoidalCategory.liftHom {a b : FreeMonoidalCategory C} (f : a ⟶ b) :=
  (FreeMonoidalCategory.project (id : C → C)).map f

def mkFreeExpr (e : Expr) : MetaM Expr := do
  mkAppM ``FreeMonoidalCategory.liftHom #[← free₂ e]

def pure_coherence (g : MVarId) : MetaM Unit := g.withContext do
  let ty ← g.getType
  let some (_, lhs, rhs) := (← whnfR ty).eq? | throwError "not an equality"
  let lift_lhs ← mkFreeExpr lhs
  let lift_rhs ← mkFreeExpr rhs
  let g₁ ← g.change (← mkEq lift_lhs lift_rhs)
  -- IO.println (← ppExpr (← g₁.getType))
  let [g₂] ← g₁.applyConst ``congrArg | throwError "apply congrArg failed"
  let [] ← g₂.applyConst ``Subsingleton.elim | throwError "apply Subsingleton.elim failed"

def monoidal (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let mvarId ← g.apply (← mkEqOfHom₂ g)
  let mvarIds' ← repeat' (fun i ↦ mkApply i) mvarId
  -- let mvarIds'' ← mvarIds'.mapM fun mvarId => do
  --   pure_coherence mvarId
  --   return mvarId
  return mvarIds'

/-- Normalize the both sides of an equality. -/
elab "monoidal_nf" : tactic => withMainContext do
  replaceMainGoal (← monoidal (← getMainGoal))

elab "pure_coherence" : tactic => withMainContext do
  let g ← getMainGoal
  pure_coherence g
  replaceMainGoal [g]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {X Y Z W U V W : C} (f : X ⟶ Y) (g : Y ⟶ Z)

example {X₁ Y₁ X₂ Y₂ : C} (Z : C) (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (Z ◁ f) ⊗ g = (α_ _ _ _).hom ≫ Z ◁ (f ⊗ g) ≫ (α_ _ _ _).inv := by
  monoidal_nf

open MonoidalCategory
#check (⊗𝟙 : V ⊗ W ⊗ X ⟶ (V ⊗ W) ⊗ X)

#whnfR (⊗𝟙 : V ⊗ W ⊗ X ⟶ (V ⊗ W) ⊗ X)

set_option trace.profiler true in
example (X₁ X₂ : C) (f : X₁ ⟶ X₁) (g : X₂ ⟶ X₂) :
  (α_ (𝟙_ C) (𝟙_ C) (X₁ ⊗ X₂)).hom ≫
    (𝟙 (𝟙_ C) ⊗ (α_ (𝟙_ C) X₁ X₂).inv) ≫
      (𝟙 (𝟙_ C) ⊗ (λ_ _).hom ≫ (ρ_ X₁).inv ⊗ 𝟙 X₂) ≫
        (𝟙 (𝟙_ C) ⊗ (α_ X₁ (𝟙_ C) X₂).hom) ⊗≫
          (α_ (𝟙_ C) X₁ (𝟙_ C ⊗ X₂)).inv ≫
            ((λ_ X₁).hom ≫ (ρ_ X₁).inv ⊗ 𝟙 (𝟙_ C ⊗ X₂)) ⊗≫
              f ▷ X₂ ⊗≫
              (α_ X₁ (𝟙_ C) (𝟙_ C ⊗ X₂)).hom ≫
                (𝟙 X₁ ⊗ 𝟙 (𝟙_ C) ⊗ (λ_ X₂).hom ≫ (ρ_ X₂).inv) ≫
                  (𝟙 X₁ ⊗ (α_ (𝟙_ C) X₂ (𝟙_ C)).inv) ⊗≫
                    X₁ ◁ g ⊗≫
                    (𝟙 X₁ ⊗ (λ_ X₂).hom ≫ (ρ_ X₂).inv ⊗ 𝟙 (𝟙_ C)) ≫
                      (𝟙 X₁ ⊗ (α_ X₂ (𝟙_ C) (𝟙_ C)).hom) ≫
                        (α_ X₁ X₂ (𝟙_ C ⊗ 𝟙_ C)).inv =
  (((λ_ (𝟙_ C)).hom ⊗ 𝟙 (X₁ ⊗ X₂)) ≫ (λ_ (X₁ ⊗ X₂)).hom ≫ (ρ_ (X₁ ⊗ X₂)).inv) ⊗≫ f ▷ X₂ ⊗≫
    X₁ ◁ g ⊗≫
    (𝟙 (X₁ ⊗ X₂) ⊗ (λ_ (𝟙_ C)).inv) := by
  simp only [id_tensorHom, tensorHom_id]
  monoidal_nf

set_option trace.profiler true in
example (X₁ X₂ : C) :
  (α_ (𝟙_ C) (𝟙_ C) (X₁ ⊗ X₂)).hom ≫
    (𝟙 (𝟙_ C) ⊗ (α_ (𝟙_ C) X₁ X₂).inv) ≫
      (𝟙 (𝟙_ C) ⊗ (λ_ _).hom ≫ (ρ_ X₁).inv ⊗ 𝟙 X₂) ≫
        (𝟙 (𝟙_ C) ⊗ (α_ X₁ (𝟙_ C) X₂).hom) ⊗≫
          (α_ (𝟙_ C) X₁ (𝟙_ C ⊗ X₂)).inv ≫
            ((λ_ X₁).hom ≫ (ρ_ X₁).inv ⊗ 𝟙 (𝟙_ C ⊗ X₂)) ⊗≫
              (α_ X₁ (𝟙_ C) (𝟙_ C ⊗ X₂)).hom ≫
                (𝟙 X₁ ⊗ 𝟙 (𝟙_ C) ⊗ (λ_ X₂).hom ≫ (ρ_ X₂).inv) ≫
                  (𝟙 X₁ ⊗ (α_ (𝟙_ C) X₂ (𝟙_ C)).inv) ⊗≫
                    (𝟙 X₁ ⊗ (λ_ X₂).hom ≫ (ρ_ X₂).inv ⊗ 𝟙 (𝟙_ C)) ≫
                      (𝟙 X₁ ⊗ (α_ X₂ (𝟙_ C) (𝟙_ C)).hom) ≫
                        (α_ X₁ X₂ (𝟙_ C ⊗ 𝟙_ C)).inv =
  (((λ_ (𝟙_ C)).hom ⊗ 𝟙 (X₁ ⊗ X₂)) ≫ (λ_ (X₁ ⊗ X₂)).hom ≫ (ρ_ (X₁ ⊗ X₂)).inv) ⊗≫
    (𝟙 (X₁ ⊗ X₂) ⊗ (λ_ (𝟙_ C)).inv) := by
  pure_coherence


example (f : U ⟶ V ⊗ (W ⊗ X)) (g : (V ⊗ W) ⊗ X ⟶ Y) :
    f ⊗≫ g = f ≫ 𝟙 _ ≫ (α_ _ _ _).inv ≫ g := by
  dsimp only [monoidalComp]
  dsimp only [MonoidalCoherence.assoc'_hom, MonoidalCoherence.whiskerRight_hom,
    MonoidalCoherence.refl_hom]
  monoidal_nf

example (f : U ⟶ V ⊗ (W ⊗ X)) (g : (V ⊗ W) ⊗ X ⟶ Y) :
    f ⊗≫ g = f ⊗≫ g := by
  monoidal_nf

example : (X ⊗ Y) ◁ f ≫ (X ⊗ Y) ◁ g = (α_ _ _ _).hom ≫ X ◁ Y ◁ f ≫ X ◁ Y ◁ g ≫ (α_ _ _ _).inv := by
  monoidal_nf
  -- · simp
  -- · monoidal_nf
  -- monoidal_coherence
  -- repeat' apply congrArg₂ (· ≫ ·) ?_ <| congrArg₂ (· ≫ ·) rfl ?_
  -- all_goals simp

example : f ≫ g = f ≫ g := by
  monoidal_nf

end Mathlib.Tactic.Monoidal
